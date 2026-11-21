-- Prove2me | solution 1 for MasulloRH.exists_positive_log_profile_rank_discriminator
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:18:51.699823+00:00
-- url     : https://prove2.me/submissions/bd9d4586-e447-44a2-a704-a7de94d8faed

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open Set MeasureTheory

private theorem pw_bump_real_mellin (b : ℝ → ℝ) (hb : Continuous b) (hc : HasCompactSupport b)
    (hz : ∀ t ≤ 1, b t = 0) (a : ℝ) :
    HasMellin (fun t => (b t : ℂ)) (a:ℂ)
      ((∫ t : ℝ, (max t 1)^(a-1) * b t : ℝ):ℂ) := by
  let g := fun t : ℝ => (max t 1)^(a-1) * b t
  have hmax (t : ℝ) : 0 < max t 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hg : Continuous g :=
    ((continuous_id.max continuous_const).rpow_const fun t => Or.inl (hmax t).ne').mul hb
  have hgc : HasCompactSupport g := hc.mul_left
  have heq : EqOn (fun t : ℝ => (t:ℂ)^((a:ℂ)-1) • (b t:ℂ)) (fun t => (g t:ℂ)) (Ioi 0) := by
    intro t ht
    by_cases h : t ≤ 1
    · simp [g,hz t h]
    · simp only [smul_eq_mul,g,max_eq_left (le_of_not_ge h),Complex.ofReal_mul,
          Complex.ofReal_cpow (le_of_lt ht),Complex.ofReal_sub, Complex.ofReal_one]
  have hgr : (∫ t in Ioi (0:ℝ), g t) = ∫ t, g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro t ht
      have ht' : t ≤ 0 := le_of_not_gt ht
      simp [g,hz t (by linarith)])
  refine ⟨(integrableOn_congr_fun heq measurableSet_Ioi).mpr
      (hg.integrable_of_hasCompactSupport hgc).ofReal.integrableOn,?_⟩
  unfold mellin
  rw [setIntegral_congr_fun measurableSet_Ioi heq]
  have hr : (∫ t in Ioi (0:ℝ), (g t:ℂ)) = Complex.ofReal (∫ t in Ioi (0:ℝ), g t) :=
    integral_ofReal (𝕜:=ℂ) (μ:=volume.restrict (Ioi (0:ℝ))) (f:=g)
  exact hr.trans (congrArg Complex.ofReal hgr)

private theorem pw_test_bump :
    ∃ b : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ t : ℝ, t ≤ 5/4 ∨ 7/4 ≤ t → b t = 0) ∧
      (∀ a : ℝ, MellinConvergent (fun t => (b t:ℂ)) (a:ℂ)) ∧
      0 < (mellin (fun t => (b t:ℂ)) (1/2:ℂ)).re := by
  let φ : ContDiffBump (3/2 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  have hz (t : ℝ) (ht : t ≤ 5/4 ∨ 7/4 ≤ t) : φ t = 0 := by
    apply φ.zero_of_le_dist
    change 1/4 ≤ dist t (3/2)
    rw [Real.dist_eq]
    rcases ht with ht | ht
    · linarith [neg_le_abs (t-3/2)]
    · linarith [le_abs_self (t-3/2)]
  have hM (a:ℝ) := pw_bump_real_mellin φ φ.continuous φ.hasCompactSupport
    (fun t ht => hz t (Or.inl (by linarith))) a
  refine ⟨φ,φ.contDiff,φ.hasCompactSupport,hz,fun a => (hM a).1,?_⟩
  have hh := (hM (1/2)).2
  push_cast at hh
  rw [hh,Complex.ofReal_re]
  have hw : Continuous (fun t : ℝ => (max t 1)^((1/2:ℝ)-1)) :=
    (continuous_id.max continuous_const).rpow_const fun t => Or.inl (zero_lt_one.trans_le (le_max_right t 1)).ne'
  apply (hw.mul φ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
    φ.hasCompactSupport.mul_left (fun t => mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_max_right _ _)) _) φ.nonneg) (x := 3/2)
  change (max (3/2:ℝ) 1)^((1/2:ℝ)-1) * φ (3/2) ≠ 0
  rw [φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le),mul_one]
  exact (Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_right _ _)) _).ne'

private theorem pw_mellin_scale4 (b : ℝ → ℝ) (a : ℝ)
    (hb : MellinConvergent (fun t => (b t:ℂ)) (a:ℂ)) :
    HasMellin (fun t : ℝ => (b (t/4):ℂ)) (a:ℂ)
      ((((4:ℝ)^a:ℝ):ℂ) * mellin (fun t => (b t:ℂ)) (a:ℂ)) := by
  have hq : 0 < (1/4:ℝ) := by norm_num
  have he (t : ℝ) : 1/4*t = t/4 := by ring
  have hmul : ((1/4:ℝ):ℂ)^(-(a:ℂ)) = (((4:ℝ)^a:ℝ):ℂ) := by
    rw [← Complex.ofReal_neg,← Complex.ofReal_cpow hq.le,Real.rpow_neg_eq_inv_rpow]
    norm_num
  refine ⟨?_,?_⟩
  · simpa only [he] using (MellinConvergent.comp_mul_left hq).mpr hb
  · simpa only [he,smul_eq_mul,hmul] using mellin_comp_mul_left (fun t => (b t:ℂ)) (a:ℂ) hq

private theorem pw_log_pullback_mellin (f : ℝ → ℂ) (z : ℂ) :
    let F (y : ℝ) := if 0 < y then f (Real.log y) else 0
    (MellinConvergent F z ↔ Integrable (fun x : ℝ => Complex.exp (z*x)*f x)) ∧
    mellin F z = ∫ x : ℝ, Complex.exp (z*x)*f x := by
  let F (y : ℝ) := if 0 < y then f (Real.log y) else 0
  let g (y : ℝ) := (y:ℂ)^(z-1) • F y
  have hexp : Set.image Real.exp Set.univ = Ioi (0:ℝ) := by rw [image_univ,Real.range_exp]
  have hder : ∀ x ∈ (Set.univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) Set.univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hg (x:ℝ) : |Real.exp x| • g (Real.exp x) = Complex.exp (z*x)*f x := by
    rw [abs_of_pos (Real.exp_pos x)]
    change ((Real.exp x : ℝ) : ℂ) * ((Real.exp x : ℂ)^(z-1) * F (Real.exp x)) = _
    simp only [F, if_pos (Real.exp_pos x), Real.log_exp]
    have hn : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
    rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp,
      Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hder
    Real.exp_injective.injOn g
  have hv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hder
    Real.exp_injective.injOn g
  simpa only [hexp, hg, integrableOn_univ, setIntegral_univ, g, F, mellin, MellinConvergent] using And.intro hI hv


private theorem pw_mellin_stencil (b : ℝ → ℝ) (a : ℝ)
    (hb : MellinConvergent (fun t=> (b t:ℂ)) (a:ℂ)) :
    let g (t : ℝ) := b (t/4) - b t/2
    let u (t : ℝ) := 4*g t - g (t/4)
    let d : ℂ := ((4:ℝ)^a:ℝ)
    HasMellin (fun t=> (u t:ℂ)) (a:ℂ)
      ((4-d)*(d-1/2)*mellin (fun t=> (b t:ℂ)) (a:ℂ)) := by
  intro g u d
  have hD := pw_mellin_scale4 b a hb
  have hG : HasMellin (fun t=> (g t:ℂ)) (a:ℂ) ((d-1/2)*mellin (fun t => (b t:ℂ)) (a:ℂ)) := by
    have hh := hasMellin_sub hD.1 (hb.div_const 2)
    simp only [g,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_ofNat]
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [mellin_div_const, hD.2]
    dsimp only [d]; ring
  have hDG := pw_mellin_scale4 g a hG.1
  have h4 : HasMellin (fun t=> (4:ℂ)*(g t:ℂ)) (a:ℂ) (4*mellin (fun t=> (g t:ℂ)) (a:ℂ)) := by
    simpa only [smul_eq_mul] using hasMellin_const_smul hG.1 (4:ℂ)
  have hu := hasMellin_sub h4.1 hDG.1
  simp only [u,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_ofNat]
  refine ⟨hu.1,hu.2.trans ?_⟩
  rw [h4.2,hDG.2,hG.2]
  dsimp only [d]; ring

theorem solution :
    ∃ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ tsupport u ⊆ Ioo 1 32 ∧
      HasMellin (fun t => (u t:ℂ)) 1 0 ∧ HasMellin (fun t => (u t:ℂ)) (-(1/2):ℂ) 0 ∧
      0 < (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re ∧
      (let f := fun s : ℝ => u (Real.exp s)
       ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi 0 ∧
       (∫ s : ℝ, f s * Real.exp (-|s|/2)) = 0) := by
  obtain ⟨b,hb,hc,hz,hM,hpos⟩ := pw_test_bump
  let g (t : ℝ) := b (t/4) - b t/2
  let u (t : ℝ) := 4*g t - g (t/4)
  have hg : ContDiff ℝ (⊤:ℕ∞) g := by dsimp [g]; fun_prop
  have hu : ContDiff ℝ (⊤:ℕ∞) u := by dsimp [u]; fun_prop
  have huv (t : ℝ) (h : t ≤ 5/4 ∨ 28 ≤ t) : u t = 0 := by
    dsimp only [u,g]
    rcases h with h | h
    · simp only [hz _ (Or.inl (by linarith) : t ≤ 5/4 ∨ _),
        hz _ (Or.inl (by linarith) : t/4 ≤ 5/4 ∨ _),
        hz _ (Or.inl (by linarith) : t/4/4 ≤ 5/4 ∨ _),zero_div,sub_zero,mul_zero]
    · simp only [hz _ (Or.inr (by linarith) : _ ∨ 7/4 ≤ t),
        hz _ (Or.inr (by linarith) : _ ∨ 7/4 ≤ t/4),
        hz _ (Or.inr (by linarith) : _ ∨ 7/4 ≤ t/4/4),zero_div,sub_zero,mul_zero]
  have hsu : tsupport u ⊆ Icc (5/4) 28 := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    constructor <;> by_contra! h
    · exact ht (huv _ (Or.inl h.le))
    · exact ht (huv _ (Or.inr h.le))
  have hmall (a:ℝ) := pw_mellin_stencil b a (hM a)
  have half : (4:ℝ)^(1/2:ℝ) = 2 := by rw [← Real.sqrt_eq_rpow,show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
  have h₁ : HasMellin (fun t=> (u t:ℂ)) 1 0 := by
    simpa only [u,g,Real.rpow_one,Complex.ofReal_ofNat,Complex.ofReal_one,sub_self,zero_mul] using hmall 1
  have h₂ : HasMellin (fun t=> (u t:ℂ)) (-(1/2):ℂ) 0 := by
    have hz' := hmall (-(1/2))
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤4),half] at hz'
    norm_num [u,g] at hz' ⊢
    exact hz'
  have h₃ : 0 < (mellin (fun t => (u t:ℂ)) (1/2:ℂ)).re := by
    have hz' : mellin (fun t => (u t:ℂ)) ((1/2:ℝ):ℂ) =
        ((4-((4:ℝ)^(1/2:ℝ):ℝ)) * (((4:ℝ)^(1/2:ℝ):ℝ)-1/2) *
        mellin (fun t => (b t:ℂ)) ((1/2:ℝ):ℂ)) := (hmall (1/2)).2
    rw [half] at hz'
    norm_num only [Complex.ofReal_ofNat,Complex.ofReal_one,Complex.ofReal_div] at hz'
    rw [hz']
    norm_num [Complex.mul_re] at *
    linarith
  let f := fun s => u (Real.exp s)
  have hsf : tsupport f ⊆ Icc (Real.log (5/4)) (Real.log 28) := by
    apply closure_minimal _ isClosed_Icc
    intro s hs
    constructor <;> by_contra! h
    · exact hs (huv _ (Or.inl ((Real.exp_lt_exp.mpr h).trans_eq (Real.exp_log (by norm_num))).le))
    · exact hs (huv _ (Or.inr (by simpa only [Real.exp_log (by norm_num : (0:ℝ)<28)] using (Real.exp_lt_exp.mpr h).le)))
  refine ⟨u,hu,HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (subset_trans subset_closure hsu),fun t ht => ⟨by linarith [(hsu ht).1],by linarith [(hsu ht).2]⟩,h₁,h₂,h₃,?_,?_,?_,?_⟩
  · exact hu.comp Real.contDiff_exp
  · exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc (subset_trans subset_closure hsf)
  · exact fun s hs => (Real.log_pos (by norm_num : (1:ℝ)<5/4)).trans_le (hsf hs).1
  · have hL := (pw_log_pullback_mellin (fun s => (f s:ℂ)) (-(1/2):ℂ)).2
    have he : (fun t : ℝ => if 0<t then (f (Real.log t):ℂ) else 0) = fun t => (u t:ℂ) := by
      funext t
      by_cases ht : 0<t
      · simp [ht,f,Real.exp_log ht]
      · have hv0 : u t = 0 := huv t (Or.inl (by linarith))
        simp [ht,hv0]
    rw [he,h₂.2] at hL
    change (∫ s : ℝ, f s*Real.exp (-|s|/2)) = 0
    apply Complex.ofReal_injective
    rw [Complex.ofReal_zero]
    calc
      _ = ∫ s : ℝ, ((f s*Real.exp (-|s|/2):ℝ):ℂ) :=
        (integral_ofReal (𝕜:=ℂ) (μ:=volume) (f:=fun s => f s*Real.exp (-|s|/2))).symm
      _ = ∫ s : ℝ, Complex.exp (-(1/2:ℂ)*(s:ℂ))*(f s:ℂ) := by
        apply integral_congr_ae
        filter_upwards with s
        by_cases hs : 0 ≤ s
        · have ec : (Real.exp (-|s|/2):ℂ) = Complex.exp (-(1/2:ℂ)*(s:ℂ)) := by
            rw [abs_of_nonneg hs,Complex.ofReal_exp]
            congr 1
            push_cast
            ring
          rw [Complex.ofReal_mul,ec,mul_comm]
        · have hf0 : f s = 0 := huv _ (Or.inl (by
              have hle := Real.exp_le_one_iff.mpr (le_of_not_ge hs)
              linarith))
          simp [hf0]
      _ = _ := hL.symm

