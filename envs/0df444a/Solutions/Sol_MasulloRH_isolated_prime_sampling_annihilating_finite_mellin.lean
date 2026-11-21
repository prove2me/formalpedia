-- Prove2me | solution 1 for MasulloRH.isolated_prime_sampling_annihilating_finite_mellin
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:35:21.365845+00:00
-- url     : https://prove2.me/submissions/75637804-3211-45d8-b2bd-9118abfada2f

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
section
open MeasureTheory Set

open MeasureTheory Set

private noncomputable def lm (z : ℂ) (f : ℝ → ℂ) := ∫ x : ℝ, Complex.exp (z*x)*f x

private theorem lm_integrable (z : ℂ) {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x : ℝ => Complex.exp (z*x)*f x) :=
  (by fun_prop : Continuous (fun x : ℝ => Complex.exp (z*x)*f x)).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_left (f := fun x : ℝ => Complex.exp (z*x)) hc)

private theorem shifted (z : ℂ) (h : ℝ) (f : ℝ → ℂ) :
    lm z (fun x => f (x-h)) = Complex.exp (z*h)*lm z f := by
  unfold lm
  rw [← integral_const_mul]
  have H := integral_sub_right_eq_self (μ := volume) (fun x : ℝ => Complex.exp (z*(h:ℂ))*(Complex.exp (z*x)*f x)) h
  rw [← H]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Complex.ofReal_sub]
  rw [← mul_assoc, ← Complex.exp_add]
  ring_nf

private theorem compact_of_vanish {f : ℝ → ℂ} {c R : ℝ}
    (h : ∀ x, R ≤ |x-c| → f x=0) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=c-R) (b:=c+R))
  intro x hx
  have ht : |x-c| < R := lt_of_not_ge (fun hh => hx (h x hh))
  rw [abs_lt] at ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem MasulloRH.local_finite_mellin_annihilator (S : Finset ℂ) (c R : ℝ) (hR : 0<R) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ f c = 1 ∧
      (∀ x, R ≤ |x-c| → f x=0) ∧
      ∀ z ∈ S, (∫ x : ℝ, Complex.exp (z*x)*f x) = 0 := by
  classical
  induction S using Finset.induction_on generalizing R with
  | empty =>
    let b : ContDiffBump c := ⟨R/2,R,by linarith,by linarith⟩
    have hv (x : ℝ) (hx : R ≤ |x-c|) : (b x:ℂ)=0 := by
      exact_mod_cast b.zero_of_le_dist (by simpa [Real.dist_eq,b] using hx)
    exact ⟨fun x => (b x : ℂ),Complex.ofRealCLM.contDiff.comp b.contDiff,compact_of_vanish hv,
      by change (b c : ℂ) = 1; rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp, hv, by simp⟩
  | @insert s S hs ih =>
    obtain ⟨f,hf,hc,h1,hv,hM⟩ := ih (R/4) (by linarith)
    let h := R/2
    let k := (Complex.exp (s*h))⁻¹
    let g (x : ℝ) := f (x-h)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.sub contDiff_const)
    have hgv (x : ℝ) (hx : R ≤ |x-c|) : g x = 0 := by
      apply hv
      rcases le_abs.mp hx with hx | hx
      · exact le_abs.mpr (Or.inl (by dsimp [h]; linarith))
      · exact le_abs.mpr (Or.inr (by dsimp [h]; linarith))
    have hfv (x : ℝ) (hx : R ≤ |x-c|) : f x-k*g x=0 := by
      rw [hv x (by linarith), hgv x hx]; ring
    refine ⟨fun x => f x-k*g x,hf.sub (contDiff_const.mul hg),compact_of_vanish hfv, ?_, hfv, ?_⟩
    · have hh : g c = 0 := hv _ (le_abs.mpr (Or.inr (by dsimp [h]; linarith)))
      change f c-k*g c=1
      rw [hh,h1]; ring
    · intro z hz
      have A := lm_integrable z hf.continuous hc
      have B := (lm_integrable z hg.continuous (compact_of_vanish hgv)).const_mul k
      simp_rw [mul_sub, mul_left_comm (Complex.exp _) k]
      rw [integral_sub A B,integral_const_mul]
      change lm z f - k * lm z g = 0
      rw [show lm z g = _ from shifted z h f]
      rcases Finset.mem_insert.mp hz with rfl | hz
      · dsimp [k]; rw [← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul, sub_self]
      · have hz0 : lm z f = 0 := hM z hz
        rw [hz0]; ring
end

section
open MeasureTheory Set

open Set Filter
open scoped Topology

namespace MasulloRH

/-- A compact logarithmic profile pulls back to a smooth test on the positive ray with a
smooth zero extension across the origin. -/
theorem smooth_log_pullback (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c R : ℝ)
    (hcut : ∀ y : ℝ, R ≤ |y-c| → f y = 0) :
    let φ (x : ℝ) := if 0 < x then f (Real.log x) else 0
    ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x : ℝ, x ≤ Real.exp (c-R) ∨ Real.exp (c+R) ≤ x → φ x = 0) := by
  let φ (x : ℝ) := if 0 < x then f (Real.log x) else 0
  change ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ _
  have hz (x : ℝ) (hx : x ≤ Real.exp (c-R) ∨ Real.exp (c+R) ≤ x) : φ x = 0 := by
    by_cases hpos : 0 < x
    · rw [show φ x = f (Real.log x) from if_pos hpos]
      apply hcut
      rcases hx with hx | hx
      · have hl := (Real.log_le_iff_le_exp hpos).2 hx
        linarith [neg_le_abs (Real.log x-c)]
      · have hl := (Real.le_log_iff_exp_le hpos).2 hx
        linarith [le_abs_self (Real.log x-c)]
    · exact if_neg hpos
  refine ⟨contDiff_iff_contDiffAt.mpr ?_,?_,hz⟩
  · intro x
    by_cases hpos : 0 < x
    · apply ((hf.contDiffAt).comp x (Real.contDiffAt_log.mpr hpos.ne')).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hpos] with y hy
      exact if_pos hy
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      have hx := (le_of_not_gt hpos).trans_lt (Real.exp_pos (c-R))
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact hz y (Or.inl hy.le)
  · apply HasCompactSupport.intro (K := Icc (Real.exp (c-R)) (Real.exp (c+R))) isCompact_Icc
    intro x hx
    apply hz
    by_cases h : x ≤ Real.exp (c-R)
    · exact Or.inl h
    · right; by_contra! h'; exact hx ⟨le_of_not_ge h,h'.le⟩

end MasulloRH
end

section
open MeasureTheory Set

open MeasureTheory Set

namespace MasulloRH

/-- Exponential substitution on the positive ray, including absolute convergence. -/
theorem log_pullback_mellin (f : ℝ → ℂ) (z : ℂ) :
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

theorem log_pullback_hasMellin (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (z : ℂ) :
    HasMellin (fun y : ℝ => if 0 < y then f (Real.log y) else 0) z
      (∫ x : ℝ, Complex.exp (z*(x:ℂ))*f x) := by
  obtain ⟨hI,hval⟩ := log_pullback_mellin f z
  refine ⟨hI.mpr ((?_ : Continuous (fun x : ℝ => Complex.exp (z*x)*f x)).integrable_of_hasCompactSupport (hc.mul_left (f := fun x : ℝ => Complex.exp (z*x)))), hval⟩
  fun_prop

end MasulloRH
end

section
open MeasureTheory Set
open Filter Set MeasureTheory
open scoped Topology

theorem solution
    (p : ℕ) (hp : p.Prime) (S : Finset ℂ) :
    ∃ f : ℝ → ℂ,
      let φ (x : ℝ) := if 0<x then f (Real.log x) else 0
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ f (Real.log p) = 1 ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x : ℝ, x ≤ (p:ℝ)-1/2 ∨ (p:ℝ)+1/2 ≤ x → φ x = 0) ∧
      (∀ n : ℕ, φ n = if n = p then 1 else 0) ∧
      (∀ x : ℝ, 0 < x → φ (x⁻¹*x) = 0) ∧
      HasMellin φ 0 0 ∧ HasMellin φ 1 0 ∧ (∀ z ∈ S, HasMellin φ z 0) ∧
      HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ):ℂ) *
        (φ n + φ (1/(n:ℝ)))) ((Real.log p / Real.sqrt p : ℝ):ℂ) ∧
      0 < Real.log p / Real.sqrt p := by
  classical
  let c := Real.log p
  let L := (p:ℝ)-1/2
  let U := (p:ℝ)+1/2
  let R := min (c-Real.log L) (Real.log U-c)
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hL0 : 0<L := by dsimp [L]; linarith
  have hLc : Real.log L < c := Real.log_lt_log hL0 (by dsimp [L]; linarith)
  have hcU : c < Real.log U := Real.log_lt_log hp0 (by dsimp [U]; linarith)
  have hR : 0<R := lt_min (sub_pos.mpr hLc) (sub_pos.mpr hcU)
  let S' : Finset ℂ := insert 0 (insert 1 S)
  obtain ⟨f,hf,hfc,hpval,hcut,hz⟩ := MasulloRH.local_finite_mellin_annihilator S' c R hR
  let φ (x : ℝ) := if 0 < x then f (Real.log x) else 0
  obtain ⟨hφ,hφc,_⟩ := MasulloRH.smooth_log_pullback f hf c R hcut
  have hvan (x : ℝ) (hx : x ≤ L ∨ U ≤ x) : φ x = 0 := by
    by_cases hx0 : 0 < x
    · rw [show φ x = f (Real.log x) by simp [φ,hx0]]
      apply hcut
      rcases hx with hx | hx
      · have hlog := Real.log_le_log hx0 hx
        have hr : R ≤ c-Real.log L := min_le_left _ _
        linarith [neg_le_abs (Real.log x - c)]
      · have hlog := Real.log_le_log (show 0<U by dsimp [U]; linarith) hx
        have hr : R ≤ Real.log U-c := min_le_right _ _
        linarith [le_abs_self (Real.log x - c)]
    · simp [φ,hx0]
  have hsamp (n : ℕ) : φ n = if n=p then 1 else 0 := by
    by_cases hn : n=p
    · subst n
      simp only [φ, if_pos hp0]
      exact hpval
    · rw [if_neg hn]
      apply hvan
      rcases lt_or_gt_of_ne hn with hl | hr
      · left
        have h : (n:ℝ)+1 ≤ p := by exact_mod_cast hl
        dsimp [L]; linarith
      · right
        have h : (p:ℝ)+1 ≤ n := by exact_mod_cast hr
        dsimp [U]; linarith
  have hlo (x : ℝ) (hx : x≤1) : φ x=0 := hvan _ (Or.inl (by dsimp [L]; linarith))
  have hM (z : ℂ) (hz' : z ∈ S') : HasMellin φ z 0 := by
    have h := MasulloRH.log_pullback_hasMellin f hf.continuous hfc z
    rw [hz z hz'] at h
    exact h
  refine ⟨f,hf,hfc,hpval,hφ,hφc,hvan,hsamp,fun x hx => ?_,hM 0 (by simp [S']),
    hM 1 (by simp [S']), fun z hzs => hM z (by simp [S',hzs]),?_,?_⟩
  · rw [inv_mul_cancel₀ hx.ne']
    exact hlo _ le_rfl
  · have hinv (n : ℕ) : φ (1 / (n:ℝ)) = 0 := by
      apply hlo
      by_cases hz0 : n = 0
      · simp [hz0]
      · have hn : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz0
        simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn
    have hS := hasSum_ite_eq p ((Real.log p / Real.sqrt p:ℝ):ℂ)
    convert hS using 1
    funext n
    change ((ArithmeticFunction.vonMangoldt n/Real.sqrt n:ℝ):ℂ) * (φ n + φ (1/(n:ℝ))) = _
    rw [hinv,hsamp,add_zero]
    by_cases hnp : n=p
    · subst n
      simp [ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hnp]
  · exact div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) (Real.sqrt_pos.mpr hp0)
end

