-- Prove2me | solution 1 for MasulloRH.smooth_trace_finite_height_error
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:25:45.683974+00:00
-- url     : https://prove2.me/submissions/1ea7a275-2487-4e53-8445-9c2075b0de65

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Mathlib

open MeasureTheory Set Filter Topology
open scoped ContDiff
open MasulloRH

private noncomputable def eulerD (g : ℝ → ℂ) (t : ℝ) := (t:ℂ)*deriv g t

private noncomputable def testSize (j : ℕ) (g : ℝ → ℂ) : ℝ :=
  ∫ t in Ioi (0:ℝ), (t^(-3/2:ℝ)+t^(-1/2:ℝ))*‖(eulerD^[j] g) t‖

private theorem euler_test (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (ht : tsupport g ⊆ Ioi 0) (j : ℕ) :
    ContDiff ℝ ∞ (eulerD^[j] g) ∧ HasCompactSupport (eulerD^[j] g) ∧
      tsupport (eulerD^[j] g) ⊆ Ioi 0 := by
  induction j with
  | zero => exact ⟨hg,hc,ht⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hs,hc,ht⟩ := ih
    refine ⟨Complex.ofRealCLM.contDiff.mul (contDiff_infty_iff_deriv.mp hs).2,hc.deriv.mul_left,?_⟩
    exact tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans ht)

private theorem weighted_continuous (g : ℝ → ℂ) (hg : Continuous g) (ht : tsupport g ⊆ Ioi 0) (s : ℂ) :
    Continuous (fun t : ℝ => (t:ℂ)^s*g t) := by
  apply continuous_of_tsupport
  intro t h
  have hp : 0 < t := ht (tsupport_mul_subset_right h)
  exact (Complex.continuousAt_ofReal_cpow_const t s (.inr hp.ne')).mul hg.continuousAt

private theorem weighted_integrable (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (ht : tsupport g ⊆ Ioi 0) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t:ℂ)^s*g t) (Ioi 0) :=
  ((weighted_continuous g hg ht s).integrable_of_hasCompactSupport hc.mul_left).integrableOn

private theorem mellin_euler (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (ht : tsupport g ⊆ Ioi 0) (s : ℂ) (hs : s ≠ 0) : mellin (eulerD g) s = -s*mellin g s := by
  let f (t : ℝ) := (t:ℂ)^s*g t
  let d (t : ℝ) := s*((t:ℂ)^(s-1)*g t)+(t:ℂ)^s*deriv g t
  have hfg : HasCompactSupport f := hc.mul_left
  have hd (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) : HasDerivAt f (d x) x := by
    apply ((hasDerivAt_ofReal_cpow_const hx.ne' hs).mul ((hg.differentiable (by simp)).differentiableAt.hasDerivAt)).congr_deriv
    dsimp only [d]
    ring
  have hInt := weighted_integrable g hg.continuous hc ht (s-1)
  have hInt' := weighted_integrable (deriv g) (hg.continuous_deriv (by simp)) hc.deriv
    (tsupport_deriv_subset.trans ht) s
  have hdint : IntegrableOn d (Ioi 0) := (hInt.const_mul s).add hInt'
  have hf0 : f 0=0 := by
    dsimp [f]
    simp [hs]
  have hlim : Tendsto f atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    rw [hasCompactSupport_iff_eventuallyEq,Filter.coclosedCompact_eq_cocompact] at hfg
    exact (hfg.filter_mono atTop_le_cocompact).symm
  have hv := integral_Ioi_of_hasDerivAt_of_tendsto
    (weighted_continuous g hg.continuous ht s).continuousAt.continuousWithinAt hd hdint hlim
  change (∫ x in Ioi (0:ℝ),d x)=0-f 0 at hv
  rw [hf0,sub_zero] at hv
  change (∫ t in Ioi (0:ℝ), s*((t:ℂ)^(s-1)*g t)+(t:ℂ)^s*deriv g t) = 0 at hv
  rw [integral_add (hInt.const_mul s) hInt',integral_const_mul] at hv
  have he : mellin (eulerD g) s = ∫ t in Ioi (0:ℝ), (t:ℂ)^s*deriv g t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    change (t:ℂ)^(s-1)*((t:ℂ)*deriv g t) = _
    have ht0 := Complex.ofReal_ne_zero.mpr ht.ne'
    calc _ = ((t:ℂ)^(s-1)*(t:ℂ)^(1:ℂ))*deriv g t := by rw [Complex.cpow_one,mul_assoc]
         _ = _ := by rw [←Complex.cpow_add _ _ ht0,sub_add_cancel]
  rw [he,neg_mul,eq_neg_iff_add_eq_zero,add_comm]
  exact hv

private theorem mellin_euler_iterate (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (ht : tsupport g ⊆ Ioi 0) (s : ℂ) (hs : s ≠ 0) (j : ℕ) :
    mellin (eulerD^[j] g) s = (-s)^j*mellin g s := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨hd,hc',ht'⟩ := euler_test g hg hc ht j
    rw [Function.iterate_succ_apply',mellin_euler _ hd hc' ht' s hs,ih,pow_succ]
    ring

private theorem mellin_strip_size (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (ht : tsupport g ⊆ Ioi 0) (s : ℂ) (hs : s ≠ 0) (hl : -(1/2:ℝ) ≤ s.re)
    (hu : s.re ≤ 1/2) (j : ℕ) : |s.im|^j*‖mellin g s‖ ≤ testSize j g := by
  let G := eulerD^[j] g
  obtain ⟨hd,hc',ht'⟩ := euler_test g hg hc ht j
  have hw (a : ℝ) : IntegrableOn (fun t : ℝ => t^a*‖G t‖) (Ioi 0) := by
    apply (weighted_integrable G hd.continuous hc' ht' (a:ℂ)).norm.congr
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    simp [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht]
  have he : IntegrableOn (fun t : ℝ => (t^(-3/2:ℝ)+t^(-1/2:ℝ))*‖G t‖) (Ioi 0) := by
    simp_rw [add_mul]
    exact (hw (-3/2)).add (hw (-1/2))
  have hb : ‖mellin G s‖ ≤ testSize j g := by
    apply norm_integral_le_of_norm_le he
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    change ‖(t:ℂ)^(s-1)*G t‖ ≤ _
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.sub_re,Complex.one_re]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    by_cases h1 : 1 ≤ t
    · exact (Real.rpow_le_rpow_of_exponent_le h1 (by linarith only [hu])).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge h1) (by linarith only [hl])).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  rw [show mellin G s = _ from mellin_euler_iterate g hg hc ht s hs j,
    norm_mul,norm_pow,norm_neg] at hb
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm s) j)
    (norm_nonneg _)).trans hb

private def stripAsSubset (α : ℝ) : ZetaZerosInTraceStrip α ≃
    {z : ZetaZerosInTraceStrip (1/2) // |z.val.re-1/2| < α} where
  toFun z := ⟨⟨z.val,z.property.1,z.property.2.1,z.property.2.2.1,
    abs_lt.mpr ⟨by linarith [z.property.2.1],by linarith [z.property.2.2.1]⟩⟩,z.property.2.2.2⟩
  invFun z := ⟨z.val.val,z.val.property.1,z.val.property.2.1,z.val.property.2.2.1,z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (α : ℝ) (n k : ℕ) :
    let H : ℝ := 5/2+2*n
    let D : (ℝ → ℂ) → ℝ → ℂ := fun f t => (t:ℂ)*deriv f t
    let B := ∫ t in Ioi (0:ℝ), (t^(-3/2:ℝ)+t^(-1/2:ℝ))*‖(D^[k+2] φ) t‖
    ‖(mellin φ (1/2) + mellin φ (-1/2) -
       ((∫ t in Ioi (1:ℝ),realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i))) -
       (∑' z : ZetaZerosInTraceStrip α,zetaTraceTerm φ α z) -
       (∑' z : ZetaZerosInTraceStrip (1/2),if α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ H
         then zetaTraceTerm φ (1/2) z else 0)‖ ≤
    (2*B/H^k) * (2/(H-1) * (8*((zetaLogDeriv 3).re -
      (zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re) -
      (zetaLogDeriv (5/2)).re + (1+Real.log n)/2)) := by
  classical
  dsimp only
  let H : ℝ := 5/2+2*n
  let M := testSize (k+2) φ
  let c := 2*M/H^k
  let Z := ZetaZerosInTraceStrip (1/2)
  let f := zetaTraceTerm φ (1/2)
  let w := zeroDecayWeight (1/2)
  have hH : 1 ≤ H := by dsimp [H]; linarith [n.cast_nonneg (α:=ℝ)]
  have hH0 : 0 < H := by linarith
  have hM : 0 ≤ M := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    exact mul_nonneg (add_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)) (norm_nonneg _)
  have hc : 0 ≤ c := div_nonneg (by positivity) (pow_nonneg hH0.le _)
  have hgeom := trace_formula_rational_full_strip φ hφ
  have hf : Summable f := hgeom.2.2.1
  have hw : Summable w := weighted_zero_summability (1/2) (by norm_num)
  have hg : mellin φ (1/2) + mellin φ (-1/2) -
       ((∫ t in Ioi (1:ℝ),realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i)) = ∑' z,f z := by
    rw [hgeom.2.2.2]; abel
  let A : Set Z := {z | |z.val.re-1/2| < α}
  let E : Set Z := {z | H < |z.val.im|}
  let L : Set Z := Aᶜ ∩ Eᶜ
  let K : Set Z := Aᶜ ∩ E
  have hsplit (z : Z) : f z-A.indicator f z-L.indicator f z=K.indicator f z := by
    simp only [A,L,K,E,Set.indicator_apply,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_compl_iff]
    split_ifs <;> simp_all <;> grind
  have hnarrow : (∑' z : ZetaZerosInTraceStrip α,zetaTraceTerm φ α z) = ∑' z,A.indicator f z := by
    rw [←tsum_subtype]
    exact (stripAsSubset α).tsum_eq (fun z => f z.val)
  have hr : (∑' z,f z)-(∑' z,A.indicator f z)-(∑' z,L.indicator f z) = ∑' z,K.indicator f z := by
    rw [←hf.tsum_sub (hf.indicator A),←(hf.sub (hf.indicator A)).tsum_sub (hf.indicator L)]
    exact tsum_congr hsplit
  have ht (z : Z) (hz : z ∈ E) : ‖f z‖ ≤ c*w z := by
    let s := z.val-1/2
    let y := |z.val.im|
    have hsy : s.im = z.val.im := by simp [s,Complex.sub_im,Complex.div_ofNat_im]
    have hsr : s.re = z.val.re-1/2 := by simp [s,Complex.sub_re,Complex.div_ofNat_re]
    have hy : H < y := hz
    have hs0 : s ≠ 0 := by
      intro he; have hh := congrArg Complex.im he; rw [hsy,Complex.zero_im] at hh
      change H < |z.val.im| at hy; rw [hh,abs_zero] at hy; linarith
    have hφm := mellin_strip_size φ hφ.1 hφ.2.1 hφ.2.2.1 s hs0
      (by rw [hsr]; linarith [z.prop.2.1]) (by rw [hsr]; linarith [z.prop.2.2.1]) (k+2)
    rw [hsy] at hφm
    have hy0 : 0 ≤ y := abs_nonneg _
    have hysq : 1+z.val.im^2 ≤ 2*y^2 := by dsimp [y]; nlinarith [sq_abs z.val.im,sq_nonneg (y-1)]
    have hcomp : (1+z.val.im^2)*H^k ≤ 2*y^(k+2) := by
      calc _ ≤ (2*y^2)*y^k := mul_le_mul hysq (pow_le_pow_left₀ hH0.le hy.le k)
              (pow_nonneg hH0.le _) (by positivity)
           _ = _ := by rw [pow_add]; ring
    have hn : ‖mellin φ s‖ ≤ c/(1+z.val.im^2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      apply (le_div_iff₀ (pow_pos hH0 k)).mpr
      calc _ = ((1+z.val.im^2)*H^k)*‖mellin φ s‖ := by ring
           _ ≤ (2*y^(k+2))*‖mellin φ s‖ := mul_le_mul_of_nonneg_right hcomp (norm_nonneg _)
           _ = 2*(y^(k+2)*‖mellin φ s‖) := by ring
           _ ≤ 2*M := mul_le_mul_of_nonneg_left hφm (by norm_num)
    dsimp only [f,zetaTraceTerm,w,zeroDecayWeight]
    rw [norm_mul,Complex.norm_natCast]
    calc _ ≤ (analyticOrderNatAt riemannZeta z.val:ℝ)*(c/(1+z.val.im^2)) :=
              mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
         _ = _ := by ring
  have hb (z : Z) : ‖K.indicator f z‖ ≤ c*E.indicator w z := by
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz,Set.indicator_of_mem hz.2]; exact ht z hz.2
    · rw [Set.indicator_of_notMem hz,norm_zero]
      exact mul_nonneg hc (Set.indicator_nonneg (fun z _ => div_nonneg (Nat.cast_nonneg _) (by positivity)) z)
  have htail : ‖∑' z,K.indicator f z‖ ≤ c*(∑' z,E.indicator w z) := by
    rw [←tsum_mul_left]
    exact (norm_tsum_le_tsum_norm (hf.indicator K).norm).trans
      (((hf.indicator K).norm).tsum_le_tsum hb ((hw.indicator E).mul_left c))
  have hfin (z : Z) : (if α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ H then f z else 0) =
      L.indicator f z := by
    simp only [L,A,E,Set.indicator_apply,Set.mem_inter_iff,Set.mem_compl_iff,Set.mem_setOf_eq,not_lt]
  rw [hg,hnarrow,show (∑' z : Z,if α ≤ |z.val.re-1/2| ∧ |z.val.im| ≤ H then f z else 0) =
    (∑' z,L.indicator f z) from tsum_congr hfin,hr]
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ hc
  exact zero_decay_tail_at_real_lattice n

