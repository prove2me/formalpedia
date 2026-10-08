-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrt_quadratic_bounded_height_zero_free
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:36:10.737729+00:00
-- url     : https://prove2.me/submissions/885ede05-1a5b-4b89-84f8-7268e79d388c

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_mrt_character_logderiv_growth_constant

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Basic
namespace OAI

/-!
# Ordinary two-point correlations: concrete sums and affine transfer

Definitions follow the introduction of the supplied manuscript
*Ordinary two-point correlations of multiplicative functions* (September 24, 2026).
The exact Liouville identities below are the algebraic part of §8.
No cancellation estimate is assumed or asserted here.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations







@[simp] theorem liouville_mul (m n : ℕ) :
    liouville (m * n) = liouville m * liouville n := by
  simp [liouville, ArithmeticFunction.liouville_apply_mul]

@[simp] theorem liouville_sq {n : ℕ} (hn : n ≠ 0) : liouville n ^ 2 = 1 := by
  have h : (ArithmeticFunction.liouville n) ^ 2 = (1 : ℤ) := by
    rw [ArithmeticFunction.liouville_apply hn, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
    norm_num
  unfold liouville
  exact_mod_cast h





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.EulerMaclaurin
namespace Erdos970

open _root_.Finset _root_.Interval _root_.MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}


@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.MertensClassical
namespace Erdos970


namespace Real

open _root_.Real _root_.Filter _root_.Asymptotics



end Real

section Issue1584
open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology




end Issue1584

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open ArithmeticFunction hiding log













































attribute [fun_prop] measurable_from_top












section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg



@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]






end LogZetaInteg
end











section
open _root_.MeasureTheory _root_.Set








end












































end Mertens

end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterSums
namespace OAI

/-! Explicit modulus dependence in nonprincipal character partial sums,
and the resulting exact Abel integral on its initial half-plane. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Asymptotics _root_.MeasureTheory
open scoped _root_.Classical _root_.Topology

lemma mrt_character_shift {q : ℕ} (χ : DirichletCharacter ℂ q) (k n : ℕ) :
    χ ((q*k+n:ℕ):ZMod q)=χ (n:ZMod q) := by
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add]

lemma mrt_character_period_sum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (∑ n∈range q,χ (n:ZMod q))=0 := by
  have hs := χ.sum_eq_zero_of_ne_one hχ
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
    calc
      _ = ∑ n : Fin (q+1),χ (n.val:ZMod (q+1)) :=
        (Fin.sum_univ_eq_sum_range (fun n : ℕ => χ (n:ZMod (q+1))) (q+1)).symm
      _ = ∑ n : ZMod (q+1),χ n := by
        apply sum_congr rfl
        intro n _
        exact congrArg χ (ZMod.natCast_zmod_val (n := q+1) n)
      _ = 0 := hs

lemma mrt_character_full_periods {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (k : ℕ) :
    (∑ n∈range (q*k),χ (n:ZMod q))=0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,sum_range_add,ih,zero_add]
    simp_rw [mrt_character_shift]
    exact mrt_character_period_sum χ hχ

lemma mrt_character_prefix_remainder {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    (∑ n∈range N,χ (n:ZMod q))=∑ n∈range (N%q),χ (n:ZMod q) := by
  have hN : N=q*(N/q)+N%q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  conv_lhs => rw [hN,sum_range_add,mrt_character_full_periods χ hχ,zero_add]
  exact sum_congr rfl (fun n _ => mrt_character_shift χ (N/q) n)

theorem mrt_character_prefix_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    ‖∑ n∈range N,χ (n:ZMod q)‖≤(q:ℝ) := by
  rw [mrt_character_prefix_remainder χ hχ]
  calc
    _ ≤ ∑ n∈range (N%q),‖χ (n:ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _n∈range (N%q),(1:ℝ) := sum_le_sum (fun n _ => χ.norm_le_one _)
    _ = (N%q:ℕ) := by simp
    _ ≤ (q:ℝ) := by exact_mod_cast (Nat.mod_lt N (NeZero.pos q)).le

lemma mrt_character_Icc_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    (∑ n∈Icc 1 N,χ (n:ZMod q))=∑ n∈range (N+1),χ (n:ZMod q) := by
  have hq : q≠1 := by
    intro hq
    subst q
    apply hχ
    ext n
    have hn : n=(1:ZMod 1) := Subsingleton.elim _ _
    simp [hn]
  let : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  rw [Nat.range_succ_eq_Icc_zero]
  have hset : Icc 1 N=Ioc 0 N := by ext n; simp; omega
  rw [hset,←add_sum_Ioc_eq_sum_Icc (Nat.zero_le N),Nat.cast_zero,
    MulChar.map_zero χ,zero_add]

theorem mrt_character_Icc_norm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (N : ℕ) :
    ‖∑ n∈Icc 1 N,χ (n:ZMod q)‖≤(q:ℝ) := by
  rw [mrt_character_Icc_eq χ hχ]
  exact mrt_character_prefix_norm χ hχ (N+1)

lemma mrt_character_sum_bigO {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    (fun N : ℕ => ∑ n∈Icc 1 N,χ (n:ZMod q)) =O[atTop]
      (fun N : ℕ => (N:ℝ)^(0:ℝ)) := by
  refine isBigO_iff.mpr ⟨(q:ℝ),Eventually.of_forall (fun N => ?_)⟩
  simpa only [Real.rpow_zero,norm_one,mul_one] using mrt_character_Icc_norm χ hχ N

theorem mrt_character_LFunction_Abel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) {s : ℂ} (hs : 1< s.re) :
    DirichletCharacter.LFunction χ s =
      s*∫ t in Set.Ioi (1:ℝ),
        (∑ n∈Icc 1 ⌊t⌋₊,χ (n:ZMod q))*(t:ℂ)^(-(s+1)) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_eq_mul_integral (fun n => χ (n:ZMod q)) (by norm_num : (0:ℝ)≤0)
    (by linarith : (0:ℝ)< s.re) (χ.LSeriesSummable_of_one_lt_re hs)
    (mrt_character_sum_bigO χ hχ)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterAbel
namespace OAI

/-! Abel-integral bounds for every nonprincipal character, retaining the
explicit modulus q in the bound q * norm(s) / re(s). -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]




omit [NeZero q] in
lemma mrtCharacterSummatory_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (mrtCharacterSummatory χ) := by
  exact (measurable_from_nat (f := fun N => ∑ n ∈ Icc 1 N, χ (n : ZMod q))).comp
    Nat.measurable_floor

lemma mrtCharacterSummatory_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖mrtCharacterSummatory χ t‖ ≤ (q : ℝ) :=
  mrt_character_Icc_norm χ hχ ⌊t⌋₊


lemma mrtCharacterAbelKernel_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) {t : ℝ} (ht : 1 < t) :
    ‖mrtCharacterAbelKernel χ s t‖ ≤ (q : ℝ) * t ^ (-(s.re + 1)) := by
  rw [mrtCharacterAbelKernel, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.neg_re,
    Complex.add_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (mrtCharacterSummatory_norm χ hχ t)
    (Real.rpow_nonneg (zero_lt_one.trans ht).le _)


lemma mrtCharacterAbelKernel_integral_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), mrtCharacterAbelKernel χ s t‖ ≤ (q : ℝ) / s.re := by
  have hexp : -(s.re + 1) < -1 := by linarith
  calc
    _ ≤ ∫ t in Set.Ioi (1 : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul (q : ℝ))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mrtCharacterAbelKernel_norm_le χ hχ s ht
    _ = (q : ℝ) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
      field_simp [ne_of_gt hs]
      ring

theorem mrtCharacterAbelIntegral_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mrtCharacterAbelIntegral χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [mrtCharacterAbelIntegral, norm_mul]
  calc
    _ ≤ ‖s‖ * ((q : ℝ) / s.re) :=
      mul_le_mul_of_nonneg_left (mrtCharacterAbelKernel_integral_norm χ hχ hs) (norm_nonneg s)
    _ = _ := by ring

theorem mrtCharacterAbelIntegral_eq_LFunction (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mrtCharacterAbelIntegral χ s = DirichletCharacter.LFunction χ s :=
  (mrt_character_LFunction_Abel χ hχ hs).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterContinuation
namespace OAI

/-! The nonprincipal character Abel integral agrees with the existing
L-function throughout re(s)>0, with explicit modulus dependence. -/

namespace TwoPointCorrelations

open _root_.Filter _root_.MeasureTheory _root_.Asymptotics
open scoped _root_.BigOperators _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]


omit [NeZero q] in
lemma mrtCharacterAbelInput_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (mrtCharacterAbelInput χ) :=
  (mrtCharacterSummatory_measurable χ).indicator measurableSet_Ioi

lemma mrtCharacterAbelInput_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖mrtCharacterAbelInput χ t‖ ≤ (q : ℝ) := by
  by_cases ht : 1 < t
  · simpa only [mrtCharacterAbelInput, Set.mem_Ioi, Set.indicator_apply, if_pos ht] using
      mrtCharacterSummatory_norm χ hχ t
  · simp only [mrtCharacterAbelInput, Set.mem_Ioi, Set.indicator_apply, if_neg ht, norm_zero]
    exact Nat.cast_nonneg q

lemma mrtCharacterAbelInput_locallyIntegrable (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    LocallyIntegrableOn (mrtCharacterAbelInput χ) (Set.Ioi (0 : ℝ)) := by
  refine (locallyIntegrableOn_const (s := Set.Ioi (0 : ℝ)) (q : ℝ)).mono
    (mrtCharacterAbelInput_measurable χ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by simpa using mrtCharacterAbelInput_norm χ hχ t

lemma mrtCharacterAbelInput_bigO_atTop (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    mrtCharacterAbelInput χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound (q : ℝ) (Eventually.of_forall fun t => ?_)
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using mrtCharacterAbelInput_norm χ hχ t

omit [NeZero q] in
lemma mrtCharacterAbelInput_bigO_zero (χ : DirichletCharacter ℂ q) (b : ℝ) :
    mrtCharacterAbelInput χ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hnot : t ∉ Set.Ioi (1 : ℝ) := by change ¬1 < t; linarith
  simp only [mrtCharacterAbelInput, Set.indicator_of_notMem hnot, norm_zero, zero_mul, le_refl]

omit [NeZero q] in
lemma mrtCharacterAbelIntegral_eq_mellin (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mrtCharacterAbelIntegral χ s = s * mellin (mrtCharacterAbelInput χ) (-s) := by
  unfold mrtCharacterAbelIntegral mellin
  congr 1
  have heq : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • mrtCharacterAbelInput χ t) =
      (Set.Ioi (1 : ℝ)).indicator (mrtCharacterAbelKernel χ s) := by
    funext t
    by_cases ht : 1 < t
    · simp only [mrtCharacterAbelInput, Set.indicator_apply, Set.mem_Ioi, if_pos ht,
        smul_eq_mul, mrtCharacterAbelKernel]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · have hn : t ∉ Set.Ioi (1 : ℝ) := ht
      simp only [mrtCharacterAbelInput, Set.indicator_of_notMem hn, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Ioi]
  rw [Set.inter_eq_right.mpr (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) from
    fun t ht => lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)]

theorem mrtCharacterAbelIntegral_differentiableAt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (mrtCharacterAbelIntegral χ) s := by
  have hm : DifferentiableAt ℂ (mellin (mrtCharacterAbelInput χ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (mrtCharacterAbelInput_locallyIntegrable χ hχ) (mrtCharacterAbelInput_bigO_atTop χ hχ)
      (b := -s.re - 1)
    · simpa only [Complex.neg_re] using neg_neg_of_pos hs
    · exact mrtCharacterAbelInput_bigO_zero χ _
    · simp only [Complex.neg_re]
      linarith
  have heq : mrtCharacterAbelIntegral χ = fun z => z * mellin (mrtCharacterAbelInput χ) (-z) :=
    funext (mrtCharacterAbelIntegral_eq_mellin χ)
  rw [heq]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- The bounded-partial-sum integral is the existing L-function on the
entire half-plane of convergence of that integral. -/
theorem mrtCharacterAbelIntegral_eq_LFunction_of_pos (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    mrtCharacterAbelIntegral χ s = DirichletCharacter.LFunction χ s := by
  let U : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ (mrtCharacterAbelIntegral χ) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    exact (mrtCharacterAbelIntegral_differentiableAt χ hχ hz).differentiableWithinAt
  have heq : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] mrtCharacterAbelIntegral χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    exact (mrtCharacterAbelIntegral_eq_LFunction χ hχ hz).symm
  exact (hF.eqOn_of_preconnected_of_eventuallyEq hG hc.isPreconnected
    (show (2 : ℂ) ∈ U by change 0 < (2 : ℂ).re; norm_num) heq hs).symm

theorem mrt_character_LFunction_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [← mrtCharacterAbelIntegral_eq_LFunction_of_pos χ hχ hs]
  exact mrtCharacterAbelIntegral_norm χ hχ hs

theorem mrt_character_LFunction_norm_halfPlane (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (2 * q : ℝ) * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  calc
    _ ≤ (q : ℝ) * ‖s‖ / s.re := mrt_character_LFunction_norm_le χ hχ hs0
    _ ≤ (q : ℝ) * ‖s‖ / (1/2) :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg q) (norm_nonneg s))
        (by norm_num) hs
    _ = _ := by ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHarmonic
namespace OAI

/-! Ordered harmonic sums for a nonprincipal character converge to the
existing analytic L-function at one. No absolute convergence at one is used. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.MeasureTheory _root_.Asymptotics
open scoped _root_.Classical _root_.Topology

variable {q : ℕ} [NeZero q]

lemma mrt_character_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ (0 : ZMod q) = 0 := by
  have hq : q ≠ 1 := by
    intro hq
    subst q
    apply hχ
    ext n
    have hn : n = (1 : ZMod 1) := Subsingleton.elim _ _
    simp [hn]
  let : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
  exact MulChar.map_zero χ

lemma mrt_character_Icc_zero_eq (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) :
    (∑ n ∈ Icc 0 N, χ (n : ZMod q)) = ∑ n ∈ Icc 1 N, χ (n : ZMod q) := by
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp),
    Nat.cast_zero, mrt_character_zero χ hχ, zero_add, zero_add]

theorem mrt_character_harmonic_tendsto (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, χ (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  let c : ℕ → ℂ := fun n => χ (n : ZMod q)
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ (-1 : ℂ)
  have hc : c 0 = 0 := by simpa only [c, Nat.cast_zero] using mrt_character_zero χ hχ
  have hsum (N : ℕ) : (∑ n ∈ Icc 0 N, c n) = ∑ n ∈ Icc 1 N, χ (n : ZMod q) :=
    mrt_character_Icc_zero_eq χ hχ N
  have hdiff (t : ℝ) (ht : t ∈ Set.Ici (1 : ℝ)) : DifferentiableAt ℝ f t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hint : LocallyIntegrableOn (deriv f) (Set.Ici (1 : ℝ)) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one (by norm_num : (-1 : ℂ).re < 0))).locallyIntegrableOn
  have hlim : Tendsto (fun N : ℕ => f N * ∑ n ∈ Icc 0 N, c n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (q : ℝ) * (N : ℝ)⁻¹)
    · intro N
      dsimp only [f]
      rw [norm_mul, hsum, Complex.cpow_neg_one, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N)]
      calc
        _ ≤ (N : ℝ)⁻¹ * q := mul_le_mul_of_nonneg_left
          (mrt_character_Icc_norm χ hχ N) (inv_nonneg.mpr (Nat.cast_nonneg N))
        _ = _ := mul_comm _ _
    · simpa using Tendsto.const_mul (q : ℝ)
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hO : (fun N : ℕ => ∑ n ∈ Icc 0 N, c n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (0 : ℝ)) := by
    simpa only [hsum] using mrt_character_sum_bigO χ hχ
  have hderiv : (fun t : ℝ => deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) =O[atTop]
      (fun t : ℝ => t ^ (-2 : ℝ)) := by
    refine IsBigO.mul_atTop_rpow_of_isBigO_rpow (-2) 0 (-2) ?_ ?_ (by norm_num)
    · have hh := isBigO_deriv_ofReal_cpow_const_atTop (-1 : ℂ)
      norm_num only [Complex.neg_re, Complex.one_re] at hh
      simpa only [f] using! hh
    · simpa only [Real.rpow_zero, Function.comp_apply] using!
        hO.comp_tendsto tendsto_nat_floor_atTop
  have ht := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc hdiff hint hlim hderiv
    (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num : (-2 : ℝ) < -1))
  have he : (0 : ℂ) - ∫ t in Set.Ioi (1 : ℝ), deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n =
      DirichletCharacter.LFunction χ 1 := by
    rw [zero_sub, ← integral_neg,
      ← mrtCharacterAbelIntegral_eq_LFunction_of_pos χ hχ (by norm_num : 0 < (1 : ℂ).re)]
    simp only [mrtCharacterAbelIntegral, one_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ n ∈ Icc 0 ⌊t⌋₊, c n) = mrtCharacterAbelKernel χ 1 t
    rw [show deriv f t = (-1 : ℂ) * (t : ℂ) ^ (-2 : ℂ) by
      have hh := Complex.deriv_ofReal_cpow_const
        (zero_lt_one.trans ht).ne' (by norm_num : (-1 : ℂ) ≠ 0)
      norm_num only at hh
      exact hh, hsum]
    simp only [mrtCharacterAbelKernel, mrtCharacterSummatory]
    norm_num
    ring
  rw [he] at ht
  convert (preTransparency := .instances) ht using 1
  funext N
  have hz : (f 0) * c 0 = 0 := by rw [hc, mul_zero]
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), Nat.cast_zero, hz, zero_add,
    zero_add]
  apply sum_congr rfl
  intro n _
  simp [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticCoefficients
namespace OAI

/-! The coefficients of zeta times a real quadratic character are
nonnegative, and every positive square contributes at least one. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.ArithmeticFunction
open scoped _root_.Classical _root_.ComplexOrder

lemma mrt_character_zeta_coefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ.zetaMul n = ∑ d ∈ n.divisors, χ (d : ZMod q) := by
  rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply]
  apply sum_congr rfl
  intro d hd
  simp only [toArithmeticFunction, coe_mk,
    (Nat.pos_of_mem_divisors hd).ne', ↓reduceIte]


lemma mrt_quadratic_prime_square_coefficient {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (1 : ℂ) ≤ χ.zetaMul (p ^ (2 * k)) := by
  rw [mrt_character_zeta_coefficient, Nat.sum_divisors_prime_pow hp]
  simp only [Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · simp [h]
  · simp only [h, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast (by omega : 1 ≤ 2 * k + 1)
  · simp [h, neg_one_geom_sum]

theorem mrt_quadratic_square_coefficient {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) (hn : n ≠ 0) :
    (1 : ℂ) ≤ χ.zetaMul (n ^ 2) := by
  have hall : ∀ n : ℕ, n ≠ 0 → (1 : ℂ) ≤ χ.zetaMul (n ^ 2) := by
    apply Nat.recOnPrimeCoprime
    · simp
    · intro p k hp _
      rw [← pow_mul, Nat.mul_comm k 2]
      exact mrt_quadratic_prime_square_coefficient χ hχ hp k
    · intro a b _ _ hab ha hb hne
      have ha0 : a ≠ 0 := left_ne_zero_of_mul hne
      have hb0 : b ≠ 0 := right_ne_zero_of_mul hne
      rw [mul_pow, χ.isMultiplicative_zetaMul.map_mul_of_coprime (hab.pow 2 2)]
      exact one_le_mul_of_one_le_of_one_le (ha ha0) (hb hb0)
  exact hall n hn


lemma mrt_quadratic_coefficient_re_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ (χ.zetaMul n).re :=
  (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg hχ n)).1

lemma mrt_quadratic_square_coefficient_re {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (n : ℕ) (hn : n ≠ 0) :
    1 ≤ (χ.zetaMul (n ^ 2)).re :=
  (Complex.le_def.mp (mrt_quadratic_square_coefficient χ hχ n hn)).1


lemma mrt_character_zeta_coefficient_norm {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ.zetaMul n‖ ≤ n := by
  rw [mrt_character_zeta_coefficient]
  calc
    _ ≤ ∑ d ∈ n.divisors, ‖χ (d : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := sum_le_sum (fun d _ => χ.norm_le_one _)
    _ = (n.divisors.card : ℝ) := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLambert
namespace OAI

/-! An absolutely convergent Lambert-series identity for a bounded
character. The convolution is the actual zeta-character coefficient. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

lemma mrt_character_lambert_pair_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p : ℕ+ × ℕ+ => χ (p.1 : ZMod q) * (r : ℂ) ^ (p.1 * p.2 : ℕ)) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs : Summable (fun p : ℕ+ × ℕ+ => r ^ (p.1 * p.2 : ℕ)) := by
    simpa only [pow_zero, one_mul] using summable_prod_mul_pow (𝕜 := ℝ) 0 hr
  apply hs.of_norm_bounded
  intro p
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact mul_le_of_le_one_left (pow_nonneg hr0 _) (χ.norm_le_one _)

lemma mrt_character_lambert_inner {q : ℕ} (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℕ+) :
    (∑' m : ℕ+, χ (d : ZMod q) * (r : ℂ) ^ (d * m : ℕ)) =
      χ (d : ZMod q) * (r : ℂ) ^ (d : ℕ) / (1 - (r : ℂ) ^ (d : ℕ)) := by
  have hr : ‖(r : ℂ) ^ (d : ℕ)‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact pow_lt_one₀ hr0 hr1 d.pos.ne'
  have hi : (∑' m : ℕ+, (r : ℂ) ^ (d * m : ℕ)) =
      (r : ℂ) ^ (d : ℕ) / (1 - (r : ℂ) ^ (d : ℕ)) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun m => (r : ℂ) ^ ((d : ℕ) * m))]
    simp_rw [Nat.mul_succ, pow_add, pow_mul]
    rw [tsum_mul_right, tsum_geometric_of_norm_lt_one hr]
    ring
  rw [tsum_mul_left, hi]
  ring

lemma mrt_character_lambert_fiber {q : ℕ} (χ : DirichletCharacter ℂ q)
    (r : ℝ) (n : ℕ+) :
    (∑ p : Nat.divisorsAntidiagonal (n : ℕ),
      χ (p.val.1 : ZMod q) * (r : ℂ) ^ (p.val.1 * p.val.2)) =
      χ.zetaMul n * (r : ℂ) ^ (n : ℕ) := by
  rw [mrt_character_zeta_coefficient, sum_mul]
  simp only [Finset.univ_eq_attach]
  rw [(n : ℕ).divisorsAntidiagonal.sum_attach
    (fun p => χ (p.1 : ZMod q) * (r : ℂ) ^ (p.1 * p.2))]
  rw [Nat.sum_divisorsAntidiagonal
    (fun d m => χ (d : ZMod q) * (r : ℂ) ^ (d * m))]
  apply sum_congr rfl
  intro d hd
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

theorem mrt_character_lambert {q : ℕ} (χ : DirichletCharacter ℂ q)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ+, χ.zetaMul n * (r : ℂ) ^ (n : ℕ)) =
      ∑' d : ℕ+, χ (d : ZMod q) * (r : ℂ) ^ (d : ℕ) /
        (1 - (r : ℂ) ^ (d : ℕ)) := by
  let g : ℕ+ × ℕ+ → ℂ := fun p =>
    χ (p.1 : ZMod q) * (r : ℂ) ^ (p.1 * p.2 : ℕ)
  have hg : Summable g := mrt_character_lambert_pair_summable χ hr0 hr1
  have hsig := (sigmaAntidiagonalEquivProd.summable_iff).mpr hg
  calc
    _ = ∑' n : ℕ+, ∑' p : Nat.divisorsAntidiagonal (n : ℕ),
        χ (p.val.1 : ZMod q) * (r : ℂ) ^ (p.val.1 * p.val.2) := by
      apply tsum_congr
      intro n
      rw [tsum_fintype, mrt_character_lambert_fiber]
    _ = ∑' p : ℕ+ × ℕ+, g p := by
      change (∑' n : ℕ+, ∑' p : Nat.divisorsAntidiagonal (n : ℕ),
        (g ∘ sigmaAntidiagonalEquivProd) ⟨n, p⟩) = _
      rw [← hsig.tsum_sigma]
      exact sigmaAntidiagonalEquivProd.tsum_eq g
    _ = ∑' d : ℕ+, ∑' m : ℕ+, χ (d : ZMod q) * (r : ℂ) ^ (d * m : ℕ) :=
      hg.tsum_prod
    _ = _ := tsum_congr (mrt_character_lambert_inner χ hr0 hr1)

theorem mrt_character_thermal_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => χ.zetaMul n * (Real.exp (-t * n) : ℂ)) := by
  have hs := Real.summable_pow_mul_exp_neg_nat_mul 1 ht
  apply hs.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), pow_one]
  exact mul_le_mul_of_nonneg_right (mrt_character_zeta_coefficient_norm χ n)
    (Real.exp_nonneg _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticKernel
namespace OAI

/-! The elementary exponential smoothing remainder. Its monotonicity
makes the error in a periodic-character convolution bounded independently
of the smoothing scale. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter _root_.Set
open scoped _root_.Classical _root_.Topology


lemma mrt_quadratic_remainder_nonneg {u : ℝ} (hu : 0 < u) :
    0 ≤ mrtQuadraticRemainder u := by
  have he : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  exact sub_nonneg.mpr (by simpa only [one_div] using one_div_le_one_div_of_le hu he)


lemma mrt_quadratic_remainder_le_one {u : ℝ} (hu : 0 < u) :
    mrtQuadraticRemainder u ≤ 1 := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-u)) (Real.exp_pos u).le
  have hprod : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  rw [hprod] at hm
  unfold mrtQuadraticRemainder
  rw [inv_eq_one_div, inv_eq_one_div]
  apply (sub_le_iff_le_add).mpr
  have hh : 1 + 1 / (Real.exp u - 1) = Real.exp u / (Real.exp u - 1) := by
    field_simp
    ring
  rw [hh]
  apply (div_le_div_iff₀ hu he).mpr
  nlinarith

lemma mrt_quadratic_exponential_square {u : ℝ} (hu : 0 ≤ u) :
    u ^ 2 * Real.exp u ≤ (Real.exp u - 1) ^ 2 := by
  let E := Real.exp (u / 2)
  have hE : 0 < E := Real.exp_pos _
  have hs := mul_le_mul_of_nonneg_right
    (Real.self_le_sinh_iff.mpr (show 0 ≤ u / 2 by positivity)) hE.le
  have he2 : E ^ 2 = Real.exp u := by
    dsimp only [E]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hei : Real.exp (-(u / 2)) * E = 1 := by
    dsimp only [E]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [Real.sinh_eq] at hs
  have hlin : u * E ≤ Real.exp u - 1 := by
    dsimp only [E] at hs
    change Real.exp (u / 2) ^ 2 = _ at he2
    change Real.exp (-(u / 2)) * Real.exp (u / 2) = 1 at hei
    dsimp only [E]
    nlinarith only [hs, he2, hei]
  have hsq := (sq_le_sq₀ (mul_nonneg hu hE.le)
    (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu))).mpr hlin
  rwa [mul_pow, he2] at hsq

lemma mrt_quadratic_remainder_hasDeriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt mrtQuadraticRemainder
      (Real.exp u / (Real.exp u - 1) ^ 2 - 1 / u ^ 2) u := by
  have he : Real.exp u - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))
  have hh : HasDerivAt mrtQuadraticRemainder
      (-1 / u ^ 2 - -Real.exp u / (Real.exp u - 1) ^ 2) u :=
    ((hasDerivAt_id u).inv hu.ne').sub
    (((Real.hasDerivAt_exp u).sub_const 1).inv he)
  convert (preTransparency := .instances) hh using 1
  ring

lemma mrt_quadratic_remainder_deriv_nonpos {u : ℝ} (hu : 0 < u) :
    Real.exp u / (Real.exp u - 1) ^ 2 - 1 / u ^ 2 ≤ 0 := by
  have he : 0 < Real.exp u - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  apply sub_nonpos.mpr
  apply (div_le_div_iff₀ (sq_pos_of_pos he) (sq_pos_of_pos hu)).mpr
  simpa only [mul_one, one_mul, mul_comm] using mrt_quadratic_exponential_square hu.le

lemma mrt_quadratic_remainder_antitone : AntitoneOn mrtQuadraticRemainder (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · exact fun u hu => (mrt_quadratic_remainder_hasDeriv hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (mrt_quadratic_remainder_hasDeriv (by simpa using hu)).hasDerivWithinAt
  · intro u hu
    exact mrt_quadratic_remainder_deriv_nonpos (by simpa using hu)


/-- Finite Dirichlet summation with a nonnegative decreasing weight. -/
lemma mrt_antitone_weighted_prefix (a : ℕ → ℂ) (b : ℕ → ℝ) {Q : ℝ}
    (hQ : 0 ≤ Q) (hA : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ Q)
    (hb : ∀ n, 0 ≤ b n) (hanti : Antitone b) (N : ℕ) :
    ‖∑ i ∈ range N, (b i : ℂ) * a i‖ ≤ Q * b 0 := by
  cases N with
  | zero => simpa using mul_nonneg hQ (hb 0)
  | succ N =>
    have he : (∑ i ∈ range (N + 1), (b i : ℂ) * a i) =
        (b N : ℂ) * (∑ i ∈ range (N + 1), a i) -
          ∑ i ∈ range N, ((b (i + 1) - b i : ℝ) : ℂ) * (∑ j ∈ range (i + 1), a j) := by
      simpa only [Nat.add_sub_cancel, Complex.real_smul] using
        (sum_range_by_parts b a (N + 1))
    rw [he]
    calc
      _ ≤ ‖(b N : ℂ) * (∑ i ∈ range (N + 1), a i)‖ +
          ‖∑ i ∈ range N, ((b (i + 1) - b i : ℝ) : ℂ) * (∑ j ∈ range (i + 1), a j)‖ :=
        norm_sub_le _ _
      _ ≤ b N * Q + ∑ i ∈ range N, (b i - b (i + 1)) * Q := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb N)]
          exact mul_le_mul_of_nonneg_left (hA (N + 1)) (hb N)
        · apply (norm_sum_le _ _).trans
          apply sum_le_sum
          intro i _
          have hi : b (i + 1) ≤ b i := hanti (Nat.le_succ i)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hi)]
          have hh := mul_le_mul_of_nonneg_left (hA (i + 1)) (sub_nonneg.mpr hi)
          simpa only [neg_sub] using hh
      _ = Q * b 0 := by rw [← sum_mul, sum_range_sub']; ring

lemma mrt_quadratic_remainder_weighted_prefix (a : ℕ → ℂ) {Q t : ℝ}
    (hQ : 0 ≤ Q) (ht : 0 < t) (hA : ∀ n, ‖∑ i ∈ range n, a i‖ ≤ Q) (N : ℕ) :
    ‖∑ i ∈ range N, (mrtQuadraticRemainder (t * (i + 1 : ℕ)) : ℂ) * a i‖ ≤ Q := by
  let b : ℕ → ℝ := fun i => mrtQuadraticRemainder (t * (i + 1 : ℕ))
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact mrt_quadratic_remainder_nonneg (mul_pos ht (by positivity))
  have hanti : Antitone b := by
    intro i j hij
    apply mrt_quadratic_remainder_antitone (mul_pos ht (by positivity))
      (mul_pos ht (by positivity))
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hij 1) ht.le
  exact (mrt_antitone_weighted_prefix a b hQ hA hb hanti N).trans
    (mul_le_of_le_one_right hQ (by simpa only [b, Nat.cast_zero, Nat.cast_add,
      Nat.cast_one, zero_add, mul_one] using
      mrt_quadratic_remainder_le_one ht))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterThermal
namespace OAI

/-! The exponentially smoothed zeta-character convolution differs from
L(1,chi)/t by at most the modulus, uniformly for every positive t. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology


lemma mrt_exp_geometric_power (t : ℝ) (n : ℕ) :
    (Real.exp (-t) : ℂ) ^ n = (Real.exp (-t * n) : ℂ) := by
  norm_cast
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma mrt_exp_geometric_quotient (u : ℝ) (hu : 0 < u) :
    (Real.exp (-u) : ℂ) / (1 - (Real.exp (-u) : ℂ)) =
      1 / ((Real.exp u : ℂ) - 1) := by
  have he : (Real.exp u : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_ne_zero u)
  have he1 : (Real.exp u : ℂ) - 1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)))
  rw [Real.exp_neg, Complex.ofReal_inv]
  field_simp

lemma mrt_character_thermal_lambert {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    mrtCharacterThermal χ t =
      ∑' d : ℕ+, χ (d : ZMod q) / ((Real.exp (t * d) : ℂ) - 1) := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  calc
    _ = ∑' n : ℕ+, χ.zetaMul n * (Real.exp (-t) : ℂ) ^ (n : ℕ) := by
      exact tsum_congr (fun n => by rw [mrt_exp_geometric_power])
    _ = ∑' d : ℕ+, χ (d : ZMod q) * (Real.exp (-t) : ℂ) ^ (d : ℕ) /
        (1 - (Real.exp (-t) : ℂ) ^ (d : ℕ)) :=
      mrt_character_lambert χ (Real.exp_nonneg _) he
    _ = _ := by
      apply tsum_congr
      intro d
      rw [mrt_exp_geometric_power]
      have hu : 0 < t * (d : ℕ) := mul_pos ht (by exact_mod_cast d.pos)
      have hh := mrt_exp_geometric_quotient (t * (d : ℕ)) hu
      have hn : -t * (d : ℕ) = -(t * (d : ℕ)) := by ring
      rw [hn]
      calc
        _ = χ (d : ZMod q) * ((Real.exp (-(t * (d : ℕ))) : ℂ) /
            (1 - (Real.exp (-(t * (d : ℕ))) : ℂ))) := by ring
        _ = _ := by rw [hh]; ring

lemma mrt_character_thermal_lambert_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun d : ℕ+ => χ (d : ZMod q) / ((Real.exp (t * d) : ℂ) - 1)) := by
  have hs := (mrt_character_lambert_pair_summable χ (Real.exp_nonneg (-t))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))).prod
  apply hs.congr
  intro d
  rw [mrt_character_lambert_inner χ (Real.exp_nonneg (-t))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))]
  rw [mrt_exp_geometric_power]
  have hu : 0 < t * (d : ℕ) := mul_pos ht (by exact_mod_cast d.pos)
  have hh := mrt_exp_geometric_quotient (t * (d : ℕ)) hu
  have hn : -t * (d : ℕ) = -(t * (d : ℕ)) := by ring
  rw [hn]
  calc
    _ = χ (d : ZMod q) * ((Real.exp (-(t * (d : ℕ))) : ℂ) /
        (1 - (Real.exp (-(t * (d : ℕ))) : ℂ))) := by ring
    _ = _ := by rw [hh]; ring

lemma mrt_sum_positive_range (f : ℕ → ℂ) (N : ℕ) :
    (∑ i ∈ range N, f (i + 1)) = ∑ n ∈ Icc 1 N, f n := by
  rw [range_eq_Ico, sum_Ico_add' f 0 N 1]
  simp only [Nat.zero_add, Finset.Ico_add_one_right_eq_Icc]

theorem mrt_character_thermal_error {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {t : ℝ} (ht : 0 < t) :
    ‖DirichletCharacter.LFunction χ 1 / (t : ℂ) - mrtCharacterThermal χ t‖ ≤ q := by
  let a : ℕ → ℂ := fun i => χ ((i + 1 : ℕ) : ZMod q)
  have hA (N : ℕ) : ‖∑ i ∈ range N, a i‖ ≤ q := by
    change ‖∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q)‖ ≤ q
    rw [mrt_sum_positive_range (fun n => χ (n : ZMod q)) N]
    exact mrt_character_Icc_norm χ hχ N
  have hfinite (N : ℕ) :
      ‖(∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q) / (i + 1 : ℕ)) / (t : ℂ) -
        ∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q) /
          ((Real.exp (t * (i + 1 : ℕ)) : ℂ) - 1)‖ ≤ q := by
    have hh := mrt_quadratic_remainder_weighted_prefix a (Nat.cast_nonneg q) ht hA N
    convert (preTransparency := .instances) hh using 1
    congr 1
    rw [sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    simp only [mrtQuadraticRemainder, a, Complex.ofReal_sub, Complex.ofReal_inv,
      Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one]
    simp only [mul_inv_rev]
    ring
  have hharm : Tendsto (fun N : ℕ =>
      (∑ i ∈ range N, χ ((i + 1 : ℕ) : ZMod q) / (i + 1 : ℕ)) / (t : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction χ 1 / (t : ℂ))) := by
    have he (N : ℕ) : (∑ i ∈ range N,
        χ ((i + 1 : ℕ) : ZMod q) / (i + 1 : ℕ)) =
        ∑ n ∈ Icc 1 N, χ (n : ZMod q) / (n : ℂ) :=
      mrt_sum_positive_range (fun n => χ (n : ZMod q) / (n : ℂ)) N
    simpa only [he] using (mrt_character_harmonic_tendsto χ hχ).div_const (t : ℂ)
  have hs := (summable_pnat_iff_summable_succ (f := fun d : ℕ =>
    χ (d : ZMod q) / ((Real.exp (t * d) : ℂ) - 1))).mp
      (mrt_character_thermal_lambert_summable χ ht)
  have hlam : Tendsto (fun N : ℕ => ∑ i ∈ range N,
      χ ((i + 1 : ℕ) : ZMod q) / ((Real.exp (t * (i + 1 : ℕ)) : ℂ) - 1))
      atTop (𝓝 (mrtCharacterThermal χ t)) := by
    rw [mrt_character_thermal_lambert χ ht,
      tsum_pnat_eq_tsum_succ (f := fun d => χ (d : ZMod q) /
        ((Real.exp (t * d) : ℂ) - 1))]
    exact hs.hasSum.tendsto_sum_nat
  exact le_of_tendsto' ((hharm.sub hlam).norm) hfinite

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticLower
namespace OAI

/-! A weak effective polynomial lower bound at one for every nonprincipal
quadratic character, obtained from nonnegative convolution coefficients. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology

lemma mrt_character_thermal_nat {q : ℕ} (χ : DirichletCharacter ℂ q)
    {t : ℝ} (ht : 0 < t) :
    mrtCharacterThermal χ t = ∑' n : ℕ, χ.zetaMul n * (Real.exp (-t * n) : ℂ) := by
  have hh := tsum_zero_pnat_eq_tsum_nat (mrt_character_thermal_summable χ ht)
  simpa only [ArithmeticFunction.map_zero, zero_mul, zero_add, mrtCharacterThermal] using hh

lemma mrt_exp_neg_one_ge_quarter : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) (by linarith [Real.exp_one_lt_three])

theorem mrt_quadratic_thermal_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) {t : ℝ} (ht : 0 < t) (K : ℕ)
    (hK : t * (K : ℝ) ^ 2 ≤ 1) :
    (K : ℝ) / 4 ≤ (mrtCharacterThermal χ t).re := by
  let F : ℕ → ℝ := fun n => (χ.zetaMul n).re * Real.exp (-t * n)
  have hF (n : ℕ) : 0 ≤ F n := mul_nonneg
    (mrt_quadratic_coefficient_re_nonneg χ hχ n) (Real.exp_nonneg _)
  have hs : Summable F := by
    simpa only [F, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using (Complex.hasSum_re
        (mrt_character_thermal_summable χ ht).hasSum).summable
  have heq : (mrtCharacterThermal χ t).re = ∑' n, F n := by
    rw [mrt_character_thermal_nat χ ht,
      Complex.re_tsum (mrt_character_thermal_summable χ ht)]
    simp only [F, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [heq]
  calc
    _ = ∑ _n ∈ Icc 1 K, (1 / 4 : ℝ) := by simp; ring
    _ ≤ ∑ n ∈ Icc 1 K, F (n ^ 2) := by
      apply sum_le_sum
      intro n hn
      have hnK : (n : ℝ) ≤ K := by exact_mod_cast (mem_Icc.mp hn).2
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      have hsquare : t * (n : ℝ) ^ 2 ≤ 1 :=
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) hnK 2) ht.le).trans hK
      have hexp : 1 / 4 ≤ Real.exp (-t * (n ^ 2 : ℕ)) := by
        apply mrt_exp_neg_one_ge_quarter.trans
        apply Real.exp_le_exp.mpr
        push_cast
        linarith
      exact hexp.trans (le_mul_of_one_le_left (Real.exp_nonneg _)
        (mrt_quadratic_square_coefficient_re χ hχ n hn0))
    _ = ∑ n ∈ (Icc 1 K).image (fun n : ℕ => n ^ 2), F n := by
      apply (sum_image ?_).symm
      intro a _ b _ hab
      nlinarith
    _ ≤ ∑' n, F n := hs.sum_le_tsum _ (fun n _ => hF n)

theorem mrt_quadratic_LFunction_one_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) :
    1 / (64 * (q : ℝ)) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  let t : ℝ := 1 / (64 * (q : ℝ) ^ 2)
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have ht : 0 < t := by dsimp only [t]; positivity
  have hscale : t * ((8 * q : ℕ) : ℝ) ^ 2 ≤ 1 := by
    dsimp only [t]
    push_cast
    field_simp
    norm_num
  have hlower := mrt_quadratic_thermal_lower χ hsq ht (8 * q) hscale
  have herr := mrt_character_thermal_error χ hχ ht
  have hnorm : (2 * q : ℝ) ≤ ‖mrtCharacterThermal χ t‖ := by
    have hre := (Complex.abs_re_le_norm (mrtCharacterThermal χ t))
    push_cast at hlower
    have hle := (le_abs_self (mrtCharacterThermal χ t).re).trans hre
    linarith
  have htri := norm_sub_le (DirichletCharacter.LFunction χ 1 / (t : ℂ))
    (DirichletCharacter.LFunction χ 1 / (t : ℂ) - mrtCharacterThermal χ t)
  have hid : DirichletCharacter.LFunction χ 1 / (t : ℂ) -
      (DirichletCharacter.LFunction χ 1 / (t : ℂ) - mrtCharacterThermal χ t) =
      mrtCharacterThermal χ t := by ring
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at htri
  have hdiv : (q : ℝ) ≤ ‖DirichletCharacter.LFunction χ 1‖ / t := by linarith
  have hh := (le_div_iff₀ ht).mp hdiv
  have heq : (q : ℝ) * t = 1 / (64 * (q : ℝ)) := by
    dsimp only [t]
    field_simp
  rwa [heq] at hh

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticDisk
namespace OAI

/-! An effective disk about one for a real quadratic character. The
radius is polynomial in the modulus and does not use an exceptional-zero input. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Metric
open scoped _root_.Classical

lemma mrt_character_LFunction_deriv_local {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : ‖s - 1‖ ≤ (1 / 4 : ℝ)) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ 12 * q := by
  have hd := (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
    (s := ball s (1 / 4))
  have hb : ∀ z ∈ sphere s (1 / 4 : ℝ), ‖DirichletCharacter.LFunction χ z‖ ≤ 3 * q := by
    intro z hz
    have hzdist : ‖z - s‖ = (1 / 4 : ℝ) := by simpa only [mem_sphere_iff_norm] using hz
    have hz1 : ‖z - 1‖ ≤ (1 / 2 : ℝ) := by
      have hh := norm_sub_le_norm_sub_add_norm_sub z s (1 : ℂ)
      linarith
    have hr : (1 / 2 : ℝ) ≤ z.re := by
      have hh := (Complex.abs_re_le_norm (z - 1)).trans hz1
      rw [Complex.sub_re, Complex.one_re] at hh
      linarith [(abs_le.mp hh).1]
    have hn : ‖z‖ ≤ (3 / 2 : ℝ) := by
      have hh := norm_sub_le_norm_sub_add_norm_sub z (1 : ℂ) 0
      simp only [sub_zero, norm_one] at hh
      linarith
    exact (mrt_character_LFunction_norm_halfPlane χ hχ hr).trans (by
      have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (2 * q : ℝ))
      nlinarith)
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) hd hb
  norm_num at hh ⊢
  linarith

lemma mrt_character_LFunction_local_difference {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : ‖s - 1‖ ≤ (1 / 4 : ℝ)) :
    ‖DirichletCharacter.LFunction χ s - DirichletCharacter.LFunction χ 1‖ ≤
      (12 * q : ℝ) * ‖s - 1‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (s := closedBall (1 : ℂ) (1 / 4))
    (fun z _ => DirichletCharacter.differentiable_LFunction hχ z)
    (fun z hz => mrt_character_LFunction_deriv_local χ hχ
      (by simpa only [mem_closedBall_iff_norm] using hz))
    (convex_closedBall (1 : ℂ) (1 / 4))
  · exact mem_closedBall_self (by norm_num)
  · simpa only [mem_closedBall_iff_norm] using hs

theorem mrt_quadratic_near_one_nonzero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (1536 * (q : ℝ) ^ 2)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  have hr : 1 / (1536 * (q : ℝ) ^ 2) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 1536 * (q : ℝ) ^ 2)).mpr
    nlinarith
  have hh := mrt_character_LFunction_local_difference χ hχ (hs.trans hr)
  have hl := mrt_quadratic_LFunction_one_lower χ hχ hsq
  intro hz
  rw [hz, zero_sub, norm_neg] at hh
  have hu := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (12 * q : ℝ))
  have he : (12 * q : ℝ) * (1 / (1536 * (q : ℝ) ^ 2)) = 1 / (128 * q) := by
    field_simp
    ring
  rw [he] at hu
  have hlt : 1 / (128 * (q : ℝ)) < 1 / (64 * (q : ℝ)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith
  exact (not_lt_of_ge (hl.trans (hh.trans hu))) hlt

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Rectangle
namespace Erdos970

open _root_.Complex _root_.Set _root_.Topology

open scoped _root_.Interval

variable {z w : ℂ} {c : ℝ}

namespace Rectangle



end Rectangle




@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl

@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl





































end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ResidueCalcOnRectangles
namespace Erdos970

open _root_.Complex _root_.BigOperators _root_.Nat _root_.Classical _root_.Real _root_.Topology _root_.Filter
open _root_.Set _root_.MeasureTheory _root_.intervalIntegral _root_.Asymptotics

open scoped _root_.Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
















theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩







































lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U






























end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Sobolev
namespace Erdos970

open _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap _root_.BigOperators
open scoped _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun




section lemmas




end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun



















end CS

namespace trunc







end trunc

namespace W1











end W1

namespace W21













end W21


end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.Fourier
namespace Erdos970

open _root_.FourierTransform _root_.Real _root_.Complex _root_.MeasureTheory _root_.Filter _root_.Topology _root_.BoundedContinuousFunction _root_.SchwartzMap VectorFourier _root_.BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]


@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl



@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas


@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv






end Erdos970

end

section
-- module Solutions.OAIChowla.PrimeNumberTheoremAnd.Erdos970.ZetaBounds
namespace Erdos970


open _root_.Complex _root_.Topology _root_.Filter _root_.Interval _root_.Set _root_.Asymptotics






local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by
                                                                
  have h_event : ∀ᶠ s in 𝓝[≠] p, ‖(s - p) * f s - A‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_nhds :
      ∀ᶠ s in 𝓝 p, s ≠ p → ‖(s - p) * f s - A‖ < 1 := by
    exact (eventually_nhdsWithin_iff).1 h_event
  rcases (eventually_nhds_iff.1 h_event_nhds) with ⟨V₀, hV₀_mem, hV₀_prop⟩
  have h_bound :
      ∀ s, s ∈ V₀ \ {p} → ‖(s - p) * f s‖ ≤ ‖A‖ + 1 := by
    intro s hs
    rcases hs with ⟨hV₀, hsne⟩
    calc ‖(s - p) * f s‖ = ‖((s - p) * f s - A) + A‖ := by
          ring_nf
        _ ≤ ‖(s - p) * f s - A‖ + ‖A‖ := norm_add_le ((s - p) * f s - A) A
        _ ≤ 1 + ‖A‖ := add_le_add_left (le_of_lt (hV₀_mem s hV₀ hsne)) ‖A‖
        _ = ‖A‖ + 1 := add_comm 1 ‖A‖
  have h_bdd :
      BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (V₀ \ {p})) := by
    refine ⟨‖A‖ + 1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact h_bound s hs
                                                                 
  set W : Set ℂ := V₀ ∩ U with hW_def
  have hW_mem : (W : Set ℂ) ∈ 𝓝 p := inter_mem (IsOpen.mem_nhds hV₀_prop.1 hV₀_prop.2) hU
  have h_subset_V₀ : (W \ {p}) ⊆ (V₀ \ {p}) := by
    intro z hz; exact ⟨hz.1.1, hz.2⟩
  have h_prod_holo : HolomorphicOn (fun z ↦ (z - p) * f z) (W \ {p}) := by
    have h_id : HolomorphicOn (fun z : ℂ ↦ z - p) (W \ {p}) :=
      Differentiable.differentiableOn (Differentiable.sub_const differentiable_fun_id p)
    have hfW : HolomorphicOn f (W \ {p}) := by
      apply hf.mono
      exact Set.sdiff_subset_sdiff_left inter_subset_right
    simpa using! h_id.mul hfW
  have h_bdd_W : BddAbove (norm ∘ (fun s ↦ (s - p) * f s) '' (W \ {p})) :=
    h_bdd.mono (image_mono h_subset_V₀)
                                                                    
  obtain ⟨g, hg_holo, hg_eq⟩ :=
    existsDifferentiableOn_of_bddAbove hW_mem h_prod_holo h_bdd_W
  have h_event_eq :
      (fun z ↦ g z) =ᶠ[𝓝[≠] p] fun z ↦ (z - p) * f z := by
    have hW_diff_mem : (W \ {p} : Set ℂ) ∈ 𝓝[≠] p :=
      sdiff_mem_nhdsWithin_compl hW_mem {p}
    exact (hg_eq.eventuallyEq_of_mem hW_diff_mem).symm
  have h_tendsto_gA : Tendsto g (𝓝[≠] p) (𝓝 A) :=
      h_limit.congr' (id (EventuallyEq.symm h_event_eq))
  have hpW : p ∈ W := by
    exact mem_of_mem_nhds hW_mem
  have h_cont_g : ContinuousAt g p := by
    apply (hg_holo.continuousOn.continuousWithinAt hpW).continuousAt hW_mem
  have h_tendsto_gp : Tendsto g (𝓝[≠] p) (𝓝 (g p)) :=
    h_cont_g.tendsto.mono_left inf_le_left
  have g_p_eq : g p = A :=
    tendsto_nhds_unique' (NormedField.nhdsNE_neBot p) h_tendsto_gp h_tendsto_gA
  let q : ℂ → ℂ := fun z ↦ (g z - A) / (z - p)
  have h_deriv : HasDerivAt g (deriv g p) p := by
    exact DifferentiableOn.hasDerivAt hg_holo hW_mem
  have h_q_limit : Tendsto q (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [hasDerivAt_iff_tendsto_slope] at h_deriv
    unfold slope at h_deriv
    simp only [vsub_eq_sub, smul_eq_mul, inv_mul_eq_div, g_p_eq] at h_deriv
    exact h_deriv
  have h_event_q : ∀ᶠ z in 𝓝[≠] p, ‖q z - deriv g p‖ < 1 := by
    simp_rw [← dist_eq_norm_sub]
    exact h_q_limit.eventually (Metric.ball_mem_nhds _ (by norm_num))
  have h_event_q_nhds : ∀ᶠ z in 𝓝 p, z ≠ p → ‖q z - deriv g p‖ < 1 := by
    simpa using (eventually_nhdsWithin_iff).1 h_event_q
  rcases (eventually_nhds_iff.1 h_event_q_nhds) with
    ⟨V₁, hV₁_mem, hV₁_prop⟩
  have h_q_bound :
      ∀ z, z ∈ V₁ \ {p} → ‖q z‖ ≤ ‖deriv g p‖ + 1 := by
    intro z hz
    rcases hz with ⟨hV₁, hz_ne⟩
    calc ‖q z‖ = ‖(q z - deriv g p) + (deriv g p)‖ := by
          ring_nf
        _ ≤ ‖q z - deriv g p‖ + ‖deriv g p‖ := norm_add_le (q z - deriv g p) (deriv g p)
        _ ≤ 1 + ‖deriv g p‖  := add_le_add_left (le_of_lt (hV₁_mem z hV₁ hz_ne)) ‖deriv g p‖
        _ = ‖deriv g p‖ + 1 := add_comm 1 ‖deriv g p‖
                                                   
  have h_eq_diff :
      EqOn (fun z ↦ f z - A * (z - p)⁻¹) q (W \ {p}) := by
    intro z hz
    simp only
    have hz_ne : (z - p) ≠ 0 := sub_ne_zero.mpr hz.2
    have hgz : g z = (z - p) * f z := by
      exact id (EqOn.symm hg_eq) hz
    simp only [hgz, q]
    field_simp
  apply IsBigO_to_BddAbove
  rw [isBigO_iff]
  use ‖deriv g p‖ + 1
  apply eventually_nhdsWithin_iff.mpr
  filter_upwards [IsOpen.mem_nhds hV₁_prop.1 hV₁_prop.2, hW_mem] with z hV₁ hW z_ne_p
  specialize h_eq_diff ⟨ hW, z_ne_p⟩
  simp only [Pi.sub_apply, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary,
    mul_one] at h_eq_diff ⊢
  rw [h_eq_diff]
  exact h_q_bound _ ⟨hV₁, z_ne_p⟩



theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  have zeta_holc : HolomorphicOn ζ (univ \ {1}) := by
    intro y hy
    exact DifferentiableAt.differentiableWithinAt <| differentiableAt_riemannZeta hy.2
  convert (preTransparency := .instances) ResidueOfTendsTo univ_mem zeta_holc riemannZeta_residue_one using 6
  simp

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by
  intro x hx
  apply EventuallyEq.deriv_eq
  filter_upwards [IsOpen.mem_nhds (hU_open.sdiff isClosed_singleton) hx] with t ht using h_eq ht

theorem analytic_deriv_bounded_near_point
    (f : ℂ → ℂ) {U : Set ℂ} {p : ℂ} (hU : IsOpen U) (hp : p ∈ U) (hf : HolomorphicOn f U) :
    (deriv f) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  have U_in_filter : U ∈ 𝓝 p := by
    exact IsOpen.mem_nhds hU hp
  have T := (analyticOn_iff_differentiableOn hU).mpr hf
  have T2 : ContDiffOn ℂ 1 f U :=
      DifferentiableOn.contDiffOn hf hU
  have T3 : ContinuousOn (fun x ↦ ((deriv f) x)) U := by
    apply T2.continuousOn_deriv_of_isOpen hU (by simp)
  have T4 := T3.continuousAt U_in_filter
  have T5 : (deriv f) =O[𝓝 p] (1 : ℂ → ℂ) :=
    T4.norm.isBoundedUnder_le.isBigO_one ℂ
  exact Asymptotics.IsBigO.mono T5 inf_le_left

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by
  rw [deriv_add (by fun_prop) (by fun_prop), deriv_const, deriv_mul hg (by fun_prop)]
  simp

lemma deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by
  rw [deriv_fun_inv'' (by fun_prop) (by grind)]
  simp
  field

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by
  have h1 : DifferentiableAt ℂ (fun z => (z - p)⁻¹) x := by
    fun_prop (disch := grind)
  rw [deriv_sub hf (h1.const_mul A), deriv_const_mul A h1, deriv_inv_sub hp]
  ring

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by

  have h_decomp : ∀ s, f s = (f s - A * (s - p)⁻¹) + A * (s - p)⁻¹ := by
    intro s
    ring
                                      
  obtain ⟨M, hM⟩ := f_near_p

  have A_norm_pos : 0 < ‖A‖ := norm_pos_iff.mpr A_ne_zero
                                                                        
  let δ := ‖A‖ / (‖M‖ + 1)
  have δ_pos : 0 < δ := by
    refine div_pos A_norm_pos (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)
                                                                            
  obtain ⟨V, hV_open, hV_mem, hV_sub⟩ : ∃ V, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∩ Metric.ball p δ := by
                                     
    obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp U_in_nhds
    let V := W ∩ Metric.ball p δ
    have VNp : V ∈ 𝓝 p := (𝓝 p).inter_mem (IsOpen.mem_nhds hW_open hW_mem)
      (Metric.ball_mem_nhds p δ_pos)
    exact ⟨V, IsOpen.inter hW_open Metric.isOpen_ball, mem_of_mem_nhds VNp,
      inter_subset_inter_left _ hW_sub⟩
  use V, mem_nhds_iff.mpr ⟨V, subset_refl V, hV_open, hV_mem⟩, hV_open
                    
  intro s hs
  have hs_in_U : s ∈ U := hV_sub hs.1 |>.1
  have hs_near_p : dist s p < δ := hV_sub hs.1 |>.2
  have hs_ne_p : s ≠ p := hs.2
                                                              
  rw [h_decomp s]
                                 
  have bound_first : ‖f s - A * (s - p)⁻¹‖ ≤ M := by
    apply hM
    exact ⟨s, ⟨hs_in_U, hs_ne_p⟩, rfl⟩
                                      
  have large_second : ‖M‖ + 1 < ‖A * (s - p)⁻¹‖ := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    rw [lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs_ne_p))]
    rw [mul_comm, ← lt_div_iff₀ (add_pos_of_nonneg_of_pos (norm_nonneg M) one_pos)]
    rw [dist_eq_norm_sub] at hs_near_p
    exact hs_near_p
                                                
  by_contra h_zero
                                                                  
  rw [add_eq_zero_iff_eq_neg] at h_zero
  rw [h_zero, norm_neg] at bound_first
                                    
  have : ‖M‖ + 1 < ‖M‖ := (lt_of_lt_of_le (lt_of_lt_of_le large_second bound_first)
    (Real.le_norm_self M))
  norm_num at this

theorem logDerivResidue' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by

  have simpleHolo : HolomorphicOn (fun s ↦ A / (s - p)) (U \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by rw [sub_ne_zero]; exact hx
    · rintro s ⟨_, hs⟩ ; exact hs

  have f_minus_pole_is_holomorphic : HolomorphicOn (f - (fun s ↦ A * (s - p)⁻¹)) (U \ {p}) := by
    exact (DifferentiableOn.sub_iff_right holc).mpr simpleHolo

  let ⟨g, ⟨g_is_holomorphic, g_is_f_minus_pole⟩⟩ := existsDifferentiableOn_of_bddAbove
    U_in_nhds f_minus_pole_is_holomorphic f_near_p

  let h := (fun _ ↦ A) + g * (fun (s : ℂ) ↦ (s - p))

  have linear_is_holomorphic : HolomorphicOn (fun (s : ℂ ) ↦ (s - p)) U := by
    exact DifferentiableOn.sub_const differentiableOn_id p

  have h_is_holomorphic : HolomorphicOn h U := by
    have T := DifferentiableOn.mul g_is_holomorphic linear_is_holomorphic
    exact DifferentiableOn.const_add A T

  have h_continuous : ContinuousOn h U :=
    by exact DifferentiableOn.continuousOn h_is_holomorphic

  have deriv_h_identity : ∀x ∈ (U \ {p}), (deriv h) x = f x + (deriv f x) * (x - p) := by
    intro x x_in_u_not_p
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff x_in_u_not_p
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2

    have weird : U ∈ 𝓝 x := by
      exact IsOpen.mem_nhds (U_is_open) (x_in_u)

    rw [derivative_const_plus_product, ← g_is_f_minus_pole x_in_u_not_p,
      ← deriv_eqOn_of_eqOn_punctured _ _ U p U_is_open g_is_f_minus_pole x_in_u_not_p,
      deriv_f_minus_A_inv_sub_clean]
    · simp only [Pi.sub_apply]
      have := sub_ne_zero_of_ne x_not_p
      field_simp
      ring
    · apply holc.differentiableAt
      exact Filter.inter_mem weird <| compl_singleton_mem_nhds x_not_p
    · exact x_not_p
    · exact g_is_holomorphic.differentiableAt weird
  have h_identity : ∀x ∈ (U \ {p}), h x = (f x) * (x - p)  := by
    intro x x_in_u_not_p
    have hyp_x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp x_in_u_not_p).2
    simp only [h, Pi.add_apply, Pi.mul_apply]
    rw [← g_is_f_minus_pole x_in_u_not_p]
    simp only [Pi.sub_apply]
    field [sub_ne_zero.mpr hyp_x_not_p]
  have log_deriv_f_plus_pole_equal_log_deriv_h :
      EqOn (deriv f * f⁻¹ + fun s ↦ (s - p)⁻¹) ((deriv h) * h⁻¹) (U \ {p}) := by
    simp only [Set.mem_sdiff, mem_singleton_iff, ne_eq, and_imp, Function.comp_apply, Pi.sub_apply,
      DifferentiableOn.sub_iff_right, differentiableOn_const, DifferentiableOn.fun_sub_iff_left,
      holc] at *
    intro x hyp_x
    have x_not_p : x ≠ p := by
      exact ((Set.mem_sdiff x).mp hyp_x).2
    have x_in_u : x ∈ U := by exact Set.mem_of_mem_sdiff hyp_x
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply]
    rw [deriv_h_identity _ x_in_u x_not_p, h_identity _ x_in_u x_not_p]

    field [sub_ne_zero.mpr x_not_p, non_zero x (x_in_u) x_not_p]
  have h_inv_bounded :
      h⁻¹ =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
    have : ContinuousAt h⁻¹ p := by
      apply ContinuousOn.continuousAt h_continuous U_in_nhds |>.inv₀
      simp [h, A_ne_zero]
    exact Asymptotics.IsBigO.mono (this.norm.isBoundedUnder_le.isBigO_one ℂ) inf_le_left

  have h_deriv_bounded :
        (deriv h) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
          analytic_deriv_bounded_near_point h U_is_open
            (by exact mem_of_mem_nhds U_in_nhds) h_is_holomorphic

  have h_log_deriv_bounded :
    ((deriv h) * h⁻¹) =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
      have T := Asymptotics.IsBigO.mul h_deriv_bounded h_inv_bounded
      exact IsBigO.of_const_mul_right T

  have u_not_p_in_filter : U \ {p} ∈ 𝓝[≠] p := by
    exact sdiff_mem_nhdsWithin_compl U_in_nhds {p}
  have T := Set.EqOn.eventuallyEq_of_mem log_deriv_f_plus_pole_equal_log_deriv_h u_not_p_in_filter
  exact EventuallyEq.trans_isBigO T h_log_deriv_bounded

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) :=
    by
      let ⟨U', ⟨a,b,c⟩⟩ := mem_nhds_iff.mp U_in_nhds
      have W : (U' \ {p}) ⊆ U' := by
        exact Set.sdiff_subset

      have T : (U' \ {p}) ⊆ (U \ {p}) := by
        exact Set.sdiff_subset_sdiff a (subset_refl _)

      refine logDerivResidue' b ?_ ?_ (IsOpen.mem_nhds b c) A_ne_zero ?_
      · intro x hyp_x
        exact non_zero x <| T hyp_x
      · exact DifferentiableOn.mono holc T
      · exact (f_near_p.mono (image_mono (Set.sdiff_subset_sdiff a (subset_refl _))))

lemma BddAbove_to_IsBigO {f : ℂ → ℂ} {p : ℂ}
    {U : Set ℂ} (hU : U ∈ 𝓝 p) (bdd : BddAbove (norm ∘ f '' (U \ {p}))) :
    f =O[𝓝[≠] p] (1 : ℂ → ℂ)  := by
  dsimp [BddAbove, upperBounds] at bdd
  rcases bdd with ⟨C, hC⟩

  have h : ∀ x ∈ U \ {p}, ‖f x‖ ≤ C := by
    intro x hx
    have fx_is_norm : ‖f x‖ ∈ norm ∘ f ''(U \ {p}) := by
      exact ⟨x, hx, rfl⟩
    exact hC fx_is_norm

  rw [Asymptotics.isBigO_iff]
  use C
  rw [eventually_nhdsWithin_iff]
  simp only [Set.mem_sdiff, mem_singleton_iff, and_imp, mem_compl_iff, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one] at h ⊢
  filter_upwards [hU] using h

theorem logDerivResidue'' {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by
  apply IsBigO_to_BddAbove
  exact logDerivResidue non_zero holc U_in_nhds A_ne_zero f_near_p


theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by
  obtain ⟨U,U_in_nhds, hU⟩ := riemannZetaResidue
  have hU' : BddAbove (norm ∘ (ζ - fun s ↦ 1 * (s - 1)⁻¹) '' (U \ {1})) := by
    simp only [Function.comp_apply, Pi.sub_apply, one_mul] at hU ⊢
    exact hU
  obtain ⟨V,V_in_nhds, V_is_open, hV⟩ := nonZeroOfBddAbove U_in_nhds one_ne_zero hU'
  let W := V ∩ interior U
  have hW : ∀ s ∈ W \ {1}, ζ s ≠ 0 := by
    intro s hs
    have s_in_V_diff : s ∈ V \ {1} := ⟨hs.1.1, hs.2⟩
    exact hV s s_in_V_diff
  have ζ_holc: HolomorphicOn ζ (W \ {1}) := by
    intro y hy
    simp only [Set.mem_sdiff, mem_singleton_iff] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    apply differentiableAt_riemannZeta hy.2
  have W_in_nhds : W ∈ 𝓝 1 := by
    refine inter_mem V_in_nhds ?_
    exact interior_mem_nhds.mpr U_in_nhds
  have := logDerivResidue'' hW ζ_holc W_in_nhds one_ne_zero
  have HW : BddAbove (norm ∘ (ζ - fun s ↦ (s - 1)⁻¹) '' (W \ {1})) := by
    obtain ⟨c, hc⟩ := bddAbove_def.mp hU
    apply bddAbove_def.mpr
    use c
    rintro y ⟨x, x_in_W, fxy⟩
    apply hc
    exact ⟨x, ⟨interior_subset x_in_W.1.2, x_in_W.2⟩, fxy⟩
  simp only [one_mul] at this
  have aux: ∀ a, ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by
    intro a
    calc ‖-(deriv ζ a / ζ a) - (a - 1)⁻¹‖
         = ‖-((deriv ζ a / ζ a) + (a - 1)⁻¹)‖ := by ring_nf
       _ = ‖(deriv ζ a / ζ a) + (a - 1)⁻¹‖ := by rw [norm_neg]
  simp only [Function.comp_apply, Pi.sub_apply] at hU
  simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply, aux]
  apply this HW

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
  obtain ⟨U, hU, bdd⟩ := riemannZetaLogDerivResidue
  convert (preTransparency := .instances) BddAbove_to_IsBigO hU bdd using 2
  rw [neg_div]


local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

































































































































open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
                                                              



end Erdos970

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterLogGrowth
namespace OAI

/-! One absolute constant in the nonprincipal disk bounds, with all
modulus and height dependence kept in log(q*(abs(t)+2)). -/

namespace TwoPointCorrelations


lemma mrt_character_height_split (q : ℕ) [NeZero q] (t : ℝ) :
    mrtCharacterHeight q t=Real.log (q:ℝ)+Real.log (|t|+2) := by
  exact Real.log_mul (by exact_mod_cast NeZero.ne q) (by positivity)

lemma mrt_character_height_ge (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (|t|+2) ≤ mrtCharacterHeight q t := by
  rw [mrt_character_height_split]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  linarith [Real.log_nonneg hq]


lemma mrt_character_log_modulus_le_height (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (q:ℝ) ≤ mrtCharacterHeight q t := by
  rw [mrt_character_height_split]
  linarith [Real.log_nonneg (show 1 ≤ |t|+2 by linarith [abs_nonneg t])]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrincipalCorrection
namespace OAI

/-! The principal character differs from zeta by the Euler factors at
primes dividing its modulus. Their total logarithmic derivative has norm
at most log(q), uniformly on Re(s)>=1. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Finset _root_.Filter
open scoped _root_.Classical _root_.Topology


lemma mrt_principal_factor_cpow_norm {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) : ‖(p:ℂ)^(-s)‖≤1/(p:ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos,Complex.neg_re]
  calc
    _ ≤ (p:ℝ)^(-(1:ℝ)) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hp.one_le) (by linarith)
    _ = _ := by rw [Real.rpow_neg_one,one_div]

lemma mrt_principal_factor_norm_ge {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) : (1/2:ℝ)≤‖mrtPrincipalEulerFactor p s‖ := by
  have hh := norm_sub_norm_le (1:ℂ) ((p:ℂ)^(-s))
  have hb := mrt_principal_factor_cpow_norm hp hs
  have hi : 1/(p:ℝ)≤1/2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)
  simp only [norm_one] at hh
  change _≤‖1-(p:ℂ)^(-s)‖
  linarith

lemma mrt_principal_factor_ne_zero {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) : mrtPrincipalEulerFactor p s≠0 := by
  have hh := mrt_principal_factor_norm_ge hp hs
  intro he
  rw [he,norm_zero] at hh
  norm_num at hh

lemma mrt_principal_factor_hasDeriv {p : ℕ} (hp : p≠0) (s : ℂ) :
    HasDerivAt (mrtPrincipalEulerFactor p) ((p:ℂ)^(-s)*Complex.log p) s := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp
  have hh := (hasDerivAt_id s).neg.const_cpow (c := (p:ℂ)) (Or.inl hpC)
  change HasDerivAt (fun z => 1-(p:ℂ)^(-z)) _ s
  convert (preTransparency := .instances) hh.const_sub (1:ℂ) using 1 <;> simp

lemma mrt_principal_factor_logderiv_norm {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1≤ s.re) :
    ‖logDeriv (mrtPrincipalEulerFactor p) s‖≤ Real.log (p:ℝ) := by
  have hl : 0≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlog : ‖Complex.log (p:ℂ)‖=Real.log (p:ℝ) := by
    rw [← Complex.ofReal_natCast,←Complex.ofReal_log (Nat.cast_nonneg p),
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl]
  have hd := mrt_principal_factor_norm_ge hp hs
  have hn := mrt_principal_factor_cpow_norm hp hs
  have hi : 1/(p:ℝ)≤‖mrtPrincipalEulerFactor p s‖ :=
    (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)).trans hd
  rw [logDeriv_apply,(mrt_principal_factor_hasDeriv hp.ne_zero s).deriv,
    norm_div,norm_mul,hlog]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hd)).mpr
  calc
    _ ≤ (1/(p:ℝ))*Real.log (p:ℝ) := mul_le_mul_of_nonneg_right hn hl
    _ ≤ ‖mrtPrincipalEulerFactor p s‖*Real.log (p:ℝ) :=
      mul_le_mul_of_nonneg_right hi hl
    _ = _ := by ring

lemma mrt_prime_factor_log_sum {q : ℕ} (hq : q≠0) :
    (∑ p∈q.primeFactors,Real.log (p:ℝ))≤ Real.log (q:ℝ) := by
  have hp (p : ℕ) (hp : p∈q.primeFactors) : (0:ℝ)< p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hprod : (0:ℝ)<∏ p∈q.primeFactors,(p:ℝ) := prod_pos hp
  have hle : (∏ p∈q.primeFactors,(p:ℝ))≤(q:ℝ) := by
    have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) q.prod_primeFactors_dvd
    simpa only [Nat.cast_prod] using
      (Nat.cast_le.mpr hh : ((∏ p∈q.primeFactors,p : ℕ):ℝ)≤(q:ℝ))
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  exact Real.log_le_log hprod hle

theorem mrt_principal_logderiv {q : ℕ} [NeZero q] {s : ℂ} (hs : 1< s.re) :
    logDeriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q)) s =
      (∑ p∈q.primeFactors,logDeriv (mrtPrincipalEulerFactor p) s)+
        logDeriv riemannZeta s := by
  let e : ℂ→ℂ := fun z => ∏ p∈q.primeFactors,mrtPrincipalEulerFactor p z
  have he (p : ℕ) (hp : p∈q.primeFactors) : mrtPrincipalEulerFactor p s≠0 :=
    mrt_principal_factor_ne_zero (Nat.prime_of_mem_primeFactors hp) hs.le
  have hd (p : ℕ) (hp : p∈q.primeFactors) :
      DifferentiableAt ℂ (mrtPrincipalEulerFactor p) s :=
    (mrt_principal_factor_hasDeriv (Nat.prime_of_mem_primeFactors hp).ne_zero s).differentiableAt
  have hene : e s≠0 := prod_ne_zero_iff.mpr he
  have hed : DifferentiableAt ℂ e s := DifferentiableAt.fun_finsetProd hd
  have hs1 : s≠1 := by intro h; rw [h] at hs; norm_num at hs
  have heq : DirichletCharacter.LFunction (1:DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => e z*riemannZeta z := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz
  have hh := (logDeriv_congr_nhds heq).self_of_nhds
  rw [logDeriv_mul s hene (riemannZeta_ne_zero_of_one_le_re hs.le)
    hed (differentiableAt_riemannZeta hs1)] at hh
  have hprod : logDeriv e s=∑ p∈q.primeFactors,logDeriv (mrtPrincipalEulerFactor p) s :=
    logDeriv_prod he hd
  rw [hprod] at hh
  exact hh

theorem mrt_principal_logderiv_error {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1< s.re) :
    ‖logDeriv (DirichletCharacter.LFunction (1:DirichletCharacter ℂ q)) s-
      logDeriv riemannZeta s‖≤ Real.log (q:ℝ) := by
  rw [mrt_principal_logderiv hs,add_sub_cancel_right]
  calc
    _ ≤ ∑ p∈q.primeFactors,‖logDeriv (mrtPrincipalEulerFactor p) s‖ := norm_sum_le _ _
    _ ≤ ∑ p∈q.primeFactors,Real.log (p:ℝ) :=
      sum_le_sum (fun p hp => mrt_principal_factor_logderiv_norm
        (Nat.prime_of_mem_primeFactors hp) hs.le)
    _ ≤ _ := mrt_prime_factor_log_sum (NeZero.ne q)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterPositivity
namespace OAI

/-! The de la Vallée Poussin positivity inequality for arbitrary positive modulus.
The proof is termwise and uses the actual Mangoldt Dirichlet series.
It does not assume a zero-free region or a prime-number estimate.
-/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation

variable {q : ℕ}


lemma mrtCharacter_three_four_one_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hn : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := sq_le_sq₀ (norm_nonneg z) zero_le_one |>.mpr hz
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq, one_pow] using this
  have hs := sq_nonneg (z.re + 1)
  simp only [pow_two, Complex.mul_re]
  nlinarith

lemma mrtCharacter_phase_norm (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖(n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

lemma mrtCharacter_twisted_phase_norm (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rw [norm_mul, mrtCharacter_phase_norm n hn t, mul_one]
  exact χ.norm_le_one _

lemma mrtCharacter_real_mangoldt_term (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n =
      ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg,
    ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_mul]

lemma mrtCharacter_twisted_mangoldt_term (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term (mrtCharacterMangoldtTwist χ) ((σ : ℂ) + Complex.I * (t : ℂ)) n =
      ((vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) *
        (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, neg_add,
    Complex.cpow_add _ _ (by exact_mod_cast hn)]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow n.cast_nonneg]
  simp only [mrtCharacterMangoldtTwist, Complex.ofReal_mul]
  ring

lemma mrtCharacter_double_phase (χ : DirichletCharacter ℂ q) (n : ℕ) (t : ℝ) :
    (χ ^ 2) (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * ((2 * t : ℝ) : ℂ))) =
      (χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) ^ 2 := by
  rw [χ.pow_apply' (by decide : 2 ≠ 0)]
  rw [show -(Complex.I * ((2 * t : ℝ) : ℂ)) =
      (2 : ℕ) * (-(Complex.I * (t : ℂ))) by push_cast; ring,
    Complex.cpow_nat_mul, mul_pow]

lemma mrtCharacter_mangoldt_term_positivity (χ : DirichletCharacter ℂ q)
    (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun m => (vonMangoldt m : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (mrtCharacterMangoldtTwist χ)
        ((σ : ℂ) + Complex.I * (t : ℂ)) n).re +
      (LSeries.term (mrtCharacterMangoldtTwist (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, Complex.zero_re, mul_zero, add_zero, le_refl]
  rw [mrtCharacter_real_mangoldt_term σ n hn,
    mrtCharacter_twisted_mangoldt_term χ σ t n hn,
    mrtCharacter_twisted_mangoldt_term (χ ^ 2) σ (2 * t) n hn,
    mrtCharacter_double_phase]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hpoly := mrtCharacter_three_four_one_nonneg (mrtCharacter_twisted_phase_norm χ n hn t)
  simp only [Complex.mul_re] at hpoly
  have ha : 0 ≤ vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)
  nlinarith [mul_nonneg ha hpoly]

/-- Positivity of the three actual, absolutely convergent Mangoldt series. -/
theorem mrtCharacter_mangoldt_series_positivity (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (LSeries (fun m => (vonMangoldt m : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (mrtCharacterMangoldtTwist χ) ((σ : ℂ) + Complex.I * (t : ℂ))).re +
      (LSeries (mrtCharacterMangoldtTwist (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re := by
  have hs0 : 1 < (σ : ℂ).re := hσ
  have hs1 : 1 < ((σ : ℂ) + Complex.I * (t : ℂ)).re := by simpa using hσ
  have hs2 : 1 < ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)).re := by simpa using hσ
  have h0 := Complex.hasSum_re (LSeriesSummable_vonMangoldt hs0).LSeriesHasSum
  have h1 := Complex.hasSum_re (χ.LSeriesSummable_twist_vonMangoldt hs1).LSeriesHasSum
  have h2 := Complex.hasSum_re ((χ ^ 2).LSeriesSummable_twist_vonMangoldt hs2).LSeriesHasSum
  exact (((h0.mul_left 3).add (h1.mul_left 4)).add h2).nonneg
    (mrtCharacter_mangoldt_term_positivity χ σ t)

lemma mrtCharacter_twisted_series_logderiv [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (mrtCharacterMangoldtTwist χ) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact χ.LSeries_twist_vonMangoldt_eq hs

/-- The general-character logarithmic-derivative inequality needed by the
quantitative zero-free-region proof. -/
theorem mrtCharacter_logderiv_positivity [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re +
      4 * (-deriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + Complex.I * (t : ℂ)) /
        DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re +
      (-deriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ)) /
        DirichletCharacter.LFunction (χ ^ 2)
          ((σ : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re := by
  have h := mrtCharacter_mangoldt_series_positivity χ hσ t
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ,
    mrtCharacter_twisted_series_logderiv χ (by simpa using hσ),
    mrtCharacter_twisted_series_logderiv (χ ^ 2) (by simpa using hσ)] at h
  exact h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterHighZeros
namespace OAI

/-! A classical logarithmic zero-free strip, uniform in the character modulus.
This is the high-height part only; it makes no Vinogradov--Korobov claim. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

lemma mrt_character_principal_neg_logderiv_re {q : ℕ} [NeZero q]
    {s : ℂ} (hs : 1 < s.re) :
    (-deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s).re ≤
        (-deriv riemannZeta s / riemannZeta s).re + Real.log (q : ℝ) := by
  have h := (Complex.abs_re_le_norm _).trans (mrt_principal_logderiv_error (q := q) hs)
  rw [Complex.sub_re] at h
  have := (abs_le.mp h).1
  simp only [logDeriv_apply] at this
  simp only [neg_div, Complex.neg_re]
  linarith


lemma mrt_character_zero_free_arithmetic {D H delta eps : ℝ}
    (hD : 0 < D) (hH : 0 < H) (hd : delta = 1 / (10 * D * H))
    (he : 0 ≤ eps) (heu : eps ≤ delta / 4) :
    3 / delta + D * H - 4 / (delta + eps) < 0 := by
  have hdp : 0 < delta := by rw [hd]; positivity
  have hde : 0 < delta + eps := by linarith
  have hinv : 16 / (5 * delta) ≤ 4 / (delta + eps) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 5 * delta) hde).mpr
    nlinarith
  have heq : 3 / delta + D * H - 16 / (5 * delta) = -(D * H) := by
    rw [hd]
    field_simp [hD.ne', hH.ne']
    ring
  have hle : 3 / delta + D * H - 4 / (delta + eps) ≤
      3 / delta + D * H - 16 / (5 * delta) := by linarith
  rw [heq] at hle
  exact hle.trans_lt (neg_neg_of_pos (mul_pos hD hH))


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTZetaPole
namespace OAI

/-! Uniform removal of the zeta pole on a bounded part of the closed right half-plane. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.Metric _root_.Set _root_.Filter
open scoped _root_.Topology


lemma mrt_zeta_pole_correction_continuousAt {s : ℂ}
    (hs : s ≠ 1) (hr : 1 ≤ s.re) :
    ContinuousAt mrtZetaPoleCorrection s := by
  have hd := (analyticOn_riemannZeta s hs).deriv.continuousAt
  have hz := (differentiableAt_riemannZeta hs).continuousAt
  exact (hd.neg.div hz (riemannZeta_ne_zero_of_one_le_re hr)).sub
    ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hs))

/-- After subtracting the pole, the logarithmic derivative is uniformly bounded
on each bounded part of `Re s ≥ 1`, with constants independent of characters. -/
theorem mrt_zeta_pole_correction_bounded (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re → ‖s‖ ≤ B → s ≠ 1 →
      ‖mrtZetaPoleCorrection s‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := Erdos970.riemannZetaLogDerivResidueBigO.bound
  have he : ∀ᶠ s : ℂ in 𝓝[({1}ᶜ)] 1, ‖mrtZetaPoleCorrection s‖ ≤ C₀ := by
    filter_upwards [hC₀] with s hs
    simpa only [mrtZetaPoleCorrection, Pi.sub_apply, Pi.neg_apply, Pi.div_apply,
      Pi.one_apply, norm_one, mul_one] using hs
  obtain ⟨r, hr, hlocal⟩ := Metric.mem_nhdsWithin_iff.mp he
  let K : Set ℂ := closedBall 0 B ∩ {s : ℂ | 1 ≤ s.re}
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) B).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  have hA : IsCompact (K \ ball (1 : ℂ) r) := hK.diff isOpen_ball
  have hcont : ContinuousOn mrtZetaPoleCorrection (K \ ball (1 : ℂ) r) := by
    intro s hs
    have hn : s ≠ 1 := by
      intro heq
      apply hs.2
      rw [heq]
      exact mem_ball_self hr
    exact (mrt_zeta_pole_correction_continuousAt hn hs.1.2).continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := hA.exists_bound_of_continuousOn hcont
  refine ⟨max 0 (max C₀ C₁), le_max_left _ _, ?_⟩
  intro s hs hn hs1
  by_cases hsr : s ∈ ball (1 : ℂ) r
  · exact (hlocal ⟨hsr, hs1⟩).trans ((le_max_left C₀ C₁).trans (le_max_right _ _))
  · have hm : s ∈ K \ ball (1 : ℂ) r := by
      exact ⟨⟨by simpa only [mem_closedBall, dist_zero_right] using hn, hs⟩, hsr⟩
    exact (hC₁ s hm).trans ((le_max_right C₀ C₁).trans (le_max_right _ _))

lemma mrt_zeta_neg_logderiv_bounded (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re → ‖s‖ ≤ B → s ≠ 1 →
      (-deriv riemannZeta s / riemannZeta s).re ≤ C + ‖(s - 1)⁻¹‖ := by
  obtain ⟨C, hC, hb⟩ := mrt_zeta_pole_correction_bounded B
  refine ⟨C, hC, ?_⟩
  intro s hs hn hs1
  have h := (Complex.abs_re_le_norm _).trans (hb s hs hn hs1)
  have hi := (le_abs_self ((s - 1)⁻¹).re).trans (Complex.abs_re_le_norm _)
  have hc := (le_abs_self (mrtZetaPoleCorrection s).re).trans h
  dsimp only [mrtZetaPoleCorrection] at hc
  rw [Complex.sub_re] at hc
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTQuadraticLowZeros
namespace OAI

/-! The effective quadratic disk supplies the bounded-height part of a
zero-free strip, with its polynomial modulus dependence displayed. -/

namespace TwoPointCorrelations

open _root_.Complex
open scoped _root_.Classical

lemma mrt_character_height_half (q : ℕ) [NeZero q] (t : ℝ) :
    (1 / 2 : ℝ) ≤ mrtCharacterHeight q t := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact hlog2.trans ((Real.log_le_log (by norm_num)
    (by linarith [abs_nonneg t])).trans (mrt_character_height_ge q t))

lemma mrt_real_shift_norm {delta t : ℝ} (hd : 0 ≤ delta) :
    ‖((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)‖ ≤ 1 + delta + |t| := by
  calc
    _ ≤ |(((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)).re| +
        |(((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = _ := by simp [abs_of_nonneg (show 0 ≤ 1 + delta by linarith)]

lemma mrt_real_shift_inv_norm {delta t : ℝ} (ht : t ≠ 0) :
    ‖((((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)) - 1)⁻¹‖ ≤ 1 / |t| := by
  rw [norm_inv, one_div]
  apply inv_anti₀ (abs_pos.mpr ht)
  have hh := Complex.abs_im_le_norm
    ((((1 + delta : ℝ) : ℂ) + Complex.I * (t : ℂ)) - 1)
  simpa using hh

lemma mrt_quadratic_zero_cost {C Z Q H : ℝ}
    (hC : 0 ≤ C) (hZ : 0 ≤ Z) (hQ : 1 ≤ Q) (hH : 1 / 2 ≤ H) :
    4 * Z + 4 * C * H + 3072 * Q + H ≤ (8 * Z + 4 * C + 6200) * (Q * H) := by
  have hH0 : 0 ≤ H := le_trans (by norm_num) hH
  have hQH : H ≤ Q * H := by nlinarith only [hQ, hH0]
  have hQHhalf : 1 / 2 ≤ Q * H := hH.trans hQH
  have hCH := mul_le_mul_of_nonneg_left hQH hC
  have hZH := mul_le_mul_of_nonneg_left hQHhalf hZ
  have hQH' : Q ≤ 2 * (Q * H) := by nlinarith only [hH, hQ]
  nlinarith only [hQH, hQHhalf, hCH, hZH, hQH']

lemma mrt_quadratic_zero_combine {a b d Z C Q H delta eps D : ℝ}
    (hpos : 0 ≤ 3 * a + 4 * b + d)
    (ha : a ≤ Z + 1 / delta) (hb : b ≤ C * H - 1 / (delta + eps))
    (hd : d ≤ Z + 3072 * Q + H)
    (hcost : 4 * Z + 4 * C * H + 3072 * Q + H ≤ D * (Q * H)) :
    0 ≤ 3 / delta + D * (Q * H) - 4 / (delta + eps) := by
  calc
    0 ≤ 3 * a + 4 * b + d := hpos
    _ ≤ 3 * (Z + 1 / delta) + 4 * (C * H - 1 / (delta + eps)) +
        (Z + 3072 * Q + H) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ha (by norm_num))
        (mul_le_mul_of_nonneg_left hb (by norm_num))) hd
    _ = 3 / delta + (4 * Z + 4 * C * H + 3072 * Q + H) -
        4 / (delta + eps) := by ring
    _ ≤ 3 / delta + D * (Q * H) - 4 / (delta + eps) :=
      sub_le_sub_right (add_le_add_right hcost _) _

/-- The constant can depend on the fixed height cutoff, but not the modulus. -/
theorem mrt_quadratic_bounded_height_zero_free_oai (T : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q],
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ t beta : ℝ, |t| ≤ T →
        1 - c / ((q : ℝ) ^ 2 * mrtCharacterHeight q t) ≤ beta →
        DirichletCharacter.LFunction χ ((beta : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
  obtain ⟨C, hC, hchar⟩ := mrt_character_logderiv_growth_constant
  obtain ⟨Z, hZ, hzeta⟩ := mrt_zeta_neg_logderiv_bounded (2 * |T| + 3)
  let D := 8 * Z + 4 * C + 6200
  have hDlarge : 6200 ≤ D := by dsimp [D]; linarith
  have hD : 0 < D := by linarith
  let b := 1 / (10 * D)
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨b / 4, by positivity, ?_⟩
  intro q _ χ hχ hχsq t beta ht hbeta hzero
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq
  let Q : ℝ := (q : ℝ) ^ 2
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith only [hq]
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  let H := mrtCharacterHeight q t
  have hHhalf : (1 / 2 : ℝ) ≤ H := mrt_character_height_half q t
  have hH : 0 < H := lt_of_lt_of_le (by norm_num) hHhalf
  let delta := b / (Q * H)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdeq : delta = 1 / (10 * D * (Q * H)) := by dsimp [delta, b]; field_simp
  have hdsmall : delta ≤ 1 / (3072 * Q) := by
    rw [hdeq]
    apply one_div_le_one_div_of_le (by positivity)
    have hDH : 3072 ≤ 10 * D * H := by
      nlinarith only [hDlarge, hHhalf,
        mul_nonneg (show 0 ≤ D - 6200 by linarith only [hDlarge])
          (show 0 ≤ H - 1 / 2 by linarith only [hHhalf])]
    have hm := mul_le_mul_of_nonneg_right hDH hQ0.le
    nlinarith only [hm]
  have hd1 : delta < 1 := by
    have hh : 1 / (3072 * Q) ≤ (1 / 3072 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3072 * Q)).mpr
      nlinarith
    linarith
  have hbeta1 : beta < 1 := by
    by_contra! h
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using h) hzero
  let eps := 1 - beta
  have he : 0 ≤ eps := by dsimp [eps]; linarith
  have heu : eps ≤ delta / 4 := by
    change 1 - (b / 4) / (Q * H) ≤ beta at hbeta
    have heq : (b / 4) / (Q * H) = (b / (Q * H)) / 4 := by ring
    rw [heq] at hbeta
    dsimp only [eps, delta]
    linarith
  by_cases htiny : |t| ≤ 1 / (3072 * Q)
  · apply mrt_quadratic_near_one_nonzero χ hχ hχsq (s := (beta : ℂ) + I * (t : ℂ)) _ hzero
    have hn := Complex.norm_le_abs_re_add_abs_im ((beta : ℂ) + I * (t : ℂ) - 1)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, zero_add, one_mul, Complex.one_im] at hn
    rw [abs_of_nonpos (by linarith : beta - 1 ≤ 0)] at hn
    have htwice : 2 * (1 / (3072 * Q)) = 1 / (1536 * Q) := by
      field_simp
      norm_num
    change ‖(beta : ℂ) + I * (t : ℂ) - 1‖ ≤ 1 / (1536 * Q)
    dsimp only [eps] at heu
    have hrpos : 0 ≤ 1 / (3072 * Q) := by positivity
    linarith only [hn, heu, htiny, hdsmall, htwice, hrpos]
  have ht0 : t ≠ 0 := by
    intro heq
    apply htiny
    rw [heq, abs_zero]
    positivity
  have hlarge : 1 / |2 * t| ≤ 3072 * Q := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * |t|)).mpr
    have hu := (div_lt_iff₀ (by positivity : 0 < 3072 * Q)).mp (lt_of_not_ge htiny)
    nlinarith only [hu]
  have hnorm0 : ‖((1 + delta : ℝ) : ℂ)‖ ≤ 2 * |T| + 3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + delta)]
    linarith [abs_nonneg T]
  have hz := hzeta ((1 + delta : ℝ) : ℂ) (by simp; linarith) hnorm0 (by
    intro heq; have := congrArg Complex.re heq; simp at this; linarith)
  have hinv : ‖(((1 + delta : ℝ) : ℂ) - 1)⁻¹‖ = 1 / delta := by
    rw [show ((1 + delta : ℝ) : ℂ) - 1 = (delta : ℂ) by push_cast; ring]
    simp [norm_inv, abs_of_pos hd, one_div]
  rw [hinv] at hz
  let s₂ : ℂ := ((1 + delta : ℝ) : ℂ) + I * ((2 * t : ℝ) : ℂ)
  have hs₂ : 1 < s₂.re := by dsimp [s₂]; simp; linarith
  have hnorm₂ : ‖s₂‖ ≤ 2 * |T| + 3 := by
    have hh := mrt_real_shift_norm (t := 2 * t) hd.le
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
    have htt := ht.trans (le_abs_self T)
    dsimp only [s₂]
    linarith
  have hz₂ := hzeta s₂ hs₂.le hnorm₂ (by intro h; rw [h] at hs₂; norm_num at hs₂)
  have hi₂ := mrt_real_shift_inv_norm (delta := delta)
    (show (2 * t : ℝ) ≠ 0 from mul_ne_zero (by norm_num) ht0)
  have hp₂ := mrt_character_principal_neg_logderiv_re (q := q) hs₂
  have hsquare : (-deriv (DirichletCharacter.LFunction (χ ^ 2)) s₂ /
      DirichletCharacter.LFunction (χ ^ 2) s₂).re ≤ Z + 3072 * Q + H := by
    rw [hχsq]
    have hlogq := mrt_character_log_modulus_le_height q t
    change _ ≤ Z + 3072 * Q + mrtCharacterHeight q t
    dsimp only [s₂] at hz₂ hp₂ ⊢
    linarith
  have hbetalow : 3 / 4 ≤ beta := by dsimp [eps] at heu; linarith
  have hc := (hchar q χ hχ t (1 + delta) (by linarith) (by linarith)).2
    beta hbetalow hbeta1.le hzero
  have hdist : 1 + delta - beta = delta + eps := by dsimp [eps]; ring
  rw [hdist] at hc
  have hp := mrtCharacter_logderiv_positivity χ (σ := 1 + delta) (by linarith) t
  have hcost : 4 * Z + 4 * C * H + 3072 * Q + H ≤ D * (Q * H) :=
    mrt_quadratic_zero_cost hC.le hZ hQ hHhalf
  have hpos : 0 ≤ 3 / delta + D * (Q * H) - 4 / (delta + eps) := by
    exact mrt_quadratic_zero_combine hp hz hc hsquare hcost

  exact (not_lt_of_ge hpos)
    (mrt_character_zero_free_arithmetic hD (mul_pos hQ0 hH) hdeq he heu)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrt_quadratic_bounded_height_zero_free_oai := @OAI.TwoPointCorrelations.mrt_quadratic_bounded_height_zero_free_oai
