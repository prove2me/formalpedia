-- Prove2me | solution 1 for OAI.TwoPointCorrelations.mrtCharacterNormalizedLFunction_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:46:11.005227+00:00
-- url     : https://prove2.me/submissions/6f5a0609-2bb7-42fc-bc6f-74ceb502208a

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterCenterBounds
namespace OAI

/-! The Mobius inverse bounds the reciprocal L-function on Re(s)=2
uniformly in the modulus. Combining this with the q-dependent Abel bound
gives growth of the normalized nonprincipal character L-function on a
fixed disk. No zero-free region is asserted here. -/

namespace TwoPointCorrelations

open _root_.Complex _root_.ArithmeticFunction
open scoped _root_.BigOperators _root_.Classical _root_.LSeries.notation _root_.ArithmeticFunction.Moebius

variable {q : ℕ} [NeZero q]


lemma mrtCharacterInverseConstant_pos : 0 < mrtCharacterInverseConstant := by
  unfold mrtCharacterInverseConstant
  have : 0 ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  linarith

omit [NeZero q] in
lemma mrtCharacter_twisted_moebius_norm (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ (n : ZMod q) * ((μ n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |μ n| ≤ 1 from abs_moebius_le_one)
  exact (mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

omit [NeZero q] in
lemma mrtCharacter_inverse_series_norm_le (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 2) :
    ‖LSeries (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s‖ ≤
      mrtCharacterInverseConstant := by
  have hσ : 1 < s.re := by rw [hs]; norm_num
  have hm := χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hσ)
  have hbase : Summable (fun n : ℕ => ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖) :=
    (LSeriesSummable_one_iff.mpr (by norm_num : 1 < (2 : ℂ).re)).norm
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hm.norm
    _ ≤ ∑' n : ℕ, ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ := by
      apply Summable.tsum_le_tsum (fun n => ?_) hm.norm hbase
      simp only [LSeries.norm_term_eq, hs, Complex.re_ofNat, Pi.one_apply, norm_one]
      split_ifs with hn
      · rfl
      · exact div_le_div_of_nonneg_right (mrtCharacter_twisted_moebius_norm χ n)
          (Real.rpow_nonneg n.cast_nonneg _)
    _ ≤ mrtCharacterInverseConstant := by unfold mrtCharacterInverseConstant; linarith

/-- Uniform reciprocal bound, independent of the imaginary part and character. -/
theorem mrtCharacter_LFunction_inv_norm (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 2) :
    ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ mrtCharacterInverseConstant := by
  have hσ : 1 < s.re := by rw [hs]; norm_num
  have heq := DirichletCharacter.LSeries.mul_mu_eq_one χ hσ
  have hn := χ.LSeries_ne_zero_of_one_lt_re hσ
  have hi : (LSeries (fun n => χ (n : ZMod q)) s)⁻¹ =
      LSeries (fun n => χ (n : ZMod q) * ((μ n : ℤ) : ℂ)) s := by
    apply (mul_left_cancel₀ hn)
    simpa only [mul_inv_cancel₀ hn, Pi.mul_def] using heq.symm
  rw [DirichletCharacter.LFunction_eq_LSeries χ hσ, hi]
  exact mrtCharacter_inverse_series_norm_le χ hs




lemma mrtCharacterNormalizedLFunction_norm (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖mrtCharacterNormalizedLFunction χ t z‖ ≤
      (2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4) := by
  have hC : 0 ≤ mrtCharacterInverseConstant := mrtCharacterInverseConstant_pos.le
  let s : ℂ := (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z
  have hr : -(1 : ℝ) ≤ z.re := by
    have h := (abs_re_le_norm z).trans hz
    exact (abs_le.mp h).1
  have hs : (1 / 2 : ℝ) ≤ s.re := by
    norm_num [s, Complex.mul_re]
    linarith
  have hsbound : ‖s‖ ≤ |t| + 4 := by
    calc
      ‖s‖ ≤ ‖(2 : ℂ) + Complex.I * (t : ℂ)‖ + ‖(3 / 2 : ℂ) * z‖ := norm_add_le _ _
      _ ≤ (‖(2 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖) + ‖(3 / 2 : ℂ) * z‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = 2 + |t| + (3 / 2 : ℝ) * ‖z‖ := by
        norm_num [norm_mul]
      _ ≤ |t| + 4 := by linarith
  have hn := mrt_character_LFunction_norm_halfPlane χ hχ hs
  have hi := mrtCharacter_LFunction_inv_norm χ (s := (2 : ℂ) + Complex.I * (t : ℂ))
    (by simp)
  unfold mrtCharacterNormalizedLFunction
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ((2 * q : ℝ) * ‖s‖) * mrtCharacterInverseConstant :=
      mul_le_mul hn hi (norm_nonneg _) (by positivity)
    _ = ((2 * q : ℝ) * mrtCharacterInverseConstant) * ‖s‖ := by ring
    _ ≤ ((2 * q : ℝ) * mrtCharacterInverseConstant) * (|t| + 4) :=
      mul_le_mul_of_nonneg_left hsbound (by positivity)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.mrtCharacterNormalizedLFunction_norm := @OAI.TwoPointCorrelations.mrtCharacterNormalizedLFunction_norm
