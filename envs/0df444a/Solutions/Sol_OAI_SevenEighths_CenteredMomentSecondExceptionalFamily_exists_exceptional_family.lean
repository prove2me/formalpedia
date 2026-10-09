-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondExceptionalFamily.exists_exceptional_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:52:27.330988+00:00
-- url     : https://prove2.me/submissions/9d1aae9d-1f67-4aa4-9714-7369ada6e189

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondBlockSupport_physicalBlock_nonzero_common

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Operations
namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem elementCoeff_power_of_unit (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl

end SevenEighths.HeckeFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.RowCompletion.SupportBounds
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open CompletedGauss hiding O
open FirstPassCubeLabels hiding O

theorem rowTwist_row_factor (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z n : ActualEisensteinCubic.O) :
    rowTwist Ψ m f z n =
      rowTwist Ψ m f 1 n * idealRowHom z (Ideal.span {n}) := by
  change Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (Ψ n * idealRowHom (m^6*f^4*1) (Ideal.span {n})) * idealRowHom z (Ideal.span {n})
  rw [mul_one,idealRowHom_argument_mul]
  ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open CompletedGauss hiding O

end CanonicalRowCompletion

open scoped BigOperators Classical
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Correlation
namespace OAI

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]

theorem sum_reduction (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl

end
end SevenEighths.CenteredMomentCorrelation

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Canonical
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

end SevenEighths.CenteredMomentCanonical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CommonSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonSupport
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A]

theorem fullCorrelation_unit_change
    {X Y R : Type*} [CommRing X] [CommRing Y] [CommRing R]
    [Fintype X] [Fintype Y]
    (left : X → R) (right : Y → R) (χ : MulChar X ℂ) (ψ : MulChar Y ℂ)
    (u : Xˣ) (v : Yˣ) (j : R) :
    fullCorrelation (fun x => left ((u : X) * x)) (fun y => right ((v : Y) * y)) χ ψ j =
      χ (↑u⁻¹ : X) * star (ψ (↑v⁻¹ : Y)) * fullCorrelation left right χ ψ j := by
  have hχ (x : X) : χ x = χ (↑u⁻¹ : X) * χ ((u : X) * x) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hψ (y : Y) : ψ y = ψ (↑v⁻¹ : Y) * ψ ((v : Y) * y) := by
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  unfold fullCorrelation
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv u.mulLeft
  intro x
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv v.mulLeft
  intro y
  simp only [Units.mulLeft_apply]
  by_cases h : left ((u : X) * x) - right ((v : Y) * y) = j
  · simp only [h, ite_true]
    rw [hχ x, hψ y, star_mul]
    ring
  · simp only [h, ite_false, mul_zero]

end SevenEighths.CenteredMomentCommonSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Support
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

end SevenEighths.CenteredMomentSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.AddedZero
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentRowNorm CenteredMomentFourier CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentGaussEnergy CenteredMomentZeroMode
open CenteredExceptionalCount CenteredMomentRectangle
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero, ?_⟩
  intro P hP
  simp only [normalizedFactors_one, Multiset.notMem_zero] at hP

lemma supported_one_element : Supported (Ideal.span {(1 : O)}) := by
  simpa only [Ideal.span_singleton_one, Ideal.one_eq_top] using supported_one_ideal

end SevenEighths.CenteredMomentAddedZero

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildRows
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildRows
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem childCharacter_primary (η : Character) (χ : RayCharacter) (n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    elementCoeff (childCharacter η χ) n = elementCoeff η n * rayCharacter χ n := by
  rw [childCharacter, elementCoeff_product, primaryRayCharacter_primary χ n hn hp]

end SevenEighths.CenteredMomentChildRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CompleteCommon
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCompleteCommon
open UniqueFactorizationMonoid IdealMobiusDivisorSum CenteredMomentSupport
open CenteredExceptionalCount CenteredMomentRankinRadical CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem reconstruct (I J : Ideal O) (hI : I ≠ 0) :
    I = commonPart I J * residualPart I J := by
  rw [commonPart_eq_supportExtract, residualPart_eq_supportResidual]
  exact (support_reconstruct I hI _).symm

theorem residualPart_self (I : Ideal O) : residualPart I I = 1 := by
  simp only [residualPart, Finset.sdiff_self, Finset.prod_empty]

theorem commonPart_self (I : Ideal O) (hI : I ≠ 0) : commonPart I I = I := by
  have h := reconstruct I I hI
  rw [residualPart_self, mul_one] at h
  exact h.symm

end SevenEighths.CenteredMomentCompleteCommon

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentCanonicalFirst
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredExceptionalCount
open CenteredMomentCommonSupport CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentFirstReduced CenteredMomentActive
open CenteredMomentCompleteCommon UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

theorem common_odd (I J : Ideal O) (hI : Supported I) (P : CommonIndex I J) :
    ringChar (O ⧸ P.val)≠2 :=
  (supported_factors_good I hI P.val (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1)).2.2

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

theorem commonPart_right_product (I J : Ideal O) :
    commonPart J I=∏ P : CommonIndex I J,P.val^rightExponent I J P := by
  unfold commonPart
  rw [commonSupport_comm J I]
  exact (Finset.prod_coe_sort (s:=commonSupport I J) (f:=fun P => P^valuation J P)).symm

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Unequal
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentUnequal
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

theorem divisor_congruence (v t k : A) (hv : v ≠ 0)
    (x : Residue (v * t)) (y : Residue v) :
    scaledResidue (v * t) v ((v * t) * v) rfl x -
      scaledResidue v (v * t) ((v * t) * v) (mul_comm _ _) y =
      Ideal.Quotient.mk _ (v * k) ↔
      x = scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence, scaledResidue_mk, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  change (v * t) * v ∣ v * x - (v * t) * y - v * k ↔ v * t ∣ x - (t * y + k)
  rw [show (v * t) * v = v * (v * t) by ring,
    show v * x - (v * t) * y - v * k = v * (x - (t * y + k)) by ring]
  exact mul_dvd_mul_iff_left hv

theorem fullCorrelation_divisor (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      ∑ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) *
        star (χv y) := by
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [divisor_congruence v t k hv]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_divisor_constant (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (hχ : ∀ y : Residue v,
      χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) = χu (Ideal.Quotient.mk _ k)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      χu (Ideal.Quotient.mk _ k) * star (∑ y : Residue v, χv y) := by
  rw [fullCorrelation_divisor v t k hv χu χv]
  simp_rw [hχ]
  rw [← Finset.mul_sum, star_sum]

omit [IsDomain A] in
theorem divisor_lift_constant (p v t k : A) (hpt : p ∣ t)
    (χu : MulChar (Residue (v * t)) ℂ) (χ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : A, χu (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    ∀ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) =
      χu (Ideal.Quotient.mk _ k) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, ← map_add, hχ, hχ, map_add, map_mul]
  have ht : Ideal.Quotient.mk (Ideal.span {p}) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpt)
  rw [ht, zero_mul, zero_add]

omit [IsDomain A] in
theorem lifted_character_sum_zero (p v : A) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (χv : MulChar (Residue v) ℂ) (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1)
    (hlift : ∀ x : A, χv (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    (∑ y : Residue v, χv y) = 0 := by
  let π : Residue v →+* Residue p :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hpv)
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have he (y : Residue v) : χv y = χ (π y) := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hlift y
  simp_rw [he]
  rw [sum_reduction π hπ χ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

theorem fullCorrelation_divisor_eq_zero (p v t k : A) (hv : v ≠ 0)
    (hpv : p ∣ v) (hpt : p ∣ t)
    [Fintype (Residue p)] [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (ψu ψv : MulChar (Residue p) ℂ) (hψv : ψv ≠ 1)
    (hu : ∀ x : A, χu (Ideal.Quotient.mk _ x) = ψu (Ideal.Quotient.mk _ x))
    (hv' : ∀ x : A, χv (Ideal.Quotient.mk _ x) = ψv (Ideal.Quotient.mk _ x)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) = 0 := by
  rw [fullCorrelation_divisor_constant v t k hv χu χv
    (divisor_lift_constant p v t k hpt χu ψu hu),
    lifted_character_sum_zero p v hpv χv ψv hψv hv', star_zero, mul_zero]

end Domain
section Eisenstein
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem supported_power_character_mk (p : O) [ (Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {i : ℕ} (hi : 1 ≤ i) (x : O) :
    supportedModulusCharacter (p ^ i) (supported_power p hp i) (Ideal.Quotient.mk _ x) =
      (actualSextic (Ideal.span {p}) hg ^ i) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem supported_product_power_character_mk (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (x : O) :
    supportedModulusCharacter (p ^ j * p ^ d)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (Ideal.Quotient.mk _ x) =
      (actualSextic (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← pow_add, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem unequal_prime_power_zero_of_not_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (hj6 : ¬ 6 ∣ j) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hχ : actualSextic (Ideal.span {p}) hg ^ j ≠ 1 := by
    intro h
    apply hj6
    rw [← actualSextic_order_six (Ideal.span {p}) hg hchar]
    exact orderOf_dvd_of_pow_eq_one h
  exact fullCorrelation_divisor_eq_zero p (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
    (supportedModulusCharacter _ _ ) (supportedModulusCharacter _ _)
    (actualSextic (Ideal.span {p}) hg ^ (j + d)) (actualSextic (Ideal.span {p}) hg ^ j)
    hχ (supported_product_power_character_mk p hp hg hj)
    (supported_power_character_mk p hp hg hj)

end Eisenstein

end SevenEighths.CenteredMomentUnequal

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.HeterogeneousCRT
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentHeterogeneousCRT
open CenteredMomentCorrelation

theorem fullCorrelation_heterogeneous_pi {ι : Type*} [Fintype ι]
    {X Y R : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, CommRing (R i)]
    (left : ∀ i, X i → R i) (right : ∀ i, Y i → R i)
    (f : ∀ i, X i → ℂ) (g : ∀ i, Y i → ℂ) (k : ∀ i, R i) :
    fullCorrelation (fun (x : ∀ i, X i) i => left i (x i)) (fun (y : ∀ i, Y i) i => right i (y i))
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (left i) (right i) (f i) (g i) (k i) := by
  have hterm (x : ∀ i, X i) (y : ∀ i, Y i) :
      (if (fun i => left i (x i)) - (fun i => right i (y i)) = k
       then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if left i (x i) - right i (y i) = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, left i (x i) - right i (y i) = k i
    · have he : (fun i => left i (x i)) - (fun i => right i (y i)) = k := funext h
      simp only [he, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have he : (fun i => left i (x i)) - (fun i => right i (y i)) ≠ k :=
        fun h => hi (congrFun h i)
      rw [if_neg he]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, X i, ∏ i, ∑ y : Y i,
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : Y i) =>
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : X i) => ∑ y : Y i,
      if left i x - right i y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_three_equiv {ι X Y R : Type*} [Fintype ι]
    [Fintype X] [Fintype Y] [CommRing R]
    {Xi Yi Ri : ι → Type*} [∀ i, Fintype (Xi i)] [∀ i, Fintype (Yi i)]
    [∀ i, CommRing (Ri i)]
    (eX : X ≃ ∀ i, Xi i) (eY : Y ≃ ∀ i, Yi i) (eR : R ≃+* ∀ i, Ri i)
    (left : X → R) (right : Y → R)
    (li : ∀ i, Xi i → Ri i) (ri : ∀ i, Yi i → Ri i)
    (hl : ∀ x i, eR (left x) i = li i (eX x i))
    (hr : ∀ y i, eR (right y) i = ri i (eY y i))
    (f : ∀ i, Xi i → ℂ) (g : ∀ i, Yi i → ℂ) (k : R) :
    fullCorrelation left right (fun x => ∏ i, f i (eX x i))
      (fun y => ∏ i, g i (eY y i)) k =
      ∏ i, fullCorrelation (li i) (ri i) (f i) (g i) (eR k i) := by
  rw [← fullCorrelation_heterogeneous_pi li ri f g (eR k)]
  unfold fullCorrelation
  apply Fintype.sum_equiv eX
  intro x
  apply Fintype.sum_equiv eY
  intro y
  have he : left x - right y = k ↔
      (fun i => li i (eX x i)) - (fun i => ri i (eY y i)) = eR k := by
    rw [← eR.injective.eq_iff, map_sub]
    have hleft : eR (left x) = fun i => li i (eX x i) := funext (hl x)
    have hright : eR (right y) = fun i => ri i (eY y i) := funext (hr y)
    rw [hleft, hright]
  simp only [he]

end SevenEighths.CenteredMomentHeterogeneousCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ProductCRT
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentProductCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentHeterogeneousCRT
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

theorem factor_mul_cofactor (a : ι → A) (i : ι) : a i * cofactor a i = ∏ j, a j :=
  Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)

theorem left_crt_component (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : Residue (∏ i, a i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl x) i =
      scaledResidue (a i) (b i) (a i * b i) rfl
        (Ideal.Quotient.mk _ (cofactor b i) * productCRT a ha x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor b i]
  ring

theorem right_crt_component (a b : ι → A)
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (y : Residue (∏ i, b i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _) y) i =
      scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
        (Ideal.Quotient.mk _ (cofactor a i) * productCRT b hb y i) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor a i]
  ring

theorem fullModulusCorrelation_product (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h =
      ∏ i, fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h) := by
  have hcrt := fullCorrelation_three_equiv (productCRT a ha).toEquiv (productCRT b hb).toEquiv
    (jointCRT a b hab)
    (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl)
    (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _))
    (fun i x => scaledResidue (a i) (b i) (a i * b i) rfl
      (Ideal.Quotient.mk _ (cofactor b i) * x))
    (fun i y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
      (Ideal.Quotient.mk _ (cofactor a i) * y))
    (left_crt_component a b ha hab) (right_crt_component a b hb hab)
    (fun i => χ i) (fun i => ψ i) (Ideal.Quotient.mk _ h)
  simpa only [fullModulusCorrelation, fullCorrelation, crtCharacter_apply, jointCRT_mk,
    RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe] using hcrt

theorem cross_cofactor_coprime (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (i : ι) : IsCoprime (a i) (cofactor b i) := by
  unfold cofactor
  apply IsCoprime.prod_right
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hij := (Ideal.isCoprime_span_singleton_iff _ _).mp (hab hji.symm)
  exact (IsCoprime.mul_right_iff.mp (IsCoprime.mul_left_iff.mp hij).1).2

theorem local_cofactor_norm (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ)
    (h : A) (i : ι) :
    ‖fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h)‖ =
      ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  obtain ⟨u, hu⟩ := isUnit_residue_of_coprime (a i) (cofactor b i)
    (cross_cofactor_coprime a b hab i)
  have hba : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i * a i})) := by
    simpa only [mul_comm] using hab
  obtain ⟨v, hv⟩ := isUnit_residue_of_coprime (b i) (cofactor a i)
    (cross_cofactor_coprime b a hba i)
  rw [← hu, ← hv, fullCorrelation_unit_change, norm_mul, norm_mul, norm_star,
    FiniteRayExpansion.norm_char_unit, FiniteRayExpansion.norm_char_unit, one_mul, one_mul]
  rfl

theorem fullModulusCorrelation_product_norm (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    ‖fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h‖ =
      ∏ i, ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  rw [fullModulusCorrelation_product a b ha hb hab χ ψ h, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact local_cofactor_norm a b hab χ ψ h i

section Eisenstein
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

omit [DecidableEq ι] in
theorem supported_character_product (a : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hprod : Supported (Ideal.span {∏ i, a i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    supportedModulusCharacter (∏ i, a i) hprod =
      crtCharacter (productCRT a hcop) (fun i => supportedModulusCharacter (a i) (ha i)) := by
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [crtCharacter_apply, productCRT_mk, supportedModulusCharacter_mk]
  rw [← Ideal.prod_span_singleton Finset.univ a, map_prod]

theorem actualCorrelation_product_norm (a b : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hb : ∀ i, Supported (Ideal.span {b i}))
    (hA : Supported (Ideal.span {∏ i, a i}))
    (hB : Supported (Ideal.span {∏ i, b i}))
    (hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) (h : O) :
    ‖actualCorrelation (∏ i, a i) (∏ i, b i) hA hB h‖ =
      ∏ i, ‖actualCorrelation (a i) (b i) (ha i) (hb i) h‖ := by
  let : ∀ i, Finite (Residue (a i)) := fun i => finite_quotient_span (supported_element_ne_zero (a i) (ha i))
  let : ∀ i, Finite (Residue (b i)) := fun i => finite_quotient_span (supported_element_ne_zero (b i) (hb i))
  let : ∀ i, Fintype (Residue (a i)) := fun i => Fintype.ofFinite _
  let : ∀ i, Fintype (Residue (b i)) := fun i => Fintype.ofFinite _
  let := finite_quotient_span (supported_element_ne_zero _ hA)
  let := finite_quotient_span (supported_element_ne_zero _ hB)
  let : Fintype (Residue (∏ i, a i)) := Fintype.ofFinite _
  let : Fintype (Residue (∏ i, b i)) := Fintype.ofFinite _
  change ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ hA)
    (supportedModulusCharacter _ hB) h‖ =
    ∏ i, ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ (ha i))
      (supportedModulusCharacter _ (hb i)) h‖
  rw [supported_character_product a ha hA hca, supported_character_product b hb hB hcb]
  exact fullModulusCorrelation_product_norm a b hca hcb hcab _ _ h

end Eisenstein

end SevenEighths.CenteredMomentProductCRT

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Partition
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartition
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A]
theorem fullModulusCorrelation_swap (u v h : A)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ) :
    fullModulusCorrelation u v χ ψ h = star (fullModulusCorrelation v u ψ χ (-h)) := by
  simp only [fullModulusCorrelation, fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : u * v ∣ v * x - u * y - h ↔ v * u ∣ u * y - v * x - (-h) := by
    rw [mul_comm v u, show u * y - v * x - (-h) = -(v * x - u * y - h) by ring,
      dvd_neg]
  simp only [scaledResidue_congruence]
  by_cases hc : u * v ∣ v * x - u * y - h
  · simp only [hc, he.mp hc, ite_true, star_mul, star_star]
  · simp only [hc, (not_congr he).mp hc, ite_false, star_zero]
end Domain

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentProductCRT
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem actualCorrelation_norm_swap (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (h : O) :
    ‖actualCorrelation u v hu hv h‖ = ‖actualCorrelation v u hv hu (-h)‖ := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  change ‖fullModulusCorrelation u v _ _ h‖ = ‖fullModulusCorrelation v u _ _ (-h)‖
  rw [fullModulusCorrelation_swap, norm_star]

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commonFrequency_factor (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) :
    (∏ j, p j ^ min (c j) (d j)) * w = p i ^ min (c i) (d i) * dividedFrequency p c d w i := by
  rw [dividedFrequency, ← mul_assoc, factor_mul_cofactor (fun j => p j ^ min (c j) (d j)) i]

end Product

end SevenEighths.CenteredMomentPartition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.RadicalFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstFamily CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem elementCoeff_power_pos (χ : Character) (e : ℕ) (he : 0<e) (n : O) :
    elementCoeff (χ.power e) n=(elementCoeff χ n)^e := by
  by_cases hn : IsUnit (Ideal.Quotient.mk χ.modulus n)
  · exact elementCoeff_power_of_unit χ e n hn
  · have hz : elementCoeff χ n=0 := MulChar.map_nonunit _ hn
    have hp : elementCoeff (χ.power e) n=0 := MulChar.map_nonunit _ hn
    rw [hp,hz,zero_pow (Nat.ne_zero_of_lt he)]

theorem exists_product_presentation {ι : Type*} (S : Finset ι) (base : Character)
    (χ : ι→Character) (e : ι→ℕ) (he : ∀i∈S,0<e i)
    (M : Ideal O) (hb : M≤base.modulus) (hχ : ∀i∈S,M≤(χ i).modulus) :
    ∃τ : Character,M≤τ.modulus ∧ ∀n:O,
      elementCoeff τ n=elementCoeff base n*∏i∈S,(elementCoeff (χ i) n)^(e i) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨base,hb,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨τ,hτ,ht⟩ := ih (fun i hi=>he i (Finset.mem_insert_of_mem hi))
      (fun i hi=>hχ i (Finset.mem_insert_of_mem hi))
    refine ⟨τ.product ((χ a).power (e a)),le_inf hτ (hχ a (Finset.mem_insert_self _ _)),?_⟩
    intro n
    rw [elementCoeff_product,elementCoeff_power_pos _ _ (he a (Finset.mem_insert_self _ _)),
      ht,Finset.prod_insert ha]
    ring

theorem single_row_on_base (η : Character) (m p n : O)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (hn : rowTwist (elementHom η) m 1 1 n≠0) :
    rowTwist (elementHom (η.power 0)) m 1 p n=idealRowHom p (Ideal.span {n}) := by
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  have hη : elementCoeff η n≠0 := left_ne_zero_of_mul hn
  have hunit := MulChar.apply_ne_zero_iff.mp hη
  have hp : elementCoeff (η.power 0) n=1 := by
    rw [elementCoeff_power_of_unit η 0 n hunit,pow_zero]
  have hm : IsCoprime m n := by
    by_contra h
    apply hn
    rw [rowTwist_extract_sixth_mask _ m 1 1 n hs]
    simp [coprimalityMask,h]
  rw [rowTwist_extract_sixth_mask _ m 1 p n hs]
  change elementCoeff (η.power 0) n*coprimalityMask m n*idealRowHom (1^4*p) _=_
  rw [hp,one_pow,one_mul]
  simp [coprimalityMask,hm]

theorem row_product_formula {ι : Type*} (S : Finset ι)
    (η : Character) (m : O) (p : ι→O) (e : ι→ℕ)
    (hmLam : λ₀∣m) (hm2 : (2:O)∣m) (n : O) :
    rowTwist (elementHom η) m 1 1 n*
      (∏i∈S,(rowTwist (elementHom (η.power 0)) m 1 (p i) n)^(e i))=
      rowTwist (elementHom η) m 1 (∏i∈S,(p i)^(e i)) n := by
  conv_rhs => rw [rowTwist_row_factor]
  by_cases hn : rowTwist (elementHom η) m 1 1 n=0
  · rw [hn,zero_mul,zero_mul]
  have hs := (rowTwist_nonzero_coprime η m 1 1 n hmLam hm2 hn).1
  congr 1
  simp_rw [single_row_on_base η m _ n hmLam hm2 hn]
  induction S using Finset.induction_on with
  | empty => simpa using (idealRowHom_one_supported (Ideal.span {n}) hs).symm
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,idealRowHom_argument_mul,
      idealRowHom_argument_pow _ _ _ hs,ih]

theorem exists_radical_row_presentation {ι : Type*} [Fintype ι]
    (η : Character) (m : O) (hm : m≠0) (hmLam : λ₀∣m) (hm2 : (2:O)∣m)
    (p : ι→O) (hp : ∀i,Supported (Ideal.span {p i}))
    (e : ι→ℕ) (he : ∀i,0<e i) :
    ∃τ : Character,
      η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*(∏i,Ideal.span {p i})≤τ.modulus ∧
      τ.modulus.absNorm≤η.modulus.absNorm*(Ideal.span {m}).absNorm*
        (Ideal.span {(72:O)}).absNorm*∏i,(Ideal.span {p i}).absNorm ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (∏i,(p i)^(e i)) n := by
  obtain ⟨base,hbase,hbasec⟩ := exists_supported_row_presentation η m 1 hm
    CenteredMomentAddedZero.supported_one_element hmLam hm2
  choose χ hχ hc using fun i=>exists_supported_row_presentation (η.power 0) m (p i) hm
    (hp i) hmLam hm2
  let B := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}
  let M := B*∏i,Ideal.span {p i}
  have hb : M≤base.modulus := by
    rw [hbase,Ideal.span_singleton_one,←Ideal.one_eq_top,mul_one]
    exact Ideal.mul_le_left
  have hch (i : ι) : M≤(χ i).modulus := by
    rw [hχ i]
    change B*(∏j,Ideal.span {p j})≤B*Ideal.span {p i}
    apply Ideal.dvd_iff_le.mp
    exact mul_dvd_mul_left B (Finset.dvd_prod_of_mem (fun j=>Ideal.span {p j}) (Finset.mem_univ i))
  obtain ⟨τ,hM,ht⟩ := exists_product_presentation Finset.univ base χ e (fun i _=>he i) M hb
    (fun i _=>hch i)
  have hMn : M≠0 := mul_ne_zero
    (mul_ne_zero (mul_ne_zero η.modulus_ne_bot (Ideal.span_singleton_eq_bot.not.mpr hm))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    (Finset.prod_ne_zero_iff.mpr (fun i _=>(hp i).1))
  refine ⟨τ,hM,?_,?_⟩
  · have hd : τ.modulus∣M := Ideal.dvd_iff_le.mpr hM
    have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hMn))
      (map_dvd Ideal.absNorm hd)
    simpa only [M,B,map_mul,map_prod] using hn
  · intro n
    rw [ht,hbasec]
    simp_rw [hc]
    exact row_product_formula Finset.univ η m p e hmLam hm2 n

end SevenEighths.CenteredMomentRadicalFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondLedger
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondLedger
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentPartition CenteredMomentProductCRT ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem nonzero_unequal_min_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hcd : c ≠ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) : 6 ∣ min c d := by
  by_contra h6
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hc
      (show 1 ≤ d-c by omega) (by simpa only [min_eq_left hlt.le] using h6) (-k)
    have he : c+(d-c)=d := Nat.add_sub_of_le hlt.le
    have hn := norm_ne_zero_iff.mpr hne
    rw [actualCorrelation_norm_swap] at hn
    have hz' : actualCorrelation (p^d) (p^c) (supported_power p hp d) (supported_power p hp c)
        (-(p^min c d*k)) = 0 := by
      simpa only [← pow_add,he,min_eq_left hlt.le,mul_neg] using hz
    exact hn (by rw [hz',norm_zero])
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hd
      (show 1 ≤ c-d by omega) (by simpa only [min_eq_right hgt.le] using h6) k
    have he : d+(c-d)=c := Nat.add_sub_of_le hgt.le
    exact hne (by simpa only [← pow_add,he,min_eq_right hgt.le] using hz)

section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem local_nonzero_of_global (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ) (w : O)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) (i : ι) :
    actualCorrelation (p i^c i) (p i^d i) (supported_power (p i) (hp i) (c i))
      (supported_power (p i) (hp i) (d i))
      (p i^min (c i) (d i)*dividedFrequency p c d w i) ≠ 0 := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^d i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i*p i^d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add,← pow_add]
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hn := norm_ne_zero_iff.mpr hne
  rw [actualCorrelation_product_norm (fun i => p i^c i) (fun i => p i^d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab] at hn
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [commonFrequency_factor p c d w i] at hi
  exact norm_ne_zero_iff.mp hi

end Global

end SevenEighths.CenteredMomentSecondLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonical
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonical
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentSupportedCorrelation
open CenteredMomentSourceRow UniqueFactorizationMonoid CenteredMomentSupport CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonPrime_supported_ideal (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported P.val :=
  supported_of_dvd P.val C hC
    (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp (Finset.mem_inter.mp P.property).1))

theorem commonPrime_span (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Ideal.span {commonPrime C D P}=P.val :=
  primary_span_supported P.val (commonPrime_supported_ideal C D hC P)

theorem commonPrime_supported (C D : Ideal O) (hC : Supported C) (P : CommonIndex C D) :
    Supported (Ideal.span {commonPrime C D P}) := by
  rw [commonPrime_span C D hC P]
  exact commonPrime_supported_ideal C D hC P

theorem commonPrime_coprime (C D : Ideal O) (hC : Supported C) :
    Pairwise (Function.onFun IsCoprime (commonPrime C D)) := by
  intro P Q hPQ
  change IsCoprime (commonPrime C D P) (commonPrime C D Q)
  rw [←Ideal.isCoprime_span_singleton_iff,commonPrime_span C D hC P,commonPrime_span C D hC Q]
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

theorem commonPart_eq_left (C D : Ideal O) (hC : C≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) : commonPart C D=C := by
  have hs : commonSupport C D=commonSupport C C := by
    change CompletedGauss.primeSupport C∩CompletedGauss.primeSupport D=
      CompletedGauss.primeSupport C∩CompletedGauss.primeSupport C
    rw [hCD]
  calc
    commonPart C D=commonPart C C := by unfold commonPart;rw [hs]
    _=C := commonPart_self C hC

theorem left_ideal_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P)=C := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_left_product,commonPart_eq_left C D hC.1 hCD]

theorem right_ideal_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P)=D := by
  simp_rw [commonPrime_span C D hC]
  rw [←commonPart_right_product,commonPart_eq_left D C hD.1 hCD.symm]

theorem left_generator_product (C D : Ideal O) (hC : Supported C)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)=primaryGenerator C := by
  have he := congrArg primaryGeneratorHom (left_ideal_product C D hC hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

theorem right_generator_product (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)=primaryGenerator D := by
  have he := congrArg primaryGeneratorHom (right_ideal_product C D hC hD hCD)
  simp_rw [commonPrime_span C D hC] at he
  simpa only [map_prod,map_pow,primaryGeneratorHom,MonoidWithZeroHom.coe_mk,
    ZeroHom.coe_mk,commonPrime] using he

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalLedger
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalLedger
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentForcing
local notation "O" => ActualEisensteinCubic.O

theorem span_finset_product {ι : Type*} (S : Finset ι) (p : ι→O) :
    Ideal.span {∏ i∈S,p i}=∏ i∈S,Ideal.span {p i} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi,
      ←Ideal.span_singleton_mul_span_singleton,ih]

theorem nonunitFrequencyGenerator_span (C D : Ideal O)
    (U : Finset (CommonIndex C D)) :
    Ideal.span {nonunitFrequencyGenerator C D U}=
      unitIdeal (commonPrime C D) (nonunitPartitionSet C D U) := by
  simp only [nonunitFrequencyGenerator,span_finset_product,unitIdeal]

end SevenEighths.CenteredMomentSecondCanonicalLedger

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondChildProfile
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

end SevenEighths.CenteredMomentSecondChildProfile

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [if_pos hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

end SevenEighths.CenteredMomentSecondHeightFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SectorLocalization
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondMovingSupport
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondMovingSupport
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSupport CenteredMomentSupportedCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem actual_unequal_min_six (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0)
    (P : CommonIndex C D) (hneq : leftExponent C D P≠rightExponent C D P) :
    6∣min (leftExponent C D P) (rightExponent C D P) := by
  let (P : CommonIndex C D) : (Ideal.span {commonPrime C D P}).IsMaximal := by
    rw [commonPrime_span C D hC P];infer_instance
  have hglobal : actualCorrelation (∏ P : CommonIndex C D,commonPrime C D P^leftExponent C D P)
      (∏ P : CommonIndex C D,commonPrime C D P^rightExponent C D P)
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      (supported_product _ (fun P=>supported_power _ (commonPrime_supported C D hC P) _))
      ((∏ P : CommonIndex C D,commonPrime C D P^min (leftExponent C D P) (rightExponent C D P))*w)≠0 := by
    simpa only [left_generator_product C D hC hCD,right_generator_product C D hC hD hCD,
      commonFrequencyGenerator,idealCorrelation] using hne
  have hl := local_nonzero_of_global (commonPrime C D) (commonPrime_supported C D hC)
    (commonPrime_coprime C D hC) (leftExponent C D) (rightExponent C D) w hglobal P
  exact nonzero_unequal_min_six (commonPrime C D P) (commonPrime_supported C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_good C D hC P)
    (by rw [commonPrime_span C D hC P];exact common_odd C D hC P)
    _ _ (leftExponent_pos C D P) (rightExponent_pos C D P) hneq _ hl

theorem fixedActiveSet_subset (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0) :
    fixedActiveSet C D U⊆U∪nonunitPartitionSet C D U := by
  intro P hP
  have ha := (Finset.mem_filter.mp hP).2
  by_contra hn
  have hU : P∉U := fun h=>hn (Finset.mem_union_left _ h)
  have hV : P∉nonunitPartitionSet C D U := fun h=>hn (Finset.mem_union_right _ h)
  have heq : ¬(leftExponent C D P=rightExponent C D P ∧ ¬6∣leftExponent C D P) := by
    intro he
    exact hV (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hU⟩)
  rw [fixedExponent,if_neg hV,add_zero] at ha
  by_cases hc : leftExponent C D P=rightExponent C D P
  · rw [hc,min_self] at ha
    exact heq ⟨hc,by simpa only [hc] using ha⟩
  · exact ha (actual_unequal_min_six C D hC hD hCD w hne P hc)

end SevenEighths.CenteredMomentSecondMovingSupport

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSixthReduction
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthReduction
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondMovingSupport CenteredMomentFixedRowMask
open CenteredExceptionalProfile CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem fixed_numerator_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,commonPrime C D P^fixedExponent C D U P := by
  have hv : nonunitFrequencyGenerator C D U=
      ∏ P : CommonIndex C D,if P∈nonunitPartitionSet C D U then commonPrime C D P else 1 := by
    simp only [nonunitFrequencyGenerator,Finset.prod_ite_mem,Finset.univ_inter]
  rw [commonFrequencyGenerator,hv,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  simp only [fixedExponent,pow_add]
  split_ifs <;> simp

theorem fixed_sixth_factorization (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U=
      reducedNumerator C D U*(sixthFactor C D U)^6 := by
  rw [fixed_numerator_product,reducedNumerator,sixthFactor,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  rw [←pow_mul,←pow_add]
  congr 1
  omega

end SevenEighths.CenteredMomentSecondSixthReduction

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSixthSource
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSixthSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣C := by
  conv_rhs => rw [←left_ideal_product C D hC hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hc := leftExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤leftExponent C D P := min_le_left _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem fixed_sixth_coefficient (C D : Ideal O) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I*
        (if IsCoprime I (Ideal.span {sixthFactor C D U}) then 1 else 0) := by
  rw [fixed_sixth_factorization,idealRowHom_argument_mul,idealRowHom_sixth_mask _ I hI]

theorem residual_sixth_coefficient (C D : Ideal O) (hC : Supported C)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime C I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,if_pos
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd C D hC hCD U)),mul_one]

theorem activeExponent_pos (C D : Ideal O) (U : Finset (CommonIndex C D))
    (P : ActiveIndex C D U) : 0<activeExponent C D U P := by
  have hp : ¬6∣fixedExponent C D U P.val := (Finset.mem_filter.mp P.property).2
  exact Nat.pos_of_ne_zero (fun h=>hp (Nat.dvd_of_mod_eq_zero h))

theorem reducedNumerator_active_product (C D : Ideal O) (U : Finset (CommonIndex C D)) :
    reducedNumerator C D U=∏ P : ActiveIndex C D U,activePrime C D U P^activeExponent C D U P := by
  simp only [activePrime,activeExponent]
  rw [Finset.prod_coe_sort (fixedActiveSet C D U)
    (fun P : CommonIndex C D=>commonPrime C D P^(fixedExponent C D U P%6))]
  unfold reducedNumerator
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro P hP hn
  have hp : 6∣fixedExponent C D U P := by
    simpa only [fixedActiveSet,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hn
  simp only [Nat.mod_eq_zero_of_dvd hp,pow_zero]

end SevenEighths.CenteredMomentSecondSixthSource

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRadicalFamily
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst (CommonIndex)
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource
open CenteredMomentRadicalFamily CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentCommonSupport RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem active_radical_product (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) :
    (∏ P : ActiveIndex C D U,Ideal.span {activePrime C D U P})=
      ∏ P∈fixedActiveSet C D U,P.val := by
  simp only [activePrime,commonPrime_span C D hC]
  exact Finset.prod_coe_sort _ (fun P : CommonIndex C D=>P.val)

theorem exists_second_radical_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      τ.modulus.absNorm≤(childCharacter η χ).modulus.absNorm*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (∏P∈fixedActiveSet C D U,P.val).absNorm ∧
      (∀n:O,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
        fixedBadMask 1 (reducedNumerator C D U) n) ∧
      ∀I:Ideal O,Supported I → ∀t:ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom (reducedNumerator C D U) I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hM,hN,hτ⟩ := exists_radical_row_presentation (childCharacter η χ) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    (activePrime C D U) (fun P=>commonPrime_supported C D hC P.val)
    (activeExponent C D U) (activeExponent_pos C D U)
  have he (n:O) : elementCoeff τ n=rowTwist (elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n := by
    rw [reducedNumerator_active_product]
    exact hτ n
  refine ⟨τ,?_,he,?_⟩
  · rw [←map_prod,active_radical_product C D hC U] at hN
    exact hN
  · intro I hI t
    have ht := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1
      (reducedNumerator C D U) he I
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [ht,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
    simp only [one_pow,mul_one]
    rw [heightCoeff_eq_fixed_rowWeight η t I hI]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk]
    ring_nf

end SevenEighths.CenteredMomentSecondRadicalFamily

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRadicalColumns
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondRadicalColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondMovingSupport CenteredMomentSecondSixthReduction
open CenteredMomentSecondSixthSource CenteredMomentSecondRadicalFamily CenteredMomentSecondHeightFamily
open CenteredMomentChildRows CenteredMomentHeckeColumnWindow RayFourExpansion
open CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sixthFactor_span_dvd_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D)) :
    Ideal.span {sixthFactor C D U}∣D := by
  conv_rhs => rw [←right_ideal_product C D hC hD hCD]
  simp only [sixthFactor,span_finset_product,←Ideal.span_singleton_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro P hP
  apply pow_dvd_pow
  have hd := rightExponent_pos C D P
  have hm : min (leftExponent C D P) (rightExponent C D P)≤ rightExponent C D P := min_le_right _ _
  unfold fixedExponent
  split_ifs <;> omega

theorem residual_sixth_coefficient_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (I : Ideal O) (hI : Supported I) (hcop : IsCoprime D I) :
    idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I=
      idealRowHom (reducedNumerator C D U) I := by
  rw [fixed_sixth_coefficient C D U I hI,if_pos
    (hcop.symm.of_isCoprime_of_dvd_right (sixthFactor_span_dvd_right C D hC hD hCD U)),mul_one]

end SevenEighths.CenteredMomentSecondRadicalColumns

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
namespace SevenEighths.CenteredMomentSecondRadicalBudget
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalFamily CenteredMomentSecondMovingSupport
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondHeightFamily
open CenteredMomentCanonicalFirst CenteredMomentChildRows CenteredMomentPartitionNorm
open CenteredMomentHeckeColumnWindow RayFourExpansion CenteredMomentCommonSupport CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_modulus_bound (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus.absNorm≤η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm := by
  have hn : η.modulus*Ideal.span {(12:O)}≠0 := mul_ne_zero η.modulus_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num))
  have hd : (childCharacter η χ).modulus∣η.modulus*Ideal.span {(12:O)} := by
    apply Ideal.dvd_iff_le.mpr
    exact le_inf Ideal.mul_le_left Ideal.mul_le_right
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) (map_dvd Ideal.absNorm hd)

theorem active_radical_dvd (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val)∣
      (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U} := by
  have hd := Finset.prod_dvd_prod_of_subset (fixedActiveSet C D U)
    (U∪nonunitPartitionSet C D U) (fun P:CommonIndex C D=>P.val)
    (fixedActiveSet_subset C D hC hD hCD U w hne)
  have hdis : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hdis] at hd
  rw [nonunitFrequencyGenerator_span]
  simpa only [unitIdeal,commonPrime_span C D hC] using hd

theorem active_radical_norm_bound (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (U : Finset (CommonIndex C D)) (w : O)
    (hne : idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*w)≠0) :
    (∏P∈fixedActiveSet C D U,P.val).absNorm≤
      (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  have hp (S : Finset (CommonIndex C D)) : (∏P∈S,P.val)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  have hv : Ideal.span {nonunitFrequencyGenerator C D U}≠0 := by
    rw [nonunitFrequencyGenerator_span]
    simpa only [unitIdeal,commonPrime_span C D hC] using hp (nonunitPartitionSet C D U)
  simpa only [map_mul] using Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero (hp U) hv)))
    (map_dvd Ideal.absNorm (active_radical_dvd C D hC hD hCD U w hne))

theorem exists_second_budgeted_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀(hD : Supported D),CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*
        (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm := by
  obtain ⟨τ,hN,he,ht⟩ := exists_second_radical_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hne
  have h1 := child_modulus_bound η χ
  have h2 := active_radical_norm_bound C D hC hD hCD U w hne
  apply hN.trans
  calc
    _≤(η.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
      ((∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)) h2
    _=_ := by unfold fixedFactor;ring

theorem conductor_log_bound (η τ : Character) (A B : Ideal O) (hA : A≠0) (hB : B≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*A.absNorm*B.absNorm)
    (Z : ℝ) (hZ : 1<Z) :
    Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z (fixedFactor:ℝ)+Real.logb Z (A.absNorm:ℝ)+Real.logb Z (B.absNorm:ℝ) := by
  have hτ : (0:ℝ)<τ.modulus.absNorm := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  have hη : (η.modulus.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  have hK : (fixedFactor:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt fixedFactor_pos)
  have ha : (A.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA)
  have hb : (B.absNorm:ℝ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB)
  have hh := Real.logb_le_logb_of_le hZ hτ (show (τ.modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*fixedFactor*A.absNorm*B.absNorm by exact_mod_cast hN)
  rwa [Real.logb_mul (mul_ne_zero (mul_ne_zero hη hK) ha) hb,
    Real.logb_mul (mul_ne_zero hη hK) ha,Real.logb_mul hη hK] at hh

end SevenEighths.CenteredMomentSecondRadicalBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondRetainedWidth
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology

namespace SevenEighths.CenteredMomentSecondRetainedWidth
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondRadicalBudget CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondHeightFamily CenteredMomentChildRows CenteredMomentCanonicalFirst
open CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem retained_geometry (R : ℝ) (G V z : O)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    0<R ∧ G≠0 ∧ V≠0 ∧ z≠0 ∧ 1≤normValue z ∧
      normValue z≤4*R/(normValue G*normValue V) ∧
      1≤4*R/(normValue G*normValue V) := by
  obtain ⟨hGV,hz⟩:=retained_product_ne_zero R (G*V) z hne
  have hg:=left_ne_zero_of_mul hGV
  have hv:=right_ne_zero_of_mul hGV
  have hrow:=retained_norm_enclosure R (G*V) z hGV hne
  rw [normValue_mul] at hrow
  have hn:=normValue_ge_one z hz
  have hr:=retainedWeight_enclosure R _ hne
  refine ⟨by linarith,hg,hv,hz,hn,hrow,hn.trans hrow⟩

theorem retained_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (max 1 (4*R/(normValue G*normValue V)))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨hR,hG,hV,_,_,_,hmax⟩:=retained_geometry R G V z hne
  have hg:=normValue_pos G hG
  have hv:=normValue_pos V hV
  have hF : (fixedFactor:ℝ)≠0:=by exact_mod_cast fixedFactor_pos.ne'
  have hc:=conductor_log_bound η τ U (Ideal.span {V}) hU
    (Ideal.span_singleton_eq_bot.not.mpr hV) hN Z hZ
  change Real.logb Z (τ.modulus.absNorm:ℝ)≤Real.logb Z (η.modulus.absNorm:ℝ)+
    Real.logb Z (fixedFactor:ℝ)+Real.logb Z (U.absNorm:ℝ)+Real.logb Z (normValue V) at hc
  rw [max_eq_right hmax,Real.logb_div (mul_ne_zero (by norm_num) hR.ne')
    (mul_ne_zero hg.ne' hv.ne'),Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne',
    Real.logb_mul hg.ne' hv.ne',Real.logb_mul (by norm_num : (4:ℝ)≠0) hF]
  linarith

theorem retained_row_log_budget (η τ : Character) (G V z : O) (U : Ideal O)
    (hU : U≠0)
    (hN : τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*U.absNorm*
      (Ideal.span {V}).absNorm)
    (R Z : ℝ) (hZ : 1<Z)
    (hne : retainedWeight R (normValue ((G*V)*z))≠0) :
    Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue G)+
        Real.logb Z (U.absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨_,_,_,hz,_,hn,_⟩:=retained_geometry R G V z hne
  have hh:=Real.logb_le_logb_of_le hZ (normValue_pos z hz) (hn.trans (le_max_right 1 _))
  have hb:=retained_log_budget η τ G V z U hU hN R Z hZ hne
  linarith

theorem exists_retained_width_family (η : Character) (χ : RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    ∃τ : Character,
      (∀n:O,elementCoeff τ n=rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
        fixedBadMask 1 (CenteredMomentSecondSixthReduction.reducedNumerator C D U) n) ∧
      (∀I:Ideal O,Supported I → ∀t:ℝ,heightCoeff τ t I=heightCoeff η t I*
        idealRowHom (CenteredMomentSecondSixthReduction.reducedNumerator C D U) I*
        rayCharacter χ (primaryGenerator I)) ∧
      ∀hD : Supported D,CompletedGauss.primeSupport C=CompletedGauss.primeSupport D →
      ∀w:O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 →
      τ.modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
      ∀Z R:ℝ,1<Z → ∀z:O,
        retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0 →
        0<R ∧ z≠0 ∧ 1≤normValue z ∧
        normValue z≤4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)) ∧
        Real.logb Z (max 1 (4*R/(normValue (commonFrequencyGenerator C D)*
          normValue (nonunitFrequencyGenerator C D U))))+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) ∧
        Real.logb Z (normValue z)+Real.logb Z (τ.modulus.absNorm:ℝ)≤
          Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-Real.logb Z (normValue (commonFrequencyGenerator C D))+
            Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
  obtain ⟨τ,he,ht,hN⟩:=exists_second_budgeted_family η χ C D hC U
  refine ⟨τ,he,ht,?_⟩
  intro hD hCD w hw
  have hb:=hN hD hCD w hw
  refine ⟨hb,?_⟩
  intro Z R hZ z hz
  have hU : (∏P∈U,P.val)≠0:=Finset.prod_ne_zero_iff.mpr
    (fun P _=>(commonPrime_supported_ideal C D hC P).1)
  obtain ⟨hR,_,_,hne,h1,hrow,_⟩:=retained_geometry R _ _ z hz
  exact ⟨hR,hne,h1,hrow,retained_log_budget η τ _ _ z _ hU hb R Z hZ hz,
    retained_row_log_budget η τ _ _ z _ hU hb R Z hZ hz⟩

end SevenEighths.CenteredMomentSecondRetainedWidth

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondLiveBlock
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
local notation "O" => HeckeFamily.O

lemma liveRows_weight (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    retainedWeight R (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))≠0:=
  (Finset.mem_filter.mp hz).2

lemma liveRows_geometry (C D:Ideal O) (U:Finset (CommonIndex C D)) (R:ℝ) (rows:Finset O)
    (z:O) (hz:z∈liveRows C D U R rows):
    0<R ∧ z≠0 ∧ 1≤normValue z ∧ normValue z≤
      4*R/(normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U)):=by
  obtain ⟨hr,hg,hv,hz0,h1,hbound,hmax⟩:=CenteredMomentSecondRetainedWidth.retained_geometry R
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U R rows z hz)
  exact ⟨hr,hz0,h1,hbound⟩

lemma physicalBlock_live_rows (η:Character) (t:ℝ) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (C D:Ideal O) (hC:Supported C) (hD:Supported D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n:=by
  unfold physicalBlock liveRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hr:retainedWeight R
      (normValue ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z))=0
  · simp only [hr,ne_eq,not_true_eq_false,physicalKernel,Complex.ofReal_zero,
      mul_zero,zero_mul,Finset.sum_const_zero,ite_self]
  · simp only [hr,ne_eq,not_false_eq_true,ite_true]

end SevenEighths.CenteredMomentSecondLiveBlock

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource
local notation "O" => HeckeFamily.O

theorem exists_exceptional_family_oai (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)) : ∃τ,Family η C D hC hD U τ := by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

end SevenEighths.CenteredMomentSecondExceptionalFamily

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentSecondExceptionalFamily.exists_exceptional_family_oai := @OAI.SevenEighths.CenteredMomentSecondExceptionalFamily.exists_exceptional_family_oai
