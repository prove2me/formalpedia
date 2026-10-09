-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentSecondPhysicalLedger.original_block_physical_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T02:59:13.480014+00:00
-- url     : https://prove2.me/submissions/00f670a7-e3a8-4b35-94fa-99c88a3cd5c4

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028
import Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondPhysicalLedger_actual_canonical_physical_cost

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Mask
namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentMask
open ActualEisensteinCubic IdealMobiusDivisorSum
open UniqueFactorizationMonoid

theorem ideal_coprime_mobius (I R : Ideal O) (hR : R ≠ 0) :
    (if IsCoprime I R then (1 : ℂ) else 0) =
      ∑ D ∈ idealDivisors R, if D ∣ I then (moebius D : ℂ) else 0 := by
  let G : Ideal O := R ⊔ I
  have hG : G ≠ 0 := by
    intro hz
    apply hR
    apply le_antisymm _ bot_le
    exact le_sup_left.trans_eq hz
  have hdiv : (idealDivisors R).filter (fun D => D ∣ I) = idealDivisors G := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hR, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G, sup_comm]

end SevenEighths.CenteredMomentMask
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

lemma coprime_mul_dvd_iff (d a n : A) (h : IsCoprime d a) :
    d * a ∣ n ↔ d ∣ n ∧ a ∣ n := by
  constructor
  · intro hn
    exact ⟨(dvd_mul_right d a).trans hn, (dvd_mul_left a d).trans hn⟩
  · rintro ⟨hd, ha⟩
    exact h.mul_dvd hd ha

theorem full_product_congruence (D E a b n : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ n ↔ D * E ∣ n ∧ a ∣ n ∧ b ∣ n := by
  have heq : (D * a) * (E * b) = (D * E) * (a * b) := by ring
  rw [heq, coprime_mul_dvd_iff _ _ _ (ha.mul_right hb), coprime_mul_dvd_iff _ _ _ hab]

lemma residue_eq_zero_iff_dvd (d n : A) :
    Ideal.Quotient.mk (Ideal.span {d}) n = 0 ↔ d ∣ n := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

theorem full_congruence_split (D E a b x y j : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b) :
    (D * a) * (E * b) ∣ (E * b) * x - (D * a) * y - j ↔
      (D * E ∣ E * (b * x) - D * (a * y) - j) ∧
      Ideal.Quotient.mk (Ideal.span {a}) (E * b * x) = Ideal.Quotient.mk _ j ∧
      Ideal.Quotient.mk (Ideal.span {b}) (D * a * y) = Ideal.Quotient.mk _ (-j) := by
  rw [full_product_congruence D E a b _ ha hb hab]
  have hzeroa : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    (residue_eq_zero_iff_dvd a a).mpr dvd_rfl
  have hzerob : Ideal.Quotient.mk (Ideal.span {b}) b = 0 :=
    (residue_eq_zero_iff_dvd b b).mpr dvd_rfl
  have heq : (E * b) * x - (D * a) * y - j = E * (b * x) - D * (a * y) - j := by ring
  refine and_congr (by rw [heq]) (and_congr ?_ ?_)
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzeroa, mul_zero, zero_mul, sub_zero]
    exact sub_eq_zero
  · rw [← residue_eq_zero_iff_dvd]
    simp only [map_sub, map_mul, hzerob, mul_zero, zero_mul, zero_sub, map_neg]
    constructor <;> intro h <;> linear_combination -h

theorem sum_residual_constraints
    {X Y S T : Type*} [Fintype X] [Fintype Y] [CommRing S] [CommRing T]
    [Fintype S] [Fintype T]
    (p : X → Y → Prop) [∀ x y, Decidable (p x y)]
    (f : X → ℂ) (g : Y → ℂ) (α : S → ℂ) (β : T → ℂ)
    (a : Sˣ) (b : Tˣ) (j : S) (k : T) :
    (∑ x : X × S, ∑ y : Y × T,
      if p x.1 y.1 ∧ (a : S) * x.2 = j ∧ (b : T) * y.2 = k
      then (f x.1 * α x.2) * star (g y.1 * β y.2) else 0) =
    (∑ x : X, ∑ y : Y, if p x y then f x * star (g y) else 0) *
      α ((↑a⁻¹ : S) * j) * star (β ((↑b⁻¹ : T) * k)) := by
  have ha (x : S) : (a : S) * x = j ↔ x = (↑a⁻¹ : S) * j := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  have hb (y : T) : (b : T) * y = k ↔ y = (↑b⁻¹ : T) * k := by
    constructor
    · intro h
      rw [← h, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
  simp only [Fintype.sum_prod_type, ha, hb]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : p x y
  · simp only [h, true_and, star_mul]
    simp [ite_and, Finset.sum_ite_eq', mul_assoc, mul_left_comm, mul_comm]
  · simp [h]

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

lemma character_unit_inverse {X : Type*} [CommRing X] [Fintype X]
    (χ : MulChar X ℂ) (u : Xˣ) : χ (↑u⁻¹ : X) = star (χ (u : X)) := by
  rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit]

theorem scaledCommonCorrelation_eq (D E a b : A)
    (hDb : IsCoprime D b) (hEa : IsCoprime E a)
    [Fintype (Residue D)] [Fintype (Residue E)]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ) (j : A) :
    scaledCommonCorrelation D E a b χD χE j =
      star (χD (Ideal.Quotient.mk _ b)) * χE (Ideal.Quotient.mk _ a) *
        fullModulusCorrelation D E χD χE j := by
  have h := fullCorrelation_unit_change
    (scaledResidue D E (D * E) rfl) (scaledResidue E D (D * E) (mul_comm _ _))
    χD χE (residueUnit D b hDb) (residueUnit E a hEa) (Ideal.Quotient.mk _ j)
  simpa only [residueUnit_coe, character_unit_inverse, star_star,
    scaledCommonCorrelation, fullModulusCorrelation] using h

theorem fullModulusCorrelation_extract (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
    let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      scaledCommonCorrelation D E a b χD χE j *
        χa ((↑α⁻¹ : Residue a) * Ideal.Quotient.mk _ j) *
        star (χb ((↑β⁻¹ : Residue b) * Ideal.Quotient.mk _ (-j))) := by
  dsimp only
  let e₁ := principalCRT D a (IsCoprime.mul_left_iff.mp ha).1
  let e₂ := principalCRT E b (IsCoprime.mul_left_iff.mp hb).2
  let α := residueUnit a (E * b) (((IsCoprime.mul_left_iff.mp ha).2.symm).mul_right hab)
  let β := residueUnit b (D * a) (((IsCoprime.mul_left_iff.mp hb).1.symm).mul_right hab.symm)
  let p := fun x : Residue D => fun y : Residue E =>
    scaledResidue D E (D * E) rfl (Ideal.Quotient.mk _ b * x) -
      scaledResidue E D (D * E) (mul_comm _ _) (Ideal.Quotient.mk _ a * y) =
        Ideal.Quotient.mk _ j
  have hextract : fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      ∑ x : Residue D × Residue a, ∑ y : Residue E × Residue b,
        if p x.1 y.1 ∧ (α : Residue a) * x.2 = Ideal.Quotient.mk _ j ∧
          (β : Residue b) * y.2 = Ideal.Quotient.mk _ (-j)
        then (χD x.1 * χa x.2) * star (χE y.1 * χb y.2) else 0 := by
    unfold fullModulusCorrelation fullCorrelation
    apply Fintype.sum_equiv e₁.toEquiv
    intro x
    apply Fintype.sum_equiv e₂.toEquiv
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [e₁, e₂, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, principalCRT_mk,
      hχDa, hχEb, p, α, β, residueUnit_coe, ← map_mul]
    rw [scaledResidue_congruence, scaledResidue_congruence,
      full_congruence_split D E a b x y j ha hb hab]
    split_ifs <;> rfl
  rw [hextract, sum_residual_constraints]
  rfl

theorem fullModulusCorrelation_complete_support (D E a b : A)
    (ha : IsCoprime (D * E) a) (hb : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))]
    (χD : MulChar (Residue D) ℂ) (χE : MulChar (Residue E) ℂ)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (χDa : MulChar (Residue (D * a)) ℂ) (χEb : MulChar (Residue (E * b)) ℂ)
    (hχDa : ∀ x : A, χDa (Ideal.Quotient.mk _ x) =
      χD (Ideal.Quotient.mk _ x) * χa (Ideal.Quotient.mk _ x))
    (hχEb : ∀ x : A, χEb (Ideal.Quotient.mk _ x) =
      χE (Ideal.Quotient.mk _ x) * χb (Ideal.Quotient.mk _ x)) (j : A) :
    fullModulusCorrelation (D * a) (E * b) χDa χEb j =
      fullModulusCorrelation D E χD χE j *
        (χE (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ E))) *
        (χb (Ideal.Quotient.mk _ D) * star (χD (Ideal.Quotient.mk _ b))) *
        (χb (Ideal.Quotient.mk _ a) * star (χa (Ideal.Quotient.mk _ b))) *
        χa (Ideal.Quotient.mk _ j) * star (χb (Ideal.Quotient.mk _ (-j))) := by
  rw [fullModulusCorrelation_extract D E a b ha hb hab χD χE χa χb χDa χEb hχDa hχEb j]
  rw [scaledCommonCorrelation_eq D E a b (IsCoprime.mul_left_iff.mp hb).1
    (IsCoprime.mul_left_iff.mp ha).2 χD χE j]
  simp only [map_mul, character_unit_inverse, residueUnit_coe, star_mul, star_star]
  ring

end SevenEighths.CenteredMomentCommonSupport
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SupportedCorrelation
namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupportedCorrelation
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentCommonSupport

theorem supportedModulusCharacter_mul (d a : O)
    (hd : Supported (Ideal.span {d})) (ha : Supported (Ideal.span {a})) (x : O) :
    supportedModulusCharacter (d * a) (supported_mul_elements d a hd ha) (Ideal.Quotient.mk _ x) =
      supportedModulusCharacter d hd (Ideal.Quotient.mk _ x) *
        supportedModulusCharacter a ha (Ideal.Quotient.mk _ x) := by
  simp only [supportedModulusCharacter_mk, ← Ideal.span_singleton_mul_span_singleton, map_mul]

lemma sexticReciprocityPhase_symm (a b : O) :
    sexticReciprocityPhase a b = sexticReciprocityPhase b a := by
  exact congrArg (fun z : ℤ => (z : ℂ)) (QuadraticAllOddCRT.quadraticRaySign_symm _ _)

theorem supported_opposite_phase (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcop : IsCoprime a b) [Fintype (Residue a)] :
    idealRowHom a (Ideal.span {b}) * star (idealRowHom b (Ideal.span {a})) =
      sexticReciprocityPhase a b := by
  rw [idealRowHom_primary_reciprocity b a hpb hpa hb ha,
    sexticReciprocityPhase_symm b a, mul_assoc]
  have hunit := isUnit_residue_of_coprime a b hcop
  have hn := (supportedModulusCharacter a ha).apply_ne_zero_iff.mpr hunit
  change idealRowHom b (Ideal.span {a}) ≠ 0 at hn
  have heq : idealRowHom b (Ideal.span {a}) * star (idealRowHom b (Ideal.span {a})) = 1 := by
    change supportedModulusCharacter a ha (Ideal.Quotient.mk _ b) *
      star (supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)) = 1
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ hn
  rw [heq, mul_one]

theorem supported_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    [Fintype (Residue D)] [Fintype (Residue E)]
    [Fintype (Residue a)] [Fintype (Residue b)]
    [Fintype (Residue (D * a))] [Fintype (Residue (E * b))] (j : O) :
    supportedCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      supportedCorrelation D E hD hE j * sexticReciprocityPhase a E *
        star (sexticReciprocityPhase b D) * sexticReciprocityPhase a b *
        idealRowHom j (Ideal.span {a}) * star (idealRowHom (-j) (Ideal.span {b})) := by
  unfold supportedCorrelation
  rw [fullModulusCorrelation_complete_support D E a b hcopA hcopB hab
    (supportedModulusCharacter D hD) (supportedModulusCharacter E hE)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)
    (supportedModulusCharacter (D * a) (supported_mul_elements D a hD ha))
    (supportedModulusCharacter (E * b) (supported_mul_elements E b hE hb))
    (supportedModulusCharacter_mul D a hD ha) (supportedModulusCharacter_mul E b hE hb) j]
  simp only [supportedModulusCharacter_mk]
  rw [supported_opposite_phase a E ha hE hpa hpE (IsCoprime.mul_left_iff.mp hcopA).2.symm,
    supported_opposite_phase D b hD hb hpD hpb (IsCoprime.mul_left_iff.mp hcopB).1,
    supported_opposite_phase a b ha hb hpa hpb hab,
    sexticReciprocityPhase_symm D b, star_sexticReciprocityPhase]

theorem actual_complete_common_support (D E a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a - 1)
    (hpb : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b - 1)
    (hcopA : IsCoprime (D * E) a) (hcopB : IsCoprime (D * E) b) (hab : IsCoprime a b)
    (j : O) :
    actualCorrelation (D * a) (E * b)
      (supported_mul_elements D a hD ha) (supported_mul_elements E b hE hb) j =
      completeSupportExtension D E hD hE j a b := by
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero D hD)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero E hE)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero a ha)
  let := ConcreteTraceCRT.finite_quotient_span (supported_element_ne_zero b hb)
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero D hD) (supported_element_ne_zero a ha))
  let := ConcreteTraceCRT.finite_quotient_span
    (mul_ne_zero (supported_element_ne_zero E hE) (supported_element_ne_zero b hb))
  let : Fintype (Residue D) := Fintype.ofFinite _
  let : Fintype (Residue E) := Fintype.ofFinite _
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  let : Fintype (Residue (D * a)) := Fintype.ofFinite _
  let : Fintype (Residue (E * b)) := Fintype.ofFinite _
  exact supported_complete_common_support D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB hab j

end SevenEighths.CenteredMomentSupportedCorrelation
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.FixedRay
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFixedRay
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open RayFourExpansion CenteredMomentPrimary HeckeFamily HeckeRowClosure
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem supported_rayMask (a : O) (ha : Supported (Ideal.span {a})) : rayMask a = 1 := by
  rw [rayMask, if_pos (CenteredMomentCommonSupport.isUnit_residue_of_coprime
    4 a (supported_coprime_four a ha))]

theorem phaseTable_mk (D E a b : O) :
    phaseTable D E (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) =
      sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b := by
  simp only [phaseTable, QuadraticGaussRay.residueQuotientFour_mk,
    sexticReciprocityPhase, star_intCast]

theorem phaseTable_expansion (D E a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
        sexticReciprocityPhase a b =
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (phaseTable D E) χ ξ * rayCharacter χ a * rayCharacter ξ b := by
  have h := pair_phase_expansion (phaseTable D E) a b
  simpa only [supported_rayMask a ha, supported_rayMask b hb, one_mul,
    phaseTable_mk] using h

theorem completeSupportExtension_separated (D E h a b : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    completeSupportExtension D E hD hE h a b =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            (rayCharacter χ a * idealRowHom h (Ideal.span {a})) *
            (rayCharacter ξ b * star (idealRowHom (-h) (Ideal.span {b}))) := by
  rw [completeSupportExtension]
  have he := phaseTable_expansion D E a b ha hb
  calc
    _ = actualCorrelation D E hD hE h *
        (sexticReciprocityPhase a E * star (sexticReciprocityPhase b D) *
          sexticReciprocityPhase a b) *
        idealRowHom h (Ideal.span {a}) * star (idealRowHom (-h) (Ideal.span {b})) := by ring
    _ = _ := by
      rw [he]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring

end SevenEighths.CenteredMomentFixedRay

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.MobiusRegroup
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentMobiusRegroup
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

theorem mobius_on_pool {β : Type*} (T : Finset β) (B : β → Ideal O)
    (hB : ∀ j ∈ T, B j ≠ 0) (j : β) (hj : j ∈ T) (I : Ideal O) :
    (if IsCoprime I (B j) then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T B, if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
  rw [ideal_coprime_mobius I (B j) (hB j hj)]
  have hsub : idealDivisors (B j) ⊆ divisorPool T B :=
    fun D hD => Finset.mem_biUnion.mpr ⟨j,hj,hD⟩
  calc
    _ = ∑ D ∈ idealDivisors (B j), if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors (hB j hj)).mp hD, and_true]
    _ = _ := Finset.sum_subset hsub (by
      intro D hD hn
      have hnd : ¬ D ∣ B j := fun hd => hn ((mem_idealDivisors (hB j hj)).mpr hd)
      simp only [hnd, and_false, ite_false])

theorem finite_pair_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal O) (B : β → Ideal O) (hB : ∀ j ∈ T, B j ≠ 0)
    (F : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if IsCoprime (A i) (B j) then F i j else 0) =
      ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T, if D ∣ A i ∧ D ∣ B j then F i j else 0 := by
  have ht (i : α) (j : β) (hj : j ∈ T) :
      (if IsCoprime (A i) (B j) then F i j else 0) =
        ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
          (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
    have hm := congrArg (fun z : ℂ => z * F i j) (mobius_on_pool T B hB j hj (A i))
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul, mul_ite, mul_zero] using hm
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := divisorPool T B)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [Finset.mul_sum]

open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation

theorem finite_correlation_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}), (moebius L : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T,
          if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
            completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j
          else 0 := by
  have he (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hab : IsCoprime (a i) (b j)
    · rw [if_pos hab, if_pos hab, actual_complete_common_support D E (a i) (b j)
        hD hE (ha i) (hb j) hpD hpE (hpa i) (hpb j) (hcopA i) (hcopB j) hab]
    · simp only [if_neg hab, zero_mul]
  simp_rw [he]
  exact finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1) _

end SevenEighths.CenteredMomentMobiusRegroup

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

theorem rightExponent_pos (I J : Ideal O) (P : CommonIndex I J) : 0< rightExponent I J P :=
  (common_valuations_pos I J P.val P.property).2

end SevenEighths.CenteredMomentCanonicalFirst

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.ChildAssembly
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentMobiusRegroup CenteredMomentRowNorm RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rayCharacter_inverse_star (χ : RayCharacter) (a : O) :
    star (rayCharacter (χ⁻¹) a) = rayCharacter χ a := by
  change star ((χ⁻¹) (Ideal.Quotient.mk _ a)) = χ (Ideal.Quotient.mk _ a)
  rw [MulChar.star_apply', inv_inv]

theorem divisor_pair_separation {α β : Type*} (L : Ideal O) (a : α → O) (b : β → O)
    (c : α → ℂ) (d : β → ℂ) (D E h : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (i : α) (j : β) (K : ℂ) :
    (if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
      completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K else 0) =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
              star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K := by
  by_cases hi : L ∣ Ideal.span {a i}
  · by_cases hj : L ∣ Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [completeSupportExtension_separated D E h (a i) (b j) hD hE (ha i) (hb j)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,Finset.sum_const_zero,mul_zero]

theorem pair_ray_fubini {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (S : Finset α) (T : Finset β) (A : γ → δ → ℂ)
    (L : α → γ → ℂ) (R : β → δ → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, ∑ χ : γ, ∑ ξ : δ, A χ ξ * (L i χ * R j ξ) * K i j) =
      ∑ χ : γ, ∑ ξ : δ, A χ ξ * ∑ i ∈ S, ∑ j ∈ T, (L i χ * R j ξ) * K i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := S)]
  simp_rw [Finset.sum_comm (s := S) (t := Finset.univ)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem finite_correlation_children {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) * actualCorrelation D E hD hE h *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable D E) χ ξ *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K i j := by
  rw [finite_correlation_mobius S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB h c d K]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [divisor_pair_separation L a b c d D E h hD hE ha hb]
  simp_rw [← Finset.mul_sum (s := T), ← Finset.mul_sum (s := S)]
  rw [pair_ray_fubini]
  ring

end SevenEighths.CenteredMomentChildAssembly

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.Scale
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentScale
open CenteredMomentSmooth EisensteinSchwartzPoisson

theorem logarithmic_kernel_argument (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    (K₀ * H₀ / (A₀ * B₀)) *
      Real.exp (Real.log (K / K₀) + Real.log (H / H₀) -
        Real.log (A / A₀) - Real.log (B / B₀)) = K * H / (A * B) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_add,
    Real.exp_log (div_pos hK hK₀), Real.exp_log (div_pos hH hH₀),
    Real.exp_log (div_pos hA hA₀), Real.exp_log (div_pos hB hB₀)]
  field_simp

theorem rootWindow_log_ratio (V : ℝ → ℂ) (A A₀ : ℝ) (hA : 0 < A) (hA₀ : 0 < A₀) :
    rootWindow V (Real.log (A / A₀)) =
      (Real.sqrt A₀ : ℂ) * V (Real.log (A / A₀)) / (Real.sqrt A : ℂ) := by
  rw [rootWindow, Real.exp_log (div_pos hA hA₀), Real.sqrt_div hA.le, Complex.ofReal_div]
  field_simp

theorem wholeKernel_actual (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (K H A B K₀ H₀ A₀ B₀ : ℝ)
    (hK : 0 < K) (hH : 0 < H) (hA : 0 < A) (hB : 0 < B)
    (hK₀ : 0 < K₀) (hH₀ : 0 < H₀) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀) :
    wholeKernel W V (K₀ * H₀ / (A₀ * B₀))
      (Real.log (K / K₀)) (Real.log (H / H₀))
      (Real.log (A / A₀)) (Real.log (B / B₀)) =
      (((Real.sqrt A₀ : ℂ) * (Real.sqrt B₀ : ℂ)) /
        ((Real.sqrt A : ℂ) * (Real.sqrt B : ℂ))) *
      (V 0 (Real.log (K / K₀)) * V 1 (Real.log (H / H₀)) *
        V 2 (Real.log (A / A₀)) * V 3 (Real.log (B / B₀))) *
      paperRadialFourier W (K * H / (A * B)) := by
  rw [wholeKernel, rootWindow_log_ratio _ A A₀ hA hA₀,
    rootWindow_log_ratio _ B B₀ hB hB₀,
    logarithmic_kernel_argument K H A B K₀ H₀ A₀ B₀ hK hH hA hB hK₀ hH₀ hA₀ hB₀]
  ring

end SevenEighths.CenteredMomentScale

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondWholeKernel
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson CompletedGauss
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentScale CenteredMomentSmooth
open CenteredMomentFirstWholeKernel CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

theorem secondEffectiveScale_pos (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (A : O) (hA : A≠0) (K : ℝ) (hK : 0<K) : 0<secondEffectiveScale C D A K := by
  apply div_pos (mul_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hA))))
  exact mul_pos (CenteredMomentFirstScale.norm_pos C hC) (CenteredMomentFirstScale.norm_pos D hD)

theorem primary_norm_sq (I : Ideal O) (hI : Supported I) :
    ‖eisEmbedding (primaryGenerator I)‖^2=(Ideal.absNorm I:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,primary_span_supported I hI]

theorem second_kernel_argument (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (K : ℝ) :
    K*‖eisEmbedding (A*h)‖^2/
      ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2=
      secondEffectiveScale C D A K*‖eisEmbedding h‖^2/((Ideal.absNorm a:ℝ)*(Ideal.absNorm b:ℝ)) := by
  simp only [map_mul,norm_mul,mul_pow,primary_norm_sq (C*a) ((supported_mul_iff _ _).mpr ⟨hC,ha⟩),
    primary_norm_sq (D*b) ((supported_mul_iff _ _).mpr ⟨hD,hb⟩),map_mul,Nat.cast_mul,secondEffectiveScale]
  ring

theorem common_normalized_kernel (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (k H a b C D K K₀ H₀ A₀ B₀ : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b)
    (hC : 0<C) (hD : 0<D) (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    (K:ℂ)/((Real.sqrt (C*a):ℂ)*(Real.sqrt (D*b):ℂ))*
      windows V k H a b K₀ H₀ A₀ B₀*paperRadialFourier W (k*H/(a*b))=
      (K:ℂ)/((Real.sqrt C:ℂ)*(Real.sqrt D:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (H/H₀)) (Real.log (a/A₀)) (Real.log (b/B₀)) := by
  rw [wholeKernel_actual W V k H a b K₀ H₀ A₀ B₀ hk hH ha hb hK₀ hH₀ hA₀ hB₀]
  rw [Real.sqrt_mul hC.le a,Real.sqrt_mul hD.le b]
  simp only [Complex.ofReal_mul,windows]
  have hc : (Real.sqrt C:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hC).ne'
  have hd : (Real.sqrt D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hD).ne'
  have haa : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hbb : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  field_simp

theorem second_frequency_whole_kernel (C D a b : Ideal O)
    (hC : Supported C) (hD : Supported D) (ha : Supported a) (hb : Supported b)
    (A h : O) (hA : A≠0) (hh : h≠0) (K : ℝ) (hK : 0<K)
    (F : ℂ) (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let k := secondEffectiveScale C D A K
    ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*a):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*b):ℝ):ℂ)))*F*
      windows V k (‖eisEmbedding h‖^2) (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) K₀ H₀ A₀ B₀*
      paperRadialFourier W (K*‖eisEmbedding (A*h)‖^2/
        ‖eisEmbedding (primaryGenerator (C*a)*primaryGenerator (D*b))‖^2)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*F*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (k/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log ((Ideal.absNorm a:ℝ)/A₀)) (Real.log ((Ideal.absNorm b:ℝ)/B₀)) := by
  dsimp only
  rw [second_kernel_argument C D a b hC hD ha hb]
  simp only [map_mul,Nat.cast_mul]
  have he := common_normalized_kernel W V (secondEffectiveScale C D A K) (‖eisEmbedding h‖^2)
    (Ideal.absNorm a:ℝ) (Ideal.absNorm b:ℝ) (Ideal.absNorm C:ℝ) (Ideal.absNorm D:ℝ)
    K K₀ H₀ A₀ B₀ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))
    (CenteredMomentFirstScale.norm_pos a ha.1) (CenteredMomentFirstScale.norm_pos b hb.1)
    (CenteredMomentFirstScale.norm_pos C hC.1) (CenteredMomentFirstScale.norm_pos D hD.1)
    hK₀ hH₀ hA₀ hB₀
  convert (preTransparency := .instances) congrArg (fun z : ℂ => F*z) he using 1 <;> ring

end SevenEighths.CenteredMomentSecondWholeKernel

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.PartitionNorm
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartitionNorm
open CenteredMomentPartition CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem commonIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) : 0 < (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

omit [Fintype ι] [DecidableEq ι] in
theorem unitIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (U : Finset ι) : 0 < (Ideal.absNorm (unitIdeal p U) : ℝ) := by
  simp only [unitIdeal, map_prod, Nat.cast_prod]
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

theorem partitionNormalizer_mul_unit_norm (p : ι → O) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U * (Ideal.absNorm (unitIdeal p U) : ℝ) =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [unitIdeal, commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hU : (∏ i ∈ U, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∏ i, if i ∈ U then (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 1 := by simp
  rw [hU, partitionNormalizer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : i ∈ U
  · simp only [if_pos hmem]
    rw [← pow_succ, Nat.sub_add_cancel (le_min (hc i) (hd i))]
  · simp only [if_neg hmem, Nat.sub_zero, mul_one]

theorem partitionNormalizer_eq_norm_ratio (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) / Ideal.absNorm (unitIdeal p U) := by
  apply (eq_div_iff (unitIdeal_norm_pos p hp U).ne').mpr
  exact partitionNormalizer_mul_unit_norm p c d hc hd U

end SevenEighths.CenteredMomentPartitionNorm

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

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.LogDyadic
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

theorem logAnnulus_log (q H : ℝ) (hq : 0<q) (hH : 0<H) :
    logAnnulus (Real.log (q/H))=(annulus (q/H):ℂ) := by
  rw [logAnnulus,Real.exp_log (div_pos hq hH)]

theorem actual_dyadic_log_window (n : ℤ) (q : ℝ) (hq : 0<q) :
    (dyadicWeight n q:ℂ)=logAnnulus (Real.log (q/dyadicScale n)) := by
  rw [logAnnulus_log q _ hq (dyadicScale_pos n)];rfl

theorem actual_product_windows (k H a b : ℝ)
    (hk : 0<k) (hH : 0<H) (ha : 0<a) (hb : 0<b) (n : Fin 4→ℤ) :
    ((dyadicWeight (n 0) k*dyadicWeight (n 1) H*
      dyadicWeight (n 2) a*dyadicWeight (n 3) b:ℝ):ℂ)=
      windows (fun _=>logAnnulus) k H a b
        (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  simp only [Complex.ofReal_mul,actual_dyadic_log_window (n 0) k hk,
    actual_dyadic_log_window (n 1) H hH,actual_dyadic_log_window (n 2) a ha,
    actual_dyadic_log_window (n 3) b hb,windows]

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondScaled
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentProductCRT CenteredMomentUnequal CenteredMomentPartition
local notation "O" => ActualEisensteinCubic.O

theorem divisorCoefficient_moving {α : Type*} (L : Ideal O) (A : O) (a : α → O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  split_ifs <;> ring

theorem actual_scaled_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E A₀ : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

end SevenEighths.CenteredMomentSecondScaled

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

theorem sectorElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (Ideal.span {sectorElement C hC S a}) := by
  rw [sectorElement_span]
  exact sectorPool_supported C hC S a

theorem sectorElement_primary (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : ConcretePrimeRowBridge.goodLambda^2∣sectorElement C hC S a-1 :=
  (primaryGenerator_spec a (supported_primaryGenerator_ne_zero a (sectorPool_supported C hC S a))).2

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha,
    ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hD ha,hCD]

theorem sectorElement_coprime (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (a : sectorPool C hC.1 S) :
    IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement C hC.1 S a) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [←Ideal.span_singleton_mul_span_singleton,primary_span_supported C hC,
    primary_span_supported D hD,sectorElement_span]
  have hc := (Finset.mem_filter.mp a.property).2
  exact hc.mul_left ((coprime_of_same_support C D a hC.1 hD.1
    (sectorPool_supported C hC.1 S a).1 hCD).mp hc)

end SevenEighths.CenteredMomentSecondSectorColumns

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

end SevenEighths.CenteredMomentSecondCanonical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalFrequency
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst CenteredMomentSecondLedger
open CenteredMomentPartition CenteredMomentSupport CenteredMomentSupportedCorrelation
open CenteredMomentCorrelation CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem commonFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C) :
    commonFrequencyGenerator C D≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP
  exact pow_ne_zero _ (supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalNonunit
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalNonunit
open CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentCanonicalFirst
open CenteredMomentSecondLedger CenteredMomentPartition CenteredMomentProductCRT
open CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem nonunitFrequencyGenerator_ne_zero (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) : nonunitFrequencyGenerator C D U≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _=>
    CenteredMomentSupportedCorrelation.supported_element_ne_zero _ (commonPrime_supported C D hC P))

end SevenEighths.CenteredMomentSecondCanonicalNonunit

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondCanonicalScalar
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondCanonicalScalar
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentPartition CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization CenteredMomentSupport
local notation "O" => ActualEisensteinCubic.O

theorem normalizer_pos (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D)) :
    0<normalizer C D U := by
  rw [normalizer,partitionNormalizer_eq_norm_ratio _ (commonPrime_supported C D hC) _ _
    (leftExponent_pos C D) (rightExponent_pos C D)]
  exact div_pos (commonIdeal_norm_pos _ (commonPrime_supported C D hC) _ _)
    (unitIdeal_norm_pos _ (commonPrime_supported C D hC) _)

end SevenEighths.CenteredMomentSecondCanonicalScalar

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorChildren
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentSecondSectorColumns CenteredMomentSecondHeightFamily CenteredMomentSupport
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem sector_correlation_children (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (A₀ : O) (rows : Finset O) (q : O → ℂ) (K : O → Ideal O → Ideal O → ℂ) :
    let a := sectorElement C hC.1 S
    let b := sectorElement D hD.1 S
    let c := fun I : sectorPool C hC.1 S => β (C*I)*heightCoeff η t I
    let d := fun J : sectorPool D hD.1 S => β (D*J)*heightCoeff η t J
    (∑ z∈rows,q z*∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
      (if IsCoprime (I:Ideal O) (J:Ideal O) then
        idealCorrelation (C*I) (D*J)
          ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
          ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A₀*z)
        else 0)*(c I*star (d J))*K z I J)=
      ∑ L∈divisorPool Finset.univ (fun J : sectorPool D hD.1 S => (J:Ideal O)),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,
            pairCoeff (phaseTable (primaryGenerator C) (primaryGenerator D)) χ ξ*
              ∑ z∈rows,(q z*idealCorrelation C D hC hD (A₀*z))*
                ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
                  ((divisorCoefficient L a (movingCoefficient A₀ a c) χ I*idealRowHom z I)*
                    star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) J*idealRowHom (-z) J))*K z I J := by
  dsimp only
  have hb (J : sectorPool D hD.1 S) :
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S J) := by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S J
  have he := actual_scaled_row_children rows Finset.univ Finset.univ
    (primaryGenerator C) (primaryGenerator D) A₀
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hb q
    (fun I => β (C*I)*heightCoeff η t I) (fun J => β (D*J)*heightCoeff η t J)
    (fun z I J => K z I J)
  have hcop (I : sectorPool C hC.1 S) (J : sectorPool D hD.1 S) :
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔ IsCoprime (I:Ideal O) (J:Ideal O) := by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  simp_rw [hcop,sectorElement_span] at he
  simpa only [idealCorrelation,primaryGenerator_mul,sectorElement] using he

end SevenEighths.CenteredMomentSecondSectorChildren

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondSectorFrequency
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorFrequency
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

theorem sectorFrequency_zero_of_common (η : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) (hj : idealCorrelation C D hC hD j=0) :
    sectorFrequency η t S β C D hC hD F j=0 := by
  have he := sector_correlation_children η t S β C D hC hD hCD 1 {j} (fun _=>1) F
  simpa only [Finset.sum_singleton,one_mul,hj,zero_mul,mul_zero,Finset.sum_const_zero,
    sectorFrequency] using he

end SevenEighths.CenteredMomentSecondSectorFrequency

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalWindow
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalWindow
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentSecondSectorRetained CenteredMomentSecondSectorFrequency CenteredMomentSecondSectorColumns
open CenteredMomentSecondWholeKernel CenteredMomentFirstWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSmooth CenteredMomentLogDyadic
local notation "O" => ActualEisensteinCubic.O

theorem physical_kernel_window (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (V : Fin 4→ℝ→ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    physicalKernel C D W K R (A*h) I J*
      windows V (secondEffectiveScale C D A K) (normValue h)
        (Ideal.absNorm I:ℝ) (Ideal.absNorm J:ℝ) K₀ H₀ A₀ B₀=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log (secondEffectiveScale C D A K/K₀)) (Real.log (normValue h/H₀))
            (Real.log ((Ideal.absNorm I:ℝ)/A₀)) (Real.log ((Ideal.absNorm J:ℝ)/B₀)) := by
  have he := second_frequency_whole_kernel C D I J hC hD hI hJ A h hA hh K hK 1 W V
    K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
  dsimp only at he
  simp only [mul_one,normValue_eq_embedding] at he ⊢
  have hd : ‖eisEmbedding (CompletedGauss.primaryGenerator (C*I)*
      CompletedGauss.primaryGenerator (D*J))‖^2=
      (Ideal.absNorm (C*I):ℝ)*(Ideal.absNorm (D*J):ℝ) := by
    rw [map_mul,norm_mul,mul_pow,primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hC,hI⟩),
      primary_norm_sq _ ((supported_mul_iff _ _).mpr ⟨hD,hJ⟩)]
  rw [hd] at he
  unfold physicalKernel
  rw [hd]
  simp only [normValue_eq_embedding]
  convert (preTransparency := .instances) congrArg (fun x : ℂ=>(retainedWeight R (‖eisEmbedding (A*h)‖^2):ℂ)*x) he using 1 <;> ring

theorem physical_kernel_dyadic (C D I J : Ideal O)
    (hC : Supported C) (hD : Supported D) (hI : Supported I) (hJ : Supported J)
    (A h : O) (hA : A≠0) (hh : h≠0) (W : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K)
    (n : Fin 4→ℤ) :
    physicalKernel C D W K R (A*h) I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D A K)*dyadicWeight (n 1) (normValue h)*
        dyadicWeight (n 2) (Ideal.absNorm I:ℝ)*dyadicWeight (n 3) (Ideal.absNorm J:ℝ):ℝ):ℂ)=
      ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
        (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
        (retainedWeight R (normValue (A*h)):ℂ)*
          wholeKernel W (fun _=>logAnnulus)
            (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
            (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
            (Real.log (normValue h/dyadicScale (n 1)))
            (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
            (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3))) := by
  rw [actual_product_windows _ _ _ _ (secondEffectiveScale_pos C D hC.1 hD.1 A hA K hK)
    (normValue_pos h hh) (CenteredMomentFirstScale.norm_pos I hI.1)
    (CenteredMomentFirstScale.norm_pos J hJ.1)]
  exact physical_kernel_window C D I J hC hD hI hJ A h hA hh W K R hK _ _ _ _ _
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)

end SevenEighths.CenteredMomentSecondPhysicalWindow

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalBlock
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondSectorRetained CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

private lemma physicalBlock_scalar (a b c d e f : ℂ) (hb : b ≠ 0) :
    c * d * (a * e * f) = a * b * (b⁻¹ * e * (c * d * f)) := by
  calc
    _ = a * e * (c * d * f) := by ring
    _ = a * (b * b⁻¹) * e * (c * d * f) := by rw [mul_inv_cancel₀ hb, mul_one]
    _ = _ := by ring

theorem physicalBlock_eq (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (R : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) :
    physicalBlock η t S β C D hC hD U R rows W K n=
      (outerScalar C D K n:ℂ)*(normalizer C D U:ℂ)*
        normalizedBlock η t S β C D hC hD U R rows W K n := by
  have hA : commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U≠0 :=
    mul_ne_zero (commonFrequencyGenerator_ne_zero C D hC) (nonunitFrequencyGenerator_ne_zero C D hC U)
  unfold physicalBlock normalizedBlock
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  simp_rw [physical_kernel_dyadic C D _ _ hC hD
    (sectorPool_supported C hC.1 S _) (sectorPool_supported D hD.1 S _)
    _ z hA (hrows z hz) W K R hK n]
  have hn : (normalizer C D U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (normalizer_pos C D hC U).ne'
  simp only [outerScalar,Complex.ofReal_div,Complex.ofReal_mul,retainedScalar,canonicalPartitionScalar]
  simp only [normalizer] at hn ⊢
  by_cases hp : canonicalPartition C D U (nonunitFrequencyGenerator C D U*z)
  · simp only [hp,ite_true]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    exact physicalBlock_scalar _ _ _ _ _ _ hn
  · simp only [hp,ite_false,mul_zero,zero_mul,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondPhysicalBlock

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalLedger
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondPhysicalLedger
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
open CenteredMomentForcing
open CenteredMomentSecondSectorFrequency CenteredMomentFirstWholeKernel
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem physicalBlock_canonical_witness (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (hK:0<K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,canonicalPartition C D U (nonunitFrequencyGenerator C D U*z) ∧
      idealCorrelation C D hC hD
        (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  have hn:=right_ne_zero_of_mul hne
  unfold normalizedBlock at hn
  obtain ⟨z,hzr,hz⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
  have hr:=left_ne_zero_of_mul hz
  have hpart:canonicalPartition C D U (nonunitFrequencyGenerator C D U*z):=by
    by_contra hp
    simp only [retainedScalar,canonicalPartitionScalar,hp,ite_false,zero_mul] at hr
    exact hr rfl
  refine ⟨z,hzr,hpart,?_⟩
  intro hc
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>CenteredMomentLogDyadic.logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)
    (by simpa only [mul_assoc] using hc)
  exact (right_ne_zero_of_mul hz) (by simpa only [sectorFrequency,F] using he)

theorem original_block_physical_cost_oai (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hK:0<K) (H a Z:ℝ) (hH:0<H) (ha:0<a) (hZ:1<Z)
    (hlower:∀I:Ideal O,β I≠0→a*H≤(Ideal.absNorm I:ℝ))
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    centralPhysicalCost C D U K H n≤
      H^(1/3:ℝ)*K^(5/6:ℝ)*a^(-2/3:ℝ)*
        Z^(-(Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ))/3) := by
  obtain ⟨z,hz,hpart,hcorr⟩:=physicalBlock_canonical_witness η t S β C D hC hD hCD U R rows hrows W K hK n hne
  exact actual_canonical_physical_cost η t S β C D hC hD hCD U _ hpart hcorr R rows W K n
    hK H a Z hH ha hZ hlower hne

end SevenEighths.CenteredMomentSecondPhysicalLedger

end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CenteredMomentSecondPhysicalLedger.original_block_physical_cost_oai := @OAI.SevenEighths.CenteredMomentSecondPhysicalLedger.original_block_physical_cost_oai
