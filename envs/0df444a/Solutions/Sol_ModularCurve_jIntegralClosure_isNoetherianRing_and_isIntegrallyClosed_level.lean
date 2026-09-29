-- Prove2me | solution 1 for ModularCurve.jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/41688c18-3d97-5cd5-9639-373d654ae937

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_minpoly_jqNModC_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def coeffValuationSubring : ValuationSubring K where
  carrier := {x | (x : AlgebraicClosure ℚ) ∈ A}
  mul_mem' hx hy := A.mul_mem _ _ hx hy
  one_mem' := A.one_mem
  add_mem' hx hy := A.add_mem _ _ hx hy
  zero_mem' := A.zero_mem
  neg_mem' hx := A.neg_mem _ hx
  mem_or_inv_mem' x := A.mem_or_inv_mem (x : AlgebraicClosure ℚ)

theorem mem_coeffValuationSubring {x : K} :
    x ∈ coeffValuationSubring A K ↔ (x : AlgebraicClosure ℚ) ∈ A :=
  Iff.rfl

theorem mem_coeffSubring {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K :=
  Iff.rfl

def coeffSubringEquiv : coeffSubring A K ≃+* coeffValuationSubring A K where
  toFun x := ⟨⟨(x : AlgebraicClosure ℚ), ((mem_coeffSubring A K).mp x.2).2⟩,
    ((mem_coeffSubring A K).mp x.2).1⟩
  invFun v := ⟨((v : K) : AlgebraicClosure ℚ), (mem_coeffSubring A K).mpr ⟨v.2, (v : K).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem mem_of_isIntegral_int {x : AlgebraicClosure ℚ} (hx : IsIntegral ℤ x) : x ∈ A := by

  have hA : IsIntegral A x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A)) (algebraMap ℤ _)]
    exact hpx
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hA
  rw [← hz]
  exact z.2

theorem blockB [FiniteDimensional ℚ K] :
    IsNoetherianRing ↥(coeffSubring A K) ∧ IsIntegrallyClosed ↥(coeffSubring A K) ∧
      IsDomain ↥(coeffSubring A K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : NumberField K := NumberField.mk

  have hOV : ∀ r : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K r ∈ coeffValuationSubring A K := by
    intro r
    rw [mem_coeffValuationSubring]
    have hint : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
      NumberField.RingOfIntegers.isIntegral_coe r

    apply mem_of_isIntegral_int A
    obtain ⟨p, hp, hpr⟩ := hint
    refine ⟨p, hp, ?_⟩
    have h := congrArg (IntermediateField.val K).toRingHom hpr
    rw [map_zero, Polynomial.hom_eval₂,
      RingHom.ext_int (RingHom.comp _ _) (algebraMap ℤ (AlgebraicClosure ℚ))] at h
    exact h

  have hnoeth : IsNoetherianRing (coeffValuationSubring A K) := by
    by_cases hV : coeffValuationSubring A K = ⊤
    · have e' : (coeffValuationSubring A K).toSubring ≃+* K :=
        (RingEquiv.subringCongr (by rw [hV]; rfl)).trans Subring.topEquiv
      exact isNoetherianRing_of_ringEquiv K e'.symm
    · obtain ⟨v, hv, -⟩ :=
        ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
          (coeffValuationSubring A K) hOV hV
      rw [hv]
      infer_instance
  refine ⟨isNoetherianRing_of_ringEquiv _ (coeffSubringEquiv A K).symm,
    IsIntegrallyClosed.of_equiv (coeffSubringEquiv A K).symm, inferInstance⟩

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

open Polynomial

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def jEval : Polynomial (coeffSubring A K) →+* LaurentSeries (AlgebraicClosure ℚ) :=
  Polynomial.eval₂RingHom (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ))

theorem jEval_apply (p : Polynomial (coeffSubring A K)) :
    jEval A K p = p.eval₂ (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) :=
  rfl

theorem constSeries_eq_comp :
    CharPReduction.constSeries (coeffSubring A K)
      = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
          (coeffSubring A K).subtype :=
  rfl

theorem jEval_eq_aeval_map (p : Polynomial (coeffSubring A K)) :
    jEval A K p = Polynomial.aeval (jqModC (AlgebraicClosure ℚ)) (p.map (coeffSubring A K).subtype) := by
  rw [jEval_apply, Polynomial.aeval_def, Polynomial.eval₂_map, constSeries_eq_comp]

theorem jEval_injective : Function.Injective (jEval A K) := by
  intro p q h
  rw [jEval_eq_aeval_map, jEval_eq_aeval_map] at h
  have hinj : Function.Injective (Polynomial.aeval (R := AlgebraicClosure ℚ) (jqModC (AlgebraicClosure ℚ))) :=
    transcendental_iff_injective.mp (ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ))
  exact Polynomial.map_injective _ Subtype.val_injective (hinj h)

theorem range_jEval : (jEval A K).range = jRing A K := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a =>
        rw [jEval_apply, Polynomial.eval₂_monomial]
        have h1 : CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
          Subring.subset_closure (Or.inl ⟨a, rfl⟩)
        have h2 : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
          Subring.subset_closure (Or.inr rfl)
        exact (jRing A K).mul_mem h1 ((jRing A K).pow_mem h2 n)
  · rw [jRing, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | rfl)
    · exact ⟨Polynomial.C a, by rw [jEval_apply, Polynomial.eval₂_C]⟩
    · exact ⟨Polynomial.X, by rw [jEval_apply, Polynomial.eval₂_X]⟩

def polynomialEquivJRing : Polynomial (coeffSubring A K) ≃+* jRing A K :=
  (RingEquiv.ofBijective (jEval A K).rangeRestrict
      ⟨fun _ _ h => jEval_injective A K (congrArg Subtype.val h),
        (jEval A K).rangeRestrict_surjective⟩).trans
    (RingEquiv.subringCongr (range_jEval A K))

theorem coe_polynomialEquivJRing (p : Polynomial (coeffSubring A K)) :
    ((polynomialEquivJRing A K p : jRing A K) : LaurentSeries (AlgebraicClosure ℚ))
      = p.eval₂ (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) :=
  rfl

theorem exists_polynomial_equiv_jRing :
    ∃ e : Polynomial ↥(coeffSubring A K) ≃+* ↥(jRing A K),
      ∀ p, ((e p : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ))
        = p.eval₂ (CharPReduction.constSeries (coeffSubring A K)) (jqModC (AlgebraicClosure ℚ)) :=
  ⟨polynomialEquivJRing A K, coe_polynomialEquivJRing A K⟩

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_coeffSubring_iff {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := by
  simp only [coeffSubring, Subring.mem_inf]
  exact Iff.rfl

theorem exists_div_eq_of_mem' (x : AlgebraicClosure ℚ) (hx : x ∈ K) :
    ∃ a b : ↥(coeffSubring A K), (b : AlgebraicClosure ℚ) ≠ 0 ∧ x = a / b := by
  rcases A.mem_or_inv_mem x with h | h
  · refine ⟨⟨x, (mem_coeffSubring_iff A K).mpr ⟨h, hx⟩⟩, ⟨1, one_mem _⟩, ?_, ?_⟩
    · simp
    · simp
  · by_cases hx0 : x = 0
    · refine ⟨⟨0, zero_mem _⟩, ⟨1, one_mem _⟩, by simp, by simp [hx0]⟩
    refine ⟨⟨1, one_mem _⟩, ⟨x⁻¹, (mem_coeffSubring_iff A K).mpr ⟨h, IntermediateField.inv_mem K hx⟩⟩, ?_, ?_⟩
    · simpa using hx0
    · simp

theorem constSeries_coeffSubring_apply (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) := rfl

theorem algebraMap_mem_fieldOver (N : ℕ) [NeZero N] {x : AlgebraicClosure ℚ} (hx : x ∈ K) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) x ∈ fieldOver N K := by
  refine Subfield.subset_closure (Or.inl ⟨⟨x, hx⟩, rfl⟩)

theorem jqModC_mem_fieldOver (N : ℕ) [NeZero N] : jqModC (AlgebraicClosure ℚ) ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

theorem jqNModC_mem_fieldOver' (N : ℕ) [NeZero N] : jqNModC (AlgebraicClosure ℚ) N ∈ fieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ rfl))

theorem jqModC_mem_jRing' : jqModC (AlgebraicClosure ℚ) ∈ jRing A K :=
  Subring.subset_closure (Or.inr rfl)

theorem constSeries_mem_jRing (a : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) a ∈ jRing A K :=
  Subring.subset_closure (Or.inl ⟨a, rfl⟩)

theorem jRing_le_fieldOver' (N : ℕ) [NeZero N] : jRing A K ≤ (fieldOver N K).toSubring := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl)
  · exact algebraMap_mem_fieldOver K N ((mem_coeffSubring_iff A K).mp a.2).2
  · exact jqModC_mem_fieldOver K N

theorem fieldOver_eq_closure' (N : ℕ) [NeZero N] :
    fieldOver N K = Subfield.closure ((jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ)))
      ∪ {jqNModC (AlgebraicClosure ℚ) N}) := by
  apply le_antisymm
  · rw [fieldOver, Subfield.closure_le]
    rintro x (⟨a, rfl⟩ | rfl | rfl)
    ·
      obtain ⟨b, c, hc, hbc⟩ := exists_div_eq_of_mem' A K (a : AlgebraicClosure ℚ) a.2
      have : CharPReduction.constSeries K.toSubalgebra.toSubring a
          = CharPReduction.constSeries (coeffSubring A K) b / CharPReduction.constSeries (coeffSubring A K) c := by
        show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ) = _
        rw [hbc, map_div₀]; rfl
      rw [this]
      exact div_mem (Subfield.subset_closure (Or.inl (constSeries_mem_jRing A K b)))
        (Subfield.subset_closure (Or.inl (constSeries_mem_jRing A K c)))
    · exact Subfield.subset_closure (Or.inl (jqModC_mem_jRing' A K))
    · exact Subfield.subset_closure (Or.inr rfl)
  · rw [Subfield.closure_le]
    rintro x (hx | rfl)
    · exact jRing_le_fieldOver' A K N hx
    · exact jqNModC_mem_fieldOver' K N

theorem isIntegral_jRing_jqNModC' (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral ↥(jRing A K) (jqNModC (AlgebraicClosure ℚ) N) := by
  let jR : ↥(jRing A K) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_jRing' A K⟩
  refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(jRing A K)) jR), data.monic.map _, ?_⟩

  let F := IntermediateField.adjoin (AlgebraicClosure ℚ) ({jqModC (AlgebraicClosure ℚ)} : Set (LaurentSeries (AlgebraicClosure ℚ)))
  let jF : ↥F := ⟨jqModC (AlgebraicClosure ℚ), IntermediateField.mem_adjoin_simple_self _ _⟩
  have h0 : Polynomial.aeval (jqNModC (AlgebraicClosure ℚ) N) (minpoly ↥F (jqNModC (AlgebraicClosure ℚ) N)) = 0 :=
    minpoly.aeval ↥F _
  rw [ModularCurve.minpoly_jqNModC_eq (AlgebraicClosure ℚ) N data, Polynomial.aeval_def,
    Polynomial.eval₂_map] at h0
  rw [Polynomial.eval₂_map]
  convert h0 using 2 <;> try rfl
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [jR, jF]
  rfl

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A₀ : Subring L) {k : Type*} [Field k]
  (red : A₀ →+* k) (a b : k)

def modularRange : Subring (LaurentSeries L) := (modularEval N A₀).range

theorem modularEval_mem_modularRange (p : MvPolynomial (Fin 2) A₀) :
    modularEval N A₀ p ∈ modularRange N A₀ :=
  ⟨p, rfl⟩

theorem mem_modularRange_iff {x : LaurentSeries L} :
    x ∈ modularRange N A₀ ↔ ∃ p : MvPolynomial (Fin 2) A₀, modularEval N A₀ p = x :=
  Iff.rfl

theorem modularRange_le_modularLocalizedAtPoint :
    modularRange N A₀ ≤ modularLocalizedAtPoint N A₀ red a b := by
  rintro _ ⟨p, rfl⟩
  exact modularEval_mem_modularLocalizedAtPoint N A₀ red a b p

def nodeUnits : Submonoid (modularRange N A₀) where
  carrier := {m | ∃ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 ∧
    (m : LaurentSeries L) = modularEval N A₀ s}
  one_mem' := ⟨1, by rw [map_one]; exact one_ne_zero, by rw [map_one]; rfl⟩
  mul_mem' := by
    rintro m m' ⟨s, hs, hm⟩ ⟨t, ht, hm'⟩
    refine ⟨s * t, by rw [map_mul]; exact mul_ne_zero hs ht, ?_⟩
    rw [map_mul, ← hm, ← hm']
    rfl

theorem mem_nodeUnits_iff {m : modularRange N A₀} :
    m ∈ nodeUnits N A₀ red a b ↔ ∃ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 ∧
      (m : LaurentSeries L) = modularEval N A₀ s :=
  Iff.rfl

def nodeUnitOf (s : MvPolynomial (Fin 2) A₀) (hs : pointEval A₀ red a b s ≠ 0) :
    nodeUnits N A₀ red a b :=
  ⟨⟨modularEval N A₀ s, modularEval_mem_modularRange N A₀ s⟩, s, hs, rfl⟩

@[reducible] def modularRangeAlgebra : Algebra (modularRange N A₀) (modularLocalizedAtPoint N A₀ red a b) :=
  (Subring.inclusion (modularRange_le_modularLocalizedAtPoint N A₀ red a b)).toAlgebra

attribute [local instance] modularRangeAlgebra

theorem algebraMap_modularRange_apply (x : modularRange N A₀) :
    ((algebraMap (modularRange N A₀) (modularLocalizedAtPoint N A₀ red a b) x :
      modularLocalizedAtPoint N A₀ red a b) : LaurentSeries L) = x :=
  rfl

theorem isScalarTower_modularRange :
    IsScalarTower (modularRange N A₀) (modularLocalizedAtPoint N A₀ red a b) (LaurentSeries L) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_modularRange

theorem isLocalization_nodeUnits
    (hM : ∀ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 → modularEval N A₀ s ≠ 0) :
    IsLocalization (nodeUnits N A₀ red a b) (modularLocalizedAtPoint N A₀ red a b) where
  map_units := by
    rintro ⟨m, s, hs, hm⟩
    have hm0 : (m : LaurentSeries L) ≠ 0 := by rw [hm]; exact hM s hs

    have hinv : (m : LaurentSeries L)⁻¹ ∈ modularLocalizedAtPoint N A₀ red a b :=
      ⟨1, s, hs, by rw [← hm, inv_mul_cancel₀ hm0, map_one]⟩
    refine IsUnit.of_mul_eq_one ⟨(m : LaurentSeries L)⁻¹, hinv⟩ ?_
    apply Subtype.ext
    change (m : LaurentSeries L) * (m : LaurentSeries L)⁻¹ = 1
    exact mul_inv_cancel₀ hm0
  surj := by
    rintro ⟨z, r, s, hs, hz⟩
    refine ⟨(⟨modularEval N A₀ r, modularEval_mem_modularRange N A₀ r⟩, nodeUnitOf N A₀ red a b s hs), ?_⟩
    apply Subtype.ext
    exact hz
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    have : (x : LaurentSeries L) = y := congrArg (fun z : modularLocalizedAtPoint N A₀ red a b => (z : LaurentSeries L)) h
    rw [Subtype.ext this]

theorem exists_nodeUnit_mul_isIntegral
    (hM : ∀ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 → modularEval N A₀ s ≠ 0)
    (x : LaurentSeries L) (hx : IsIntegral (modularLocalizedAtPoint N A₀ red a b) x) :
    ∃ s : MvPolynomial (Fin 2) A₀, pointEval A₀ red a b s ≠ 0 ∧
      IsIntegral (modularRange N A₀) (x * modularEval N A₀ s) := by
  haveI := isLocalization_nodeUnits N A₀ red a b hM
  obtain ⟨m, hm⟩ := hx.exists_multiple_integral_of_isLocalization (nodeUnits N A₀ red a b)
  obtain ⟨s, hs, hms⟩ := m.2
  refine ⟨s, hs, ?_⟩
  rw [Submonoid.smul_def, Algebra.smul_def, mul_comm] at hm
  rwa [← hms]

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem modularEval_mem_fieldOver (N : ℕ) [NeZero N] (p : MvPolynomial (Fin 2) (coeffSubring A K)) :
    modularEval N (coeffSubring A K) p ∈ fieldOver N K := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_C]
      exact algebraMap_mem_fieldOver K N ((mem_coeffSubring_iff A K).mp c.2).2
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact jqModC_mem_fieldOver K N
      · exact jqNModC_mem_fieldOver' K N

theorem jRing_le_modularLocalizedAtPoint (N : ℕ) [NeZero N] {k : Type*} [Field k]
    (red₀ : ↥(coeffSubring A K) →+* k) (a b : k) :
    jRing A K ≤ modularLocalizedAtPoint N (coeffSubring A K) red₀ a b := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | rfl)
  · have : CharPReduction.constSeries (coeffSubring A K) c = modularEval N (coeffSubring A K) (MvPolynomial.C c) := by
      unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
    rw [this]
    exact modularEval_mem_modularLocalizedAtPoint N _ red₀ a b _
  · have : jqModC (AlgebraicClosure ℚ) = modularEval N (coeffSubring A K) (MvPolynomial.X 0) := by
      unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl
    rw [this]
    exact modularEval_mem_modularLocalizedAtPoint N _ red₀ a b _

theorem isIntegral_modularLocalizedAtPoint_of_isIntegral_jRing (N : ℕ) [NeZero N] {k : Type*} [Field k]
    (red₀ : ↥(coeffSubring A K) →+* k) (a b : k) {c : LaurentSeries (AlgebraicClosure ℚ)}
    (hc : IsIntegral ↥(jRing A K) c) :
    IsIntegral ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b) c := by
  have hle := jRing_le_modularLocalizedAtPoint A K N red₀ a b
  obtain ⟨p, hp, hpc⟩ := hc
  refine ⟨p.map (Subring.inclusion hle), hp.map _, ?_⟩
  have hcomp : (algebraMap ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b)
      (LaurentSeries (AlgebraicClosure ℚ))).comp (Subring.inclusion hle)
        = algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) :=
    RingHom.ext fun _ => rfl
  rw [Polynomial.eval₂_map, hcomp]
  exact hpc

theorem mem_fieldOver_and_isIntegral_of_mul_modularEval_eq (N : ℕ) [NeZero N] {k : Type*} [Field k]
    (red₀ : ↥(coeffSubring A K) →+* k) (a b : k)
    (hM : ∀ s, pointEval (coeffSubring A K) red₀ a b s ≠ 0 → modularEval N (coeffSubring A K) s ≠ 0)
    {x c : LaurentSeries (AlgebraicClosure ℚ)} (hc : c ∈ jIntegralClosure N A K)
    {s : MvPolynomial (Fin 2) ↥(coeffSubring A K)} (hs : pointEval (coeffSubring A K) red₀ a b s ≠ 0)
    (hx : x * modularEval N (coeffSubring A K) s = c) :
    x ∈ fieldOver N K ∧ IsIntegral ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b) x := by
  have hs0 : modularEval N (coeffSubring A K) s ≠ 0 := hM s hs
  have hxeq : x = c * (modularEval N (coeffSubring A K) s)⁻¹ := by
    rw [← hx, mul_inv_cancel_right₀ hs0]

  have hinv : (modularEval N (coeffSubring A K) s)⁻¹ ∈ modularLocalizedAtPoint N (coeffSubring A K) red₀ a b :=
    ⟨1, s, hs, by rw [inv_mul_cancel₀ hs0, map_one]⟩
  refine ⟨?_, ?_⟩
  · rw [hxeq]
    exact mul_mem hc.1 (inv_mem (modularEval_mem_fieldOver A K N s))
  · rw [hxeq]
    refine IsIntegral.mul (isIntegral_modularLocalizedAtPoint_of_isIntegral_jRing A K N red₀ a b hc.2) ?_
    exact isIntegral_algebraMap (R := ↥(modularLocalizedAtPoint N (coeffSubring A K) red₀ a b))
      (A := LaurentSeries (AlgebraicClosure ℚ)) (x := ⟨_, hinv⟩)

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

noncomputable section

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (N : ℕ) [NeZero N]

theorem jRing_le_modularRange : jRing A K ≤ modularRange N (coeffSubring A K) := by
  rw [jRing, Subring.closure_le]
  rintro x (⟨c, rfl⟩ | rfl)
  · refine ⟨MvPolynomial.C c, ?_⟩
    unfold modularEval; rw [MvPolynomial.eval₂Hom_C]
  · refine ⟨MvPolynomial.X 0, ?_⟩
    unfold modularEval; rw [MvPolynomial.eval₂Hom_X']; rfl

@[reducible] def jRingModularRangeAlgebra : Algebra ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) :=
  (Subring.inclusion (jRing_le_modularRange A K N)).toAlgebra

attribute [local instance] jRingModularRangeAlgebra

theorem isScalarTower_jRing_modularRange :
    IsScalarTower ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] isScalarTower_jRing_modularRange

theorem isIntegral_jRing_modularEval (data : ModularPolynomialData N)
    (p : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    IsIntegral ↥(jRing A K) (modularEval N (coeffSubring A K) p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_C]
      exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, constSeries_mem_jRing A K c⟩)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [map_mul]
      refine hp.mul ?_
      unfold modularEval
      rw [MvPolynomial.eval₂Hom_X']
      fin_cases i
      · exact isIntegral_algebraMap (R := ↥(jRing A K)) (x := ⟨_, jqModC_mem_jRing' A K⟩)
      · exact isIntegral_jRing_jqNModC' A K N data

theorem algebra_isIntegral_jRing_modularRange (data : ModularPolynomialData N) :
    Algebra.IsIntegral ↥(jRing A K) ↥(modularRange N (coeffSubring A K)) := by
  refine ⟨fun m => ?_⟩
  obtain ⟨p, hp⟩ := (mem_modularRange_iff N (coeffSubring A K)).mp m.2
  have h : IsIntegral ↥(jRing A K)
      ((IsScalarTower.toAlgHom ↥(jRing A K) ↥(modularRange N (coeffSubring A K))
        (LaurentSeries (AlgebraicClosure ℚ))) m) := by
    change IsIntegral ↥(jRing A K) (m : LaurentSeries (AlgebraicClosure ℚ))
    rw [← hp]
    exact isIntegral_jRing_modularEval A K N data p
  exact (isIntegral_algHom_iff _ Subtype.val_injective).mp h

theorem isIntegral_jRing_of_isIntegral_modularRange (data : ModularPolynomialData N)
    {y : LaurentSeries (AlgebraicClosure ℚ)}
    (hy : IsIntegral ↥(modularRange N (coeffSubring A K)) y) :
    IsIntegral ↥(jRing A K) y := by
  haveI := algebra_isIntegral_jRing_modularRange A K N data
  exact isIntegral_trans y hy

end

end NodeLocalized
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

scoped instance charZero_laurentSeries_algClosure : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := AlgebraicClosure ℚ))

scoped instance charZero_fieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    CharZero ↥(fieldOver N K) :=
  (fieldOver N K).subtype.charZero

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

open Polynomial

section Tower

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
  (N : ℕ) [NeZero N]

def jRingToFieldOver : ↥(jRing A K) →+* ↥(fieldOver N K) where
  toFun x := ⟨x, jRing_le_fieldOver' A K N x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

set_option maxHeartbeats 12800000 in
noncomputable scoped instance algebraJRingFieldOver : Algebra ↥(jRing A K) ↥(fieldOver N K) :=
  (jRingToFieldOver A K N).toAlgebra

set_option maxHeartbeats 12800000 in
scoped instance isScalarTower_jRing_fieldOver :
    IsScalarTower ↥(jRing A K) ↥(fieldOver N K) (LaurentSeries (AlgebraicClosure ℚ)) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

set_option maxHeartbeats 12800000 in
theorem jRingToFieldOver_injective : Function.Injective (jRingToFieldOver A K N) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun z : ↥(fieldOver N K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
  exact h'

set_option maxHeartbeats 12800000 in
scoped instance faithfulSMul_jRing_fieldOver : FaithfulSMul ↥(jRing A K) ↥(fieldOver N K) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (jRingToFieldOver_injective A K N)

noncomputable def jN : ↥(fieldOver N K) := ⟨jqNModC (AlgebraicClosure ℚ) N, jqNModC_mem_fieldOver' K N⟩

theorem isIntegral_jRing_jN (data : ModularPolynomialData N) : IsIntegral ↥(jRing A K) (jN K N) :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver N K) (LaurentSeries (AlgebraicClosure ℚ)))
    Subtype.val_injective).mp (isIntegral_jRing_jqNModC' A K N data)

set_option maxHeartbeats 6400000 in

theorem adjoin_jN_eq_top (F : Type*) [Field F] [Algebra ↥(jRing A K) F] [Algebra F ↥(fieldOver N K)]
    [IsScalarTower ↥(jRing A K) F ↥(fieldOver N K)] :
    IntermediateField.adjoin F ({jN K N} : Set ↥(fieldOver N K)) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hx' : x ∈ Subfield.closure ((jRing A K : Set (LaurentSeries (AlgebraicClosure ℚ)))
      ∪ {jqNModC (AlgebraicClosure ℚ) N}) := by rwa [← fieldOver_eq_closure' A K N]

  induction hx' using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with hy | rfl
    · have : (⟨y, hx⟩ : ↥(fieldOver N K)) = algebraMap F _ (algebraMap ↥(jRing A K) F ⟨y, hy⟩) := by
        rw [← IsScalarTower.algebraMap_apply]; rfl
      rw [this]; exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin F _ (Set.mem_singleton _)
  | one =>
    have e : (⟨1, hx⟩ : ↥(fieldOver N K)) = 1 := Subtype.ext rfl
    rw [e]; exact one_mem _
  | add y z hy hz ihy ihz =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have hzF : z ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hz
    have e : (⟨y + z, hx⟩ : ↥(fieldOver N K)) = (⟨y, hyF⟩ : ↥(fieldOver N K)) + ⟨z, hzF⟩ := Subtype.ext rfl
    rw [e]
    exact add_mem (ihy hyF) (ihz hzF)
  | neg y hy ihy =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have e : (⟨-y, hx⟩ : ↥(fieldOver N K)) = -(⟨y, hyF⟩ : ↥(fieldOver N K)) := Subtype.ext rfl
    rw [e]
    exact neg_mem (ihy hyF)
  | inv y hy ihy =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have e : (⟨y⁻¹, hx⟩ : ↥(fieldOver N K)) = (⟨y, hyF⟩ : ↥(fieldOver N K))⁻¹ := Subtype.ext rfl
    rw [e]
    exact inv_mem (ihy hyF)
  | mul y z hy hz ihy ihz =>
    have hyF : y ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hy
    have hzF : z ∈ fieldOver N K := by rw [fieldOver_eq_closure' A K N]; exact hz
    have e : (⟨y * z, hx⟩ : ↥(fieldOver N K)) = (⟨y, hyF⟩ : ↥(fieldOver N K)) * ⟨z, hzF⟩ := Subtype.ext rfl
    rw [e]
    exact mul_mem (ihy hyF) (ihz hzF)

def jRingToIntegralClosure : ↥(jRing A K) →+* ↥(jIntegralClosure N A K) where
  toFun x := ⟨x, jRing_le_fieldOver' A K N x.2, isIntegral_algebraMap (R := ↥(jRing A K)) (x := x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def integralClosureToFieldOver : ↥(jIntegralClosure N A K) →+* ↥(fieldOver N K) where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable scoped instance algebraJRingIntegralClosure : Algebra ↥(jRing A K) ↥(jIntegralClosure N A K) :=
  (jRingToIntegralClosure A K N).toAlgebra

noncomputable scoped instance algebraIntegralClosureFieldOver : Algebra ↥(jIntegralClosure N A K) ↥(fieldOver N K) :=
  (integralClosureToFieldOver A K N).toAlgebra

set_option maxHeartbeats 12800000 in
scoped instance isScalarTower_jRing_integralClosure_fieldOver :
    IsScalarTower ↥(jRing A K) ↥(jIntegralClosure N A K) ↥(fieldOver N K) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

set_option maxHeartbeats 12800000 in
scoped instance isIntegralClosure_jIntegralClosure :
    IsIntegralClosure ↥(jIntegralClosure N A K) ↥(jRing A K) ↥(fieldOver N K) where
  algebraMap_injective x y h := Subtype.ext (congrArg (fun z : ↥(fieldOver N K) => (z : LaurentSeries (AlgebraicClosure ℚ))) h)
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hx' : IsIntegral ↥(jRing A K) (x : LaurentSeries (AlgebraicClosure ℚ)) :=
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver N K)
          (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective).mpr hx
      exact ⟨⟨x, x.2, hx'⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver N K)
          (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective).mp y.2.2

end Tower
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve"

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple ModularPolynomialData jqModC jqNModC PlaceSpecialization transcendental_jqModC CharPReduction.constSeries minpoly_jqNModC_eq"
p2m_open "ModularCurve"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "coeffSubring fieldOver jRing jIntegralClosure modularEval pointEval modularLocalizedAtPoint modularEval_mem_modularLocalizedAtPoint"
p2m_open "ModularCurve.NodeLocalized"

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem normzLevel
    {A : ValuationSubring (AlgebraicClosure ℚ)} (M : ℕ) [NeZero M]
    (data : ModularPolynomialData M)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsNoetherianRing ↥(jIntegralClosure M A K) ∧
    IsIntegrallyClosed ↥(jIntegralClosure M A K) ∧
    (∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ fieldOver M K →
        ∃ c s : LaurentSeries (AlgebraicClosure ℚ), c ∈ jIntegralClosure M A K ∧ s ∈ jRing A K ∧ s ≠ 0 ∧ x * s = c) ∧
    (∃ s : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ jIntegralClosure M A K ∧
      ∀ x ∈ jIntegralClosure M A K, ∃ f : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
        (∀ c ∈ s, f c ∈ jRing A K) ∧ x = ∑ c ∈ s, f c * c) := by
  classical

  obtain ⟨hN, hIC, hD⟩ := blockB A K
  haveI : IsNoetherianRing ↥(jRing A K) := isNoetherianRing_of_ringEquiv _ (polynomialEquivJRing A K)
  haveI : IsIntegrallyClosed ↥(jRing A K) := IsIntegrallyClosed.of_equiv (polynomialEquivJRing A K)

  letI : Algebra (FractionRing ↥(jRing A K)) ↥(fieldOver M K) :=
    FractionRing.liftAlgebra ↥(jRing A K) ↥(fieldOver M K)
  have hint : IsIntegral (FractionRing ↥(jRing A K)) (jN K M) :=
    (isIntegral_jRing_jN A K M data).tower_top
  haveI hfd : FiniteDimensional (FractionRing ↥(jRing A K)) ↥(fieldOver M K) := by
    have h1 : FiniteDimensional (FractionRing ↥(jRing A K))
        ↥(IntermediateField.adjoin (FractionRing ↥(jRing A K)) ({jN K M} : Set ↥(fieldOver M K))) :=
      IntermediateField.adjoin.finiteDimensional hint
    rw [adjoin_jN_eq_top A K M (FractionRing ↥(jRing A K))] at h1
    exact LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := FractionRing ↥(jRing A K)) (E := ↥(fieldOver M K))).toLinearEquiv
  haveI : CharZero (FractionRing ↥(jRing A K)) :=
    (algebraMap (FractionRing ↥(jRing A K)) ↥(fieldOver M K)).charZero

  have h1 : IsNoetherianRing ↥(jIntegralClosure M A K) :=
    IsIntegralClosure.isNoetherianRing ↥(jRing A K) (FractionRing ↥(jRing A K)) ↥(fieldOver M K) _

  haveI : IsFractionRing ↥(jIntegralClosure M A K) ↥(fieldOver M K) :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(jRing A K) (FractionRing ↥(jRing A K))
      ↥(fieldOver M K) _
  haveI : Algebra.IsIntegral ↥(jRing A K) ↥(jIntegralClosure M A K) :=
    IsIntegralClosure.isIntegral_algebra ↥(jRing A K) ↥(fieldOver M K)
  have h2 : IsIntegrallyClosed ↥(jIntegralClosure M A K) := by
    refine (isIntegrallyClosed_iff ↥(fieldOver M K)).mpr fun {x} hx => ?_
    have hx' : IsIntegral ↥(jRing A K) x := isIntegral_trans x hx
    exact IsIntegralClosure.isIntegral_iff.mp hx'

  have h3 : ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ fieldOver M K →
      ∃ c s : LaurentSeries (AlgebraicClosure ℚ), c ∈ jIntegralClosure M A K ∧ s ∈ jRing A K ∧ s ≠ 0 ∧ x * s = c := by
    intro x hx
    let z : ↥(fieldOver M K) := ⟨x, hx⟩
    have hz : IsAlgebraic ↥(jRing A K) z :=
      (IsFractionRing.isAlgebraic_iff ↥(jRing A K) (FractionRing ↥(jRing A K)) ↥(fieldOver M K)).mpr
        (Algebra.IsAlgebraic.isAlgebraic z)
    obtain ⟨y, hy0, hyz⟩ := hz.exists_integral_multiple
    refine ⟨((y • z : ↥(fieldOver M K)) : LaurentSeries (AlgebraicClosure ℚ)), (y : LaurentSeries (AlgebraicClosure ℚ)), ⟨(y • z).2, ?_⟩, y.2, ?_, ?_⟩
    · first
        | exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver M K)
            (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective (x := y • z)).mpr hyz
        | simpa using (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(jRing A K) ↥(fieldOver M K)
            (LaurentSeries (AlgebraicClosure ℚ))) Subtype.val_injective (x := y • z)).mpr hyz
    · intro h; exact hy0 (Subtype.ext h)
    · rw [Algebra.smul_def]
      show x * (y : LaurentSeries (AlgebraicClosure ℚ)) = (y : LaurentSeries (AlgebraicClosure ℚ)) * x
      exact mul_comm _ _

  have h4 : ∃ s : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ jIntegralClosure M A K ∧
      ∀ x ∈ jIntegralClosure M A K, ∃ f : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
        (∀ c ∈ s, f c ∈ jRing A K) ∧ x = ∑ c ∈ s, f c * c := by

    haveI hfin : Module.Finite ↥(jRing A K) ↥(jIntegralClosure M A K) :=
      IsIntegralClosure.finite ↥(jRing A K) (FractionRing ↥(jRing A K)) ↥(fieldOver M K)
        ↥(jIntegralClosure M A K)
    obtain ⟨t, ht⟩ := hfin.fg_top
    let val : ↥(jIntegralClosure M A K) →ₗ[↥(jRing A K)] LaurentSeries (AlgebraicClosure ℚ) :=
      { toFun := fun c => (c : LaurentSeries (AlgebraicClosure ℚ))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let s : Finset (LaurentSeries (AlgebraicClosure ℚ)) :=
      Finset.image (fun c : ↥(jIntegralClosure M A K) => ((c : ↥(jIntegralClosure M A K)) : LaurentSeries (AlgebraicClosure ℚ))) t
    have hsub : (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ jIntegralClosure M A K := by
      intro x hx
      obtain ⟨c, -, hcx⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      rw [← hcx]
      exact Subtype.property c
    have hspan : ∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ jIntegralClosure M A K →
        x ∈ Submodule.span ↥(jRing A K) (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥(jIntegralClosure M A K)) ∈ Submodule.span ↥(jRing A K) (↑t : Set _) := by
        rw [ht]; exact Submodule.mem_top
      have himg := Submodule.mem_map_of_mem (f := val) hmem
      rw [Submodule.map_span] at himg
      have hx' : val ⟨x, hx⟩ = x := rfl
      rw [hx'] at himg
      have hs : (val '' (↑t : Set ↥(jIntegralClosure M A K))) ⊆ (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) := by
        rintro _ ⟨c, hc, rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨c, Finset.mem_coe.mp hc, rfl⟩)
      exact Submodule.span_mono hs himg
    refine ⟨s, hsub, fun x hx => ?_⟩
    obtain ⟨f₀, hf₀⟩ := Submodule.mem_span_finset.mp (hspan x hx)
    have hsum : ∑ i ∈ s, f₀ i • i = x := by
      first
        | exact hf₀.2
        | exact hf₀
    refine ⟨fun c => ((f₀ c : ↥(jRing A K)) : LaurentSeries (AlgebraicClosure ℚ)), fun c _ => (f₀ c).2, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun c _ => ?_
    first
      | exact Algebra.smul_def (f₀ c) c
      | (rw [Subring.smul_def, smul_eq_mul])
      | (simp [Algebra.smul_def]; rfl)

  exact ⟨h1, h2, h3, h4⟩

end NodeLocalized
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve"

open AlgebraicCurve IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level.ModularCurve.NodeLocalized ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in

theorem solution
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (dataNq : ModularPolynomialData (N * q))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    IsNoetherianRing ↥(jIntegralClosure (N * q) A K) ∧
    IsIntegrallyClosed ↥(jIntegralClosure (N * q) A K) ∧
    (∀ x : LaurentSeries (AlgebraicClosure ℚ), x ∈ fieldOver (N * q) K →
        ∃ c s : LaurentSeries (AlgebraicClosure ℚ), c ∈ jIntegralClosure (N * q) A K ∧ s ∈ jRing A K ∧ s ≠ 0 ∧
          x * s = c) ∧
    (∃ s : Finset (LaurentSeries (AlgebraicClosure ℚ)),
      (↑s : Set (LaurentSeries (AlgebraicClosure ℚ))) ⊆ jIntegralClosure (N * q) A K ∧
      ∀ x ∈ jIntegralClosure (N * q) A K, ∃ f : LaurentSeries (AlgebraicClosure ℚ) → LaurentSeries (AlgebraicClosure ℚ),
        (∀ c ∈ s, f c ∈ jRing A K) ∧ x = ∑ c ∈ s, f c * c):=
  ModularCurve.NodeLocalized.normzLevel (A := A) (N * q) dataNq K

end S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level
end P2MW
export P2MW.S_ModularCurve_jIntegralClosure_isNoetherianRing_and_isIntegrallyClosed_level (solution)
