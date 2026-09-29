-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.normReduction_of_not_dvd_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/76d469cd-9036-5bee-89ea-a043a619c88f

import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_mem
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top
import Theorems.Thm_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_CharPReduction_mem_or_inv_mem_modularLocalized
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_jqN
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.CharP.Two
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_CharPReduction_exists_modularRedLocHom_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option synthInstance.maxHeartbeats 1600000

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve"

set_option autoImplicit false

p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve.PlaceSpecialization"

set_option synthInstance.maxHeartbeats 1600000

section RosatiSliceL1
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve ModularCurve.CharPReduction"

namespace RosatiL1

variable (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] (red : A →+* k)
  (N : ℕ) [NeZero N]

private noncomputable abbrev V : Subring (LaurentSeries (AlgebraicClosure ℚ)) := modularLocalized N A.toSubring red

private theorem jqModC_mem_bar : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar N := by
  rw [← coeffEmb_jq]
  exact coeffEmb_mem_laurentBaseChange _ (jq_mem_full N)

private theorem jqNModC_mem_bar : jqNModC (AlgebraicClosure ℚ) N ∈ modularFunctionFieldBar N := by
  rw [← coeffEmb_jqN]
  exact coeffEmb_mem_laurentBaseChange _ (jqd_mem_full N (dvd_refl N))

omit [NeZero N] in
private theorem constSeries_mem_bar (a : A.toSubring) :
    constSeries A.toSubring a ∈ modularFunctionFieldBar N :=
  IntermediateField.algebraMap_mem _ _

private theorem modularRing_le_bar : modularRing N A.toSubring ≤ (modularFunctionFieldBar N).toSubalgebra.toSubring := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | hx)
  · exact constSeries_mem_bar A N a
  · rcases hx with rfl | rfl
    · exact jqModC_mem_bar N
    · exact jqNModC_mem_bar N

private theorem mem_bar_of_mem_V {f : LaurentSeries (AlgebraicClosure ℚ)} (hf : f ∈ V A red N) :
    f ∈ modularFunctionFieldBar N := by
  obtain ⟨r, s, hs, hfs⟩ := (mem_localizedAtKer _ _ _ _).mp hf
  have hr : (r : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N := modularRing_le_bar A N r.2
  have hsF : (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N := modularRing_le_bar A N s.2
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := Subtype.ext h0
    rw [this]
    exact (redKer _ _ _ _).zero_mem
  have hf' : f = (r : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ))⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hs0).mpr hfs
  rw [hf']
  exact (modularFunctionFieldBar N).mul_mem hr ((modularFunctionFieldBar N).inv_mem hsF)

private def incl : V A red N →+* modularFunctionFieldBar N where
  toFun v := ⟨(v : LaurentSeries (AlgebraicClosure ℚ)), mem_bar_of_mem_V A red N v.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[scoped simp] private theorem coe_incl_apply (v : V A red N) :
    ((incl A red N v : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) = v := rfl

private theorem incl_injective : Function.Injective (incl A red N) := by
  intro a b h
  apply Subtype.ext
  have := congrArg (fun x : modularFunctionFieldBar N => (x : LaurentSeries (AlgebraicClosure ℚ))) h
  simpa using this

@[reducible] private noncomputable def algebraBar : Algebra (V A red N) (modularFunctionFieldBar N) := (incl A red N).toAlgebra

section Dichotomy

variable {q : ℕ} [Fact q.Prime] [CharP k q]

private theorem hdeg_of_hqN (hqN : ¬ q ∣ N) :
    (IntermediateField.adjoin k {(jqModC k : LaurentSeries k)}).relfinrank (modularFunctionFieldC k N) = dedekindPsi N :=
  relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N q hqN

private theorem coe_mem_adjoin_generators (x : modularFunctionFieldBar N) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
      IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N} := by
  have htop := adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have hx : x ∈ (⊤ : IntermediateField (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := IntermediateField.mem_top
  rw [← htop] at hx

  have hcomap : x ∈ (IntermediateField.adjoin (AlgebraicClosure ℚ)
      {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N}).comap (modularFunctionFieldBar N).val := by
    refine (IntermediateField.adjoin_le_iff.mpr ?_) hx
    rintro y (rfl | rfl)
    · change coeffEmb (AlgebraicClosure ℚ) jq ∈
        IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N}
      rw [coeffEmb_jq]
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
    · change coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) ∈
        IntermediateField.adjoin (AlgebraicClosure ℚ) {jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) N}
      rw [show qExpand ℚ N jq = jqN N from rfl, coeffEmb_jqN]
      exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  exact hcomap

private theorem mem_V_or_inv_mem_V (hqN : ¬ q ∣ N) (x : modularFunctionFieldBar N) :
    (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ V A red N ∨ (x : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ V A red N := by

  obtain ⟨data⟩ := nonempty_modularPolynomialData N
  exact mem_or_inv_mem_modularLocalized A red N data (hdeg_of_hqN N hqN) (coe_mem_adjoin_generators N x)

private theorem isFractionRing_V (hqN : ¬ q ∣ N) :
    letI := algebraBar A red N
    IsFractionRing (V A red N) (modularFunctionFieldBar N) := by
  letI := algebraBar A red N
  haveI : FaithfulSMul (V A red N) (modularFunctionFieldBar N) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (incl_injective A red N)
  refine IsFractionRing.of_field (V A red N) (modularFunctionFieldBar N) fun z => ?_
  rcases mem_V_or_inv_mem_V A red N hqN z with hz | hz
  · refine ⟨⟨_, hz⟩, 1, ?_⟩
    rw [map_one, div_one]
    exact Subtype.ext rfl
  · refine ⟨1, ⟨_, hz⟩, ?_⟩
    rw [map_one]
    apply Subtype.ext
    simp only [one_div]
    show (z : LaurentSeries (AlgebraicClosure ℚ)) = ((z : LaurentSeries (AlgebraicClosure ℚ))⁻¹)⁻¹
    rw [inv_inv]

private theorem valuationRing_V (hqN : ¬ q ∣ N) : ValuationRing (V A red N) := by
  letI := algebraBar A red N
  haveI := isFractionRing_V A red N hqN
  refine (ValuationRing.iff_isInteger_or_isInteger (V A red N) (modularFunctionFieldBar N)).mpr fun x => ?_
  rcases mem_V_or_inv_mem_V A red N hqN x with hx | hx
  · exact Or.inl ⟨⟨_, hx⟩, Subtype.ext rfl⟩
  · refine Or.inr ⟨⟨_, hx⟩, ?_⟩
    apply Subtype.ext
    show ((x : LaurentSeries (AlgebraicClosure ℚ))⁻¹) = ((x⁻¹ : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
    rw [IntermediateField.coe_inv]

section LocRing

private noncomputable abbrev locRing : Subring (modularFunctionFieldBar N) :=
  (modularLocalized N A.toSubring red).comap
    (algebraMap (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)))

private theorem mem_locRing_iff (x : modularFunctionFieldBar N) :
    x ∈ locRing A red N ↔ (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ V A red N :=
  Iff.rfl

private theorem mem_locRing_or_inv_mem_locRing (hqN : ¬ q ∣ N) (x : modularFunctionFieldBar N) :
    x ∈ locRing A red N ∨ x⁻¹ ∈ locRing A red N := by
  rcases mem_V_or_inv_mem_V A red N hqN x with hx | hx
  · exact Or.inl ((mem_locRing_iff A red N x).mpr hx)
  · refine Or.inr ((mem_locRing_iff A red N x⁻¹).mpr ?_)
    rw [IntermediateField.coe_inv]
    exact hx

private theorem faithfulSMul_locRing : FaithfulSMul (locRing A red N) (modularFunctionFieldBar N) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr fun _ _ h => Subtype.ext h

private theorem isFractionRing_locRing (hqN : ¬ q ∣ N) :
    IsFractionRing (locRing A red N) (modularFunctionFieldBar N) := by
  haveI := faithfulSMul_locRing A red N
  refine IsFractionRing.of_field (locRing A red N) (modularFunctionFieldBar N) fun z => ?_
  rcases mem_locRing_or_inv_mem_locRing A red N hqN z with hz | hz
  · refine ⟨⟨z, hz⟩, 1, ?_⟩
    rw [map_one, div_one]
    rfl
  · refine ⟨1, ⟨z⁻¹, hz⟩, ?_⟩
    rw [map_one]
    show z = 1 / z⁻¹
    rw [one_div, inv_inv]

private theorem valuationRing_locRing (hqN : ¬ q ∣ N) : ValuationRing (locRing A red N) := by
  haveI := isFractionRing_locRing A red N hqN
  refine (ValuationRing.iff_isInteger_or_isInteger (locRing A red N) (modularFunctionFieldBar N)).mpr fun x => ?_
  rcases mem_locRing_or_inv_mem_locRing A red N hqN x with hx | hx
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr ⟨⟨x⁻¹, hx⟩, rfl⟩

end LocRing

end Dichotomy

#print axioms valuationRing_locRing
#print axioms isFractionRing_locRing

end RosatiL1
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"
end RosatiSliceL1
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

section RosatiSliceFrob
namespace RosatiNormRed

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve IntermediateField Polynomial"

variable (k : Type*) [Field k] {q : ℕ} [Fact (Nat.Prime q)] [CharP k q]
  (N : ℕ) [NeZero N] (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)

private theorem finrankAlong_frobeniusGeomLevel (hqN : ¬ q ∣ N) :
    finrankAlong k (frobeniusGeomLevel k N data hKr) = q := by
  have hq : q.Prime := Fact.out
  set F : IntermediateField k (LaurentSeries k) := modularFunctionFieldC k N with hF
  set φ := frobeniusGeomLevel k N data hKr with hφ
  set E : IntermediateField k (LaurentSeries k) := (F.val.comp φ).fieldRange with hEdef

  have hE : E ≤ F := by
    rintro x ⟨y, rfl⟩
    exact (φ y).2

  have hjq : jqModC k ^ q ∈ E := by
    refine ⟨⟨jqModC k, jqModC_mem k N⟩, ?_⟩
    change ((φ ⟨jqModC k, jqModC_mem k N⟩ : F) : LaurentSeries k) = jqModC k ^ q
    rw [hφ, frobeniusGeomLevel_jq]
    rfl
  have hjqN : jqNModC k N ^ q ∈ E := by
    refine ⟨⟨jqNModC k N, jqNModC_mem k N⟩, ?_⟩
    change ((φ ⟨jqNModC k N, jqNModC_mem k N⟩ : F) : LaurentSeries k) = jqNModC k N ^ q
    rw [hφ, frobeniusGeomLevel_jqN]
    rfl

  have hnot : jqModC k ∉ E := by
    rintro ⟨y, hy⟩
    change ((φ y : F) : LaurentSeries k) = jqModC k at hy
    rw [hφ, frobeniusGeomLevel_apply_coe] at hy
    have hnd : ¬ ((q : ℕ) : ℤ) ∣ (-1 : ℤ) := by
      intro h
      have h1 : ((q : ℕ) : ℤ) ∣ (1 : ℤ) := Int.dvd_neg.mp h
      have h2 : q ∣ 1 := by exact_mod_cast h1
      exact hq.one_lt.ne' (Nat.dvd_one.mp h2)
    have hc := congrArg (fun s : LaurentSeries k => s.coeff (-1 : ℤ)) hy
    rw [qExpand_coeff_of_not_dvd q _ hnd, coeff_jqModC_neg_one k] at hc
    exact zero_ne_one hc

  set S : IntermediateField k (LaurentSeries k) := (adjoin E {jqModC k}).restrictScalars k with hS
  have hjqS : jqModC k ∈ S :=
    (mem_restrictScalars k).mpr (subset_adjoin E {jqModC k} (Set.mem_singleton _))
  have hE_S : ∀ x ∈ E, x ∈ S := fun x hx =>
    (mem_restrictScalars k).mpr (by simpa using (adjoin E {jqModC k}).algebraMap_mem (⟨x, hx⟩ : E))
  have hjqNS : jqNModC k N ∈ S := by
    set L₀ : IntermediateField k (LaurentSeries k) := adjoin k {jqModC k} with hL₀
    have hsep : IsSeparable L₀ (jqNModC k N) := isSeparable_jqNModC_of_good k N q hqN
    haveI : CharP L₀ q := charP_of_injective_algebraMap (algebraMap k L₀).injective q
    haveI : ExpChar L₀ q := ExpChar.prime hq
    have hadj := adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable L₀ (LaurentSeries k) hsep q
    have hL₀S : L₀ ≤ S := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjqS)
    have hmem : jqNModC k N ∈ adjoin L₀ {jqNModC k N ^ q} := by
      rw [← hadj]
      exact mem_adjoin_simple_self L₀ (jqNModC k N)
    have hle : adjoin L₀ {jqNModC k N ^ q} ≤ extendScalars hL₀S :=
      adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (hE_S _ hjqN))
    exact hle hmem
  have hF_S : F ≤ S := by
    rw [hF]
    change adjoin k {jqModC k, jqNModC k N} ≤ S
    exact adjoin_le_iff.mpr (Set.insert_subset_iff.mpr ⟨hjqS, Set.singleton_subset_iff.mpr hjqNS⟩)
  have hT : E.extendScalars hE = adjoin E {jqModC k} := by
    apply le_antisymm
    · intro x hx
      exact (mem_restrictScalars k).mp (hF_S hx)
    · exact adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem k N))

  haveI : CharP E q := charP_of_injective_algebraMap (algebraMap k E).injective q
  haveI : ExpChar E q := ExpChar.prime hq
  have hint : IsIntegral E (jqModC k) :=
    ⟨X ^ q - C (⟨jqModC k ^ q, hjq⟩ : E), monic_X_pow_sub_C _ hq.ne_zero, by simp⟩
  have hsepdeg : (minpoly E (jqModC k)).natSepDegree = 1 :=
    (minpoly.natSepDegree_eq_one_iff_pow_mem q).mpr ⟨1, by rw [pow_one]; exact ⟨⟨_, hjq⟩, rfl⟩⟩
  obtain ⟨n, y, hmin⟩ := (minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mp hsepdeg
  have hdvd : minpoly E (jqModC k) ∣ X ^ q - C (⟨jqModC k ^ q, hjq⟩ : E) :=
    minpoly.dvd E (jqModC k) (by simp)
  have hdeg_le : (minpoly E (jqModC k)).natDegree ≤ q := by
    have h := natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero hq.pos _)
    rwa [natDegree_X_pow_sub_C] at h
  have hdeg : (minpoly E (jqModC k)).natDegree = q ^ n := by
    rw [hmin, natDegree_X_pow_sub_C]
  have hn : n = 1 := by
    have hn1 : n ≤ 1 := by
      have h1 : q ^ n ≤ q ^ 1 := by rw [pow_one, ← hdeg]; exact hdeg_le
      exact (Nat.pow_le_pow_iff_right hq.one_lt).mp h1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with h0 | h1
    · exfalso
      apply hnot
      have hroot := minpoly.aeval E (jqModC k)
      rw [hmin, h0, pow_zero, pow_one, map_sub, aeval_X, aeval_C, sub_eq_zero] at hroot
      rw [hroot]
      exact y.2
    · exact h1

  refine (finrankAlong_eq_relfinrank_fieldRange _ _ φ).trans ?_
  change relfinrank E F = q
  rw [relfinrank_eq_finrank_of_le hE, hT, adjoin.finrank hint, hdeg, hn, pow_one]

private theorem finrank_algebraAlong_frobeniusGeomLevel (hqN : ¬ q ∣ N) :
    @Module.finrank (modularFunctionFieldC k N) (modularFunctionFieldC k N) _ _
      (@Algebra.toModule _ _ _ _ (AlgebraicCurve.algebraAlong (frobeniusGeomLevel k N data hKr))) = q := by
  have h := finrankAlong_frobeniusGeomLevel k N data hKr hqN
  unfold finrankAlong at h
  exact h

#print axioms finrankAlong_frobeniusGeomLevel
#print axioms finrank_algebraAlong_frobeniusGeomLevel

end RosatiNormRed
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"
end RosatiSliceFrob
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

section RosatiSliceDeg
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve"

namespace DegreeLegReceipt

variable (L : Type*) [Field L] [Algebra ℚ L]

omit [Algebra ℚ L] in

private theorem finrankAlong_algEquiv {A B : Type*} [Field A] [Field B] [Algebra L A] [Algebra L B] (e : A ≃ₐ[L] B) :
    finrankAlong L (e : A →ₐ[L] B) = 1 := by
  have h := finrankAlong_comp (e : A →ₐ[L] B) (e.symm : B →ₐ[L] A)
  rw [AlgEquiv.symm_comp, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

variable [Algebra.IsAlgebraic ℚ L]

private theorem finrankAlong_heckeAlphaBar_of_not_dvd (K p : ℕ) [NeZero K] [hp : Fact p.Prime] (hpK : ¬ p ∣ K) :
    finrankAlong L (heckeAlphaBar L K p) = p + 1 := by
  obtain ⟨σ, hσ⟩ := exists_isAtkinLehnerAutFull_of_prime_of_not_dvd K p hp.out hpK
  have h := congrArg (finrankAlong L) (geomAut_atkinLehner_comp_legs L K p σ hσ).1
  rw [finrankAlong_comp, finrankAlong_algEquiv, mul_one, finrankAlong_heckeBetaBar, if_neg hpK] at h
  exact h

private theorem finrank_bar_algebraAlong_heckeAlphaBar (N q : ℕ) [NeZero N] [Fact (Nat.Prime q)]
    (hqN : ¬ q ∣ N) :
    (letI := AlgebraicCurve.algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q);
      Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q))) = q + 1 :=
  finrankAlong_heckeAlphaBar_of_not_dvd (AlgebraicClosure ℚ) N q hqN

#print axioms finrankAlong_heckeAlphaBar_of_not_dvd
#print axioms finrank_bar_algebraAlong_heckeAlphaBar

end DegreeLegReceipt
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"
end RosatiSliceDeg
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar qExpand qExpand_coeff_of_not_dvd jq jqN dedekindPsi ModularPolynomialData jqd_mem_full coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_apply_coe frobeniusGeomLevel_jq frobeniusGeomLevel_jqN frobOnPlacesGeomLevel isFrobeniusEndo_frobeniusGeomLevel ord_frobOnPlaces_of_pow_eq perfect_of_isAlgClosed KroneckerCongruence jq_mem_full coeff_jqModC_neg_one modularFunctionFieldFullC CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom CharPReduction.modularRedLocHom_mem relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi coeffEmb_jq coeffEmb_jqN adjoin_jBar_jNBar_eq_top nonempty_modularPolynomialData isSeparable_jqNModC_of_good finrankAlong_heckeBetaBar exists_isAtkinLehnerAutFull_of_prime_of_not_dvd geomAut_atkinLehner_comp_legs CharPReduction.exists_modularRedLocHom_eq"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple.atkinLehnerBar ProlongationTuple ProlongationTuple.residue₂_apply ProlongationTuple.exists_orderSubalgebra_finite_span_eq_top"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable (A N) in
private scoped instance shortcutAlgebraFullC :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) :=
  inferInstance

variable (A N) in
private scoped instance shortcutFieldFullC : Field ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) N) :=
  inferInstance

variable (N) in
private scoped instance shortcutAlgebraBar : Algebra (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) :=
  inferInstance

private def NormReduction' : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    ∃ (hn : ((Algebra.norm (modularFunctionFieldBar N) f : modularFunctionFieldBar N) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red),
      CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hn⟩ ≠ 0 ∧
      ∀ u : Place k (modularFunctionFieldC k N),
        (frobOnPlacesGeomLevel k N data hKr u).ord
            (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hn⟩,
              CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, hn⟩⟩ : modularFunctionFieldC k N) =
          (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨f, h₁⟩) + u.ord (R.residue₂ ⟨f, h₂⟩)

private def NormResidueFactorization : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    ∃ (hn : ((Algebra.norm (modularFunctionFieldBar N) f : modularFunctionFieldBar N) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red)
      (g₂ : modularFunctionFieldC k N),
      frobeniusGeomLevel k N data hKr g₂ = (R.residue₂ ⟨f, h₂⟩) ^ q ∧
      (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hn⟩,
          CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, hn⟩⟩ : modularFunctionFieldC k N) =
        R.residue₁ ⟨f, h₁⟩ * g₂

private theorem residue₁_ne_zero {f : modularFunctionFieldBar (N * q)} (h₁ : f ∈ R.R₁.integers)
    (hr₁ : R.R₁.residue ⟨f, h₁⟩ ≠ 0) : R.residue₁ ⟨f, h₁⟩ ≠ 0 := by
  rw [R.residue₁_apply]
  exact (map_ne_zero R.ι).mpr hr₁

private theorem residue₂_ne_zero {f : modularFunctionFieldBar (N * q)} (h₂ : f ∈ R.R₂.integers)
    (hr₂ : R.R₂.residue ⟨f, h₂⟩ ≠ 0) : R.residue₂ ⟨f, h₂⟩ ≠ 0 := by
  rw [R.residue₂_apply]
  exact (map_ne_zero R.ι).mpr hr₂

private theorem normReduction'_of_factorization [IsAlgClosed k] (hfac : NormResidueFactorization R) :
    NormReduction' R := by
  intro f h₁ h₂ hr₁ hr₂
  obtain ⟨hn, g₂, hg, hfacf⟩ := hfac f h₁ h₂ hr₁ hr₂
  have hperf : ∀ c : k, ∃ d : k, d ^ q = c := perfect_of_isAlgClosed k
  have hres₁ := residue₁_ne_zero R h₁ hr₁
  have hres₂ := residue₂_ne_zero R h₂ hr₂
  have hg₂ : g₂ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hg
    exact pow_ne_zero q hres₂ hg.symm
  refine ⟨hn, ?_, fun u => ?_⟩
  · intro h0
    have h := congrArg (fun x : modularFunctionFieldC k N => (x : LaurentSeries k)) hfacf
    simp only at h
    rw [h0] at h
    exact (mul_ne_zero hres₁ hg₂) (Subtype.ext h.symm)
  · rw [hfacf, (frobOnPlacesGeomLevel k N data hKr u).ord_mul hres₁ hg₂,
      ord_frobOnPlaces_of_pow_eq k N data hKr hperf hg u]

section EngineDock

variable (A red) in

private def locRing (M : ℕ) [NeZero M] : Subring ↥(modularFunctionFieldBar M) :=
  (CharPReduction.modularLocalized M A.toSubring red).comap
    (algebraMap ↥(modularFunctionFieldBar M) (LaurentSeries (AlgebraicClosure ℚ)))

private theorem mem_locRing_iff {M : ℕ} [NeZero M] (x : ↥(modularFunctionFieldBar M)) :
    x ∈ locRing A red M ↔
      (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized M A.toSubring red := Iff.rfl

private scoped instance algebraVK : Algebra ↥(locRing A red N) ↥(modularFunctionFieldBar N) :=
  inferInstance

private scoped instance algebraLocRing :
    Algebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)) :=
  ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (locRing A red N).subtype).toAlgebra

private scoped instance algebraOrder (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q))) :
    Algebra ↥(locRing A red N) ↥S :=
  Subalgebra.algebra S

omit [CharP k q] in
private theorem algebraMap_locRing_apply (v : ↥(locRing A red N)) :
    algebraMap ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)) v =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) := rfl

private scoped instance algebraKF : Algebra ↥(modularFunctionFieldBar N) ↥(modularFunctionFieldBar (N * q)) :=
  algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)

private scoped instance towerVKF : IsScalarTower ↥(locRing A red N) ↥(modularFunctionFieldBar N) ↥(modularFunctionFieldBar (N * q)) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private def resV : ↥(locRing A red N) →+* ↥(modularFunctionFieldC k N) where
  toFun v := ⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨_, v.2⟩,
    CharPReduction.modularRedLocHom_mem A.toSubring red N ⟨_, v.2⟩⟩
  map_one' := Subtype.ext (by
    show CharPReduction.modularRedLocHom N A.toSubring red _ = 1
    rw [← map_one (CharPReduction.modularRedLocHom N A.toSubring red)]; rfl)
  map_mul' v w := Subtype.ext (by
    show CharPReduction.modularRedLocHom N A.toSubring red _ =
      CharPReduction.modularRedLocHom N A.toSubring red _ * CharPReduction.modularRedLocHom N A.toSubring red _
    rw [← map_mul]; rfl)
  map_zero' := Subtype.ext (by
    show CharPReduction.modularRedLocHom N A.toSubring red _ = 0
    rw [← map_zero (CharPReduction.modularRedLocHom N A.toSubring red)]; rfl)
  map_add' v w := Subtype.ext (by
    show CharPReduction.modularRedLocHom N A.toSubring red _ =
      CharPReduction.modularRedLocHom N A.toSubring red _ + CharPReduction.modularRedLocHom N A.toSubring red _
    rw [← map_add]; rfl)

omit [Fact q.Prime] [CharP k q] in
private theorem resV_apply_coe (v : ↥(locRing A red N)) :
    ((resV v : ↥(modularFunctionFieldC k N)) : LaurentSeries k) =
      CharPReduction.modularRedLocHom N A.toSubring red ⟨_, v.2⟩ := rfl

omit [Fact q.Prime] [CharP k q] in

private theorem isUnit_of_resV_ne_zero (v : ↥(locRing A red N)) (hv : resV v ≠ 0) : IsUnit v := by
  have hv' : CharPReduction.modularRedLocHom N A.toSubring red ⟨_, v.2⟩ ≠ 0 := fun h =>
    hv (Subtype.ext (by rw [resV_apply_coe, h]; rfl))
  obtain ⟨r, s, hs, hvs⟩ := (CharPReduction.mem_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
    (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mp v.2
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing N A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ⟨_, v.2⟩ hvs
  have hr : r ∉ CharPReduction.redKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) := by
    rw [CharPReduction.notMem_redKer_iff, ← hspec]
    exact mul_ne_zero hv' (CharPReduction.redRes_ne_zero_of_notMem hs)
  have hv0 : (v : ↥(modularFunctionFieldBar N)) ≠ 0 := by
    intro h0
    apply hv'
    have : (⟨_, v.2⟩ : ↥(CharPReduction.modularLocalized N A.toSubring red)) = 0 := Subtype.ext (by
      show algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)) (v : ↥(modularFunctionFieldBar N)) = 0
      rw [h0, map_zero])
    rw [this, map_zero]
  have hinv : ((v : ↥(modularFunctionFieldBar N))⁻¹ : ↥(modularFunctionFieldBar N)) ∈ locRing A red N := by
    unfold locRing
    rw [Subring.mem_comap, map_inv₀]
    refine (CharPReduction.mem_localizedAtKer A.toSubring red (CharPReduction.modularRing N A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring)).mpr ⟨s, r, hr, ?_⟩
    have hv0' : algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))
        (v : ↥(modularFunctionFieldBar N)) ≠ 0 := (map_ne_zero _).mpr hv0
    rw [← hvs, ← mul_assoc, inv_mul_cancel₀ hv0', one_mul]
  exact ⟨⟨v, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hv0), Subtype.ext (inv_mul_cancel₀ hv0)⟩, rfl⟩

private scoped instance isLocalHom_resV : IsLocalHom (resV (A := A) (N := N) (red := red) (k := k)) :=
  ⟨fun v hv => isUnit_of_resV_ne_zero v (isUnit_iff_ne_zero.mp hv)⟩

private scoped instance isDomain_V : IsDomain ↥(locRing A red N) := inferInstance

private scoped instance isLocalRing_V [ValuationRing ↥(locRing A red N)] : IsLocalRing ↥(locRing A red N) := ValuationRing.isLocalRing ↥(locRing A red N)

variable (A N red) in

private abbrev B [IsLocalRing ↥(locRing A red N)] := IsLocalRing.ResidueField ↥(locRing A red N)

private def Lmap [IsLocalRing ↥(locRing A red N)] : B A N red →+* ↥(modularFunctionFieldC k N) :=
  IsLocalRing.ResidueField.lift (resV (A := A) (N := N) (red := red))

private theorem Lmap_residue [IsLocalRing ↥(locRing A red N)] (v : ↥(locRing A red N)) :
    Lmap (IsLocalRing.residue _ v) = (resV v : ↥(modularFunctionFieldC k N)) :=
  IsLocalRing.ResidueField.lift_residue_apply _ v

private theorem Lmap_surjective [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k))) :
    Function.Surjective (Lmap (A := A) (N := N) (red := red) (k := k)) := fun a => by
  obtain ⟨v, hv⟩ := hsurjN a
  exact ⟨IsLocalRing.residue _ v, by rw [Lmap_residue, hv]⟩

private def Emap [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k))) :=
  RingEquiv.ofBijective (Lmap (A := A) (N := N) (red := red) (k := k))
    ⟨(Lmap (A := A) (N := N) (red := red) (k := k)).injective, Lmap_surjective hsurjN⟩

private theorem Emap_apply [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k))) (b : B A N red) :
    Emap hsurjN b = Lmap b := rfl

set_option linter.unusedVariables false in

private def KOne (k : Type*) [Field k] (N : ℕ) [NeZero N] : Type _ := ↥(modularFunctionFieldC k N)

set_option linter.unusedVariables false in

private def KTwo (k : Type*) [Field k] (N : ℕ) [NeZero N] {q : ℕ} [Fact q.Prime] (data : ModularPolynomialData q)
    (hKr : KroneckerCongruence q data) : Type _ := ↥(modularFunctionFieldC k N)

private scoped instance instFieldKOne : Field (KOne k N) := inferInstanceAs (Field ↥(modularFunctionFieldC k N))

private scoped instance instFieldKTwo : Field (KTwo k N data hKr) := inferInstanceAs (Field ↥(modularFunctionFieldC k N))

private scoped instance algebraFCKOne : Algebra ↥(modularFunctionFieldC k N) (KOne k N) :=
  show Algebra ↥(modularFunctionFieldC k N) ↥(modularFunctionFieldC k N) from Algebra.id _

private scoped instance algebraFCKTwo : Algebra ↥(modularFunctionFieldC k N) (KTwo k N data hKr) :=
  show Algebra ↥(modularFunctionFieldC k N) ↥(modularFunctionFieldC k N) from
    algebraAlong (frobeniusGeomLevel k N data hKr)

private theorem finrank_KTwo_eq :
    Module.finrank ↥(modularFunctionFieldC k N) (KTwo k N data hKr) = finrankAlong k (frobeniusGeomLevel k N data hKr) :=
  rfl

private scoped instance algebraBKOne [IsLocalRing ↥(locRing A red N)] : Algebra (B A N red) (KOne k N) :=
  (show B A N red →+* KOne k N from Lmap (A := A) (N := N) (red := red) (k := k)).toAlgebra

private theorem algebraMap_BKOne [IsLocalRing ↥(locRing A red N)] (b : B A N red) :
    algebraMap (B A N red) (KOne k N) b = (Lmap b : ↥(modularFunctionFieldC k N)) := rfl

private scoped instance algebraBKTwo [IsLocalRing ↥(locRing A red N)] : Algebra (B A N red) (KTwo k N data hKr) :=
  ((algebraMap ↥(modularFunctionFieldC k N) (KTwo k N data hKr)).comp
    (Lmap (A := A) (N := N) (red := red) (k := k))).toAlgebra

private theorem algebraMap_BKTwo [IsLocalRing ↥(locRing A red N)] (b : B A N red) :
    algebraMap (B A N red) (KTwo k N data hKr) b = frobeniusGeomLevel k N data hKr (Lmap b) := rfl

private scoped instance algebraVKOne [IsLocalRing ↥(locRing A red N)] : Algebra ↥(locRing A red N) (KOne k N) :=
  ((algebraMap (B A N red) (KOne k N)).comp (IsLocalRing.residue ↥(locRing A red N))).toAlgebra

private scoped instance algebraVKTwo [IsLocalRing ↥(locRing A red N)] : Algebra ↥(locRing A red N) (KTwo k N data hKr) :=
  ((algebraMap (B A N red) (KTwo k N data hKr)).comp (IsLocalRing.residue ↥(locRing A red N))).toAlgebra

private scoped instance towerVBKOne [IsLocalRing ↥(locRing A red N)] :
    IsScalarTower ↥(locRing A red N) (B A N red) (KOne k N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance towerVBKTwo [IsLocalRing ↥(locRing A red N)] :
    IsScalarTower ↥(locRing A red N) (B A N red) (KTwo k N data hKr) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private scoped instance charP_FC : CharP ↥(modularFunctionFieldC k N) q :=
  (Algebra.charP_iff k ↥(modularFunctionFieldC k N) q).mp inferInstance

private scoped instance charP_B [IsLocalRing ↥(locRing A red N)] : CharP (B A N red) q :=
  letI : Algebra (B A N red) ↥(modularFunctionFieldC k N) := (Lmap (A := A) (N := N) (red := red) (k := k)).toAlgebra
  (Algebra.charP_iff (B A N red) ↥(modularFunctionFieldC k N) q).mpr inferInstance

private theorem finrank_BKOne [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k))) :
    Module.finrank (B A N red) (KOne k N) = 1 :=
  (Algebra.finrank_eq_of_equiv_equiv (Emap hsurjN) (RingEquiv.refl (KOne k N)) (RingHom.ext fun _ => rfl)).trans
    (Module.finrank_self ↥(modularFunctionFieldC k N))

private theorem finrank_BKTwo [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k)))
    (hfinFrob : finrankAlong k (frobeniusGeomLevel k N data hKr) = q) :
    Module.finrank (B A N red) (KTwo k N data hKr) = q :=
  (Algebra.finrank_eq_of_equiv_equiv (Emap hsurjN) (RingEquiv.refl (KTwo k N data hKr))
    (RingHom.ext fun _ => rfl)).trans (finrank_KTwo_eq.trans hfinFrob)

private theorem finite_BKOne [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k))) :
    FiniteDimensional (B A N red) (KOne k N) :=
  Module.finite_of_finrank_pos (by rw [finrank_BKOne hsurjN]; exact Nat.one_pos)

private theorem finite_BKTwo [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k)))
    (hfinFrob : finrankAlong k (frobeniusGeomLevel k N data hKr) = q) :
    FiniteDimensional (B A N red) (KTwo k N data hKr) :=
  Module.finite_of_finrank_pos (by rw [finrank_BKTwo hsurjN hfinFrob]; exact (Fact.out : q.Prime).pos)

private theorem exists_algebraMap_BKTwo_eq_pow [IsLocalRing ↥(locRing A red N)]
    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k)))
    (hperf : ∀ c : k, ∃ d : k, d ^ q = c) (y : KTwo k N data hKr) :
    ∃ c : B A N red, algebraMap (B A N red) (KTwo k N data hKr) c = y ^ q := by
  have hFrob := isFrobeniusEndo_frobeniusGeomLevel k N data hKr hperf
  obtain ⟨c, hc⟩ := Lmap_surjective hsurjN (hFrob.frobNorm y)
  refine ⟨c, ?_⟩
  rw [algebraMap_BKTwo, hc]
  exact hFrob.map_frobNorm y

open Polynomial IntermediateField in
private theorem algebraMap_norm_eq_pow_of_finrank_eq_prime {κ κ₂ : Type*} [Field κ] [Field κ₂] [Algebra κ κ₂]
    (p : ℕ) [Fact p.Prime] [CharP κ p] (hfin : Module.finrank κ κ₂ = p)
    (hpow : ∀ y : κ₂, ∃ c : κ, algebraMap κ κ₂ c = y ^ p) (x : κ₂) :
    algebraMap κ κ₂ (Algebra.norm κ x) = x ^ p := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨c, hc⟩ := hpow x
  by_cases hx : ∃ b : κ, algebraMap κ κ₂ b = x
  · obtain ⟨b, rfl⟩ := hx
    rw [Algebra.norm_algebraMap, hfin, map_pow]
  haveI : FiniteDimensional κ κ₂ := Module.finite_of_finrank_pos (by rw [hfin]; exact hp.pos)
  have hint : IsIntegral κ x := IsIntegral.of_finite κ x
  have hdvd : minpoly κ x ∣ X ^ p - C c := minpoly.dvd κ x (by simp [hc])
  have hdeg : (minpoly κ x).natDegree = p := by
    have h1 : Module.finrank κ κ⟮x⟯ ∣ p := by
      rw [← hfin]
      exact Dvd.intro _ (Module.finrank_mul_finrank κ κ⟮x⟯ κ₂)
    rcases (Nat.dvd_prime hp).mp h1 with h1 | h1
    · exfalso
      apply hx
      have hmem : x ∈ κ⟮x⟯ := mem_adjoin_simple_self κ x
      rw [finrank_eq_one_iff.mp h1, mem_bot] at hmem
      obtain ⟨b, hb⟩ := hmem
      exact ⟨b, hb⟩
    · rw [← adjoin.finrank hint]
      exact h1
  have hmin : X ^ p - C c = minpoly κ x :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_X_pow_sub_C c hp0) hdvd
      (by rw [natDegree_X_pow_sub_C, hdeg])
  have htop : κ⟮x⟯ = ⊤ := by
    refine eq_of_le_of_finrank_eq le_top ?_
    rw [finrank_top', hfin, adjoin.finrank hint, hdeg]
  let pb : PowerBasis κ κ₂ := (adjoin.powerBasis hint).map ((equivOfEq htop).trans topEquiv)
  have hgen : pb.gen = x := rfl
  have hdim : pb.dim = p := hdeg
  have hcoeff : (X ^ p - C c).coeff 0 = -c := by simp [Ne.symm hp0]
  have hnorm : Algebra.norm κ x = c := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rw [hgen, hdim, ← hmin, hcoeff] at h
    rw [h]
    rcases hp.eq_two_or_odd' with h2 | hodd
    · subst h2
      rw [neg_one_sq, one_mul, CharTwo.neg_eq]
    · rw [hodd.neg_one_pow, neg_one_mul, neg_neg]
  rw [hnorm, hc]

omit [Fact q.Prime] [CharP k q] in
private theorem algebraMap_VKOne_apply [IsLocalRing ↥(locRing A red N)] (v : ↥(locRing A red N)) :
    algebraMap ↥(locRing A red N) (KOne k N) v =
      (Lmap (IsLocalRing.residue ↥(locRing A red N) v) : ↥(modularFunctionFieldC k N)) := rfl

private theorem algebraMap_VKTwo_apply [IsLocalRing ↥(locRing A red N)] (v : ↥(locRing A red N)) :
    algebraMap ↥(locRing A red N) (KTwo k N data hKr) v =
      frobeniusGeomLevel k N data hKr (Lmap (IsLocalRing.residue ↥(locRing A red N) v)) := rfl

omit [CharP k q] in

private theorem coe_algebraMap_order (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)))
    (v : ↥(locRing A red N)) :
    ((algebraMap ↥(locRing A red N) ↥S v : ↥S) : ↥(modularFunctionFieldBar (N * q))) =
      heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) :=
  (Subalgebra.coe_algebraMap S v).trans (algebraMap_locRing_apply v)

omit [CharP k q] in
private theorem algebraMap_mem_order (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)))
    (v : ↥(locRing A red N)) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ S := by
  rw [← coe_algebraMap_order S v]
  exact (algebraMap ↥(locRing A red N) ↥S v).2

section Rho1
variable [IsLocalRing ↥(locRing A red N)] (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q))) (hS₁ : ∀ s ∈ S, s ∈ R.R₁.integers)

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₁_one : (R.residue₁ ⟨((1 : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₁ _ (1 : ↥S).2⟩ : ↥(modularFunctionFieldC k N)) = 1 :=
  map_one R.residue₁

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₁_mul (s t : ↥S) :
    (R.residue₁ ⟨((s * t : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₁ _ (s * t).2⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₁ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₁ _ s.2⟩ * R.residue₁ ⟨(t : ↥(modularFunctionFieldBar (N * q))), hS₁ _ t.2⟩ := by
  rw [← map_mul]; rfl

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₁_zero : (R.residue₁ ⟨((0 : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₁ _ (0 : ↥S).2⟩ : ↥(modularFunctionFieldC k N)) = 0 :=
  map_zero R.residue₁

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₁_add (s t : ↥S) :
    (R.residue₁ ⟨((s + t : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₁ _ (s + t).2⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₁ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₁ _ s.2⟩ + R.residue₁ ⟨(t : ↥(modularFunctionFieldBar (N * q))), hS₁ _ t.2⟩ := by
  rw [← map_add]; rfl
omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₁_commutes
    (hρ₁ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₁.integers),
      R.residue₁ ⟨_, h⟩ = resV v) (v : ↥(locRing A red N)) :
    (R.residue₁ ⟨((algebraMap ↥(locRing A red N) ↥S v : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₁ _ (algebraMap ↥(locRing A red N) ↥S v).2⟩ : ↥(modularFunctionFieldC k N)) = resV v := by
  have earg : (⟨((algebraMap ↥(locRing A red N) ↥S v : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₁ _ (algebraMap ↥(locRing A red N) ↥S v).2⟩ : ↥R.R₁.integers) =
      ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)), hS₁ _ (algebraMap_mem_order S v)⟩ :=
    Subtype.ext (coe_algebraMap_order S v)
  rw [earg]
  exact hρ₁ v _

private def rho₁
    (hρ₁ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₁.integers),
      R.residue₁ ⟨_, h⟩ = resV v) :
    ↥S →ₐ[↥(locRing A red N)] KOne k N where
  toFun s := (R.residue₁ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₁ _ s.2⟩ : ↥(modularFunctionFieldC k N))
  map_one' := rho₁_one R S hS₁
  map_mul' s t := rho₁_mul R S hS₁ s t
  map_zero' := rho₁_zero R S hS₁
  map_add' s t := rho₁_add R S hS₁ s t
  commutes' v := by
    rw [algebraMap_VKOne_apply, Lmap_residue]
    exact rho₁_commutes R S hS₁ hρ₁ v

private theorem rho₁_apply
    (hρ₁ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₁.integers),
      R.residue₁ ⟨_, h⟩ = resV v) (s : ↥S) :
    rho₁ R S hS₁ hρ₁ s = (R.residue₁ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₁ _ s.2⟩ : ↥(modularFunctionFieldC k N)) :=
  rfl

end Rho1
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

section Rho2
variable [IsLocalRing ↥(locRing A red N)] (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q))) (hS₂ : ∀ s ∈ S, s ∈ R.R₂.integers)

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₂_one : (R.residue₂ ⟨((1 : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₂ _ (1 : ↥S).2⟩ : ↥(modularFunctionFieldC k N)) = 1 :=
  map_one R.residue₂

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₂_mul (s t : ↥S) :
    (R.residue₂ ⟨((s * t : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₂ _ (s * t).2⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₂ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₂ _ s.2⟩ * R.residue₂ ⟨(t : ↥(modularFunctionFieldBar (N * q))), hS₂ _ t.2⟩ := by
  rw [← map_mul]; rfl

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₂_zero : (R.residue₂ ⟨((0 : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₂ _ (0 : ↥S).2⟩ : ↥(modularFunctionFieldC k N)) = 0 :=
  map_zero R.residue₂

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₂_add (s t : ↥S) :
    (R.residue₂ ⟨((s + t : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₂ _ (s + t).2⟩ : ↥(modularFunctionFieldC k N)) =
      R.residue₂ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₂ _ s.2⟩ + R.residue₂ ⟨(t : ↥(modularFunctionFieldBar (N * q))), hS₂ _ t.2⟩ := by
  rw [← map_add]; rfl

omit [IsLocalRing ↥(locRing A red N)] in
private theorem rho₂_commutes
    (hρ₂ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₂.integers),
      R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (resV v)) (v : ↥(locRing A red N)) :
    (R.residue₂ ⟨((algebraMap ↥(locRing A red N) ↥S v : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₂ _ (algebraMap ↥(locRing A red N) ↥S v).2⟩ : ↥(modularFunctionFieldC k N)) = frobeniusGeomLevel k N data hKr (resV v) := by
  have earg : (⟨((algebraMap ↥(locRing A red N) ↥S v : ↥S) : ↥(modularFunctionFieldBar (N * q))), hS₂ _ (algebraMap ↥(locRing A red N) ↥S v).2⟩ : ↥R.R₂.integers) =
      ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)), hS₂ _ (algebraMap_mem_order S v)⟩ :=
    Subtype.ext (coe_algebraMap_order S v)
  rw [earg]
  exact hρ₂ v _

private def rho₂
    (hρ₂ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₂.integers),
      R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (resV v)) :
    ↥S →ₐ[↥(locRing A red N)] KTwo k N data hKr where
  toFun s := (R.residue₂ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₂ _ s.2⟩ : ↥(modularFunctionFieldC k N))
  map_one' := rho₂_one R S hS₂
  map_mul' s t := rho₂_mul R S hS₂ s t
  map_zero' := rho₂_zero R S hS₂
  map_add' s t := rho₂_add R S hS₂ s t
  commutes' v := by
    rw [algebraMap_VKTwo_apply, Lmap_residue]
    exact rho₂_commutes R S hS₂ hρ₂ v

private theorem rho₂_apply
    (hρ₂ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₂.integers),
      R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (resV v)) (s : ↥S) :
    rho₂ R S hS₂ hρ₂ s = (R.residue₂ ⟨(s : ↥(modularFunctionFieldBar (N * q))), hS₂ _ s.2⟩ : ↥(modularFunctionFieldC k N)) :=
  rfl

end Rho2
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

section Dock
variable [ValuationRing ↥(locRing A red N)] [IsFractionRing ↥(locRing A red N) ↥(modularFunctionFieldBar N)]
  (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k)))
  (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q))) [Module.Finite ↥(locRing A red N) ↥S]
  (hspan : letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    Submodule.span ↥(modularFunctionFieldBar N) (S : Set ↥(modularFunctionFieldBar (N * q))) = ⊤)
  (hS₁ : ∀ s ∈ S, s ∈ R.R₁.integers) (hS₂ : ∀ s ∈ S, s ∈ R.R₂.integers)
  (hρ₁ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₁.integers),
      R.residue₁ ⟨_, h⟩ = resV v)
  (hρ₂ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₂.integers),
      R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (resV v))
  (hsurjS : ∀ a b : ↥(modularFunctionFieldC k N), ∃ (s : ↥(modularFunctionFieldBar (N * q))) (hs : s ∈ S),
    R.residue₁ ⟨s, hS₁ s hs⟩ = a ∧ R.residue₂ ⟨s, hS₂ s hs⟩ = b)
  (hfinFrob : finrankAlong k (frobeniusGeomLevel k N data hKr) = q)
  (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1)

include hsurjN hspan hsurjS hfinFrob hdeg in

private theorem engine_out (f : ↥(modularFunctionFieldBar (N * q))) (hfS : f ∈ S) :
    algebraMap ↥(locRing A red N) ↥(modularFunctionFieldBar N) (Algebra.norm ↥(locRing A red N) (⟨f, hfS⟩ : ↥S)) = Algebra.norm ↥(modularFunctionFieldBar N) f ∧
      IsLocalRing.residue ↥(locRing A red N) (Algebra.norm ↥(locRing A red N) (⟨f, hfS⟩ : ↥S)) =
        Algebra.norm (B A N red) (rho₁ R S hS₁ hρ₁ ⟨f, hfS⟩) *
          Algebra.norm (B A N red) (rho₂ R S hS₂ hρ₂ ⟨f, hfS⟩) := by
  haveI := finite_BKOne (k := k) hsurjN
  haveI := finite_BKTwo (data := data) (hKr := hKr) hsurjN hfinFrob
  have hsurj : Function.Surjective fun s : ↥S => (rho₁ R S hS₁ hρ₁ s, rho₂ R S hS₂ hρ₂ s) := by
    intro p
    obtain ⟨s, hs, ha, hb⟩ := hsurjS p.1 p.2
    refine ⟨⟨s, hs⟩, ?_⟩
    show (rho₁ R S hS₁ hρ₁ ⟨s, hs⟩, rho₂ R S hS₂ hρ₂ ⟨s, hs⟩) = p
    rw [rho₁_apply, rho₂_apply]
    exact Prod.ext ha hb
  have hdim : Module.finrank (B A N red) (KOne k N) + Module.finrank (B A N red) (KTwo k N data hKr) =
      Module.finrank ↥(modularFunctionFieldBar N) ↥(modularFunctionFieldBar (N * q)) := by
    rw [finrank_BKOne hsurjN, finrank_BKTwo hsurjN hfinFrob,
      show Module.finrank ↥(modularFunctionFieldBar N) ↥(modularFunctionFieldBar (N * q)) = finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q)
        from rfl, hdeg, add_comm]

  exact @Subalgebra.algebraMap_norm_eq_and_residue_norm_eq_mul ↥(locRing A red N) ↥(modularFunctionFieldBar N) ↥(modularFunctionFieldBar (N * q))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance S inferInstance hspan (KOne k N) (KTwo k N data hKr) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (rho₁ R S hS₁ hρ₁) (rho₂ R S hS₂ hρ₂) hsurj hdim ⟨f, hfS⟩

include hsurjN in
omit [IsFractionRing ↥(locRing A red N) ↥(modularFunctionFieldBar N)] [Module.Finite ↥(locRing A red N) ↥S] in

private theorem norm_rho₁_eq (f : ↥(modularFunctionFieldBar (N * q))) (hfS : f ∈ S) (h₁ : f ∈ R.R₁.integers) (b : B A N red)
    (hb : Lmap b = R.residue₁ ⟨f, h₁⟩) : Algebra.norm (B A N red) (rho₁ R S hS₁ hρ₁ ⟨f, hfS⟩) = b := by
  rw [show rho₁ R S hS₁ hρ₁ ⟨f, hfS⟩ = algebraMap (B A N red) (KOne k N) b by rw [algebraMap_BKOne, hb]; rfl,
    Algebra.norm_algebraMap, finrank_BKOne hsurjN, pow_one]

include hsurjN hfinFrob in
omit [IsFractionRing ↥(locRing A red N) ↥(modularFunctionFieldBar N)] [Module.Finite ↥(locRing A red N) ↥S] in

private theorem frob_norm_rho₂_eq [IsAlgClosed k] (f : ↥(modularFunctionFieldBar (N * q))) (hfS : f ∈ S) (h₂ : f ∈ R.R₂.integers) :
    frobeniusGeomLevel k N data hKr (Lmap (Algebra.norm (B A N red) (rho₂ R S hS₂ hρ₂ ⟨f, hfS⟩))) =
      (R.residue₂ ⟨f, h₂⟩) ^ q := by
  have hL4 := algebraMap_norm_eq_pow_of_finrank_eq_prime (κ := B A N red) (κ₂ := KTwo k N data hKr) q
    (finrank_BKTwo hsurjN hfinFrob) (exists_algebraMap_BKTwo_eq_pow hsurjN (perfect_of_isAlgClosed k))
    (rho₂ R S hS₂ hρ₂ ⟨f, hfS⟩)
  rw [algebraMap_BKTwo, rho₂_apply] at hL4
  exact hL4

end Dock
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

private theorem normResidueFactorization_of_engine [IsAlgClosed k]

    [ValuationRing ↥(locRing A red N)] [IsFractionRing ↥(locRing A red N) ↥(modularFunctionFieldBar N)]

    (hsurjN : Function.Surjective (resV (A := A) (N := N) (red := red) (k := k)))

    (S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)))
    [Module.Finite ↥(locRing A red N) ↥S]
    (hspan : letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
      Submodule.span ↥(modularFunctionFieldBar N) (S : Set ↥(modularFunctionFieldBar (N * q))) = ⊤)
    (hS₁ : ∀ s ∈ S, s ∈ R.R₁.integers) (hS₂ : ∀ s ∈ S, s ∈ R.R₂.integers)

    (hcont : ∀ (f : ↥(modularFunctionFieldBar (N * q))), f ∈ R.R₁.integers → f ∈ R.R₂.integers → f ∈ S)

    (hρ₁ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₁.integers),
      R.residue₁ ⟨_, h⟩ = resV v)
    (hρ₂ : ∀ (v : ↥(locRing A red N))
      (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₂.integers),
      R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (resV v))

    (hsurjS : ∀ a b : ↥(modularFunctionFieldC k N), ∃ (s : ↥(modularFunctionFieldBar (N * q))) (hs : s ∈ S),
      R.residue₁ ⟨s, hS₁ s hs⟩ = a ∧ R.residue₂ ⟨s, hS₂ s hs⟩ = b)

    (hfinFrob : finrankAlong k (frobeniusGeomLevel k N data hKr) = q)
    (hdeg : finrankAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) = q + 1) :
    NormResidueFactorization R := by
  intro f h₁ h₂ _hr₁ _hr₂
  have hfS : f ∈ S := hcont f h₁ h₂
  obtain ⟨hint, hres⟩ := engine_out R hsurjN S hspan hS₁ hS₂ hρ₁ hρ₂ hsurjS hfinFrob hdeg f hfS

  have hint' : ((Algebra.norm ↥(locRing A red N) (⟨f, hfS⟩ : ↥S) : ↥(locRing A red N)) : ↥(modularFunctionFieldBar N)) =
      (letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q); Algebra.norm ↥(modularFunctionFieldBar N) f) := hint
  have hn : (((letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q); Algebra.norm ↥(modularFunctionFieldBar N) f) : ↥(modularFunctionFieldBar N)) :
      LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red := by
    have h := (Algebra.norm ↥(locRing A red N) (⟨f, hfS⟩ : ↥S)).2
    rw [mem_locRing_iff, hint'] at h
    exact h

  obtain ⟨b, hb⟩ := Lmap_surjective hsurjN (R.residue₁ ⟨f, h₁⟩)

  have hres' := congrArg (Lmap (A := A) (N := N) (red := red) (k := k)) hres
  rw [map_mul, Lmap_residue, norm_rho₁_eq R hsurjN S hS₁ hρ₁ f hfS h₁ b hb, hb] at hres'
  refine ⟨hn, Lmap (Algebra.norm (B A N red) (rho₂ R S hS₂ hρ₂ ⟨f, hfS⟩)),
    frob_norm_rho₂_eq R hsurjN S hS₂ hρ₂ hfinFrob f hfS h₂, ?_⟩
  rw [← hres']
  apply Subtype.ext
  rw [resV_apply_coe]
  show CharPReduction.modularRedLocHom N A.toSubring red ⟨_, hn⟩ = _
  congr 1
  exact Subtype.ext
    (congrArg (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))) hint').symm

end EngineDock
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

#print axioms normResidueFactorization_of_engine
#print axioms normReduction'_of_factorization

section Closing
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

variable {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

private def NormReduction : Prop :=
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    ∃ hn : ((Algebra.norm (modularFunctionFieldBar N) f : modularFunctionFieldBar N) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red,
      CharPReduction.modularRedLocHom N A.toSubring red ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩ ≠ 0 ∧
      ∀ u : Place k (modularFunctionFieldC k N),
        (frobOnPlacesGeomLevel k N data hKr u).ord
            (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩,
              CharPReduction.modularRedLocHom_mem A.toSubring red N
                ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩⟩ : modularFunctionFieldC k N) =
          (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨f, h₁⟩) + u.ord (R.residue₂ ⟨f, h₂⟩)

private theorem resV_surjective_of_hred (hred : Function.Surjective red) :
    Function.Surjective (resV (A := A) (N := N) (red := red) (k := k)) := by
  intro a
  obtain ⟨f, hf⟩ := CharPReduction.exists_modularRedLocHom_eq A.toSubring red N hred a.2
  have hfb : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ modularFunctionFieldBar N :=
    RosatiL1.mem_bar_of_mem_V A red N f.2
  refine ⟨⟨⟨(f : LaurentSeries (AlgebraicClosure ℚ)), hfb⟩, (mem_locRing_iff _).mpr f.2⟩, Subtype.ext ?_⟩
  rw [resV_apply_coe]
  exact hf

private theorem residue₁_heckeAlphaBar_eq_resV
    (hlev : ∀ (f : LaurentSeries (AlgebraicClosure ℚ))
              (hfN : f ∈ CharPReduction.modularLocalized N A.toSubring red)
              (hfNq : f ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
            CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hfNq⟩ =
              CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hfN⟩)
    (v : ↥(locRing A red N))
    (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ = resV v := by
  have hfNq : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) :
      ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized (N * q) A.toSubring red :=
    (R.mem_integersFst_iff _).mp h
  have hfN : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) :
      ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
        ∈ CharPReduction.modularLocalized N A.toSubring red := by
    rw [coe_heckeAlphaBar]
    exact v.2
  obtain ⟨h', e⟩ := R.residue₁_eq_modularRedLocHom _ hfNq
  apply Subtype.ext
  rw [resV_apply_coe]
  refine e.trans ?_
  rw [hlev _ hfN hfNq]
  exact congrArg (CharPReduction.modularRedLocHom N A.toSubring red)
    (Subtype.ext ((coe_heckeAlphaBar N q (v : ↥(modularFunctionFieldBar N))).trans rfl))

private theorem residue₂_heckeAlphaBar_eq_frobeniusGeomLevel_resV
    (hwq : ∀ (v : modularFunctionFieldBar N)
              (hv : (v : LaurentSeries (AlgebraicClosure ℚ))
                ∈ CharPReduction.modularLocalized N A.toSubring red)
              (hw : ((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
                  modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
                ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
            CharPReduction.modularRedLocHom (N * q) A.toSubring red
                ⟨((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
                    modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)), hw⟩ =
              qExpand k q (CharPReduction.modularRedLocHom N A.toSubring red
                ⟨(v : LaurentSeries (AlgebraicClosure ℚ)), hv⟩))
    (v : ↥(locRing A red N))
    (h : heckeAlphaBar (AlgebraicClosure ℚ) N q (v : ↥(modularFunctionFieldBar N)) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ = frobeniusGeomLevel k N data hKr (resV v) := by
  have hw : ((ProlongationTuple.atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q
      (v : ↥(modularFunctionFieldBar N))) : modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (N * q) A.toSubring red :=
    (R.mem_integersSnd_iff _).mp h
  obtain ⟨_, e⟩ := R.residue₁_eq_modularRedLocHom _ hw
  apply Subtype.ext
  rw [ProlongationTuple.residue₂_apply, R.residue₂_eq _ h, frobeniusGeomLevel_apply_coe, resV_apply_coe]
  exact e.trans (hwq (v : ↥(modularFunctionFieldBar N)) v.2 hw)

private theorem exists_residue₁_eq_and_residue₂_eq
    (hsurj : ∀ a b : modularFunctionFieldC k N, ∃ (s : modularFunctionFieldBar (N * q))
        (h₁ : (s : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
        (h₂ : ((ProlongationTuple.atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₁⟩ = (a : LaurentSeries k) ∧
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₂⟩ = (b : LaurentSeries k))
    (a b : ↥(modularFunctionFieldC k N)) :
    ∃ (s : ↥(modularFunctionFieldBar (N * q))) (h₁ : s ∈ R.R₁.integers) (h₂ : s ∈ R.R₂.integers),
      R.residue₁ ⟨s, h₁⟩ = a ∧ R.residue₂ ⟨s, h₂⟩ = b := by
  obtain ⟨s, h₁, h₂, e₁, e₂⟩ := hsurj a b
  have hi₁ : s ∈ R.R₁.integers := (R.mem_integersFst_iff s).mpr h₁
  have hi₂ : s ∈ R.R₂.integers := (R.mem_integersSnd_iff s).mpr h₂
  refine ⟨s, hi₁, hi₂, ?_, ?_⟩
  · obtain ⟨_, e⟩ := R.residue₁_eq_modularRedLocHom s h₁
    exact Subtype.ext (e.trans e₁)
  · obtain ⟨_, e⟩ := R.residue₁_eq_modularRedLocHom (ProlongationTuple.atkinLehnerBar N q s) h₂
    apply Subtype.ext
    rw [ProlongationTuple.residue₂_apply, R.residue₂_eq s hi₂]
    exact e.trans e₂

private theorem normReduction_of_engine' [IsAlgClosed k] (hqN : ¬ q ∣ N) (hred : Function.Surjective red) :
    NormReduction R := by
  obtain ⟨S₀, hS, -, -, -, hfin, hspan, hsurj, hlev, hwq⟩ :=
    ProlongationTuple.exists_orderSubalgebra_finite_span_eq_top R hqN hred

  let S : Subalgebra ↥(locRing A red N) ↥(modularFunctionFieldBar (N * q)) := S₀
  haveI : ValuationRing ↥(locRing A red N) := RosatiL1.valuationRing_locRing A red N hqN
  haveI : IsFractionRing ↥(locRing A red N) ↥(modularFunctionFieldBar N) :=
    RosatiL1.isFractionRing_locRing A red N hqN
  haveI : Module.Finite ↥(locRing A red N) ↥S := hfin
  have hfac : NormResidueFactorization R :=
    normResidueFactorization_of_engine R (resV_surjective_of_hred hred) S hspan
      (fun s hs => (R.mem_integersFst_iff s).mpr ((hS s).mp hs).1)
      (fun s hs => (R.mem_integersSnd_iff s).mpr ((hS s).mp hs).2)
      (fun f h₁ h₂ => (hS f).mpr ⟨(R.mem_integersFst_iff f).mp h₁, (R.mem_integersSnd_iff f).mp h₂⟩)
      (fun v h => residue₁_heckeAlphaBar_eq_resV R hlev v h)
      (fun v h => residue₂_heckeAlphaBar_eq_frobeniusGeomLevel_resV R hwq v h)
      (fun a b => by
        obtain ⟨s, h₁, h₂, e₁, e₂⟩ := exists_residue₁_eq_and_residue₂_eq R
          (fun a b => by
            obtain ⟨s, -, h₁, h₂, e₁, e₂⟩ := hsurj a b
            exact ⟨s, h₁, h₂, e₁, e₂⟩) a b
        exact ⟨s, (hS s).mpr ⟨(R.mem_integersFst_iff s).mp h₁, (R.mem_integersSnd_iff s).mp h₂⟩, e₁, e₂⟩)
      (RosatiNormRed.finrankAlong_frobeniusGeomLevel k N data hKr hqN)
      (DegreeLegReceipt.finrankAlong_heckeAlphaBar_of_not_dvd (AlgebraicClosure ℚ) N q hqN)
  exact normReduction'_of_factorization R hfac

#print axioms normResidueFactorization_of_engine
#print axioms normReduction_of_engine'

end Closing
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1"

end ModularCurve.PlaceSpecialization
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve.PlaceSpecialization"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.RosatiL1 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective.ModularCurve.PlaceSpecialization"

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hqN : ¬ q ∣ N) (hred : Function.Surjective red)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) :
  ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
    R.R₁.residue ⟨f, h₁⟩ ≠ 0 → R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
    letI := algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
    ∃ hn : ((Algebra.norm (modularFunctionFieldBar N) f : modularFunctionFieldBar N) :
        LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized N A.toSubring red,
      CharPReduction.modularRedLocHom N A.toSubring red ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩ ≠ 0 ∧
      ∀ u : Place k (modularFunctionFieldC k N),
        (frobOnPlacesGeomLevel k N data hKr u).ord
            (⟨CharPReduction.modularRedLocHom N A.toSubring red ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩,
              CharPReduction.modularRedLocHom_mem A.toSubring red N
                ⟨Algebra.norm (modularFunctionFieldBar N) f, hn⟩⟩ : modularFunctionFieldC k N) =
          (frobOnPlacesGeomLevel k N data hKr u).ord (R.residue₁ ⟨f, h₁⟩) + u.ord (R.residue₂ ⟨f, h₂⟩) := by
  intro f h₁ h₂ hr₁ hr₂
  exact ModularCurve.PlaceSpecialization.normReduction_of_engine' R hqN hred f h₁ h₂ hr₁ hr₂

#print axioms solution

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_normReduction_of_not_dvd_of_surjective (solution)
