-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.IsStrictTypeOne.exists_family_redFst_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e7b641d2-022a-53f2-9b11-611ef7139160

import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneComp
import Theorems.Thm_ModularCurve_sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.IsStrictTypeOne modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one deg_eq_one_modularFunctionFieldBar hasPrincipalDivisors_modularFunctionFieldBar_unconditional frobOnPlacesGeomLevel_charLGeomPlaceOfPoint"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "redFst redSnd IsStrictTypeOne sp d2 d1 d4"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective.ModularCurve"

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem IsStrictTypeOne.exists_family_redFst_injective'
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (d : ℕ) :
    ∃ Q : Fin (d + 1) → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      (∀ i, P.IsStrictTypeOne (Q i)) ∧ Function.Injective fun i => P.redFst (Q i) := by
  classical

  set φ : Place k (modularFunctionFieldC k 1) → Place k (modularFunctionFieldC k 1) :=
    frobOnPlacesGeomLevel k 1 data hKr with hφdef
  have hq : q.Prime := Fact.out
  have hq2 : 2 ≤ q := hq.two_le
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)

  have hinf : Set.Infinite {a : k | a ^ (q ^ 2) ≠ a} := by
    have hfin : Set.Finite {a : k | a ^ (q ^ 2) = a} := by
      have hP : (Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k) ≠ 0 := by
        apply FiniteField.X_pow_card_sub_X_ne_zero k
        calc 1 < 2 := by norm_num
          _ ≤ q := hq2
          _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
      refine (((Polynomial.X ^ (q ^ 2) - Polynomial.X : Polynomial k).roots.toFinset.finite_toSet)).subset ?_
      intro a ha
      simp only [Set.mem_setOf_eq] at ha
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ha, sub_self]
    have huniv : (Set.univ : Set k).Infinite := Set.infinite_univ_iff.mpr inferInstance
    have : {a : k | a ^ (q ^ 2) ≠ a} = Set.univ \ {a : k | a ^ (q ^ 2) = a} := by
      ext a; simp
    rw [this]
    exact huniv.diff hfin
  obtain ⟨a, ha_mem, ha_inj⟩ : ∃ a : Fin (d + 1) → k, (∀ i, a i ∈ {a : k | a ^ (q ^ 2) ≠ a}) ∧
      Function.Injective a := by
    let e := hinf.natEmbedding
    refine ⟨fun i => (e i : k), fun i => (e i).2, ?_⟩
    intro i j hij
    exact Fin.val_injective (e.injective (Subtype.val_injective hij))

  set vbar : Fin (d + 1) → Place k (modularFunctionFieldC k 1) :=
    fun i => charLGeomPlaceOfPoint k (a i) with hvbar
  have hφv : ∀ i, φ (vbar i) = charLGeomPlaceOfPoint k (a i ^ q) := fun i =>
    frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr (a i)
  have hφφv : ∀ i, φ (φ (vbar i)) ≠ vbar i := by
    intro i h
    rw [hφv] at h
    simp only [hφdef, hvbar, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, ← pow_mul, ← pow_two] at h
    exact ha_mem i (charLGeomPlaceOfPoint_injective k h)

  have key : ∀ i, ∃ U : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeOne U ∧ φ (P.redFst U) = vbar i := by
    intro i
    obtain ⟨v, hv⟩ := P.d4 (vbar i)
    have hguard : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.sp v))
        ≠ P.sp v := by rw [hv]; exact hφφv i
    obtain ⟨W₀, hW₀β, hW₀α, hW₀e, huniq⟩ := P.d2 v hguard

    have hsum := ModularCurve.sum_ramificationIndexAlong_heckeBetaBar_of_deg_eq_one 1 q
      (hq.one_lt.ne' ∘ Nat.dvd_one.mp) hβ (ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * q)) v
    have hW₀mem : W₀ ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ v :=
      Place.mem_fiberAlong.mpr hW₀β
    obtain ⟨U, hUmem, hUne⟩ : ∃ U ∈ Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ v,
        U ≠ W₀ := by
      by_contra hcon
      push Not at hcon
      have hfib : Place.fiberAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ v = {W₀} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hW₀mem, hcon⟩
      rw [hfib, Finset.sum_singleton, hW₀e] at hsum
      norm_num at hsum
      omega
    have hUβ : U.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ = v :=
      Place.mem_fiberAlong.mp hUmem

    rcases P.d1 U with h1 | h1
    · exact absurd (huniq U hUβ (by rw [h1, hUβ])) hUne
    · refine ⟨U, ⟨?_, ?_⟩, ?_⟩
      ·
        show frobOnPlacesGeomLevel k 1 data hKr (P.sp (U.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα))
          = P.sp (U.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ)
        exact h1
      ·
        intro h2
        apply hφφv i
        have h3 : φ (P.redFst U) = vbar i := by
          show frobOnPlacesGeomLevel k 1 data hKr (P.sp (U.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)) = vbar i
          rw [h1, hUβ, hv]
        have h2' : φ (φ (P.redFst U)) = P.redFst U := h2
        calc φ (φ (vbar i)) = φ (φ (φ (P.redFst U))) := by rw [h3]
          _ = φ (P.redFst U) := by rw [h2']
          _ = vbar i := h3
      · show frobOnPlacesGeomLevel k 1 data hKr (P.sp (U.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)) = vbar i
        rw [h1, hUβ, hv]
  choose U hU using key
  refine ⟨U, fun i => (hU i).1, ?_⟩
  intro i j hij
  have h : vbar i = vbar j := by rw [← (hU i).2, ← (hU j).2]; exact congrArg φ hij
  exact ha_inj (charLGeomPlaceOfPoint_injective k h)

end ModularCurve.PlaceSpecialization

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective.ModularCurve in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (d : ℕ) :
    ∃ Q : Fin (d + 1) → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      (∀ i, P.IsStrictTypeOne (Q i)) ∧ Function.Injective fun i => P.redFst (Q i) :=
  ModularCurve.PlaceSpecialization.IsStrictTypeOne.exists_family_redFst_injective' P d

end S_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective (solution)
