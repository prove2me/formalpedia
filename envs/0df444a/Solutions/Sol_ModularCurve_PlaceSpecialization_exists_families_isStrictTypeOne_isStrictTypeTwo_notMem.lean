-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/698d1d5e-9e90-5ec6-8dcc-516e6b8aa915

import Definitions.Def_ModularCurve_LevelOneGlueData
import Theorems.Thm_ModularCurve_PlaceSpecialization_IsStrictTypeOne_exists_family_redFst_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d2 d4 IsStrictTypeOne.exists_family_redFst_injective"
namespace AuxFamilies
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

theorem exists_reindex_notMem {β : Type*} [DecidableEq β] (B : Finset β) (m : ℕ)
    (f : Fin (m + B.card + 1) → β) (hf : Function.Injective f) :
    ∃ g : Fin m → Fin (m + B.card + 1), Function.Injective g ∧ ∀ i, f (g i) ∉ B := by
  classical
  set s : Finset (Fin (m + B.card + 1)) := Finset.univ.filter (fun i => f i ∉ B) with hs
  have ht : (Finset.univ.filter (fun i : Fin (m + B.card + 1) => ¬ (f i ∉ B))).card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
      simpa using h2
    · intro a _ b _ h
      exact hf h
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (m + B.card + 1)))) (p := fun i => f i ∉ B)
  have huniv : (Finset.univ : Finset (Fin (m + B.card + 1))).card = m + B.card + 1 := by
    simp
  have hcard : m ≤ s.card := by
    rw [hs]; omega
  let e : Fin m ↪ Fin (m + B.card + 1) :=
    (Fin.castLEEmb hcard).trans (s.orderEmbOfFin rfl).toEmbedding
  refine ⟨e, e.injective, fun i => ?_⟩
  have hmem : e i ∈ s := Finset.orderEmbOfFin_mem s rfl _
  rw [hs] at hmem
  exact (Finset.mem_filter.mp hmem).2

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem exists_isStrictTypeTwo_redSnd_eq
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k (modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v) :
    ∃ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeTwo W ∧ P.redSnd W = v := by
  obtain ⟨w, hw⟩ := P.d4 v
  have hguard : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.sp w))
      ≠ P.sp w := by rw [hw]; exact hv
  obtain ⟨W₀, hW₀β, hW₀α, -, -⟩ := P.d2 w hguard
  refine ⟨W₀, ⟨?_, ?_⟩, ?_⟩
  · show P.sp (W₀.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα)
      = frobOnPlacesGeomLevel k 1 data hKr
          (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ))
    rw [hW₀α, hW₀β]
  · show frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr
        (P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ)))
      ≠ P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ)
    rw [hW₀β]; exact hguard
  · show P.sp (W₀.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ) = v
    rw [hW₀β, hw]

end ModularCurve.PlaceSpecialization.AuxFamilies

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (B : Finset (Place k ↥(modularFunctionFieldC k 1))) (m₁ m₂ : ℕ) :
    ∃ (Q₁ : Fin m₁ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
      (Q₂ : Fin m₂ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      (∀ i, P.IsStrictTypeOne (Q₁ i)) ∧ (∀ j, P.IsStrictTypeTwo (Q₂ j)) ∧
      (Function.Injective fun i => P.redFst (Q₁ i)) ∧
      (Function.Injective fun j => P.redSnd (Q₂ j)) ∧
      (∀ i, P.redFst (Q₁ i) ∉ B) ∧ (∀ j, P.redSnd (Q₂ j) ∉ B) := by
  classical

  obtain ⟨Q, hQ, hQinj⟩ :=
    IsStrictTypeOne.exists_family_redFst_injective P (m₁ + m₂ + B.card)

  obtain ⟨g, hg, hgB⟩ :=
    AuxFamilies.exists_reindex_notMem B (m₁ + m₂) (fun i => P.redFst (Q i)) hQinj

  have lift : ∀ i, ∃ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictTypeTwo W ∧ P.redSnd W = P.redFst (Q i) :=
    fun i => AuxFamilies.exists_isStrictTypeTwo_redSnd_eq P (P.redFst (Q i)) (hQ i).2
  choose W hW hWred using lift
  refine ⟨fun i => Q (g (Fin.castAdd m₂ i)), fun j => W (g (Fin.natAdd m₁ j)),
    fun i => hQ _, fun j => hW _, ?_, ?_, fun i => hgB _, fun j => ?_⟩
  · intro i i' h
    have h1 : g (Fin.castAdd m₂ i) = g (Fin.castAdd m₂ i') := hQinj h
    have h2 := congrArg Fin.val (hg h1)
    simp only [Fin.val_castAdd] at h2
    exact Fin.ext h2
  · intro j j' h
    have h0 : P.redFst (Q (g (Fin.natAdd m₁ j))) = P.redFst (Q (g (Fin.natAdd m₁ j'))) := by
      rw [← hWred, ← hWred]; exact h
    have h1 : g (Fin.natAdd m₁ j) = g (Fin.natAdd m₁ j') := hQinj h0
    have h2 := congrArg Fin.val (hg h1)
    simp only [Fin.val_natAdd] at h2
    exact Fin.ext (by omega)
  · show P.redSnd (W (g (Fin.natAdd m₁ j))) ∉ B
    rw [hWred]; exact hgB _

end S_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem (solution)
