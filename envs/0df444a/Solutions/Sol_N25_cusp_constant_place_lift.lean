-- Prove2me | solution 1 for N25.cusp_constant_place_lift
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:30.493781+00:00
-- url     : https://prove2.me/submissions/cbb0c2da-872d-4517-bbc8-54fdf20fb70c

import Mathlib
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_N25_cusp_coefficient_embedding
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

open scoped MatrixGroups

namespace N25

/-- Every geometric place has a unique natural complex lift preserving normalized orders. -/
theorem _root_.solution
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    let K := AlgebraicClosure ℚ
    let F₀ := xHFunctionField 25 N25.H25
    let F := xHFunctionFieldBar 25 N25.H25
    let Fℂ := laurentBaseChange ℂ F₀
    ∃ κ : F →+* Fℂ,
      (∀ x : F, (κ x : LaurentSeries ℂ) = coeffMap ι (x : LaurentSeries K)) ∧
      ∀ P : Place K F, ∃ P' : Place ℂ Fℂ,
        P'.toValuationSubring.comap κ = P.toValuationSubring ∧
        (∀ x : F, P'.ord (κ x) = P.ord x) ∧
        ∀ Q' : Place ℂ Fℂ,
          Q'.toValuationSubring.comap κ = P.toValuationSubring → Q' = P' := by
  let K := AlgebraicClosure ℚ
  let Γ := CohCarrier.GammaH 25 H25
  let F₀ := xHFunctionField 25 H25
  let F := xHFunctionFieldBar 25 H25
  let Fℂ := laurentBaseChange ℂ F₀
  obtain ⟨κ,hκ,hconst,htower⟩ := cusp_coefficient_embedding ι
  refine ⟨κ,hκ,?_⟩
  letI : Algebra K ℂ := ι.toAlgebra
  letI : Algebra K Fℂ := ((algebraMap ℂ Fℂ).comp ι).toAlgebra
  letI : Algebra F Fℂ := κ.toAlgebra
  letI : IsScalarTower K ℂ Fℂ := htower.1
  letI : IsScalarTower K F Fℂ := htower.2.1
  letI : IsCurveOver K F :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField K 25 H25).1
  letI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH 25 H25)
  have hT : ModularGroup.T∈Γ := translation_mem_GammaH 25 H25
  have hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange K Γ hT
  have hfg' : ∃ x : Fℂ, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set Fℂ)) Fℂ :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ Γ hT
  intro P
  exact Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F ℂ Fℂ hfg hfg' htower.2.2 P

end N25
