-- Prove2me | solution 1 for N25.cusp_middle_closed_degree_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:57.184483+00:00
-- url     : https://prove2.me/submissions/954a3f3f-e60b-405e-9129-8606b49af013

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_N25_cusp_pole_lift_bijection
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
import Theorems.Thm_N25_cusp_complex_endpoints
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_N25_cusp_middle_geometric_residue
import Theorems.Thm_N25_jqTwentyFive_mem_xH25
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_N25_cusp_geometric_contraction
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_N25_cusp_contraction_order
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension
import Theorems.Thm_N25_cusp_contraction_residue_embedding
import Theorems.Thm_N25_cusp_residue_degree_lower_bound
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_not_mem_iff_ord_neg
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve N25.Endgame

open scoped MatrixGroups Topology

namespace N25

/-- The actual middle closed cusp has j-order minus five and residue degree at least four. -/
theorem _root_.solution (ι : Qbar →+* ℂ) :
    ∃ Q : QPlace, IsCusp j25 Q ∧ Q.ord j25 = -5 ∧ 4 ≤ Q.deg := by
  classical
  let B : SL(2, ℤ) := ⟨!![1,0;5,1],by norm_num [Matrix.det_fin_two]⟩
  obtain ⟨κ,j,jC,hκ,hj,hjC,hκj,hfin,hfinC,hcard,hcardC,lift,hlift⟩ :=
    cusp_pole_lift_bijection ι
  obtain ⟨jC',endpoint,hjC',hwidth,hmem,hlead⟩ := cusp_complex_endpoints
  have hjcc : jC' = jC := Subtype.ext (hjC'.trans hjC.symm)
  rw [hjcc] at hwidth
  let W := endpoint B
  have hW : W.ord jC = -5 := by
    have hh := hwidth B
    norm_num [B] at hh
    exact hh
  have hWneg : W.ord jC < 0 := by rw [hW]; norm_num
  let V : {R : Place ℂ (laurentBaseChange ℂ FQ) // R.ord jC < 0} := ⟨W,hWneg⟩
  let S := lift.symm V
  let P : GPlace := S.val
  have hlW : (lift S).val = W := congrArg Subtype.val (lift.apply_symm_apply V)
  have hcon : W.toValuationSubring.comap κ = P.toValuationSubring := by
    simpa only [hlW] using (hlift S).1
  have hord (y : FG) : W.ord (κ y) = P.ord y := by
    simpa only [hlW] using (hlift S).2 y
  have hjActual : j = emb25 j25 := by
    apply Subtype.ext
    exact hj.trans (map_jqModC (algebraMap ℚ Qbar)).symm
  have hPord : P.ord (emb25 j25) = -5 := by
    rw [←hjActual,←hord,hκj]
    exact hW
  have hPcusp : IsCusp (emb25 j25) P :=
    (Place.not_mem_iff_ord_neg P _).mpr (by rw [hPord]; norm_num)
  obtain ⟨Q,⟨hQc,hQ⟩,_⟩ := cusp_geometric_contraction P hPcusp
  have hQo : Q.ord j25 = -5 :=
    (cusp_contraction_order Q P hQ j25).symm.trans hPord
  have hB5 : (5 : ℤ) ∣ B 1 0 := by norm_num [B]
  have hB25 : ¬ (25 : ℤ) ∣ B 1 0 := by norm_num [B]
  have hleadW : ∀ y : laurentBaseChange ℂ FQ, y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (fun τ : UpperHalfPlane =>
        realizeOf Γ25 (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (W.ord y : ℂ) * (τ : ℂ) / (5 : ℂ))))
        UpperHalfPlane.atImInfty (nhds L) := by
    have hwB : (if (B 1 0 : ZMod 25).val = 0 then 1 else
        if (B 1 0 : ZMod 25).val % 5 = 0 then 5 else 25 : ℕ) = 5 := by decide
    simpa only [hwB,Nat.cast_ofNat] using hlead B
  have hres := cusp_middle_geometric_residue ι κ hκ P W hcon hord B hB5 hB25
    (hmem B) 5 (by norm_num) hleadW
  let x : FQ := (⟨jqNModC ℚ 25,jqTwentyFive_mem_xH25 ℚ⟩ : FQ) / j25
  change emb25 x ∈ P.toValuationSubring ∧ IsPrimitiveRoot (P.evalAt (emb25 x)) 5 at hres
  have hxQ : x ∈ Q.toValuationSubring := by
    rw [hQ]
    exact hres.1
  obtain ⟨ρ,hρinj,hρ⟩ := cusp_contraction_residue_embedding Q P hQ
  let a : Q.toValuationSubring := ⟨x,hxQ⟩
  let ζ : Q.ResidueField := IsLocalRing.residue _ a
  have : IsCurveOver Qbar FG :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField Qbar 25 H25).1
  have hr : P.IsRational := by
    intro t
    have : Module.Finite Qbar P.ResidueField := IsCurveOver.finiteResidue P
    have : Algebra.IsIntegral Qbar P.ResidueField := Algebra.IsIntegral.of_finite Qbar P.ResidueField
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective t
  have heval : ρ ζ = algebraMap Qbar P.ResidueField (P.evalAt (emb25 x)) := by
    exact (hρ a).trans (P.algebraMap_evalAt hr hres.1).symm
  have hpρ : IsPrimitiveRoot (ρ ζ) 5 := by
    rw [heval]
    exact hres.2.map_of_injective (algebraMap Qbar P.ResidueField).injective
  have hpζ : IsPrimitiveRoot ζ 5 := hpρ.of_map_of_injective hρinj
  exact ⟨Q,hQc,hQo,cusp_residue_degree_lower_bound Q ζ hpζ⟩

end N25
