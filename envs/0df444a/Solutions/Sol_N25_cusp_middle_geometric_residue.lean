-- Prove2me | solution 1 for N25.cusp_middle_geometric_residue
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:39.698999+00:00
-- url     : https://prove2.me/submissions/2cd5c81b-2293-43f1-89db-727dffaaf13a

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_N25_jqTwentyFive_mem_xH25
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_N25_jqRatioTwentyFive_middle_sub_const_limit
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_hasSum_jNum_qParam
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
import Theorems.Thm_ModularCurve_laurent_qParam_coeff_unique
import Theorems.Thm_ModularCurve_realizeOf_eq_div
import Theorems.Thm_N25_cusp_complex_order_zero_of_nonzero_limit
import Theorems.Thm_N25_fifth_root_exp_ne_rat

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open ModularCurve AlgebraicCurve N25.Endgame Filter Topology

open scoped MatrixGroups

namespace N25

/-- The middle endpoint has a primitive fifth root as the residue of the actual rational j-ratio. -/
theorem _root_.solution
    (ι : Qbar →+* ℂ) (κ : FG →+* laurentBaseChange ℂ FQ)
    (hκ : ∀ y : FG, (κ y : LaurentSeries ℂ) = coeffMap ι (y : LaurentSeries Qbar))
    (P : GPlace) (W : Place ℂ (laurentBaseChange ℂ FQ))
    (hcon : W.toValuationSubring.comap κ = P.toValuationSubring)
    (hord : ∀ y : FG, W.ord (κ y) = P.ord y)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hB5 : (5 : ℤ) ∣ B 1 0) (hB25 : ¬ (25 : ℤ) ∣ B 1 0)
    (hmem : ∀ y : laurentBaseChange ℂ FQ, y ∈ W.toValuationSubring ↔
      ∃ L : ℂ, Tendsto (fun τ : UpperHalfPlane =>
        realizeOf Γ25 (y : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds L))
    (w : ℕ) (hw : 0 < w)
    (hlead : ∀ y : laurentBaseChange ℂ FQ, y ≠ 0 →
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : UpperHalfPlane =>
        realizeOf Γ25 (y : LaurentSeries ℂ) (B • τ) *
          Complex.exp (-(2 * Real.pi * Complex.I * (W.ord y : ℂ) * (τ : ℂ) / (w : ℂ))))
        UpperHalfPlane.atImInfty (nhds L)) :
    let x : FQ := (⟨jqNModC ℚ 25,jqTwentyFive_mem_xH25 ℚ⟩ : FQ) / j25
    emb25 x ∈ P.toValuationSubring ∧ IsPrimitiveRoot (P.evalAt (emb25 x)) 5 := by
  classical
  let x : FQ := (⟨jqNModC ℚ 25,jqTwentyFive_mem_xH25 ℚ⟩ : FQ) / j25
  have hxe : (κ (emb25 x) : LaurentSeries ℂ) = jqNModC ℂ 25 / jqModC ℂ := by
    rw [hκ, coe_emb25]
    change coeffMap ι (coeffMap (algebraMap ℚ Qbar) (jqNModC ℚ 25 / jqModC ℚ)) = _
    rw [map_div₀,map_div₀,coeffMap_jqNModC,coeffMap_jqModC,
      coeffMap_jqNModC,coeffMap_jqModC]
  have hconst (c : Qbar) :
      (κ (algebraMap Qbar FG c) : LaurentSeries ℂ) = HahnSeries.C (ι c) := by
    rw [hκ]
    change coeffMap ι (algebraMap Qbar (LaurentSeries Qbar) c) = _
    rw [algebraMap_laurentSeries_eq_single]
    ext n
    simp only [coeffMap_coeff,HahnSeries.coeff_single]
    split_ifs <;> simp_all
  obtain ⟨v,hv,hlim⟩ := jqRatioTwentyFive_middle_sub_const_limit B hB5 hB25
  let limitValue : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) / 5)))
  have hxlim : Tendsto (fun τ : UpperHalfPlane =>
      realizeOf Γ25 (κ (emb25 x) : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds limitValue) := by
    simpa only [hxe,map_zero,sub_zero] using hlim 0
  have hxm : emb25 x ∈ P.toValuationSubring := by
    rw [←hcon]
    exact (hmem _).mpr ⟨limitValue,hxlim⟩
  have : IsCurveOver Qbar FG :=
    (isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField Qbar 25 H25).1
  have hr : P.IsRational := by
    intro t
    have : Module.Finite Qbar P.ResidueField := IsCurveOver.finiteResidue P
    have : Algebra.IsIntegral Qbar P.ResidueField := Algebra.IsIntegral.of_finite Qbar P.ResidueField
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective t
  let c := P.evalAt (emb25 x)
  let z : FG := emb25 x - algebraMap Qbar FG c
  have hzm : z ∈ P.toValuationSubring := sub_mem hxm (P.algebraMap_mem' c)
  have hres : IsLocalRing.residue P.toValuationSubring ⟨z,hzm⟩ = 0 := by
    have ha : (⟨z,hzm⟩ : P.toValuationSubring) =
        ⟨emb25 x,hxm⟩ - algebraMap Qbar P.toValuationSubring c := rfl
    rw [ha,map_sub,←P.algebraMap_evalAt hr hxm]
    rw [←IsLocalRing.ResidueField.algebraMap_eq,
      ←IsScalarTower.algebraMap_apply Qbar P.toValuationSubring P.ResidueField]
    exact sub_self _
  have hzcoe : (κ z : LaurentSeries ℂ) =
      jqNModC ℂ 25 / jqModC ℂ - HahnSeries.C (ι c) := by
    change (κ (emb25 x-algebraMap Qbar FG c) : LaurentSeries ℂ) = _
    rw [map_sub]
    change (κ (emb25 x) : LaurentSeries ℂ)-(κ (algebraMap Qbar FG c) : LaurentSeries ℂ) = _
    rw [hxe,hconst]
  have heq : limitValue = ι c := by
    by_contra hn
    have hl : Tendsto (fun τ : UpperHalfPlane =>
        realizeOf Γ25 (κ z : LaurentSeries ℂ) (B • τ)) UpperHalfPlane.atImInfty (nhds (limitValue-ι c)) := by
      simpa only [hzcoe] using hlim (ι c)
    obtain ⟨hnz,ho⟩ := cusp_complex_order_zero_of_nonzero_limit W B w hw hlead
      (κ z) _ (sub_ne_zero.mpr hn) hl
    have hz0 : z ≠ 0 := by intro h; exact hnz (h ▸ map_zero κ)
    have hpz : P.ord z = 0 := (hord z).symm.trans ho
    obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
    obtain ⟨u,hu⟩ := P.exists_unit_mul_zpow hz0 hπ
    rw [hpz,zpow_zero,mul_one] at hu
    have haunit : IsUnit (⟨z,hzm⟩ : P.toValuationSubring) :=
      (Subtype.ext hu : (⟨z,hzm⟩ : P.toValuationSubring) = u).symm ▸ u.isUnit
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr haunit) hres
  have hpow : limitValue ^ 5 = 1 := by
    rw [←Complex.exp_nat_mul]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-v,?_⟩
    push_cast
    ring
  have hn1 : limitValue ≠ 1 := by
    simpa only [Rat.cast_one] using fifth_root_exp_ne_rat v hv 1
  have hprim : IsPrimitiveRoot limitValue 5 := by
    apply isPrimitiveRoot_of_mem_nthRootsFinset (by decide : Nat.Prime 5) ?_ hn1
    simpa only [Polynomial.mem_nthRootsFinset (by decide : 0 < (5 : ℕ))] using hpow
  refine ⟨hxm,?_⟩
  have hp : IsPrimitiveRoot (ι c) 5 := heq ▸ hprim
  exact hp.of_map_of_injective ι.injective

end N25
