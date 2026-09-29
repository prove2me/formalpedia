-- Prove2me | solution 1 for ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5e2cfe4c-cd74-5a42-a2b1-a52aff50f427

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LevelNFunctionField
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
import Theorems.Thm_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
import Theorems.Thm_ModularCurve_LevelN_exists_algHom_laurentBaseChange_apply_eq_qExpand
import Theorems.Thm_ModularCurve_LevelN_exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one
import Theorems.Thm_ModularCurve_LevelN_valuation_apply_smul_le_one_of_tendsto_div_smul
import Theorems.Thm_ModularCurve_LevelN_isDomain_ring
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
import Theorems.Thm_ModularCurve_LevelN_exists_algHom_laurentSeries_qExpansion
import Theorems.Thm_ModularCurve_LevelN_exists_monoidHom_algEquiv_fixedField_eq_adjoin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Polynomial
open scoped MatrixGroups Topology

namespace ModularCurve
p2m_export "ModularCurve" "realizeOf laurentBaseChange qExpand jGen qExpFunctionFieldC jqModC LevelN.ring LevelN.jGen exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand LevelN.exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul LevelN.isDomain_ring exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem LevelN.exists_algHom_laurentSeries_qExpansion LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin"
namespace CuspPlaceGlue
p2m_open "ModularCurve"

theorem exists_monic_pullback {F K : Type*} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K]
    (Ψ : F →ₐ[ℂ] K) (y : F) (z : F) (P : K[X]) (hP : P.Monic) (hz : P.eval (Ψ z) = 0)
    (hPc : ∀ i, ∃ p q : ℂ[X], q.coeff 0 ≠ 0 ∧ P.coeff i = aeval (Ψ y)⁻¹ p / aeval (Ψ y)⁻¹ q) :
    ∃ P₀ : F[X], P₀.Monic ∧ P₀.eval z = 0 ∧
      ∀ i, ∃ p q : ℂ[X], q.coeff 0 ≠ 0 ∧ P₀.coeff i = aeval y⁻¹ p / aeval y⁻¹ q := by
  classical
  have hinj : Function.Injective Ψ := Ψ.toRingHom.injective
  choose p q hq hPq using hPc
  set c₀ : ℕ → F := fun i => aeval y⁻¹ (p i) / aeval y⁻¹ (q i) with hc₀
  have hΨc : ∀ i, Ψ (c₀ i) = P.coeff i := by
    intro i
    rw [hPq i, hc₀]
    simp only [map_div₀, ← Polynomial.aeval_algHom_apply, map_inv₀]
  set P₀ : F[X] := ∑ i ∈ Finset.range (P.natDegree + 1), C (c₀ i) * X ^ i with hP₀
  have hcoeff : ∀ i, P₀.coeff i = if i < P.natDegree + 1 then c₀ i else 0 := by
    intro i
    rw [hP₀, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (P.natDegree + 1)) i c₀]
    simp only [Finset.mem_range]
  have hmap : P₀.map (Ψ : F →+* K) = P := by
    ext i
    rw [Polynomial.coeff_map, hcoeff]
    split_ifs with hi
    · exact hΨc i
    · rw [map_zero, eq_comm]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  refine ⟨P₀, ?_, ?_, ?_⟩
  · exact Polynomial.monic_of_injective (Ψ : F →+* K).injective (by rw [hmap]; exact hP)
  · apply (Ψ : F →+* K).injective
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hmap]
    exact hz
  · intro i
    rw [hcoeff]
    split_ifs
    · exact ⟨p i, q i, hq i, rfl⟩
    · exact ⟨0, 1, by simp, by simp⟩

end ModularCurve.CuspPlaceGlue

namespace ModularCurve p2m_export "ModularCurve" "realizeOf laurentBaseChange qExpand jGen qExpFunctionFieldC jqModC LevelN.ring LevelN.jGen exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand LevelN.exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul LevelN.isDomain_ring exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem LevelN.exists_algHom_laurentSeries_qExpansion LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin" namespace CuspPlaceGlue end ModularCurve.CuspPlaceGlue
p2m_open_scoped "ModularCurve" in
open ModularCurve.CuspPlaceGlue in

theorem ModularCurve.CuspPlaceGlue.ord_eq_zero_aux
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (M : ℕ) [NeZero M] (hΓM : CongruenceSubgroup.Gamma M ≤ Γ)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K]
    (x : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (F : ℍ → ℂ)
    (hFx : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (y : ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hv : y ∉ v.toValuationSubring) :
    v.ord x = 0 := by
  classical

  obtain ⟨hst, σ, hσ, hker, hfixed, htr, hfin, _, hgal⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin M K
  obtain ⟨E, hEj, hEq⟩ := ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion M K
  have hEinj : Function.Injective E := E.toRingHom.injective

  obtain ⟨Ψ, hΨ⟩ := ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand M K σ hker hfixed
    E hEj Γ hΓM hT
  have hΨinj : Function.Injective Ψ := Ψ.toRingHom.injective
  have hΨy : Ψ y = algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M) := by
    apply hEinj
    rw [hΨ, hy, hEj]

  obtain ⟨k, g, h, hh, hxgh⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC_of_T_mem
      Γ hT (x : LaurentSeries ℂ) x.2
  have hlim : ∀ γ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => (g : ℍ → ℂ) (γ • τ) / (h : ℍ → ℂ) (γ • τ)) atImInfty (𝓝 L) :=
    ModularCurve.exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto Γ hT g h hh (x : LaurentSeries ℂ)
      hxgh F hFx hcusp

  set z : K := Ψ x with hzdef
  set qg : LaurentSeries ℂ := ModularCurve.qExpand ℂ M
    ((UpperHalfPlane.qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hqg
  set qh : LaurentSeries ℂ := ModularCurve.qExpand ℂ M
    ((UpperHalfPlane.qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hqh
  have hz : E z * qh = qg := by
    rw [hzdef, hΨ, hqh, hqg, ← map_mul, hxgh]

  have hEz : E z ≠ 0 := by
    intro h0
    have hqg0 : qg = 0 := by rw [← hz, h0, zero_mul]
    have hg0 : (UpperHalfPlane.qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) = 0 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
      apply (ModularCurve.qExpand ℂ M).injective
      rw [map_zero, map_zero]; exact hqg0
    have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
      exact AddSubgroup.mem_zmultiples _
    have hg : g = 0 := (ModularForm.qExpansion_eq_zero_iff one_pos h1 g).mp hg0
    obtain ⟨L, hL, hL'⟩ := hlim 1
    have : Filter.Tendsto (fun τ : ℍ => (g : ℍ → ℂ) ((1 : SL(2, ℤ)) • τ) / (h : ℍ → ℂ) ((1 : SL(2, ℤ)) • τ))
        atImInfty (𝓝 0) := by
      simp only [hg, ModularForm.coe_zero, Pi.zero_apply, zero_div]
      exact tendsto_const_nhds
    exact hL (tendsto_nhds_unique hL' this)
  have hz' : E z⁻¹ * qg = qh := by
    rw [map_inv₀, ← hz, inv_mul_cancel_left₀ hEz]

  have hpole : ∀ γ : SL(2, ℤ), Valued.v (E (σ γ z)) ≤ 1 := by
    intro γ
    obtain ⟨L, hL, hlimγ⟩ := hlim γ⁻¹
    exact ModularCurve.LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul M K hst σ hσ E hEj hEq
      Γ hΓM hT g h hh z hz γ L hL hlimγ
  have hg : g ≠ 0 := by
    intro hg0
    apply hEz
    have hqg0 : qg = 0 := by
      rw [hqg, hg0]
      have : UpperHalfPlane.qExpansion 1 ((0 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : ℍ → ℂ) = 0 := by
        have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
          rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
          exact AddSubgroup.mem_zmultiples _
        exact (ModularForm.qExpansion_eq_zero_iff one_pos h1 _).mpr rfl
      rw [this, map_zero, map_zero]
    have hzz := hz
    rw [hqg0] at hzz

    have hqh0 : qh ≠ 0 := by
      intro hqh0
      have hh0 : (UpperHalfPlane.qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) = 0 := by
        apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
        apply (ModularCurve.qExpand ℂ M).injective
        rw [map_zero, map_zero]; exact hqh0
      have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
        rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
        exact AddSubgroup.mem_zmultiples _
      exact hh ((ModularForm.qExpansion_eq_zero_iff one_pos h1 h).mp hh0)
    exact (mul_eq_zero.mp hzz).resolve_right hqh0
  have hpole' : ∀ γ : SL(2, ℤ), Valued.v (E (σ γ z⁻¹)) ≤ 1 := by
    intro γ
    obtain ⟨L, hL, hlimγ⟩ := hlim γ⁻¹
    have hlim' : Filter.Tendsto (fun τ : ℍ => (h : ℍ → ℂ) (γ⁻¹ • τ) / (g : ℍ → ℂ) (γ⁻¹ • τ))
        atImInfty (𝓝 L⁻¹) := by
      have := hlimγ.inv₀ hL
      simpa only [inv_div] using this
    exact ModularCurve.LevelN.valuation_apply_smul_le_one_of_tendsto_div_smul M K hst σ hσ E hEj hEq
      Γ hΓM hT h g hg z⁻¹ hz' γ L⁻¹ (inv_ne_zero hL) hlim'

  obtain ⟨P, hPm, hPz, hPc⟩ :=
    ModularCurve.LevelN.exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one
      M K σ hker hfixed E hEj z hpole
  obtain ⟨Q, hQm, hQz, hQc⟩ :=
    ModularCurve.LevelN.exists_monic_eval_eq_zero_coeff_eq_aeval_inv_div_of_forall_valuation_le_one
      M K σ hker hfixed E hEj z⁻¹ hpole'

  rw [← hΨy] at hPc hQc
  obtain ⟨P₀, hP₀m, hP₀x, hP₀c⟩ := exists_monic_pullback Ψ y x P hPm (by rw [← hzdef]; exact hPz) hPc
  obtain ⟨Q₀, hQ₀m, hQ₀x, hQ₀c⟩ :=
    exists_monic_pullback Ψ y x⁻¹ Q hQm (by rw [map_inv₀, ← hzdef]; exact hQz) hQc

  exact AlgebraicCurve.Place.ord_eq_zero_of_not_mem_of_eval_monic_eq_zero_of_coeff_eq_aeval_inv_div
    v hv hP₀m hQ₀m hP₀c hQ₀c hP₀x hQ₀x

open ModularCurve.CuspPlaceGlue in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (x : ModularCurve.laurentBaseChange ℂ F₀)
    (F : ℍ → ℂ)
    (hFx : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀))
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hv : y ∉ v.toValuationSubring) :
    v.ord x = 0 := by
  subst hF
  obtain ⟨M, hM0, hΓM⟩ := hΓ
  haveI : NeZero M := ⟨hM0⟩
  haveI : IsDomain (ModularCurve.LevelN.ring M) := ModularCurve.LevelN.isDomain_ring M
  exact ModularCurve.CuspPlaceGlue.ord_eq_zero_aux Γ hT M hΓM (FractionRing (ModularCurve.LevelN.ring M))
    x F hFx hcusp v y hy hv

end
end S_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto
end P2MW
export P2MW.S_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto (solution)
