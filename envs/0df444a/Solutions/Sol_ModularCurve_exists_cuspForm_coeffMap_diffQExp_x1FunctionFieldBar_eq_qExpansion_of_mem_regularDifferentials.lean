-- Prove2me | solution 1 for ModularCurve.exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/67c32c0e-ac30-55b8-b1ac-409cd6554d30

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg HahnSeries.ramScale_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential
open scoped MatrixGroups

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace X1ConvGlue

variable (M : ℕ) [NeZero M]

local notation "ℚb" => AlgebraicClosure ℚ
local notation "Γ₁" => CongruenceSubgroup.Gamma1 M

abbrev Fb : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) := x1FunctionFieldBar M

theorem jq_mem_x1FunctionField : jq ∈ x1FunctionField M :=
  intFormRatiosC_subset ℚ Γ₁ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ₁)

abbrev jB : Fb M :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_x1FunctionField M)⟩

theorem coeffMap_qEuler {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : LaurentSeries R) :
    coeffMap f (qEuler R s) = qEuler S (coeffMap f s) := by
  ext n
  simp [qEuler_coeff, coeffMap_coeff]

theorem qEuler_eq_thetaL (s : LaurentSeries ℂ) : qEuler ℂ s = thetaL ℂ s := by
  ext n
  rw [qEuler_coeff, thetaL_apply, ModularCurve.theta_coeff, zsmul_eq_mul]

theorem coeffMap_coeffEmb' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) z

theorem coeffMap_coeffEmb_jq (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) jq) = jqModC ℂ := by
  rw [coeffEmb, coeffMap_coeffMap, ← jqModC_rat]
  exact map_jqModC _

theorem coeffMap_algebraMap' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    coeffMap ι₀ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_laurentBaseChange_complex (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    coeffMap ι₀ x ∈ laurentBaseChange ℂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange ℂ F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

noncomputable def phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) : Fb M →+* LaurentSeries ℂ :=
  (coeffMap ι₀).comp (Fb M).toSubfield.subtype

theorem phi_apply (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : Fb M) :
    phi M ι₀ x = coeffMap ι₀ (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem phi_algebraMap (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi M ι₀ (algebraMap (AlgebraicClosure ℚ) (Fb M) c) = algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [phi_apply]
  exact coeffMap_algebraMap' ι₀ c

theorem phi_jB (ι₀ : AlgebraicClosure ℚ →+* ℂ) : phi M ι₀ (jB M) = jqModC ℂ := by
  rw [phi_apply]
  exact coeffMap_coeffEmb_jq ι₀

theorem isIntegral_phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) (a : Fb M) {y : Fb M}
    (hy : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M))) y) :
    IsIntegral (Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ))) (phi M ι₀ y) := by
  have hmem : ∀ r : Fb M,
      r ∈ Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M)) →
      phi M ι₀ r ∈ Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ)) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap c =>
        rw [phi_algebraMap]
        exact Subalgebra.algebraMap_mem _ _
    | add r s _ _ hr hs => rw [map_add]; exact add_mem hr hs
    | mul r s _ _ hr hs => rw [map_mul]; exact mul_mem hr hs
  let ψ : Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M)) →+*
      Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ)) :=
    ((phi M ι₀).comp (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M))).val.toRingHom).codRestrict
      (Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ))) (fun r => hmem r r.2)
  refine IsIntegral.map_of_comp_eq ψ (phi M ι₀) ?_ hy
  ext r
  rfl

theorem D_jB_ne_zero : D (AlgebraicClosure ℚ) (Fb M) (jB M) ≠ 0 := by
  intro h
  have h1 : diffQExp (Fb M) (D (AlgebraicClosure ℚ) (Fb M) (jB M)) =
      qEuler (AlgebraicClosure ℚ) ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) :=
    diffQExp_D _ _
  rw [h, map_zero] at h1
  have h2 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff (-1)) h1
  simp only at h2
  rw [qEuler_coeff] at h2
  have h3 : ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h3, HahnSeries.coeff_zero] at h2
  norm_num at h2

theorem alg_transport (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hF : F = qExpFunctionFieldC (AlgebraicClosure ℚ) Γ₁)
    (jbar : ↥F) (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : ↥F) (hx : x • D (AlgebraicClosure ℚ) ↥F jbar ∈ regularDifferentials (AlgebraicClosure ℚ) ↥F) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F))
        (x ^ 6 * jbar ^ 4 * (jbar - algebraMap (AlgebraicClosure ℚ) ↥F 1728) ^ 3) ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar⁻¹} : Set ↥F))
        (x ^ (2 * Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F) *
          jbar ^ (Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F + 1) *
          (jbar - algebraMap (AlgebraicClosure ℚ) ↥F 1728) ^
            Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F) := by
  subst hF
  exact ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC M Γ₁ le_rfl
    (CongruenceSubgroup.Gamma1_in_Gamma0 M) jbar hjbar x hx

theorem Fb_eq : (Fb M : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) =
    qExpFunctionFieldC (AlgebraicClosure ℚ) Γ₁ :=
  ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) Γ₁

theorem coe_jB : ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ)
  rw [coeffEmb, ← jqModC_rat]
  exact map_jqModC _

end X1ConvGlue

end

open scoped MatrixGroups in
open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential X1ConvGlue in
theorem solution
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])
    (hω : ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := by
  classical
  haveI hCO := ModularCurve.isCurveOver_x1FunctionFieldBar M

  have hrank : Module.finrank (Fb M) Ω[Fb M⁄AlgebraicClosure ℚ] = 1 := IsCurveOver.finrank_kaehler
  obtain ⟨x, hx⟩ := (finrank_eq_one_iff_of_nonzero'
    (D (AlgebraicClosure ℚ) (Fb M) (jB M)) (D_jB_ne_zero M)).mp hrank ω

  have hxreg : x • D (AlgebraicClosure ℚ) (Fb M) (jB M) ∈
      regularDifferentials (AlgebraicClosure ℚ) (Fb M) := by
    rw [hx]; exact hω
  obtain ⟨h₁, h₂⟩ := alg_transport M (Fb M) (Fb_eq M) (jB M) (coe_jB M) x hxreg

  have hXmem : phi M ι₀ x ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)) :=
    coeffMap_mem_laurentBaseChange_complex ι₀ _ x.2
  have hJ : phi M ι₀ (jB M) = jqModC ℂ := phi_jB M ι₀
  have h1728 : phi M ι₀ (algebraMap (AlgebraicClosure ℚ) (Fb M) 1728) = algebraMap ℂ (LaurentSeries ℂ) 1728 := by
    rw [phi_algebraMap, map_ofNat]
  have h₁' := isIntegral_phi M ι₀ (jB M) h₁
  have h₂' := isIntegral_phi M ι₀ ((jB M)⁻¹) h₂
  rw [map_inv₀, hJ] at h₂'
  rw [hJ] at h₁'
  simp only [map_mul, map_pow, map_sub, hJ, h1728] at h₁' h₂'
  set n : ℕ := Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB M} : Set (Fb M))) (Fb M) with hn

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  have h₁'' : IsIntegral (Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ)))
      ((phi M ι₀ x) ^ 6 * jqModC ℂ ^ (4 * 1) * (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * 1)) := by
    simpa only [mul_one] using h₁'
  have h₂'' : IsIntegral (Algebra.adjoin ℂ ({(jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      ((phi M ι₀ x) ^ (2 * n) * jqModC ℂ ^ (1 * n + 1) * (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (1 * n)) := by
    simpa only [one_mul] using h₂'
  obtain ⟨f, hf⟩ :=
    ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma1 M) hT 1 le_rfl (phi M ι₀ x) hXmem n h₁'' h₂''
  refine ⟨f, ?_⟩

  have hΘ : diffQExp (Fb M) ω =
      ((x : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) *
        qEuler (AlgebraicClosure ℚ) ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [← hx]
    exact diffQExp_smul_D _ _ _
  show coeffMap ι₀ (diffQExp (Fb M) ω) = _
  rw [hΘ, map_mul, coeffMap_qEuler, qEuler_eq_thetaL, ← phi_apply, ← phi_apply, hJ]
  rw [pow_one] at hf
  exact hf.symm

#print axioms solution

end S_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials
end P2MW
export P2MW.S_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials (solution)
