-- Prove2me | solution 1 for ModularCurve.exists_ratFamily_isEmbBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b973ee54-a66f-5baf-bbef-d31425d22d4b

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq
import Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_cuspInftyBar
import Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq
import Theorems.Thm_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ratFamily_isEmbBasis
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

open AlgebraicCurve ModularCurve

noncomputable section

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution (p : ℕ) [Fact p.Prime] {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∃ g : Fin r → ↥(modularFunctionFieldFull (1 * p)),
      IsEmbBasis (1 * p) (fun l => (⟨coeffEmb (AlgebraicClosure ℚ) ((g l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (g l).2⟩ : ↥(modularFunctionFieldBar (1 * p)))) := by
  classical
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  haveI : FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace (embDivisor (1 * p))) :=
    ModularCurve.finiteDimensional_riemannRochSpace_modularFunctionFieldBar (q := p) (embDivisor (1 * p))
  set W := riemannRochSpace (embDivisor (1 * p)) with hW
  set F₀ := modularFunctionFieldFull (1 * p) with hF₀

  have hE : ∀ σ ∈ (Set.univ : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)),
      arithmeticGalois F₀ σ • embDivisor (1 * p) = embDivisor (1 * p) := by
    intro σ _
    have hz : arithmeticGalois F₀ σ • ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ))
        = (embDegree (1 * p) : ℤ) • (arithmeticGalois F₀ σ • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) :=
      map_zsmul (DistribSMul.toAddMonoidHom (Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (arithmeticGalois F₀ σ)) (embDegree (1 * p) : ℤ) (Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ))
    show arithmeticGalois F₀ σ • ((embDegree (1 * p) : ℤ) • Finsupp.single (cuspInftyBar (1 * p)) (1 : ℤ)) = _
    rw [hz, SemilinearAut.smul_single, ModularCurve.arithmeticGalois_smul_cuspInftyBar]
    rfl
  obtain ⟨b, hbW, hbli, hbfix⟩ :=
    ModularCurve.exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq (1 * p) Set.univ
      (embDivisor (1 * p)) hE

  have hfix : ∀ c : AlgebraicClosure ℚ, (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ c = c) →
      ∃ t : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) t = c := by
    intro c h
    have hmem : c ∈ IntermediateField.fixedField (⊤ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
      fun σ => h σ
    have hbot : IntermediateField.fixedField (⊤ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) = ⊥ := by
      rw [← IntermediateField.fixingSubgroup_bot, InfiniteGalois.fixedField_fixingSubgroup]
    rw [hbot, IntermediateField.mem_bot] at hmem
    exact hmem
  have hrat : ∀ i, ∃ y : LaurentSeries ℚ, y ∈ F₀ ∧
      coeffEmb (AlgebraicClosure ℚ) y = ((b i : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro i
    have hf : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        coeffMap (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
          ((b i : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((b i : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) := by
      intro σ
      rw [← coe_arithmeticGalois_smul, hbfix i σ (Set.mem_univ σ)]
    obtain ⟨y, hy⟩ := ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq hfix hf
    refine ⟨y, ?_, hy⟩
    apply ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) F₀ y
    rw [hy]
    exact SetLike.coe_mem _
  choose y hyF hy using hrat

  have hd : Module.finrank (AlgebraicClosure ℚ) ↥W = r := by
    have h := finrank_span_eq_card hs.1
    rw [hs.2] at h
    simpa using h
  let e : Fin r ≃ Fin (Module.finrank (AlgebraicClosure ℚ) ↥W) := finCongr hd.symm
  refine ⟨fun l => ⟨y (e l), hyF (e l)⟩, ?_⟩
  have hfam : (fun l : Fin r => (⟨coeffEmb (AlgebraicClosure ℚ) (y (e l)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hyF (e l))⟩ : ↥(modularFunctionFieldBar (1 * p))))
      = b ∘ e := by
    funext l
    exact Subtype.ext (hy (e l))
  show IsEmbBasis (1 * p) (fun l : Fin r => (⟨coeffEmb (AlgebraicClosure ℚ) (y (e l)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hyF (e l))⟩ : ↥(modularFunctionFieldBar (1 * p))))
  rw [hfam]
  refine ⟨(linearIndependent_equiv e).mpr hbli, ?_⟩
  rw [e.surjective.range_comp]

  apply le_antisymm (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbW i))
  let b' : Fin (Module.finrank (AlgebraicClosure ℚ) ↥W) → ↥W := fun i => ⟨b i, hbW i⟩
  have hli' : LinearIndependent (AlgebraicClosure ℚ) b' :=
    LinearIndependent.of_comp W.subtype (by simpa [b', Function.comp_def] using hbli)
  have htop : Submodule.span (AlgebraicClosure ℚ) (Set.range b') = ⊤ :=
    hli'.span_eq_top_of_card_eq_finrank' (by simp)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥W) ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range b') := by rw [htop]; trivial
  have himg := Submodule.mem_map_of_mem (f := W.subtype) hx'
  rw [Submodule.map_span, ← Set.range_comp] at himg
  exact himg

end

end S_ModularCurve_exists_ratFamily_isEmbBasis
end P2MW
export P2MW.S_ModularCurve_exists_ratFamily_isEmbBasis (solution)
