-- Prove2me | solution 1 for ModularCurve.IgusaScheme.finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/e1eddd99-92e5-5a87-8f19-c77314656390

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_IgusaScheme_isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd
import Theorems.Thm_ModularCurve_IgusaScheme_eq_zero_of_forall_laurentLift_apply_eq_zero_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq"
p2m_attr_erase "simp" "MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open scoped TensorProduct
open ModularCurve ModularCurve.IgusaScheme

namespace E2TwoComp

noncomputable def mapHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := by
    first
      | exact HahnSeries.map_one f
      | exact HahnSeries.map_one (RingHom.toMonoidWithZeroHom f)
      | exact HahnSeries.map_one (f : R →*₀ S)
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero (f : ZeroHom R S)
  map_add' x y := HahnSeries.map_add (f : R →+ S)

theorem mapHom_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : LaurentSeries R) :
    mapHom f x = x.map f := rfl

theorem mapHom_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (mapHom f) := by
  intro x y h
  ext n
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff n) h
  simpa [mapHom_apply, HahnSeries.map_coeff] using this

theorem ringHom_ratLocalizedAt_ext {p : ℕ} {S : Type*} [Ring S]
    (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  apply RingHom.ext
  intro x

  have hden : (x : ℚ).den.Coprime p := x.2
  have hd0 : (x : ℚ).den ≠ 0 := (x : ℚ).den_nz
  let d : ↥(GaloisRep.ratLocalizedAt p) := ⟨((x : ℚ).den : ℚ), by
    show (((x : ℚ).den : ℚ)).den.Coprime p; simp⟩
  let dinv : ↥(GaloisRep.ratLocalizedAt p) := ⟨(((x : ℚ).den : ℚ))⁻¹, by
    show ((((x : ℚ).den : ℚ))⁻¹).den.Coprime p
    rw [Rat.inv_natCast_den_of_pos (Nat.pos_of_ne_zero hd0)]; exact hden⟩
  have hdu : IsUnit d := by
    refine IsUnit.of_mul_eq_one dinv (Subtype.ext ?_)
    show ((x : ℚ).den : ℚ) * (((x : ℚ).den : ℚ))⁻¹ = 1
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hd0)
  let n : ↥(GaloisRep.ratLocalizedAt p) := ⟨((x : ℚ).num : ℚ), by
    show (((x : ℚ).num : ℚ)).den.Coprime p; simp⟩
  have hxd : x * d = n := Subtype.ext (Rat.mul_den_eq_num (x : ℚ))
  have hdnat : d = ((x : ℚ).den : ↥(GaloisRep.ratLocalizedAt p)) := Subtype.ext (by push_cast; rfl)
  have hnint : n = ((x : ℚ).num : ↥(GaloisRep.ratLocalizedAt p)) := Subtype.ext (by push_cast; rfl)
  have hfd : f d = g d := by rw [hdnat, map_natCast, map_natCast]
  have hfn : f n = g n := by rw [hnint, map_intCast, map_intCast]
  have h1 : f x * f d = g x * f d := by
    rw [← map_mul, hxd, hfn, hfd, ← map_mul, hxd]
  exact (hdu.map f).mul_left_inj.mp h1

end E2TwoComp

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [Algebra ↥(GaloisRep.ratLocalizedAt p) κ] :
    (minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))).Finite ∧
    (minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))).ncard = 2 := by
  classical

  obtain ⟨-, hn2, -, -⟩ :=
    ModularCurve.IgusaScheme.isReduced_quotient_and_ncard_minimalPrimes_span_natCast_of_not_dvd N p hpN
  obtain ⟨hθex, -⟩ :=
    ModularCurve.IgusaScheme.exists_ringHom_laurentSeries_ker_eq_of_mem_minimalPrimes_of_not_dvd N p hpN
  obtain ⟨𝔮₀, 𝔮₁, hne, hset⟩ := Set.ncard_eq_two.mp hn2
  have h𝔮₀ : 𝔮₀ ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes := by rw [hset]; simp
  have h𝔮₁ : 𝔮₁ ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes := by rw [hset]; simp
  obtain ⟨θ₀, hθ₀⟩ := hθex 𝔮₀ h𝔮₀
  obtain ⟨θ₁, hθ₁⟩ := hθex 𝔮₁ h𝔮₁
  let θ : Fin 2 → (↥(chartAlgFin (N * p) p) →+* LaurentSeries (ZMod p)) := ![θ₀, θ₁]
  have hθ : ∀ i, RingHom.ker (θ i) ∈ (Ideal.span {((p : ℕ) : ↥(chartAlgFin (N * p) p))}).minimalPrimes := by
    intro i; fin_cases i
    · show RingHom.ker θ₀ ∈ _; rw [hθ₀]; exact h𝔮₀
    · show RingHom.ker θ₁ ∈ _; rw [hθ₁]; exact h𝔮₁
  have hθne : RingHom.ker (θ 0) ≠ RingHom.ker (θ 1) := by
    show RingHom.ker θ₀ ≠ RingHom.ker θ₁; rw [hθ₀, hθ₁]; exact hne

  let ι : ZMod p →+* κ := ZMod.castHom (dvd_refl p) κ
  have hι : Function.Injective ι := ι.injective
  let g : Fin 2 → (↥(chartAlgFin (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] LaurentSeries κ) := fun i =>
    { (E2TwoComp.mapHom ι).comp (θ i) with
      commutes' := fun r => by
        have h := E2TwoComp.ringHom_ratLocalizedAt_ext
          (((E2TwoComp.mapHom ι).comp (θ i)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(chartAlgFin (N * p) p)))
          (algebraMap ↥(GaloisRep.ratLocalizedAt p) (LaurentSeries κ))
        exact RingHom.congr_fun h r }
  have hg : ∀ i b, g i b = (θ i b).map ι := fun i b => rfl
  let f₀ : κ →ₐ[↥(GaloisRep.ratLocalizedAt p)] LaurentSeries κ :=
    { algebraMap κ (LaurentSeries κ) with
      commutes' := fun r => RingHom.congr_fun (E2TwoComp.ringHom_ratLocalizedAt_ext
        ((algebraMap κ (LaurentSeries κ)).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) κ)) (algebraMap ↥(GaloisRep.ratLocalizedAt p) (LaurentSeries κ))) r }
  have hf₀ : ∀ a, f₀ a = algebraMap κ (LaurentSeries κ) a := fun a => rfl
  let Θ' : Fin 2 → (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] LaurentSeries κ) := fun i =>
    Algebra.TensorProduct.productMap f₀ (g i)
  have hΘ' : ∀ i (a : κ) (b : ↥(chartAlgFin (N * p) p)), Θ' i (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = algebraMap κ (LaurentSeries κ) a * (θ i b).map ι := by
    intro i a b
    simp only [Θ', Algebra.TensorProduct.productMap_apply_tmul, hf₀, hg]
  let Θ : Fin 2 → (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p) →ₐ[κ] LaurentSeries κ) := fun i =>
    { (Θ' i).toRingHom with
      commutes' := fun a => by
        show Θ' i (algebraMap κ (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) a) = algebraMap κ (LaurentSeries κ) a
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        show Algebra.TensorProduct.productMap f₀ (g i) (a ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] 1) = _
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, hf₀] }
  have hΘ : ∀ i (b : ↥(chartAlgFin (N * p) p)), Θ i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = (θ i b).map ι := by
    intro i b
    show Θ' i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = _
    rw [hΘ', map_one, one_mul]
  have hΘg : ∀ i (b : ↥(chartAlgFin (N * p) p)),
      Θ i (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := κ) b) = g i b := by
    intro i b
    show Θ' i ((1 : κ) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) = g i b
    rw [hΘ', map_one, one_mul, hg]

  have hinj : ∀ x, (∀ i, Θ i x = 0) → x = 0 := fun x hx =>
    ModularCurve.IgusaScheme.eq_zero_of_forall_laurentLift_apply_eq_zero_of_not_dvd N p hpN κ θ hθ hθne Θ hΘ x hx

  let P : Fin 2 → Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) := fun i => RingHom.ker (Θ i)
  have hPprime : ∀ i, (P i).IsPrime := fun i => RingHom.ker_isPrime (Θ i)
  have hPinf : P 0 ⊓ P 1 = ⊥ := by
    refine le_bot_iff.mp (fun x hx => ?_)
    rw [Ideal.mem_bot]
    refine hinj x (fun i => ?_)
    fin_cases i
    · exact hx.1
    · exact hx.2
  have hcover : ∀ Q : Ideal (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)), Q.IsPrime → P 0 ≤ Q ∨ P 1 ≤ Q := by
    intro Q hQ
    refine hQ.mul_le.mp ?_
    exact (Ideal.mul_le_inf).trans (hPinf.le.trans bot_le)

  have hcomap : ∀ i, (P i).comap (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := κ) :
      ↥(chartAlgFin (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) = RingHom.ker (θ i) := by
    intro i
    ext b
    simp only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.coe_toRingHom, hΘg]
    constructor
    · intro h
      apply E2TwoComp.mapHom_injective ι hι
      rw [map_zero]; exact h
    · intro h
      show (E2TwoComp.mapHom ι) (θ i b) = 0
      simp [h]
  have hnotle : ∀ i j, i ≠ j → ¬ P i ≤ P j := by
    intro i j hij hle
    have hle' : RingHom.ker (θ i) ≤ RingHom.ker (θ j) := by
      have h := Ideal.comap_mono (f := (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := κ) :
        ↥(chartAlgFin (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)] κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p))) hle
      simp only [hcomap] at h
      exact h
    have hji : RingHom.ker (θ j) ≤ RingHom.ker (θ i) :=
      (hθ j).2 ⟨(hθ i).1.1, (hθ i).1.2⟩ hle'
    have heq : RingHom.ker (θ i) = RingHom.ker (θ j) := le_antisymm hle' hji
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact hθne heq
    · exact hθne heq.symm
    · exact hij rfl
  have hP01 : P 0 ≠ P 1 := fun h => hnotle 0 1 (by decide) h.le

  have hmin : ∀ i, P i ∈ minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) := by
    intro i
    refine ⟨⟨hPprime i, bot_le⟩, ?_⟩
    rintro Q ⟨hQ, -⟩ hQle
    rcases hcover Q hQ with h0 | h1
    · fin_cases i
      · exact h0
      · exact absurd (h0.trans hQle) (hnotle 0 1 (by decide))
    · fin_cases i
      · exact absurd (h1.trans hQle) (hnotle 1 0 (by decide))
      · exact h1
  have hset' : minimalPrimes (κ ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(chartAlgFin (N * p) p)) = {P 0, P 1} := by
    ext Q
    constructor
    · intro hQ
      rcases hcover Q hQ.1.1 with h0 | h1
      · have := hQ.2 ⟨hPprime 0, bot_le⟩ h0
        exact Or.inl (le_antisymm this h0)
      · have := hQ.2 ⟨hPprime 1, bot_le⟩ h1
        exact Or.inr (le_antisymm this h1)
    · rintro (rfl | rfl)
      · exact hmin 0
      · exact hmin 1
  refine ⟨?_, ?_⟩
  · rw [hset']; exact Set.toFinite _
  · rw [hset']; exact Set.ncard_pair hP01

end S_ModularCurve_IgusaScheme_finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_finite_minimalPrimes_tensor_chartAlgFin_mul_and_ncard_eq_two_of_not_dvd (solution)
