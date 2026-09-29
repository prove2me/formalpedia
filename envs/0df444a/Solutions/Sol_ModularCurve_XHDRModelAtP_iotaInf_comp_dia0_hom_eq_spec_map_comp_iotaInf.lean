-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.iotaInf_comp_dia0_hom_eq_spec_map_comp_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3e5d8d8b-c864-5030-9ee7-5bc16dd1475f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_XHDRModelAtP_iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf
import Theorems.Thm_ModularCurve_exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm
import Theorems.Thm_ModularCurve_coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia0_hom_eq_spec_map_comp_iotaInf
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

namespace Dia0Inf

theorem xHFunctionFieldBar_div_le (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) :
    xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H := by
  have h : xHFunctionField (M / p) (infSubgroup p M H hpM) ≤ xHFunctionField M H :=
    qExpFunctionFieldC_mono ℚ (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM)
  show laurentBaseChange (AlgebraicClosure ℚ) _ ≤ laurentBaseChange (AlgebraicClosure ℚ) _
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (h hy)

theorem coe_diamondAutHBar_symm_eq (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    [NeZero (M / p)] (d : (ZMod M)ˣ)
    (x : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hxu : (x : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    (((diamondAutHBar M H d).symm x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).symm u :
        ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) := by
  set u' := (diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).symm u with hu'
  let x' : ↥(xHFunctionFieldBar M H) := ⟨(u' : LaurentSeries (AlgebraicClosure ℚ)), xHFunctionFieldBar_div_le p M H hpM u'.2⟩
  have h1 := ModularCurve.coe_diamondAutHBar_eq_coe_diamondAutHBar_div_of_coe_eq p M H hpM d x' u' rfl
  rw [hu', AlgEquiv.apply_symm_apply, ← hxu] at h1
  have h2 : diamondAutHBar M H d x' = x := Subtype.ext h1
  rw [← h2, AlgEquiv.symm_apply_apply]

end Dia0Inf

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) (e : (ZMod (M / p))ˣ)
    (σ : ↥(chartAlgInf p (ΓN p M H hpM) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓN p M H hpM) hj))
    (hσ : ∀ b : ↥(chartAlgInf p (ΓN p M H hpM) hj),
      coeffEmb (AlgebraicClosure ℚ) (((σ b : ↥(chartAlgInf p (ΓN p M H hpM) hj)) : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) =
        (((diamondAutHBar (M / p) (infSubgroup p M H hpM) e).symm
            ⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))).2⟩
          : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ))) :
    ιInf p (ΓN p M H hpM) hj ≫ (𝔛.dia0 e).hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj := by
  haveI := 𝔛.isProper0

  obtain ⟨d, rfl⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) e

  obtain ⟨σM, hσM⟩ := ModularCurve.exists_algEquiv_chartAlgInf_forall_coeffEmb_eq_diamondAutHBar_symm p M H hj d
  have hsq := ModularCurve.XHDRModelAtP.iotaInf_comp_dia_hom_eq_spec_map_comp_iotaInf 𝔛 d σM hσM

  have hinj : Function.Injective 𝔛.iotaInf := by
    intro a b h
    apply Subtype.ext; apply Subtype.ext
    rw [← 𝔛.iotaInf_spec a, ← 𝔛.iotaInf_spec b, h]

  have hcompat : 𝔛.iotaInf.toRingHom.comp σ.toRingEquiv.toRingHom = σM.toRingEquiv.toRingHom.comp 𝔛.iotaInf.toRingHom := by
    refine RingHom.ext fun b => ?_
    show 𝔛.iotaInf (σ b) = σM (𝔛.iotaInf b)
    apply Subtype.ext; apply Subtype.ext
    apply (coeffEmb (AlgebraicClosure ℚ)).injective
    rw [𝔛.iotaInf_spec (σ b), hσ b, hσM (𝔛.iotaInf b)]
    refine (Dia0Inf.coe_diamondAutHBar_symm_eq p M H hpM d _ _ ?_).symm
    show coeffEmb (AlgebraicClosure ℚ) _ = coeffEmb (AlgebraicClosure ℚ) _
    rw [𝔛.iotaInf_spec b]

  have key : Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj ≫
        (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom =
      Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom) ≫
        Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj := by
    calc Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj ≫
          (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom
        = ιInf p (ΓM M H) hj ≫ 𝔛.π.1 ≫ (𝔛.dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom := by
          rw [← Category.assoc, ← 𝔛.pi_chartInf, Category.assoc]
      _ = ιInf p (ΓM M H) hj ≫ (𝔛.dia d).hom ≫ 𝔛.π.1 := by rw [𝔛.pi_dia d]
      _ = Spec.map (CommRingCat.ofHom σM.toRingEquiv.toRingHom) ≫ ιInf p (ΓM M H) hj ≫ 𝔛.π.1 := by
          rw [← Category.assoc, hsq, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom σM.toRingEquiv.toRingHom) ≫
            Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj := by rw [𝔛.pi_chartInf]
      _ = Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom) ≫
            Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj := by
          rw [← Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp, ← Spec.map_comp,
            ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcompat]

  haveI : IsDominant (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)) := ⟨by
    show DenseRange (PrimeSpectrum.comap 𝔛.iotaInf.toRingHom)
    have hk : RingHom.ker 𝔛.iotaInf.toRingHom = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot 𝔛.iotaInf.toRingHom).mp fun a b h => hinj h
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, hk]
    exact bot_le⟩
  refine ext_of_isDominant_of_isSeparated (toBase p (ΓN p M H hpM) hj) ?_
    (Spec.map (CommRingCat.ofHom 𝔛.iotaInf.toRingHom)) key
  rw [Category.assoc, 𝔛.dia0_over, Category.assoc, TwoChartIntegralModel.ιInf_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => (σ.commutes r).symm

end S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia0_hom_eq_spec_map_comp_iotaInf
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_iotaInf_comp_dia0_hom_eq_spec_map_comp_iotaInf (solution)
