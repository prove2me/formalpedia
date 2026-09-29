-- Prove2me | solution 1 for ModularCurve.genus_modularFunctionFieldBar_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/68d0bdc5-ba52-5df8-9a14-133ce0392923

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_JLinePlacesBar
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstance
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_deg_cuspInftyBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_AlgebraicCurve_instIsCurveOverRatFunc
import Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula_of_prime
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_nuTwo_prime
import Theorems.Thm_ModularCurve_nuThree_prime
import Theorems.Thm_ModularCurve_cuspCount_prime
import Theorems.Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_addOrderOf_cuspidalClass_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genus_modularFunctionFieldBar_two
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve AlgebraicCurve IntermediateField

attribute [local instance] ModularCurve.instDecidableEqRatFuncAlgebraicClosure

theorem solution
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar 2))] :
    AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar 2) = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprime : (2 : ℕ).Prime := Nat.prime_two
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩

  have h0 : cuspidalClass 2 = 0 := by
    have hd : addOrderOf (cuspidalClass 2) ∣ 2 - 1 := ModularCurve.addOrderOf_cuspidalClass_dvd 2
    have hd1 : addOrderOf (cuspidalClass 2) ∣ 1 := by simpa only [show (2 : ℕ) - 1 = 1 from rfl] using hd
    exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

  have hprin : Divisor.IsPrincipal
      (Finsupp.single (cuspZeroBar 2) 1 - Finsupp.single (cuspInftyBar 2) 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2)) := by
    have h1 : (QuotientAddGroup.mk (cuspidalDivisor₀ 2) : JZero 2) = 0 := h0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    exact h1

  have hne : cuspZeroBar 2 ≠ cuspInftyBar 2 :=
    cuspZeroBar_ne_cuspInftyBar 2 (isFrickeAutFull_frickeInvolutionFull_prime 2) (by norm_num)
  have hdeg : (cuspInftyBar 2).deg = 1 := deg_cuspInftyBar 2

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) := isCurveOver_modularFunctionFieldBar 2
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) := IsCurveOver.hasPrincipalDivisors
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) :=
    essFiniteType_modularFunctionFieldBar 2
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver

  letI algRE : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar 2) := (jLineBarRingEquiv 2).toRingHom.toAlgebra
  letI algRF : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar 2) :=
    ((algebraMap ↥(jLineBar 2) ↥(modularFunctionFieldBar 2)).comp (jLineBarRingEquiv 2).toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar 2) ↥(modularFunctionFieldBar 2) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar 2) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show algebraMap _ _ a = algebraMap ↥(jLineBar 2) ↥(modularFunctionFieldBar 2) (jLineBarRingEquiv 2 (algebraMap _ _ a))
    rw [jLineBarRingEquiv_algebraMap]
    rfl
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar 2) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar 2))
      (jLineBarRingEquiv 2).surjective
  haveI : FiniteDimensional ↥(jLineBar 2) ↥(modularFunctionFieldBar 2) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero 2
  haveI hfinRF : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar 2) :=
    Module.Finite.trans ↥(jLineBar 2) ↥(modularFunctionFieldBar 2)
  haveI : Algebra.IsIntegral (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar 2) :=
    Algebra.IsIntegral.of_finite _ _
  haveI : CharZero ↥(modularFunctionFieldBar 2) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : PerfectField (RatFunc (AlgebraicClosure ℚ)) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar 2) :=
    Algebra.IsSeparable.of_integral _ _
  haveI : IsCurveOver (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    AlgebraicCurve.instIsCurveOverRatFunc (AlgebraicClosure ℚ)
  haveI : Algebra.EssFiniteType (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)))
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.comp (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
  haveI hDCGR : ∀ v : Place (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver

  haveI : HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) := inferInstance
  haveI : HasSeparableResidue (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) := inferInstance

  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed
  have hC : ConstantsAreBase (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) :=
    AlgebraicCurve.constantsAreBase_of_isAlgClosed _ _

  have hg0 : genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 2) = 0 :=
    AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single hRR hC hne hdeg hprin
  exact hg0

end S_ModularCurve_genus_modularFunctionFieldBar_two
end P2MW
export P2MW.S_ModularCurve_genus_modularFunctionFieldBar_two (solution)
