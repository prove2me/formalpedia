-- Prove2me | solution 1 for ModularCurve.cuspidalClass_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f2a6e6f3-89b7-5cd5-828f-5f41175d21fa

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cuspidalClass_ne_zero
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

theorem solution (p : ℕ) [Fact p.Prime]
    (hp : p ∉ ({2, 3, 5, 7, 13} : Finset ℕ)) :
    cuspidalClass p ≠ 0 := by
  classical
  have hprime : p.Prime := Fact.out
  haveI : NeZero p := ⟨hprime.ne_zero⟩
  intro h0

  have hprin : Divisor.IsPrincipal
      (Finsupp.single (cuspZeroBar p) 1 - Finsupp.single (cuspInftyBar p) 1 :
        Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p)) := by
    have h1 : (QuotientAddGroup.mk (cuspidalDivisor₀ p) : JZero p) = 0 := h0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    exact h1

  have hne : cuspZeroBar p ≠ cuspInftyBar p :=
    cuspZeroBar_ne_cuspInftyBar p (isFrickeAutFull_frickeInvolutionFull_prime p) hprime.one_lt
  have hdeg : (cuspInftyBar p).deg = 1 := deg_cuspInftyBar p

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) := isCurveOver_modularFunctionFieldBar p
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) := IsCurveOver.hasPrincipalDivisors
  haveI : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar p)) :=
    hasCanonicalDivisor_modularFunctionFieldBar p
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) :=
    essFiniteType_modularFunctionFieldBar p
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver

  letI algRE : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar p) := (jLineBarRingEquiv p).toRingHom.toAlgebra
  letI algRF : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar p) :=
    ((algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p)).comp (jLineBarRingEquiv p).toRingHom).toAlgebra
  haveI : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar p) ↥(modularFunctionFieldBar p) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar p) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show algebraMap _ _ a = algebraMap ↥(jLineBar p) ↥(modularFunctionFieldBar p) (jLineBarRingEquiv p (algebraMap _ _ a))
    rw [jLineBarRingEquiv_algebraMap]
    rfl
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar p) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar p))
      (jLineBarRingEquiv p).surjective
  haveI : FiniteDimensional ↥(jLineBar p) ↥(modularFunctionFieldBar p) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero p
  haveI hfinRF : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar p) :=
    Module.Finite.trans ↥(jLineBar p) ↥(modularFunctionFieldBar p)
  haveI : Algebra.IsIntegral (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar p) :=
    Algebra.IsIntegral.of_finite _ _
  haveI : CharZero ↥(modularFunctionFieldBar p) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  haveI : PerfectField (RatFunc (AlgebraicClosure ℚ)) := PerfectField.ofCharZero
  haveI : Algebra.IsSeparable (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar p) :=
    Algebra.IsSeparable.of_integral _ _
  haveI : IsCurveOver (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    AlgebraicCurve.instIsCurveOverRatFunc (AlgebraicClosure ℚ)
  haveI : Algebra.EssFiniteType (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial (AlgebraicClosure ℚ)))
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) :=
    Algebra.EssFiniteType.comp (AlgebraicClosure ℚ) (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ))
  haveI hDCGR : ∀ v : Place (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver

  haveI : HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) := inferInstance
  haveI : HasSeparableResidue (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) := inferInstance

  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed
  have hC : ConstantsAreBase (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) :=
    AlgebraicCurve.constantsAreBase_of_isAlgClosed _ _

  have hg0 : genus (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p) = 0 :=
    AlgebraicCurve.genus_eq_zero_of_isPrincipal_single_sub_single hRR hC hne hdeg hprin

  have h2 : p ≠ 2 := by rintro rfl; exact hp (by decide)
  have hodd : Odd p := hprime.odd_of_ne_two h2
  have hgen := ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime p hodd
  rw [hg0, Nat.cast_zero] at hgen
  have hψ := ModularCurve.dedekindPsi_prime hprime
  have hc := ModularCurve.cuspCount_prime hprime
  have h3 : p ≠ 3 := fun h => hp (by simp [h])
  have hν2 := ModularCurve.nuTwo_prime hprime h2
  have hν3 := ModularCurve.nuThree_prime hprime h3
  have hν2le : nuTwo p ≤ 2 := by rw [hν2]; split_ifs <;> norm_num
  have hν3le : nuThree p ≤ 2 := by rw [hν3]; split_ifs <;> norm_num
  have key : ((p : ℚ) + 1) = 3 * (nuTwo p : ℚ) + 4 * (nuThree p : ℚ) := by
    unfold ModularCurve.genusFormula at hgen
    rw [hψ, hc] at hgen
    push_cast at hgen
    linarith
  have keyN : p + 1 = 3 * nuTwo p + 4 * nuThree p := by exact_mod_cast key
  have hp13 : p ≤ 13 := by omega
  have hp11 : p = 11 := by
    interval_cases p
    all_goals first
      | rfl
      | exact absurd hprime (by decide)
      | exact absurd (by decide) hp
  subst hp11
  norm_num at hν2 hν3
  omega

end S_ModularCurve_cuspidalClass_ne_zero
end P2MW
export P2MW.S_ModularCurve_cuspidalClass_ne_zero (solution)
