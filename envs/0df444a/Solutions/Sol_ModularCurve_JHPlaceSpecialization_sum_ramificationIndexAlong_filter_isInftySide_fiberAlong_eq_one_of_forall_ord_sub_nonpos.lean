-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d7ee6ed0-bc19-54b0-9293-036b152d2ec7

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import Theorems.Thm_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_le_sum_ramificationIndexAlong_filter_not_isInftySide_fiberAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace WeightOneH

theorem sum_fiber_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    (∑ W ∈ Place.fiberAlong α hα b, (W.ramificationIndexAlong α : ℤ)) = (p : ℤ) + 1 := by
  have hT : ∀ (L : ℕ) (H₀ : Subgroup (ZMod L)ˣ), ModularGroup.T ∈ CohCarrier.GammaH L H₀ := fun L H₀ => by
    apply ModularCurve.Gamma1_le_GammaH
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  haveI : (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hfin : FiniteAlong (AlgebraicClosure ℚ) α :=
    ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (hT _ _) (hT _ _) α
  haveI : CharZero ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
  have hsep : SeparableAlong (AlgebraicClosure ℚ) α := AlgebraicCurve.separableAlong_of_charZero α hα
  have hsum := AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong α hα hfin hsep b
  rw [ModularCurve.finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe] at hsum
  have h1 : ∀ W ∈ Place.fiberAlong α hα b,
      (W.ramificationIndexAlong α : ℤ) * (W.inertiaDegAlong α hα : ℤ) = (W.ramificationIndexAlong α : ℤ) := fun W _ => by
    have h761 : W.inertiaDegAlong α hα = 1 :=
      ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange_qExpFunctionFieldC (L := AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (hT _ _)
        (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) rfl α hα W
    rw [h761, Nat.cast_one, mul_one]
  rw [Finset.sum_congr rfl h1] at hsum
  rw [hsum]
  push_cast
  ring

end WeightOneH

open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hb : ∀ x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∀ a : ↥A, b.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    (∑ W ∈ (Place.fiberAlong α hα b).filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)),
        (W.ramificationIndexAlong α : ℤ)) = 1 := by
  obtain ⟨W₀, hW₀, hinf₀⟩ := ModularCurve.JHPlaceSpecialization.exists_restrictAlong_eq_and_isInftySide_of_forall_ord_sub_nonpos
    p M H hpM hpM2 hHp A hA α hα hα_coe b hb
  have htot := WeightOneH.sum_fiber_eq p M H hpM hpM2 hHp α hα hα_coe b
  have hnn : ∀ W ∈ Place.fiberAlong α hα b, (0 : ℤ) ≤ (W.ramificationIndexAlong α : ℤ) := fun W _ => by positivity
  have hone : (1 : ℤ) ≤ (W₀.ramificationIndexAlong α : ℤ) := by
    exact_mod_cast AlgebraicCurve.Place.one_le_ramificationIndexAlong α hα W₀
  have hW₀mem : W₀ ∈ Place.fiberAlong α hα b := Place.mem_fiberAlong.mpr hW₀
  have hlow : (1 : ℤ) ≤ ∑ W ∈ (Place.fiberAlong α hα b).filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)),
      (W.ramificationIndexAlong α : ℤ) :=
    hone.trans (Finset.single_le_sum (fun W hW => hnn W (Finset.mem_filter.mp hW).1) (Finset.mem_filter.mpr ⟨hW₀mem, hinf₀⟩))
  have hcomp := ModularCurve.JHPlaceSpecialization.le_sum_ramificationIndexAlong_filter_not_isInftySide_fiberAlong
    p M H hpM hpM2 hHp A hA α hα hα_coe b
  have hsplit : (∑ W ∈ (Place.fiberAlong α hα b).filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)),
        (W.ramificationIndexAlong α : ℤ))
      + (∑ W ∈ (Place.fiberAlong α hα b).filter (fun W => ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W),
        (W.ramificationIndexAlong α : ℤ))
      = ∑ W ∈ Place.fiberAlong α hα b, (W.ramificationIndexAlong α : ℤ) := by
    convert Finset.sum_filter_add_sum_filter_not (Place.fiberAlong α hα b) (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))
      (fun W => (W.ramificationIndexAlong α : ℤ))
  rw [htot] at hsplit
  omega

end S_ModularCurve_JHPlaceSpecialization_sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos (solution)
