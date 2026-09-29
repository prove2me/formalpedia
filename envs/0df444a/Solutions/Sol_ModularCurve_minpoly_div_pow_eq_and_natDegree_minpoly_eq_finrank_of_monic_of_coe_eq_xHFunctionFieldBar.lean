-- Prove2me | solution 1 for ModularCurve.minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c62244cf-52bf-54dd-8766-5f19a7c1f75f

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

open Polynomial ModularCurve AlgebraicCurve
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx₀ : (x₀ : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x' : ↥(xHFunctionFieldBar M H))
    (hx' : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      (x' : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)))
    (P : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hPm : P.Monic) (hPd : P.natDegree = p + 1)
    (hPt : P.eval₂ α.toRingHom (x' / (α x₀) ^ p) = 0) :
    @minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) _ _
        (AlgebraicCurve.algebraAlong α) (x' / (α x₀) ^ p) = P ∧
      (@minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) _ _
        (AlgebraicCurve.algebraAlong α) (x' / (α x₀) ^ p)).natDegree = AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) α := by
  classical
  letI inst1 : Algebra ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.algebraAlong α
  haveI : IsScalarTower (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.isScalarTower_along α
  letI instM : Module ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := inst1.toModule
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have halg : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) u = α u := fun _ => rfl

  have hfrA : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) α = p + 1 :=
    ModularCurve.finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe
  have hfr : Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) = p + 1 := by rw [← hfrA]; rfl
  haveI : Module.Finite ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := Module.finite_of_finrank_pos (by rw [hfr]; omega)

  have hx0 : (α x₀ : ↥(xHFunctionFieldBar M H)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1 : ℤ)) h0
    simp only [hα_coe, hx₀, ZeroMemClass.coe_zero] at h1
    rw [ModularCurve.coeff_jqModC_neg_one] at h1
    exact one_ne_zero (h1.trans (HahnSeries.coeff_zero (Γ := ℤ) (R := AlgebraicClosure ℚ) (a := -1)))
  set t : ↥(xHFunctionFieldBar M H) := x' / (α x₀) ^ p with ht

  have hQFt : Polynomial.aeval t P = 0 := hPt
  have hint : IsIntegral ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) t := ⟨P, hPm, hPt⟩

  have htop : IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ({t} : Set ↥(xHFunctionFieldBar M H)) = ⊤ := by
    set S := IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ({t} : Set ↥(xHFunctionFieldBar M H)) with hS

    set W : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
      (S.restrictScalars (AlgebraicClosure ℚ)).map (xHFunctionFieldBar M H).val with hW
    have htS : t ∈ S := IntermediateField.mem_adjoin_simple_self _ t
    have hx'S : x' ∈ S := by
      have hx'eq : x' = t * (α x₀) ^ p := by rw [ht, div_mul_cancel₀ _ (pow_ne_zero _ hx0)]
      rw [hx'eq]
      exact mul_mem htS (pow_mem (show (α x₀ : ↥(xHFunctionFieldBar M H)) ∈ S from (halg x₀) ▸ algebraMap_mem S x₀) _)
    have hle : xHFunctionFieldBar M H ≤ W := by
      have hgen := ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar p M H hpM hpM2 hHp
      rw [← hgen]
      refine sup_le ?_ ?_
      · intro u hu
        rw [hW, IntermediateField.mem_map]
        refine ⟨α ⟨u, hu⟩, ?_, ?_⟩
        · change (α ⟨u, hu⟩ : ↥(xHFunctionFieldBar M H)) ∈ S
          rw [← halg]
          exact algebraMap_mem S _
        · rw [IntermediateField.coe_val]
          exact hα_coe ⟨u, hu⟩
      · rw [IntermediateField.adjoin_simple_le_iff, hW, IntermediateField.mem_map]
        exact ⟨x', (show x' ∈ S from hx'S), by rw [IntermediateField.coe_val]; exact hx'⟩
    rw [eq_top_iff]
    intro z _
    have hz : (z : LaurentSeries (AlgebraicClosure ℚ)) ∈ W := hle z.2
    rw [hW, IntermediateField.mem_map] at hz
    obtain ⟨s, hs, hsz⟩ := hz
    rw [IntermediateField.coe_val] at hsz
    change s ∈ S at hs
    rwa [show z = s from (Subtype.ext hsz).symm]

  have hdeg : (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) t).natDegree = Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top']
  show minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) t = P ∧ (minpoly ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) t).natDegree = AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) α
  refine ⟨?_, by rw [hdeg, hfr, hfrA]⟩
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPm (minpoly.dvd ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) t hQFt)
    (by rw [hPd, hdeg, hfr])).symm

end S_ModularCurve_minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar (solution)
