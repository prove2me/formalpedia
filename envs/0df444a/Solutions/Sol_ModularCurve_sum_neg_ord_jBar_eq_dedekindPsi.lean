-- Prove2me | solution 1 for ModularCurve.sum_neg_ord_jBar_eq_dedekindPsi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a3e6b6fd-f826-5988-85fd-7af515731c8b

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_sum_ord_jBar_sub_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

theorem solution (N : ℕ) [NeZero N]
    (S : Finset (AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N)))
    (hS : ∀ v, v ∈ S ↔ v.ord (ModularCurve.jBar N) < 0) :
    ∑ v ∈ S, -v.ord (ModularCurve.jBar N) = ModularCurve.dedekindPsi N := by
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  have hHPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    IsCurveOver.hasPrincipalDivisors
  have hdeg : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  have hne : jBar N ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : ↥(modularFunctionFieldBar N) => (f : LaurentSeries (AlgebraicClosure ℚ))) h
    simp only [ZeroMemClass.coe_zero] at h1
    exact jq_ne_zero ((map_eq_zero_iff _ (coeffEmb (AlgebraicClosure ℚ)).injective).mp h1)

  obtain ⟨D, hD, hdeg0⟩ := hHPD.exists_divisor (jBar N) hne
  have hdegD : Divisor.degree D = ∑ v ∈ D.support, v.ord (jBar N) := by
    show Finsupp.liftAddHom (fun v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) =>
        AddMonoidHom.mulRight (v.deg : ℤ)) D = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [AddMonoidHom.mulRight_apply, hD, hdeg, Nat.cast_one, mul_one]
  have hsupp : ∀ v, v ∈ D.support ↔ v.ord (jBar N) ≠ 0 := fun v => by
    rw [Finsupp.mem_support_iff, hD]

  set Sp := D.support.filter (fun v => 0 < v.ord (jBar N)) with hSpdef
  have hSp : ∀ v, v ∈ Sp ↔
      0 < v.ord (jBar N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 0) := by
    intro v
    rw [map_zero, sub_zero, hSpdef, Finset.mem_filter, hsupp]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.ne', h⟩
  have hzero := sum_ord_jBar_sub_eq_dedekindPsi N 0 hdeg Sp hSp
  simp only [map_zero, sub_zero] at hzero

  have hSeq : D.support.filter (fun v => ¬ 0 < v.ord (jBar N)) = S := by
    ext v
    rw [Finset.mem_filter, hsupp, hS]
    omega
  have hsplit := Finset.sum_filter_add_sum_filter_not D.support (fun v => 0 < v.ord (jBar N))
    (fun v => v.ord (jBar N))
  rw [← hdegD, hdeg0, ← hSpdef, hzero, hSeq] at hsplit
  rw [Finset.sum_neg_distrib]
  linarith

end S_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi
end P2MW
export P2MW.S_ModularCurve_sum_neg_ord_jBar_eq_dedekindPsi (solution)
