-- Prove2me | solution 1 for ModularCurve.dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/76485080-d23d-5c87-b12e-eb8b70859a13

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

private theorem igT3s_finrank_adjoin_eq_relfinrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (x : F) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F =
      (IntermediateField.adjoin K ({(x : E)} : Set E)).relfinrank F := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin K ({x} : Set F)) =
      IntermediateField.adjoin K ({(x : E)} : Set E) := by
    rw [IntermediateField.lift_adjoin]; simp
  have hle : IntermediateField.adjoin K ({(x : E)} : Set E) ≤ F := by
    rw [← hlift]; exact IntermediateField.lift_le _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  let i : (IntermediateField.adjoin K ({x} : Set F)) ≃+*
      (IntermediateField.adjoin K ({(x : E)} : Set E)) :=
    ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin K ({x} : Set F))).trans
      (IntermediateField.equivOfEq hlift)).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars hle) := RingEquiv.refl _
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  rfl

theorem solution
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (x : ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    [FiniteDimensional
      (IntermediateField.adjoin K
        ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))] :
    ModularCurve.dedekindPsi M ≤
      Module.finrank
        (IntermediateField.adjoin K
          ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
        (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by
  have hn : 0 < Module.finrank (IntermediateField.adjoin K
      ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := Module.finrank_pos
  have h1 : Module.finrank (IntermediateField.adjoin K
      ({x} : Set (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M))))
      (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) =
      (IntermediateField.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K))).relfinrank
        (ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M)) := by
    rw [← hx]
    exact igT3s_finrank_adjoin_eq_relfinrank _ x
  have h2 : (IntermediateField.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K))).relfinrank
      (ModularCurve.modularFunctionFieldFullC K M) = ModularCurve.dedekindPsi M := by
    rw [← ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K M hM]
    exact (igT3s_finrank_adjoin_eq_relfinrank (ModularCurve.modularFunctionFieldFullC K M)
      ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K M⟩).symm
  have hAB : IntermediateField.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K)) ≤
      ModularCurve.modularFunctionFieldFullC K M :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (ModularCurve.jqModC_mem_full K M))
  have hBC : ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) :=
    ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 K M
  have htower := IntermediateField.relfinrank_mul_relfinrank hAB hBC
  rw [h2, ← h1] at htower
  exact Nat.le_of_dvd hn ⟨_, htower.symm⟩

end S_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_le_finrank_adjoin_qExpFunctionFieldC_gamma0 (solution)
