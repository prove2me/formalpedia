-- Prove2me | solution 1 for ModularCurve.SSHeckeV2.coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/91d7db7d-86fc-5fa3-98ff-1395fd511ba9

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Theorems.Thm_ModularCurve_SSHeckeV2_heckeMultiplier_spec
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul_map_D
import Theorems.Thm_ModularCurve_thetaL_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve ModularCurve

noncomputable section

namespace QReading

theorem qExpansionDiffAlong_D {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L]
    (σ : F →ₐ[K] LaurentSeries L) (y : F) :
    qExpansionDiffAlong σ (KaehlerDifferential.D K F y) = thetaL L (σ y) := by
  have h := qExpansionDiffAlong_smul_map_D (F := F) (F' := F) σ 1 y
  rw [KaehlerDifferential.map_D, one_smul, map_one, one_mul] at h
  exact h

theorem main (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    ((ModularCurve.heckeMultiplier N K ℓ : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K) * thetaL K (jqModC K)
      = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
  haveI := AlgebraicCurve.isScalarTower_along (heckeAlphaC K N ℓ)
  have hspec := SSHeckeV2.heckeMultiplier_spec p hp5 K N hN ℓ hℓN hℓK

  set σ : ↥(charLDegeneracyRoof K N ℓ) →ₐ[K] LaurentSeries K := (charLDegeneracyRoof K N ℓ).val with hσ
  have h := congrArg (qExpansionDiffAlong σ) hspec
  rw [qExpansionDiffAlong_D, qExpansionDiffAlong_smul_map_D] at h

  have hβ : σ (heckeBetaC K N ℓ (jGeomGen K N)) = qExpand K ℓ (jqModC K) := coe_heckeBetaC K N ℓ (jGeomGen K N)
  have hα : σ (algebraMap ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ) (jGeomGen K N)) = jqModC K :=
    coe_heckeAlphaC K N ℓ (jGeomGen K N)
  rw [hβ, hα, thetaL_qExpand] at h
  change σ (heckeMultiplier N K ℓ) * thetaL K (jqModC K) = _
  rw [← h, ← HahnSeries.C_apply, HahnSeries.C_mul_eq_smul]

end QReading

end

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (hℓK : (ℓ : K) ≠ 0) :
    ((ModularCurve.heckeMultiplier N K ℓ : ↥(charLDegeneracyRoof K N ℓ)) : LaurentSeries K) * thetaL K (jqModC K)
      = (ℓ : K) • qExpand K ℓ (thetaL K (jqModC K)) :=
  QReading.main p hp5 K N hN ℓ hℓN hℓK

end S_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero
end P2MW
export P2MW.S_ModularCurve_SSHeckeV2_coe_heckeMultiplier_mul_thetaL_eq_smul_qExpand_of_ne_zero (solution)
