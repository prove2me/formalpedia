-- Prove2me | solution 1 for GlobalTheory.HypRot.rot_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:37:21.611651+00:00
-- url     : https://prove2.me/submissions/5d037992-2852-470c-aa79-419f47b21813

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
import Theorems.Thm_GlobalTheory_HypRot_offN_neg
import Theorems.Thm_GlobalTheory_HypRot_offN_sq
import Theorems.Thm_GlobalTheory_HypRot_projP_offN
import Theorems.Thm_GlobalTheory_HypRot_offN_projP
import Theorems.Thm_GlobalTheory_HypRot_projP_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.HypRot
variable {r : ℕ}
namespace GlobalTheory.HypRot
theorem _root_.solution {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    offN j k u = (4 / 15 : ℂ) • (rot j k u * rot j k u - rot j k (-u) * rot j k (-u)) := by
  have hPP := projP_sq h
  have hPN := projP_offN h u
  have hNP := offN_projP h u
  have hNN := offN_sq h hu
  simp only [rot, offN_neg, smul_neg, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_neg, neg_mul, hPP, hPN, hNP, hNN]
  module
end GlobalTheory.HypRot
