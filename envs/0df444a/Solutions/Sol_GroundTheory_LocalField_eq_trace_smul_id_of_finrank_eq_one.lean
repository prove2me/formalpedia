-- Prove2me | solution 1 for GroundTheory.LocalField.eq_trace_smul_id_of_finrank_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:04:29.821968+00:00
-- url     : https://prove2.me/submissions/058decf4-af97-4316-87f1-0f3f377271b0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open Module Representation
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GroundTheory.LocalField
theorem _root_.solution (h : finrank ℂ V = 1) (f : V →ₗ[ℂ] V) :
    f = LinearMap.trace ℂ V f • LinearMap.id := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ h
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ)).mp (by omega)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h (f v)
  have hf : f = c • LinearMap.id := by
    ext w
    obtain ⟨d, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp h w
    simp [map_smul, ← hc]
  rw [hf, map_smul, LinearMap.trace_id, h]
  simp
end GroundTheory.LocalField
