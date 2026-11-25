-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.charpoly_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:48:03.998079+00:00
-- url     : https://prove2.me/submissions/b8c0d670-4e36-40cc-bf9a-76393472e124

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open Polynomial
universe u
variable {F : Type u} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution (A : Matrix (Fin n) (Fin n) F)
    (m : Module.AEval' (Matrix.toLin' A)) : A.charpoly • m = 0 := by
  have h : aeval (Matrix.toLin' A) A.charpoly = 0 := by
    rw [← Matrix.charpoly_toLin']
    exact LinearMap.aeval_self_charpoly _
  obtain ⟨v, rfl⟩ := (Module.AEval'.of (Matrix.toLin' A)).surjective m
  rw [← Module.AEval.of_aeval_smul, h, zero_smul, map_zero]
end GroundTheory.Automorphic.ContragredientTranspose
