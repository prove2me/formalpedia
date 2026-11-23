-- Prove2me | solution 1 for GroundTheory.Automorphic.indefJ_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:55.951451+00:00
-- url     : https://prove2.me/submissions/2f57a8a9-3ee3-4c8c-89db-b1f4f0137016

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
open Matrix
open scoped Matrix.Norms.L2Operator
variable (p q : ℕ)
namespace GroundTheory.Automorphic
theorem _root_.solution : (indefJ p q)ᴴ = indefJ p q := by
  rw [indefJ, diagonal_conjTranspose]
  congr 1; funext i; cases i <;> simp
end GroundTheory.Automorphic
