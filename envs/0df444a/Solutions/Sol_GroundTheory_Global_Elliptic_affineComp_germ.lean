-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.affineComp_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:46:01.01694+00:00
-- url     : https://prove2.me/submissions/a1fa0519-941e-4f7a-99ad-013c907a2d54

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (t s : ℂ) (ht : t ≠ 0) {f : ℂ → ℂ} (hf : Meromorphic f) :
    affineComp t s ht (germ f) = germ fun z ↦ f (t * z + s) := by
  rw [germ_of hf, germ_of (meromorphic_comp_affine hf t s)]
  rfl
end GroundTheory.Global.Elliptic
