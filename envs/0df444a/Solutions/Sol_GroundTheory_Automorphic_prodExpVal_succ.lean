-- Prove2me | solution 1 for GroundTheory.Automorphic.prodExpVal_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.148431+00:00
-- url     : https://prove2.me/submissions/935ade26-ca77-415a-aba2-673d35d1ee6b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord

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
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
namespace GroundTheory.Automorphic
theorem _root_.solution {d : ℕ} (X : Fin (d + 1) → 𝔸) (t : Fin (d + 1) → ℝ) :
    prodExpVal X t = exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ) := by
  simp [prodExpVal, List.ofFn_succ]
end GroundTheory.Automorphic
