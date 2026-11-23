-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:14.776889+00:00
-- url     : https://prove2.me/submissions/839b6dcf-ee0d-42dc-91e2-4c9a8049200b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace HasQ
theorem _root_.solution {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ + g τ) (fun n => a n + b n) := by
  intro τ
  simpa only [add_mul] using (hf τ).add (hg τ)
end HasQ
end GlobalTheory.QFam
