-- Prove2me | solution 1 for GlobalTheory.QFam.HasQ.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:35.409848+00:00
-- url     : https://prove2.me/submissions/45c7fa46-5f03-4185-a256-5bd01422b7b3

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
theorem _root_.solution (N : ℕ) (c : ℂ) :
    HasQ N (fun _ => c) (fun n => if n = 0 then c else 0) := by
  intro τ
  have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) 0
    (fun m hm => by simp [hm])
  simpa using h
end HasQ
end GlobalTheory.QFam
