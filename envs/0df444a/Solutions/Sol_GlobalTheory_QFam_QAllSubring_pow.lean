-- Prove2me | solution 1 for GlobalTheory.QFam.QAllSubring.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:41:22.201236+00:00
-- url     : https://prove2.me/submissions/85146d57-79e9-46af-bf10-0a6ce691d615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_const
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam GlobalTheory.QFam.QAllSubring
variable {R : Subring ℂ} {N : ℕ}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
variable {R : Subring ℂ} {N : ℕ}
namespace GlobalTheory.QFam.QAllSubring
namespace _root_.GlobalTheory.QFam.QAllSubring
theorem _root_.solution {f : ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf
end _root_.GlobalTheory.QFam.QAllSubring
end GlobalTheory.QFam.QAllSubring
