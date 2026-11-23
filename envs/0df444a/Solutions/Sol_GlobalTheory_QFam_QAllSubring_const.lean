-- Prove2me | solution 1 for GlobalTheory.QFam.QAllSubring.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:09:18.545794+00:00
-- url     : https://prove2.me/submissions/bdba5c1a-47f4-42a6-86fc-62a0c8cbf27d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
import Theorems.Thm_GlobalTheory_QFam_hasQ_iff


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
theorem _root_.solution {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩
  · rw [_root_.GlobalTheory.QFam.hasQ_iff]
    intro τ
    have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0
      (fun m hm => by simp [hm])
    simpa using h
  · show (if n = 0 then c else 0) ∈ R
    split_ifs
    · exact hc
    · exact R.zero_mem
end _root_.GlobalTheory.QFam.QAllSubring
end GlobalTheory.QFam.QAllSubring
