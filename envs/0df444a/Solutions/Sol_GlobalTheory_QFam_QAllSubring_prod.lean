-- Prove2me | solution 1 for GlobalTheory.QFam.QAllSubring.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:41:28.433366+00:00
-- url     : https://prove2.me/submissions/04e1af02-6287-4650-a401-26f5c2e59a31

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
theorem _root_.solution {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
end _root_.GlobalTheory.QFam.QAllSubring
end GlobalTheory.QFam.QAllSubring
