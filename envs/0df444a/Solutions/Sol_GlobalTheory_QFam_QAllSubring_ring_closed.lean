-- Prove2me | solution 1 for GlobalTheory.QFam.QAllSubring.ring_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:56:34.580799+00:00
-- url     : https://prove2.me/submissions/e22965d7-d936-486e-8f77-8f8e003252e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionCoeffsInSubringRingClosed
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_const
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_add
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_sub
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_mul
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_pow
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_sum
import Theorems.Thm_GlobalTheory_QFam_QAllSubring_prod

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
theorem _root_.solution : ∀ (R : Subring ℂ) (N : ℕ), 0 < N →
    (∀ c ∈ R, _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ) ∧
    (∀ f (k : ℕ), _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k) ∧
    (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ),
      (∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) →
      (_root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧
        _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  intro R N _
  exact ⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg,
    fun f k hf => _root_.GlobalTheory.QFam.QAllSubring.pow k hf,
    fun κ s f hf => ⟨_root_.GlobalTheory.QFam.QAllSubring.sum s hf,
      _root_.GlobalTheory.QFam.QAllSubring.prod s hf⟩⟩
end _root_.GlobalTheory.QFam.QAllSubring
end GlobalTheory.QFam.QAllSubring
