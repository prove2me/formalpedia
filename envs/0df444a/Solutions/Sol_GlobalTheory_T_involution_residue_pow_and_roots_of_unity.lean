-- Prove2me | solution 1 for GlobalTheory.T.involution_residue_pow_and_roots_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:10:41.819976+00:00
-- url     : https://prove2.me/submissions/3ba338ae-f2d3-490d-a745-3d2ae2dbe077

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnityStatement
import Theorems.Thm_GlobalTheory_UnitLemma_InvolRes_residue_pow_and_roots


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ), Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) → (∃ x, residue S (τ x) ≠ residue S x) → (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  first | exact @GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | exact GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | (intros; apply GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots <;> assumption)
end _root_.GlobalTheory.T
