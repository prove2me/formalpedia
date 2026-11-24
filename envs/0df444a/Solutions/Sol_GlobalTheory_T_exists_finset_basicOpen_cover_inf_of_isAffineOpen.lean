-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:49.706258+00:00
-- url     : https://prove2.me/submissions/910b60a5-6371-4a95-b1e6-ba1c77b6966f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Theorems.Thm_GlobalTheory_affine_inter_finite_basicOpen_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V → ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧ ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  first | exact @GlobalTheory.affine_inter_finite_basicOpen_cover | exact GlobalTheory.affine_inter_finite_basicOpen_cover | (intros; apply GlobalTheory.affine_inter_finite_basicOpen_cover <;> assumption)
end _root_.GlobalTheory.T
