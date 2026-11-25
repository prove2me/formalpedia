-- Prove2me | solution 1 for GlobalTheory.T.exists_candidate_borel_move_open_frames_baire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:18:06.610671+00:00
-- url     : https://prove2.me/submissions/4f64056a-7da2-4e78-ae5a-1d4c6c23c8fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaire
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCandidateBorelMoveOpenFramesBaireStatement
import Theorems.Thm_GlobalTheory_baire_one_candidate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (S : Set (GL (Fin r) E)) (a c : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ z ∈ W, ∃ γ ∈ S, ∃ b ∈ Bor X.Ψ r, lact c z = rmul (lact γ (lact a z)) b) → ∃ γ ∈ S, ∃ V : Set (Frame X.Ψ r), IsOpen V ∧ V.Nonempty ∧ V ⊆ X.dom ∧ ∀ x ∈ V, ∃ b ∈ Bor X.Ψ r, lact ((γ * a)⁻¹ * c) x = rmul x b := by
  first | exact @GlobalTheory.baire_one_candidate | exact GlobalTheory.baire_one_candidate | (intros; apply GlobalTheory.baire_one_candidate <;> assumption)
end _root_.GlobalTheory.T
