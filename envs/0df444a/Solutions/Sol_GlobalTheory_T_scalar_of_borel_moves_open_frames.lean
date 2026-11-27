-- Prove2me | solution 1 for GlobalTheory.T.scalar_of_borel_moves_open_frames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:33:43.537788+00:00
-- url     : https://prove2.me/submissions/e7a68036-a18c-49c1-9ed5-9b3d9307778a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalarOfBorelMovesOpenFrames
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScalarOfBorelMovesOpenFramesStatement
import Theorems.Thm_GlobalTheory_scalar_of_triangular_moves_open


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
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  first | exact @GlobalTheory.scalar_of_triangular_moves_open | exact GlobalTheory.scalar_of_triangular_moves_open | (intros; apply GlobalTheory.scalar_of_triangular_moves_open <;> assumption)
end _root_.GlobalTheory.T
