-- Prove2me | solution 1 for GlobalTheory.RootEx.affPt_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:57.016288+00:00
-- url     : https://prove2.me/submissions/cda2bea8-2c66-46b0-bd66-abd125ca9d3e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}
namespace GlobalTheory.RootEx
theorem _root_.solution (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    affPt p x₀ e rs.1.1 rs.1.2 = basePt c (0 : Matrix n n' k) rs.1.1 rs.1.2 + e rs := by
  obtain ⟨⟨r, s⟩, h⟩ := rs
  simp only [affPt, Matrix.add_apply, Matrix.of_apply, dif_pos h]
  congr 1
  rcases r with r | r <;> rcases s with s | s
  · exact h.elim
  all_goals rfl
end GlobalTheory.RootEx
