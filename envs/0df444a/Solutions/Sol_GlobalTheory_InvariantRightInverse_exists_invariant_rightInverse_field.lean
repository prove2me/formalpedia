-- Prove2me | solution 1 for GlobalTheory.InvariantRightInverse.exists_invariant_rightInverse_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:08:36.370921+00:00
-- url     : https://prove2.me/submissions/055c6206-622a-44aa-aec4-2c561d28492a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInvariantRightInverseField
import Theorems.Thm_GlobalTheory_InvariantRightInverse_exists_rightInverse_subfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InvariantRightInverse
namespace GlobalTheory.InvariantRightInverse
theorem _root_.solution {L : Type} [Field L] (G : Type)
    (act : G → L →+* L) (N b : Type) [Fintype N] [DecidableEq b]
    (κ : Matrix b N L) (Y : Matrix N b L) (h : κ * Y = 1)
    (hκ : ∀ g : G, Matrix.map κ (⇑(act g) : L → L) = κ) :
    ∃ Λ : Matrix N b L, κ * Λ = 1 ∧ ∀ g : G, Matrix.map Λ (⇑(act g) : L → L) = Λ := by
  have hK : ∀ x : L, x ∈ (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) ↔
      ∀ g, act g x = x := by
    intro x
    rw [Subfield.mem_iInf]
    exact Iff.rfl
  obtain ⟨Λ, h1, h2⟩ := exists_rightInverse_subfield
    (⨅ g : G, RingHom.eqLocusField (act g) (RingHom.id L)) κ Y h
    (fun i k => (hK _).2 (fun g => congrFun (congrFun (hκ g) i) k))
  refine ⟨Λ, h1, fun g => ?_⟩
  ext k j
  exact (hK _).1 (h2 k j) g
end GlobalTheory.InvariantRightInverse
