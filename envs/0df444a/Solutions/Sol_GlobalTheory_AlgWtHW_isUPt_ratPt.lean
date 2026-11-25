-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.isUPt_ratPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:37:48.61552+00:00
-- url     : https://prove2.me/submissions/da11feaa-9c98-434e-aa22-2ec1c2fdd35e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
namespace GlobalTheory.AlgWtHW
theorem _root_.solution (γ₀ : GL (Fin n) L) (h : γ₀ ∈ GQ0 L n) : IsUPt (ratPt γ₀.val) := by
  intro σ
  have h' : γ₀.val * conjT (IsCMField.complexConj L : L →+* L) γ₀.val = 1 := h
  have e : ratPt γ₀.val (ComplexEmbedding.conjugate σ) = (γ₀.val.map (IsCMField.complexConj L : L →+* L)).map σ := by
    ext i j
    simp [ratPt, IsCMField.complexEmbedding_complexConj]
  rw [e]
  have := congrArg (fun M => M.map σ) h'
  simpa [ratPt, conjT, Matrix.map_mul, Matrix.transpose_map] using this
end GlobalTheory.AlgWtHW
