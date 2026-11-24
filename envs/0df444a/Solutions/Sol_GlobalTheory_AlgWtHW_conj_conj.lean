-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:36.296678+00:00
-- url     : https://prove2.me/submissions/314faa6d-c658-4dcf-939e-120b0173e98d

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
theorem _root_.solution (φ : L →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := by
  ext x; simp
end GlobalTheory.AlgWtHW
