-- Prove2me | solution 1 for GlobalTheory.AlgWtHW.conjugate_ne_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:37.301609+00:00
-- url     : https://prove2.me/submissions/dda755df-352c-40af-8d6c-6b498a6eb470

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
theorem _root_.solution (τ : L →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
end GlobalTheory.AlgWtHW
