-- Prove2me | solution 1 for GlobalTheory.RegSS.genAlg_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:08:49.841931+00:00
-- url     : https://prove2.me/submissions/ac46719d-b659-4613-8b29-676be461a8dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n E} {γ : GL n E}
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.IsRegular σ J γ) (hA : _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.ClauseAlg σ J γ) :
    IsReduced (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) := by
  have := h.quad.etale
  have := hA.2.1
  have : Algebra.Etale F (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg (γ : Matrix n n E)) :=
    Algebra.Etale.comp F E _
  exact Algebra.FormallyUnramified.isReduced_of_field F _
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
