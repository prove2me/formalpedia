-- Prove2me | solution 1 for GlobalTheory.RegSS.commute_of_mem_genAlg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:05.260177+00:00
-- url     : https://prove2.me/submissions/4d79aaf1-bcf8-4a37-95f2-bf77c10ab3b8

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
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution {M N l : Matrix n n A} (h : N * M = M * N)
    (hl : l ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg M) : N * l = l * N := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg at hl
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hl h).eq
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
