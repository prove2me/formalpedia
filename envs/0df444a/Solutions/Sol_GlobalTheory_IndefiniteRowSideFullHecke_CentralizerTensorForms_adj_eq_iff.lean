-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:12.499259+00:00
-- url     : https://prove2.me/submissions/8bd30899-1923-4115-a675-3b98bb0d5576

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
open Matrix NumberField
open scoped TensorProduct
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (l m : Matrix n n A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J l = m ↔ _root_.Formalism.UG.cT σ l * J = J * m := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj
  constructor
  · intro h
    rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ,
      Matrix.one_mul]
  · intro h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
end GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
