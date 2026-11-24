-- Prove2me | solution 1 for GlobalTheory.RegSS.adj_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:29:20.84059+00:00
-- url     : https://prove2.me/submissions/fa455a77-e777-4122-a3ec-b99149fbc48e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_RegSS_adj_smul
import Theorems.Thm_GlobalTheory_RegSS_adj_one

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
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (e : A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (algebraMap A (Matrix n n A) e) =
      algebraMap A (Matrix n n A) (σ e) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    _root_.GlobalTheory.RegSS.adj_smul, _root_.GlobalTheory.RegSS.adj_one σ hJ]
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
