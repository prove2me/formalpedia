-- Prove2me | solution 1 for GlobalTheory.RegSS.adj_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:06:17.324015+00:00
-- url     : https://prove2.me/submissions/2cc9b5f6-22b6-42da-aaba-6dccef322885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_GlobalTheory_RegSS_mem_UJ_iff_mul_adj

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
theorem _root_.solution (σ : A →+* A) {J : Matrix n n A}
    (hJ : IsUnit J.det) {g : GL n A} (hg : g ∈ _root_.Formalism.UG.UJ σ J) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.adj σ J (g : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A) :=
  (Units.inv_eq_of_mul_eq_one_right
    ((_root_.GlobalTheory.RegSS.mem_UJ_iff_mul_adj σ hJ g).1 hg)).symm
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
