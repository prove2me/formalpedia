-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.sg_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:57.913107+00:00
-- url     : https://prove2.me/submissions/94732a43-6e76-4d94-80cb-97ef3676120c

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_zero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open GlobalTheory GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace
variable {n : ℕ}
namespace GlobalTheory.GrassModel.SuperTrace
theorem _root_.solution {ι : Type*} (s : Finset ι) (m : ℕ) (f : ι → Big n) (h : ∀ i ∈ s, Sg m (f i)) :
    Sg m (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using sg_zero m
  | cons x s hx ih =>
    rw [Finset.sum_cons]
    exact sg_add (h x (by simp)) (ih fun i hi => h i (by simp [hi]))
end GlobalTheory.GrassModel.SuperTrace
