-- Prove2me | solution 1 for GroundTheory.Global.Algebra.trace_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:10.792813+00:00
-- url     : https://prove2.me/submissions/17fe7da2-684f-4d16-969a-6470c4ba2930

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Theorems.Thm_GroundTheory_Global_Algebra_leftMulMatrix_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
namespace GroundTheory.Global.Algebra
theorem _root_.solution (x : ∀ i, A i) : Algebra.trace R _ x = ∑ i, Algebra.trace R (A i) (x i) := by
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi, Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ => (Algebra.trace_eq_matrix_trace (b i) (x i)).symm
end GroundTheory.Global.Algebra
