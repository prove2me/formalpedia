-- Prove2me | solution 1 for GroundTheory.Global.Algebra.norm_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:40:44.383025+00:00
-- url     : https://prove2.me/submissions/b6c6f29e-a4b9-410f-8bbc-dc1ebe9a0ecf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Theorems.Thm_P2M_GroundTheory_Global_Matrix_det_blockDiagonal__9aefd9cf488d
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
theorem _root_.solution (x : ∀ i, A i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  let b := fun i => Module.Free.chooseBasis R (A i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi,
    GroundTheory.Global.Matrix.det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => (Algebra.norm_eq_matrix_det (b i) (x i)).symm
end GroundTheory.Global.Algebra
