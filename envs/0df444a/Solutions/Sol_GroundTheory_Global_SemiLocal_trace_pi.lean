-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.trace_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:51.024896+00:00
-- url     : https://prove2.me/submissions/ad1c994a-be94-4bc7-92c5-45392e951d0f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Theorems.Thm_GroundTheory_Global_SemiLocal_leftMulMatrix_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]
namespace GroundTheory.Global.SemiLocal
theorem _root_.solution (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), leftMulMatrix_pi, trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ ↦ (Algebra.trace_eq_matrix_trace (b i) (x i)).symm
end GroundTheory.Global.SemiLocal
