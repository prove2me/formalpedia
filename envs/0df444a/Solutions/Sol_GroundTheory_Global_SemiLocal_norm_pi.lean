-- Prove2me | solution 1 for GroundTheory.Global.SemiLocal.norm_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:47:30.206911+00:00
-- url     : https://prove2.me/submissions/0e5094e1-ac31-4856-be2e-86bbbf8f1b7b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_det_blockDiagonal__aa8633837095
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
theorem _root_.solution (x : ∀ i, S i) : Algebra.norm R x = ∏ i, Algebra.norm R (x i) := by
  classical
  let b := fun i ↦ Module.finBasis R (S i)
  rw [Algebra.norm_eq_matrix_det (Pi.basis b), leftMulMatrix_pi, det_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ ↦ (Algebra.norm_eq_matrix_det (b i) (x i)).symm
end GroundTheory.Global.SemiLocal
