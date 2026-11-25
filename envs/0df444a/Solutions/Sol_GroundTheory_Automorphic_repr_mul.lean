-- Prove2me | solution 1 for GroundTheory.Automorphic.repr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:24.240963+00:00
-- url     : https://prove2.me/submissions/2598f255-461b-4569-8eda-dad7e0cedb29

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
import Theorems.Thm_GroundTheory_Automorphic_repr_one_tmul
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
namespace GroundTheory.Automorphic
theorem _root_.solution (z w : R ⊗[K] E) (m : κ) :
    (Algebra.TensorProduct.basis R b).repr (z * w) m =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr z k *
        (Algebra.TensorProduct.basis R b).repr w l * algebraMap K R (b.repr (b k * b l) m) := by
  set B := Algebra.TensorProduct.basis R b
  conv_lhs => rw [← B.sum_repr z, ← B.sum_repr w]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, B,
    Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum,
    map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    repr_one_tmul]
  exact Finset.sum_comm
end GroundTheory.Automorphic
