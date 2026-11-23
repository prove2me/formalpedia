-- Prove2me | solution 1 for GroundTheory.Automorphic.repr_tensorMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:51.687252+00:00
-- url     : https://prove2.me/submissions/2f30ebd3-96e7-4c83-a6b7-1e0cdbc9a007

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupEquations
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)
variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]
variable {R}
omit [Algebra.IsQuadraticExtension F E] [Fintype κ]
namespace GroundTheory.Automorphic
theorem _root_.solution (f : R →ₐ[F] S) (z : R ⊗[F] E) (k : κ) :
    (Algebra.TensorProduct.basis S b).repr (tensorMap E f z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
end GroundTheory.Automorphic
