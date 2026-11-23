-- Prove2me | solution 1 for GroundTheory.Automorphic.isUnit_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:14.029742+00:00
-- url     : https://prove2.me/submissions/190b71d3-fc7e-456a-9513-6d3d78f7631c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable (V : Type*) [AddCommGroup V] [Module E V]
variable {F E V}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
theorem _root_.solution (h : HermitianForm F E V) (v : Basis ι E V) :
    IsUnit (gram h.toSesq v).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← vecMul_surjective_iff_isUnit]
  intro w
  obtain ⟨x, hx⟩ := h.nonsingular.2 (v.constr E w)
  refine ⟨fun i => conj F E (v.repr x i), ?_⟩
  ext j
  have hxj : h.toSesq x (v j) = w j := by rw [hx, Basis.constr_basis]
  rw [← hxj, sesq_eq_sum h.toSesq v]
  simp only [vecMul, dotProduct, Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end GroundTheory.Automorphic
