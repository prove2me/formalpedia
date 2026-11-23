-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.Congr.trans
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:55.899601+00:00
-- url     : https://prove2.me/submissions/f63678f0-a5c1-47d1-a65d-3aaa144c9ccc

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type*} [Field E] {c : E →+* E} {n m : Type*} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]
namespace GlobalTheory.LocalQuad.HermClass
namespace Congr
theorem _root_.solution {G G' G'' : Matrix n n E} (h : Congr c G G') (h' : Congr c G' G'') :
    Congr c G G'' := by
  obtain ⟨P, hP, rfl⟩ := h
  obtain ⟨Q, hQ, rfl⟩ := h'
  refine ⟨P * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hP hQ, ?_⟩
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
end Congr
end GlobalTheory.LocalQuad.HermClass
