-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.Congr.submatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:55.662048+00:00
-- url     : https://prove2.me/submissions/85aa4d05-499b-4fad-a46d-9d803b4fb08f

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {G G' : Matrix n n E} (h : Congr c G G') (e : m ≃ n) :
    Congr c (G.submatrix e e) (G'.submatrix e e) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Matrix.transpose_submatrix, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv]
end Congr
end GlobalTheory.LocalQuad.HermClass
