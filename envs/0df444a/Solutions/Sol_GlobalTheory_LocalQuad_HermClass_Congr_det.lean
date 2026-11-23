-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.Congr.det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:00.910274+00:00
-- url     : https://prove2.me/submissions/8b07fbdd-df92-425c-bd6f-ea9a04ead121

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm

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
theorem _root_.solution {G G' : Matrix n n E} (h : Congr c G G') :
    ∃ x : E, x ≠ 0 ∧ G'.det = x * c x * G.det := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.det, hP, ?_⟩
  have : (P.map c).det = c P.det := (RingHom.map_det c P).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, this]
  ring
end Congr
end GlobalTheory.LocalQuad.HermClass
