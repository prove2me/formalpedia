-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.Congr.symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:53.325892+00:00
-- url     : https://prove2.me/submissions/f2f9ed99-80d2-4898-a2fa-f97390f21712

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
theorem _root_.solution {G G' : Matrix n n E} (h : Congr c G G') : Congr c G' G := by
  obtain ⟨P, hP, rfl⟩ := h
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, ?_⟩
  have e1 : P⁻¹ᵀ * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
  have e2 : P.map c * P⁻¹.map c = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc G = (P⁻¹ᵀ * Pᵀ) * G * (P.map c * P⁻¹.map c) := by
        rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]
end Congr
end GlobalTheory.LocalQuad.HermClass
