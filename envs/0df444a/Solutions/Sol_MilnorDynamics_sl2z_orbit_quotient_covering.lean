-- Prove2me | solution 1 for MilnorDynamics.sl2z_orbit_quotient_covering
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:43:15.970966+00:00
-- url     : https://prove2.me/submissions/92b4bcc2-8cd8-4de0-b2a8-2e017daac0b3

import Mathlib
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

set_option autoImplicit false

open scoped MatrixGroups UpperHalfPlane
open Matrix

namespace Cex40c2943b

lemma mapGL_neg_one : (SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.mapGL_coe_matrix]

lemma not_cover :
    ¬ IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel 𝒮ℒ ℍ)) 𝒮ℒ := by
  intro h
  have hc := h.isCancelSMul
  let g : 𝒮ℒ := ⟨SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)), -1, rfl⟩
  have hg : g • UpperHalfPlane.I = (1 : 𝒮ℒ) • UpperHalfPlane.I := by
    rw [one_smul, Subgroup.smul_def]
    change (SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) • UpperHalfPlane.I = UpperHalfPlane.I
    rw [mapGL_neg_one, UpperHalfPlane.neg_smul, one_smul]
  have h1 : g = 1 := hc.right_cancel' g 1 UpperHalfPlane.I hg
  have h2 := congrArg (fun x : 𝒮ℒ => ((x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0) h1
  simp [g, SpecialLinearGroup.mapGL_coe_matrix] at h2
  norm_num at h2

end Cex40c2943b

theorem solution : ¬ IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel 𝒮ℒ ℍ)) 𝒮ℒ := by
  exact Cex40c2943b.not_cover
