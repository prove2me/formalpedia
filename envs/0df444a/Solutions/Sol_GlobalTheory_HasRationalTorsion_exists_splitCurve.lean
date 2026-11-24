-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.exists_splitCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:30:18.304056+00:00
-- url     : https://prove2.me/submissions/98cece7a-0da3-4c68-9d9f-9f4676630182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_HasRationalTorsion_variableChange
import Theorems.Thm_GlobalTheory_exists_root_quadratic
import Theorems.Thm_GlobalTheory_exists_root_cubic
import Theorems.Thm_GlobalTheory_HasRationalTorsion_mem_range_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
namespace GlobalTheory
namespace HasRationalTorsion
theorem _root_.solution (h : HasRationalTorsion W L 2) :
    ∃ (C : VariableChange K) (A B : K), C.u = 1 ∧ C • W = splitCurve A B := by
  set C₁ : VariableChange K := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩ with hC₁
  have h₁ : (C₁ • W).a₁ = 0 := by simp only [hC₁, variableChange_a₁]; ring
  have h₃ : (C₁ • W).a₃ = 0 := by simp only [hC₁, variableChange_a₃]; ring
  have h' := h.variableChange C₁
  obtain ⟨e, he⟩ := exists_root_cubic (one_ne_zero : (1 : L) ≠ 0) (algebraMap K L (C₁ • W).a₂)
    (algebraMap K L (C₁ • W).a₄) (algebraMap K L (C₁ • W).a₆)
  rw [one_mul] at he
  obtain ⟨e, rfl⟩ := h'.mem_range_of_root h₁ h₃ he
  obtain ⟨f, hf⟩ := exists_root_quadratic (algebraMap K L ((C₁ • W).a₂ + e))
    (algebraMap K L ((C₁ • W).a₄ + (C₁ • W).a₂ * e + e ^ 2))
  obtain ⟨f, rfl⟩ := h'.mem_range_of_root h₁ h₃ (x := f) (by
    simp only [map_add, map_mul, map_pow] at hf
    linear_combination he + (f - algebraMap K L e) * hf)
  have he' : e ^ 3 + (C₁ • W).a₂ * e ^ 2 + (C₁ • W).a₄ * e + (C₁ • W).a₆ = 0 := by
    apply (algebraMap K L).injective
    simpa using he
  have hf' : f ^ 2 + ((C₁ • W).a₂ + e) * f + ((C₁ • W).a₄ + (C₁ • W).a₂ * e + e ^ 2) = 0 := by
    apply (algebraMap K L).injective
    simpa using hf
  refine ⟨⟨1, e, 0, 0⟩ * C₁, f - e, -(C₁ • W).a₂ - 2 * e - f, by simp [VariableChange.mul_def, hC₁],
    ?_⟩
  rw [mul_smul]
  generalize C₁ • W = W₁ at *
  simp only [variableChange_def, splitCurve, inv_one, Units.val_one]
  ext <;> dsimp only
  · linear_combination h₁
  · ring
  · linear_combination h₃ + e * h₁
  · linear_combination hf'
  · linear_combination he'
end HasRationalTorsion
end GlobalTheory
