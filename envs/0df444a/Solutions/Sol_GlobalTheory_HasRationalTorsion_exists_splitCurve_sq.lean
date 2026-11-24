-- Prove2me | solution 1 for GlobalTheory.HasRationalTorsion.exists_splitCurve_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:53.816247+00:00
-- url     : https://prove2.me/submissions/74c716f8-938d-45c6-be6f-3107825708bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
import Theorems.Thm_GlobalTheory_HasRationalTorsion_of_dvd
import Theorems.Thm_GlobalTheory_HasRationalTorsion_variableChange
import Theorems.Thm_GlobalTheory_HasRationalTorsion_exists_splitCurve
import Theorems.Thm_GlobalTheory_HasRationalTorsion_isSquare_neg

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
theorem _root_.solution (h : HasRationalTorsion W L 4) :
    ∃ (C : VariableChange K) (A B a c : K), C.u = 1 ∧ C • W = splitCurve A B ∧ a ^ 2 = A ∧
      c ^ 2 = A * B * (A - B) := by
  obtain ⟨C, A, B, hu, e⟩ := (h.of_dvd (by norm_num : 2 ∣ 4)).exists_splitCurve
  have e₁ : C • W = splitCurve B A := by
    rw [e, splitCurve, splitCurve, add_comm, mul_comm]
  have e₂ : ((⟨1, A, 0, 0⟩ : VariableChange K) * C) • W = splitCurve (-A) (B - A) := by
    rw [mul_smul, e]
    simp only [variableChange_def, splitCurve, inv_one, Units.val_one]
    ext <;> dsimp only <;> ring
  have e₃ : ((⟨1, A, 0, 0⟩ : VariableChange K) * C) • W = splitCurve (B - A) (-A) := by
    rw [e₂, splitCurve, splitCurve, add_comm, mul_comm (B - A)]
  have key : ∀ {C : VariableChange K} {A B : K}, C • W = splitCurve A B → ∃ a : K, a ^ 2 = -A := by
    intro C A B e
    have : (splitCurve A B).IsElliptic := e ▸ inferInstance
    exact HasRationalTorsion.isSquare_neg (L := L) (B := B) (e ▸ h.variableChange C)
  obtain ⟨a₀, h₀⟩ := key e
  obtain ⟨a₁, h₁⟩ := key e₁
  obtain ⟨a₂, h₂⟩ := key e₂
  obtain ⟨a₃, h₃⟩ := key e₃
  refine ⟨C, A, B, a₂, a₀ * a₁ * a₃, hu, e, by rw [h₂, neg_neg], ?_⟩
  rw [mul_pow, mul_pow, h₀, h₁, h₃]
  ring
end HasRationalTorsion
end GlobalTheory
