-- Prove2me | solution 1 for GlobalTheory.WeilM.splitOm_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:43.911095+00:00
-- url     : https://prove2.me/submissions/c9e581a2-b362-4c71-843c-b8bdfbb546fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Theorems.Thm_GlobalTheory_WeilM_flat_symm_apply
import Theorems.Thm_GlobalTheory_WeilM_splitOm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
omit [DecidableEq α] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution [TopologicalSpace R] [IsTopologicalRing R] (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle)
    (J : Matrix β β (R × R)) (σ : κ ≃ α × β) (h : UG (swapA R) J) {φ : (κ → R) → ℂ} (hφ : φ ∈ SB (κ → R)) :
    splitOm m χ J σ h φ ∈ SB (κ → R) := by
  have hc : ∀ M : Matrix β β R, Continuous fun u : κ → R => flat σ ((flat σ).symm u * M) := by
    intro M
    refine continuous_pi fun k => ?_
    simp only [flat_apply, Matrix.mul_apply, flat_symm_apply]
    exact continuous_finsetSum _ fun l _ => (continuous_apply _).mul continuous_const
  let e : (κ → R) ≃ₜ (κ → R) :=
    { toFun := fun u => flat σ ((flat σ).symm u * ((ugFst J h)⁻¹).valᵀ)
      invFun := fun u => flat σ ((flat σ).symm u * (ugFst J h).valᵀ)
      left_inv := fun u => by simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
      right_inv := fun u => by simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hφe : (φ ∘ e) ∈ SB (κ → R) := ⟨hφ'.1.comp_continuous e.continuous, hφ'.2.comp_homeomorph e⟩
  have hs : splitOm m χ J σ h φ =
      splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) • (φ ∘ e) := by
    funext u
    rw [splitOm_apply]
    rfl
  rw [hs]
  exact (SB (κ → R)).smul_mem _ hφe
end GlobalTheory.WeilM
