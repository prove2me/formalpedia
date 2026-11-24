-- Prove2me | solution 1 for GlobalTheory.SymplecticPeriods.exists_symplectic_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:15:05.862171+00:00
-- url     : https://prove2.me/submissions/67f75dac-042b-4a4e-a7ba-30ba04a80c84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMap
import Theorems.Thm_GlobalTheory_SymplecticPeriods_exists_symplectic_rows

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SymplecticPeriods
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SymplecticPeriods
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι]
    (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ)))
    (hF : ∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) :
    ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm →
      (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) →
      τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  obtain ⟨σ, hσ, hrows⟩ := exists_symplectic_rows F hF
  refine ⟨σ, hσ, fun τ hτ τ' M hτ' hM => ?_⟩
  have hτs : τ.IsSymm := hτ.1
  set X := spDen σ τ with hX
  set Y := qm σ.toBlocks₁₁ * τ + qm σ.toBlocks₁₂ with hY

  have colX : ∀ k, (fun l => Xᵀ l k) =
      qv (fun i => σ (Sum.inr k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inr k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hX, spDen, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]
  have columnBlock : ∀ k, (fun l => Yᵀ l k) =
      qv (fun i => σ (Sum.inl k) (Sum.inr i)) + τ *ᵥ qv (fun i => σ (Sum.inl k) (Sum.inl i)) := by
    intro k; funext l
    simp only [hY, Matrix.transpose_apply, Matrix.add_apply, Matrix.mul_apply, qm, Matrix.map_apply,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.of_apply, Pi.add_apply, qv, Matrix.mulVec, dotProduct]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hτs.apply m l, mul_comm]

  have hA : M * Xᵀ = 1 := by
    ext i k
    have h := hM (fun i => σ (Sum.inr k) (Sum.inr i), fun i => σ (Sum.inr k) (Sum.inl i))
    rw [hrows (Sum.inr k), ← colX k] at h
    rw [show (M * Xᵀ) i k = (M *ᵥ fun l => Xᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.one_apply, Matrix.mulVec, dotProduct]
    split_ifs <;> simp
  have hB : τ' = M * Yᵀ := by
    ext i k
    have h := hM (fun i => σ (Sum.inl k) (Sum.inr i), fun i => σ (Sum.inl k) (Sum.inl i))
    rw [hrows (Sum.inl k), ← columnBlock k] at h
    rw [show (M * Yᵀ) i k = (M *ᵥ fun l => Yᵀ l k) i from rfl, congrFun h i]
    simp [qv, Pi.single_apply, Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hMeq : M = (X⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_left_inv hA]
  refine ⟨?_, hMeq⟩
  calc τ' = τ'ᵀ := hτ'.eq.symm
    _ = (M * Yᵀ)ᵀ := by rw [← hB]
    _ = Y * Mᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = spAct σ τ := by rw [hMeq, Matrix.transpose_transpose]; rfl
end GlobalTheory.SymplecticPeriods
