-- Prove2me | solution 1 for GlobalTheory.SplitFlip.invFourierSum_inv_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:48.179541+00:00
-- url     : https://prove2.me/submissions/d31b3858-9b77-42e6-8e9b-bbf45e715cdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_apply
import Theorems.Thm_GlobalTheory_SplitFlip_invFourierSum_inv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*}
variable [DecidableEq D]
variable [Fintype A]
variable [DecidableEq A]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (Ψ : Matrix A D k → ℂ)
    (T : Matrix A D k) : invFourierSum ψ⁻¹ ϖ e P Ψ T =
      invFourierSum ψ ϖ e P Ψ (setCols P T (Matrix.of fun i j => -T i j)) := by
  have h1 : ∀ S, setCols P (setCols P T (Matrix.of fun i j => -T i j)) S = setCols P T S := fun S => by
    ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
  have h2 : ∀ S, -pairCols P (setCols P T (Matrix.of fun i j => -T i j)) S = pairCols P T S := fun S => by
    simp [pairCols, setCols]
  have h3 : (∀ i, ∀ j ∈ P, setCols P T (Matrix.of fun i j => -T i j) i j ∈ 𝒪[k]) ↔ ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] :=
    forall_congr' fun i => forall₂_congr fun j h => by simp [setCols, h]
  classical
  rw [invFourierSum_inv_apply, invFourierSum_apply]
  simp only [h1, h2]
  exact if_congr h3.symm rfl rfl
end GlobalTheory.SplitFlip
