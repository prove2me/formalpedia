-- Prove2me | solution 1 for GlobalTheory.SplitFlip.isPrimitiveFrame_standardBasis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:16.590181+00:00
-- url     : https://prove2.me/submissions/bf81e33c-5d7b-4318-8830-5947e6c2496e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_rank_eq_card_iff_exists_frameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_stdLat
import Theorems.Thm_GlobalTheory_SplitFlip_mem_matLat_stdLat

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
variable [Fintype D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution [Fintype A] [DecidableEq D] {A' : Type*} [Fintype A'] (σ : A ⊕ A' ≃ D) :
    IsPrimFrame (stdLat k D) (X0 k σ) := by
  have hm : X0 k σ ∈ matLat A (stdLat k D) := mem_matLat_stdLat.2 fun i j => by
    simp only [X0, of_apply]; split_ifs <;> simp
  refine ⟨(rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).2 ⟨1, by simp⟩, hm, le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨Submodule.subset_span ⟨i, rfl⟩, hm i⟩)
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : c i ∈ 𝒪[k] := by
      classical
      simpa [X0, Finset.sum_apply, Matrix.row] using mem_stdLat.1 hx' (σ (Sum.inl i))
    exact Submodule.smul_mem _ (⟨_, h1⟩ : 𝒪[k]) (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.SplitFlip
