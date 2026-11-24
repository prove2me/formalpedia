-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.isPrimFrame_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:41.227933+00:00
-- url     : https://prove2.me/submissions/254bbe45-0280-4b57-9ac8-3d26d73c08cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv

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
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
omit [DecidableEq A]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution {Λ Λ' : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} (hX : IsPrimFrame Λ X) (g : GL D k)
    (hg : ∀ x, x ᵥ* g.val ∈ Λ' ↔ x ∈ Λ) : IsPrimFrame Λ' (X * g.val) := by
  have hr : ∀ i, (X * g.val).row i = X.row i ᵥ* g.val := fun i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨?_, fun i => ?_, le_antisymm ?_ ?_⟩
  · rw [rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]; exact hX.1
  · rw [hr, hg]; exact hX.2.1 i
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, by rw [SetLike.mem_coe, hr, hg]; exact hX.2.1 i⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    have e1 : ∑ i, c i • (X * g.val).row i = (∑ i, c i • X.row i) ᵥ* g.val := by
      simp only [hr, sum_vecMul, smul_vecMul]
    rw [e1] at hx' ⊢
    have h2 : (∑ i, c i • X.row i) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      exact ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)), (hg _).1 hx'⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    rw [← hd, sum_vecMul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_vecMul, ← hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end GlobalTheory.SplitFlip.Model
