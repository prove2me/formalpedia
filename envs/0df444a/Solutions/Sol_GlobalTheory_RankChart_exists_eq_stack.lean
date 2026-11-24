-- Prove2me | solution 1 for GlobalTheory.RankChart.exists_eq_stack
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:40.274946+00:00
-- url     : https://prove2.me/submissions/f3b1c806-38ef-4c01-b545-beab39159d01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartStackDecomposition
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
import Theorems.Thm_P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e



set_option autoImplicit false
open GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.RankChart
namespace GlobalTheory.RankChart
theorem _root_.solution (k : Type) [Field k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T]
    [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) (Y : Matrix (R ⊕ T) D k)
    (hrank : Y.rank ≤ Fintype.card R) (hdet : (Y.submatrix Sum.inl τ).det ≠ 0) :
    ∃ C : Matrix T R k, Y = GlobalTheory.RankChart.stack Y.toRows₁ C := by
  classical
  set Y₁ := Y.toRows₁ with hY₁

  have hA : LinearIndependent k (fun i : R => fun j : R => Y (Sum.inl i) (τ j)) := by
    have hu : IsUnit (Y.submatrix Sum.inl τ) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    exact Matrix.linearIndependent_rows_of_isUnit hu
  have hli : LinearIndependent k (fun i : R => Y₁ i) := by
    apply LinearIndependent.of_comp (LinearMap.funLeft k k τ)
    exact hA
  have hfin₁ : Module.finrank k (Submodule.span k (Set.range fun i : R => Y₁ i)) = Fintype.card R :=
    finrank_span_eq_card hli
  have hle : Submodule.span k (Set.range fun i : R => Y₁ i) ≤ Submodule.span k (Set.range Y.row) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  have heq : Submodule.span k (Set.range fun i : R => Y₁ i) = Submodule.span k (Set.range Y.row) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [hfin₁, ← Matrix.rank_eq_finrank_span_row]
    exact hrank
  have hmem : ∀ t : T, ∃ c : R → k, ∑ i, c i • Y₁ i = Y (Sum.inr t) := by
    intro t
    have : Y (Sum.inr t) ∈ Submodule.span k (Set.range fun i : R => Y₁ i) := by
      rw [heq]; exact Submodule.subset_span ⟨Sum.inr t, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun k).1 this
  choose C hC using hmem
  refine ⟨Matrix.of fun t i => C t i, ?_⟩
  ext (i | t) j
  · simp [stack, hY₁]
  · have := congrFun (hC t) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [stack, fromRows_apply_inr, Matrix.mul_apply, Matrix.of_apply]
    rw [← this]
end GlobalTheory.RankChart
