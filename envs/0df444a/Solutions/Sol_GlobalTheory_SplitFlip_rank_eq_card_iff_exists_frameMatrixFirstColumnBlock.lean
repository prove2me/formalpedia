-- Prove2me | solution 1 for GlobalTheory.SplitFlip.rank_eq_card_iff_exists_frameMatrixFirstColumnBlock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:17.232782+00:00
-- url     : https://prove2.me/submissions/4df0a2de-2088-46df-9aa5-c8f21680a684

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixFirstColumnBlock_mul_apply

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
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [DecidableEq A] [DecidableEq A']
namespace GlobalTheory.SplitFlip
theorem _root_.solution (σ : A ⊕ A' ≃ D) (X : Matrix A D k) :
    X.rank = Fintype.card A ↔ ∃ h : GL D k, X = X0 k σ * (invT h).val := by
  have hli : X.rank = Fintype.card A ↔ LinearIndependent k X.row := by
    rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, eq_comm]; rfl
  rw [hli]
  constructor
  · intro hX
    obtain ⟨U, hU⟩ := (Submodule.span k (Set.range X.row)).exists_isCompl
    have hf : Module.finrank k U = Fintype.card A' := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hU
      rw [finrank_span_eq_card hX, Module.finrank_fintype_fun_eq_card, ← Fintype.card_congr σ,
        Fintype.card_sum] at h1
      omega
    let b := (Module.finBasisOfFinrankEq k U hf).reindex (Fintype.equivFin A').symm
    have hb : LinearIndependent k (U.subtype ∘ b) := b.linearIndependent.map' _ U.ker_subtype
    have hs := (hX.sum_type hb (hU.disjoint.mono_right (Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩; exact (b i).2)))).comp σ.symm σ.symm.injective
    obtain ⟨B, hB⟩ := (Matrix.linearIndependent_rows_iff_isUnit
      (A := Matrix.of (Sum.elim X.row (U.subtype ∘ b) ∘ σ.symm))).1 hs
    refine ⟨invT B, ?_⟩
    ext i j
    simp [frameMatrixFirstColumnBlock_mul_apply, hB]
  · rintro ⟨h, rfl⟩
    have := (Matrix.linearIndependent_rows_iff_isUnit.2 (invT h).isUnit).comp (σ ∘ Sum.inl)
      (σ.injective.comp Sum.inl_injective)
    convert this using 1
    funext i j
    exact frameMatrixFirstColumnBlock_mul_apply σ _ i j
end GlobalTheory.SplitFlip
