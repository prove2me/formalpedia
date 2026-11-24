-- Prove2me | solution 1 for GlobalTheory.RankChart.bounded_coeff_of_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:11.733155+00:00
-- url     : https://prove2.me/submissions/19a0e173-d4b8-4f64-ae9b-dbdaa43b0347

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IndicatorBoxEqCharSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartBoundedCoefficients
import Theorems.Thm_GlobalTheory_RankChart_coeffOnChart_stack
import Theorems.Thm_GlobalTheory_RankChart_coeffOnChart_continuousOn
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_BoxCharComb_exists_box_superset
import Theorems.Thm_GlobalTheory_RankChart_submatrix_inl_eq
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mono
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
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__dil_a78c4f6a5c7f
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__shear_d5dffcf9ff0a
attribute [local simp] P2M_GlobalTheory_RankChart_toRows__stack_b71dac95216e



set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open ValuativeRel
namespace GlobalTheory.RankChart
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) :
    ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) →
      ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 →
        C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  intro f hf hdet
  have hcl : IsClosed (Function.support f) := by
    have := (hf.1.isOpen_fiber 0).isClosed_compl
    simpa [Function.support, Set.compl_setOf] using this
  have hK : IsCompact (Function.support f) := by
    have h2 : HasCompactSupport f := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at h2
    exact h2
  have hcont : ContinuousOn (coeffOnChart (T := T) (k := k) τ) (Function.support f) :=
    (coeffOnChart_continuousOn τ).mono fun Y hY => hdet Y hY
  obtain ⟨a, ha⟩ := GlobalTheory.BoxCharComb.exists_box_superset (hK.image_of_continuousOn hcont)
  refine ⟨a, fun Y₁ C hY => ?_⟩
  have hd := hdet _ hY
  rw [submatrix_inl_eq, toRows₁_stack] at hd
  have := ha _ ⟨_, hY, coeffOnChart_stack τ Y₁ C hd⟩
  exact this
end GlobalTheory.RankChart
