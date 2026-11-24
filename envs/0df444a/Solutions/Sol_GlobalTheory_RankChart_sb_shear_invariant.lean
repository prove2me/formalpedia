-- Prove2me | solution 1 for GlobalTheory.RankChart.sb_shear_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:12.19544+00:00
-- url     : https://prove2.me/submissions/7c8c6ff1-0bb2-4439-89fe-eea74556a288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartShearInvariance
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_box_subset
import Theorems.Thm_GlobalTheory_RankChart_shear_sub_self
import Theorems.Thm_GlobalTheory_RootEx_sb_matrix_exists_isOpen_addSubgroup
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
noncomputable section
open Filter
open scoped Topology
open GlobalTheory GlobalTheory.RankChart
namespace GlobalTheory.RankChart
theorem _root_.solution :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D],
      ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k),
        ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ f hf
  obtain ⟨Λ, hΛo, hΛ⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ f hf
  have hK : IsCompact (tsupport f) := hf.2
  have hc : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k =>
      fromRows (0 : Matrix R D k) (p.1 * p.2.toRows₁) := by
    have hm : Continuous fun p : Matrix T R k × Matrix (R ⊕ T) D k => p.1 * p.2.toRows₁ :=
      continuous_fst.matrix_mul (continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply_apply (Sum.inl i) j).comp continuous_snd)
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i
    · simpa using continuous_const
    · simp only [fromRows_apply_inr]
      exact (continuous_apply_apply i j).comp hm
  have hev : ∀ᶠ c in 𝓝 (0 : Matrix T R k), ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ :=
    hK.eventually_forall_of_forall_eventually fun Y _ => by
      have h0 : fromRows (0 : Matrix R D k) ((0 : Matrix T R k) * Y.toRows₁) ∈ Λ := by
        simp
      exact (hc.tendsto ((0 : Matrix T R k), Y)) (hΛo.mem_nhds h0)
  obtain ⟨b, hb⟩ := GlobalTheory.LocMod.Inhab.exists_box_subset hev
  refine ⟨b, fun Y c hcb => ?_⟩
  have hZ : ∀ Y ∈ tsupport f, fromRows (0 : Matrix R D k) (c * Y.toRows₁) ∈ Λ := hb c hcb
  by_cases hY : Y ∈ tsupport f
  · rw [← hΛ Y _ (hZ Y hY), ← shear_sub_self, add_sub_cancel]
  by_cases hY' : shear c Y ∈ tsupport f
  · have h1 := hZ _ hY'
    rw [toRows₁_shear, ← shear_sub_self] at h1
    rw [← hΛ (shear c Y) _ (Λ.neg_mem h1), neg_sub, add_sub_cancel]
  · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hY']
end GlobalTheory.RankChart
