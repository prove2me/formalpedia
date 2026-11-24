-- Prove2me | solution 1 for GlobalTheory.RootEx.RowSupport.exists_box
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:12.164598+00:00
-- url     : https://prove2.me/submissions/abb49dc6-950c-4201-83de-c586f85b6707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport
namespace GlobalTheory.RootEx.RowSupport
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : Set (n → k)) (hW : W ∈ 𝓝 (0 : n → k)) :
    ∃ B : Set (n → k), IsCompact B ∧ ∀ u, u ∉ B → ∃ β ∈ W, ψ (u ⬝ᵥ β) ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (AddChar.map_zero_eq_one ψ)
  have hU : ∀ s : n, {x : k | (Pi.single s x : n → k) ∈ W} ∈ 𝓝 (0 : k) := by
    intro s
    have hcont : Continuous fun x : k => (Pi.single s x : n → k) := by
      refine continuous_pi fun j => ?_
      simp only [Pi.single_apply]
      split_ifs
      · exact continuous_id
      · exact continuous_const
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp (Filter.iInter_mem.mpr hU)
  refine ⟨Set.univ.pi fun _ => {x : k | valuation k x ≤ valuation k a / (γ : ValueGroupWithZero k)},
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _, ?_⟩
  intro u hu
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, not_forall, not_le] at hu
  obtain ⟨s, hs⟩ := hu
  have hus : u s ≠ 0 := by
    intro h
    rw [h, map_zero] at hs
    exact not_lt.mpr zero_le hs
  have hv : 0 < valuation k (u s) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hus
  refine ⟨Pi.single s (a / u s), ?_, ?_⟩
  · have hsmall : valuation k (a / u s) < γ := by
      rw [map_div₀, div_lt_iff₀ hv]
      have hg : (0 : ValueGroupWithZero k) < γ := by
        rw [zero_lt_iff]
        exact γ.ne_zero
      rw [div_lt_iff₀ hg] at hs
      simpa [mul_comm] using hs
    exact Set.mem_iInter.mp (hγ hsmall) s
  · rw [dotProduct_single, mul_div_cancel₀ _ hus]
    exact ha
end GlobalTheory.RootEx.RowSupport
