-- Prove2me | solution 1 for GlobalTheory.LastSteps.integral_qLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:28.751172+00:00
-- url     : https://prove2.me/submissions/778ec81c-cfa4-404f-bee5-eb5d7488c0c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_isClopen_isCompact_qLat
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n]
variable [MeasurableSpace k] [BorelSpace k] (q : Unif k) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
  (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
include hψ
open Classical
namespace GlobalTheory.LastSteps
theorem _root_.solution (η : n → k) :
    ∫ y, (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ) ∂μ =
      if InDual L (q.1 • η) then (volQ μ q L : ℂ) else 0 := by
  haveI := secondCountable k
  have hd : ∀ y : n → k, (q.1 • η) ⬝ᵥ y = η ⬝ᵥ (q.1 • y) := fun y => by rw [smul_dotProduct, dotProduct_smul]
  split_ifs with h
  · have : ∀ y, (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ) =
        {y : n → k | q.inv • y ∈ L}.indicator (fun _ => (1 : ℂ)) y := fun y => by
      by_cases hy : q.inv • y ∈ L
      · have h1 := h _ hy
        rw [hd, q.smul_inv_smul] at h1
        rw [if_pos hy, Set.indicator_of_mem (show y ∈ {y : n → k | q.inv • y ∈ L} from hy),
          apply_int_eq_one hψ ⟨_, h1⟩, Circle.coe_one, mul_one]
      · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ {y : n → k | q.inv • y ∈ L} from hy), zero_mul]
    simp only [this]
    rw [integral_indicator_const _ (isClopen_isCompact_qLat q L).1.2.measurableSet]
    simp [volQ]
  · obtain ⟨w, hw, hne⟩ : ∃ w : n → k, q.inv • w ∈ L ∧ ψ (η ⬝ᵥ w) ≠ 1 := by
      by_contra hc
      push Not at hc
      refine h fun z hz => ?_
      by_cases h0 : (q.1 • η) ⬝ᵥ z = 0
      · rw [h0]; exact zero_mem _
      refine (Valuation.mem_integer_iff _ _).2 ?_
      have := (hψ ((q.1 • η) ⬝ᵥ z)).1 fun y hy => by
        have ht : y / ((q.1 • η) ⬝ᵥ z) ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff, map_div₀]
          exact div_le_one_of_le₀ hy zero_le'
        have h1 := hc (q.1 • (⟨_, ht⟩ : 𝒪[k]) • z) (by rw [q.inv_smul_smul]; exact L.smul_mem _ hz)
        rw [← hd, dotProduct_smul] at h1
        rwa [← div_mul_cancel₀ y h0]
      simpa using this
    have h1 := integral_add_right_eq_self (μ := μ)
      (fun y => (if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) w
    have h2 : ∀ y, (if q.inv • (y + w) ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ (y + w)) : ℂ) =
        (ψ (η ⬝ᵥ w) : ℂ) * ((if q.inv • y ∈ L then (1 : ℂ) else 0) * (ψ (η ⬝ᵥ y) : ℂ)) := fun y => by
      simp only [smul_add, L.add_mem_iff_left hw]
      rw [dotProduct_add, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    simp only [h2, integral_const_mul] at h1
    have h3 : (ψ (η ⬝ᵥ w) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, h1, one_mul, sub_self]
end GlobalTheory.LastSteps
