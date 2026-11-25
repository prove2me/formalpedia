-- Prove2me | solution 1 for GlobalTheory.BasicFlow.pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:25.013705+00:00
-- url     : https://prove2.me/submissions/43cf7dfe-1402-464a-b3f9-bcff947f72d3

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DropLevelsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open GlobalTheory GlobalTheory.BasicFlow
namespace GlobalTheory.BasicFlow
theorem _root_.solution {ι κ : Type} [DecidableEq ι] [Fintype κ] (s : Finset ι)
    (T : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hT : ∀ v : ι → ℝ, (∀ i, i ∉ s → v i = 0) → (∀ i, 0 ≤ v i) → T v = 0 → v = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hs : ∀ i, i ∉ s → x i = 0)
    (hc : Fintype.card κ < (s.filter fun i => x i ≠ 0).card) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ T y = T x ∧ φ x ≤ φ y ∧ (∀ i, x i = 0 → y i = 0) ∧
      (s.filter fun i => y i ≠ 0).card < (s.filter fun i => x i ≠ 0).card := by
  set t := s.filter fun i => x i ≠ 0 with ht
  let E : (t → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => if h : i ∈ t then v ⟨i, h⟩ else 0
      map_add' := fun v w => by ext i; by_cases h : i ∈ t <;> simp [h]
      map_smul' := fun c v => by ext i; by_cases h : i ∈ t <;> simp [h] }
  have hker : LinearMap.ker (T ∘ₗ E) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hc
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw' : T (E w) = 0 := hw
  have hE0 : E w ≠ 0 := by
    intro h
    apply hw0
    ext ⟨i, hi⟩
    have := congrFun h i
    simpa [E, hi] using this
  have hEt : ∀ i, i ∉ t → E w i = 0 := fun i hi => by simp [E, hi]
  obtain ⟨v, hv0, hvt, hvT, hvφ⟩ :
      ∃ v : ι → ℝ, v ≠ 0 ∧ (∀ i, i ∉ t → v i = 0) ∧ T v = 0 ∧ 0 ≤ φ v := by
    rcases le_total 0 (φ (E w)) with h | h
    · exact ⟨E w, hE0, hEt, hw', h⟩
    · refine ⟨-E w, neg_ne_zero.2 hE0, fun i hi => by simp [hEt i hi], by simp [hw'], ?_⟩
      simpa using h
  have hneg : (t.filter fun i => v i < 0).Nonempty := by
    by_contra hn
    apply hv0
    refine hT v (fun i hi => hvt i fun h => hi (Finset.mem_filter.1 h).1) (fun i => ?_) hvT
    by_cases hi : i ∈ t
    · by_contra hlt
      exact hn ⟨i, Finset.mem_filter.2 ⟨hi, not_le.1 hlt⟩⟩
    · exact (hvt i hi).ge
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ (fun i => x i / (-v i)) hneg
  obtain ⟨hjt, hjv⟩ := Finset.mem_filter.1 hj
  have hc0 : 0 ≤ x j / (-v j) := div_nonneg (hx j) (by linarith)
  have hzero : ∀ i, x i = 0 → (x + (x j / (-v j)) • v) i = 0 := by
    intro i hi
    have : v i = 0 := hvt i fun h => (Finset.mem_filter.1 h).2 hi
    simp [hi, this]
  refine ⟨x + (x j / (-v j)) • v, fun i => ?_, by simp [hvT], ?_, hzero, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : v i < 0
    · have hit : i ∈ t := by
        by_contra h
        exact hi.ne (hvt i h)
      have := hmin i (Finset.mem_filter.2 ⟨hit, hi⟩)
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · have := mul_nonneg hc0 (not_lt.1 hi)
      linarith [hx i]
  · rw [map_add, map_smul, smul_eq_mul]
    have := mul_nonneg hc0 hvφ
    linarith
  · apply Finset.card_lt_card
    refine ⟨fun i hi => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨h1, fun h => h2 (hzero i h)⟩
    · apply (Finset.mem_filter.1 (h hjt)).2
      have : v j ≠ 0 := hjv.ne
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
end GlobalTheory.BasicFlow
