-- Prove2me | solution 1 for MartOT.Card.theorem_7_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:11:40.877613+00:00
-- url     : https://prove2.me/submissions/1d1a9967-e4d2-4a98-a53a-01d374701a23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Card_lemma_1_11
import Theorems.Thm_MartOT_Card_exceptional_countable

open MeasureTheory ProbabilityTheory

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (k : ℕ)
    (hk : ∀ s t : ℝ, {x : ℝ | deriv h x = s * x + t}.encard ≤ k)
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x)))
    (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π)
    (hfin : MartOT.Var.cost (fun x y => h (y - x)) π < ⊤) :
    (∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧ π = μ ⊗ₘ κ ∧
      ∀ x : ℝ, 0 < μ {x} ∨ ∃ F : Set ℝ, F.encard ≤ k ∧ κ x Fᶜ = 0) ∧
    ((∀ x : ℝ, μ {x} = 0) → ∀ κ : Kernel ℝ ℝ, IsMarkovKernel κ → π = μ ⊗ₘ κ →
      ∀ᵐ x ∂μ, ∃ F : Set ℝ, F.encard ≤ k ∧ κ x Fᶜ = 0) := by
  have hc : Measurable (Function.uncurry fun x y : ℝ => h (y - x)) := by
    have : Continuous (Function.uncurry fun x y : ℝ => h (y - x)) :=
      hh.continuous.comp (continuous_snd.sub continuous_fst)
    exact this.measurable
  obtain ⟨Γ, hΓm, hΓ0, hΓ⟩ := MartOT.Card.lemma_1_11 μ ν hμν _ hc hint π hπ hfin
  have hE := MartOT.Card.exceptional_countable μ h hh k hk Γ hΓ
  set E := {x : ℝ | μ {x} = 0 ∧ ((k + 1 : ℕ) : ℕ∞) ≤ {y : ℝ | (x, y) ∈ Γ}.encard} with hEdef
  have hEnull : μ E = 0 := by
    rw [← Set.biUnion_of_singleton E]
    exact (measure_biUnion_null_iff hE).2 (fun x hx => hx.1)
  have hEae : ∀ᵐ x ∂μ, x ∉ E := measure_eq_zero_iff_ae_notMem.1 hEnull
  -- fibres of Γ carry the whole kernel mass, for any disintegration
  have hfib : ∀ κ : Kernel ℝ ℝ, IsMarkovKernel κ → π = μ ⊗ₘ κ →
      ∀ᵐ x ∂μ, κ x (Prod.mk x ⁻¹' Γᶜ) = 0 := by
    intro κ _ hπκ
    have h0 : (μ ⊗ₘ κ) Γᶜ = 0 := hπκ ▸ hΓ0
    rw [Measure.compProd_apply hΓm.compl,
      lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hΓm.compl)] at h0
    exact h0
  -- the pointwise conclusion off `E`
  have key : ∀ κ : Kernel ℝ ℝ, ∀ x : ℝ, x ∉ E → κ x (Prod.mk x ⁻¹' Γᶜ) = 0 → μ {x} = 0 →
      ∃ F : Set ℝ, F.encard ≤ k ∧ κ x Fᶜ = 0 := by
    intro κ x hxE hx0 hμx
    refine ⟨{y : ℝ | (x, y) ∈ Γ}, ?_, ?_⟩
    · have : ¬ (((k + 1 : ℕ) : ℕ∞) ≤ {y : ℝ | (x, y) ∈ Γ}.encard) := fun h' => hxE ⟨hμx, h'⟩
      push_neg at this
      push_cast at this
      exact Order.le_of_lt_add_one this
    · exact hx0
  refine ⟨?_, ?_⟩
  · -- part 1
    have hk1 : 1 ≤ k := by
      have h1 := hk 0 (deriv h 0)
      have h2 : ({0} : Set ℝ) ⊆ {x : ℝ | deriv h x = 0 * x + deriv h 0} := by
        intro x hx; simp at hx; simp [hx]
      have h3 := (Set.encard_le_encard h2).trans h1
      rw [Set.encard_singleton] at h3
      exact_mod_cast h3
    haveI : IsProbabilityMeasure π := by
      constructor
      have := hπ.1.1.1
      have h4 : (π.map Prod.fst) Set.univ = μ Set.univ := by rw [this]
      rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h4
      simpa using h4
    have hfst : π.fst = μ := hπ.1.1.1
    set κ₀ := π.condKernel
    have hπ0 : π = μ ⊗ₘ κ₀ := by
      conv_lhs => rw [← π.disintegrate π.condKernel]
      rw [hfst]
    let B := {x : ℝ | ¬ (0 < μ {x} ∨ ∃ F : Set ℝ, F.encard ≤ k ∧ κ₀ x Fᶜ = 0)}
    have hB : μ B = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hEae, hfib κ₀ inferInstance hπ0] with x hxE hx0
      simp only [B, Set.mem_setOf_eq, not_not]
      by_cases hμx : μ {x} = 0
      · exact Or.inr (key κ₀ x hxE hx0 hμx)
      · exact Or.inl (pos_iff_ne_zero.2 hμx)
    set N := toMeasurable μ B
    have hNm : MeasurableSet N := measurableSet_toMeasurable μ B
    have hN0 : μ N = 0 := by rw [measure_toMeasurable]; exact hB
    classical
    let κ : Kernel ℝ ℝ := Kernel.piecewise hNm (Kernel.const ℝ (Measure.dirac 0)) κ₀
    refine ⟨κ, inferInstance, ?_, ?_⟩
    · rw [hπ0]
      apply Measure.compProd_congr
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with x hx
      simp [κ, Kernel.piecewise_apply, hx]
    · intro x
      by_cases hxN : x ∈ N
      · right
        refine ⟨{0}, ?_, ?_⟩
        · rw [Set.encard_singleton]; exact_mod_cast hk1
        · simp [κ, Kernel.piecewise_apply, hxN]
      · have hxB : x ∉ B := fun hb => hxN (subset_toMeasurable μ B hb)
        simp only [B, Set.mem_setOf_eq, not_not] at hxB
        simpa [κ, Kernel.piecewise_apply, hxN] using hxB
  · intro hatom κ hκ hπκ
    filter_upwards [hEae, hfib κ hκ hπκ] with x hxE hx0
    exact key κ x hxE hx0 (hatom x)
