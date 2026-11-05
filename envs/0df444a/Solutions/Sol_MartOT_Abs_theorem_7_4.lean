-- Prove2me | solution 1 for MartOT.Abs.theorem_7_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T04:55:31.559576+00:00
-- url     : https://prove2.me/submissions/46ce0ac5-853a-459a-ac69-03ffb0f598af
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Opt_optimizer_exists
import Theorems.Thm_MartOT_Abs_theorem_2_6_sufficiency
import Theorems.Thm_MartOT_Abs_theorem_2_6_necessity
import Theorems.Thm_MartOT_Abs_optimizers_convex
import Theorems.Thm_MartOT_Abs_stay_part_eq_inf
import Theorems.Thm_MartOT_Abs_fibres_le_two
import Theorems.Thm_MartOT_Abs_reduced_optimal
import Theorems.Thm_MartOT_Abs_lemma_5_6

open MeasureTheory

/-- A set of reals with at most two elements is covered by two points. -/
lemma abs74_exists_pair (s : Set ℝ) (h : s.encard ≤ 2) :
    ∃ a b : ℝ, ∀ y ∈ s, y = a ∨ y = b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, -, -⟩ := hcon 0 0
  obtain ⟨b, hb, hba, -⟩ := hcon a a
  obtain ⟨c, hc, hca, hcb⟩ := hcon a b
  have hsub : ({a, b, c} : Set ℝ) ⊆ s := by
    intro y hy
    rcases hy with rfl | rfl | rfl <;> assumption
  have h3 : ({a, b, c} : Set ℝ).encard = 3 := by
    rw [Set.encard_insert_of_notMem, Set.encard_pair hcb.symm]
    · rfl
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hba.symm, hca.symm⟩
  have := Set.encard_le_encard hsub
  rw [h3] at this
  have := this.trans h
  exact absurd this (by decide)

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π ∧
      (∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π' → π' = π) ∧
      (∃ Γ : Set (ℝ × ℝ), π Γᶜ = 0 ∧ ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 3) ∧
      ∃ πgo : Measure (ℝ × ℝ), π = (μ ⊓ ν).map (fun x : ℝ => (x, x)) + πgo ∧
        ∃ T₁ T₂ : ℝ → ℝ, πgo {p : ℝ × ℝ | p.2 ≠ T₁ p.1 ∧ p.2 ≠ T₂ p.1} = 0 := by
  set c : ℝ → ℝ → ℝ := fun x y => |y - x| with hcdef
  set Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 = p.2} with hΔdef
  have hΔ : MeasurableSet Δ := measurableSet_eq_fun measurable_fst measurable_snd
  set stay : Measure (ℝ × ℝ) := (μ ⊓ ν).map (fun x : ℝ => (x, x)) with hstay
  -- every optimal plan splits as `stay + π|Δᶜ`
  have hsplit : ∀ ρ : Measure (ℝ × ℝ), MartOT.Var.IsOptimal c μ ν ρ →
      ρ = stay + ρ.restrict Δᶜ := by
    intro ρ hρ
    have h1 := MartOT.Abs.stay_part_eq_inf μ ν hμν ρ hρ
    calc ρ = ρ.restrict Δ + ρ.restrict Δᶜ := (Measure.restrict_add_restrict_compl hΔ).symm
      _ = stay + ρ.restrict Δᶜ := by rw [h1]
  -- existence
  have hc : LowerSemicontinuous (Function.uncurry c) := by
    have : Continuous (Function.uncurry c) := by
      show Continuous (fun p : ℝ × ℝ => |p.2 - p.1|)
      exact continuous_abs.comp (continuous_snd.sub continuous_fst)
    exact this.lowerSemicontinuous
  have hint : MartOT.Var.SuffIntegrable μ ν c :=
    ⟨0, 0, integrable_zero _ _ _, integrable_zero _ _ _, fun x y => by
      simp [hcdef, abs_nonneg]⟩
  obtain ⟨π, hπ⟩ := MartOT.Opt.optimizer_exists μ ν hμν.1 hμν.2.1 c hc hint
    (MartOT.Abs.theorem_2_6_sufficiency μ ν hμν)
  obtain ⟨Γ, -, hΓ0, hΓfib⟩ := MartOT.Abs.fibres_le_two μ ν hμν hμc π hπ
  refine ⟨π, hπ, ?_, ?_, ?_⟩
  · -- uniqueness
    intro π' hπ'
    set E : Set (Measure (ℝ × ℝ)) :=
      {σ | ∃ ρ, MartOT.Var.IsOptimal c μ ν ρ ∧ σ = ρ.restrict Δᶜ} with hEdef
    have hred : ∀ ρ, MartOT.Var.IsOptimal c μ ν ρ →
        MartOT.Var.IsMartingalePlan (μ - μ ⊓ ν) (ν - μ ⊓ ν) (ρ.restrict Δᶜ) := by
      intro ρ hρ
      have h1 := (MartOT.Abs.reduced_optimal μ ν hμν ρ hρ).1.1
      have h2 : ρ - stay = ρ.restrict Δᶜ := by
        haveI : IsFiniteMeasure (μ ⊓ ν) := isFiniteMeasure_of_le μ inf_le_left
        conv_lhs => rw [hsplit ρ hρ, add_comm]
        exact Measure.add_sub_cancel
      rw [← h2]; exact h1
    have hInM : ∀ η : Measure ℝ, η ≤ μ ∨ η ≤ ν → MartOT.Var.InM η := by
      intro η hη
      rcases hη with hη | hη
      · have : IsFiniteMeasure η := isFiniteMeasure_of_le μ hη
        exact ⟨inferInstance, hμν.1.2.mono_measure hη⟩
      · have : IsFiniteMeasure η := isFiniteMeasure_of_le ν hη
        exact ⟨inferInstance, hμν.2.1.2.mono_measure hη⟩
    have hcvx : MartOT.Var.ConvexLE (μ - μ ⊓ ν) (ν - μ ⊓ ν) :=
      MartOT.Abs.theorem_2_6_necessity _ _ (hInM _ (Or.inl Measure.sub_le))
        (hInM _ (Or.inr Measure.sub_le)) _ (hred π hπ)
    have hE : ∀ σ ∈ E, MartOT.Var.IsMartingalePlan (μ - μ ⊓ ν) (ν - μ ⊓ ν) σ := by
      rintro σ ⟨ρ, hρ, rfl⟩
      exact hred ρ hρ
    have hne : E.Nonempty := ⟨_, π, hπ, rfl⟩
    have hconv : ∀ σ ∈ E, ∀ σ' ∈ E, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal t • σ + ENNReal.ofReal (1 - t) • σ' ∈ E := by
      rintro σ ⟨ρ, hρ, rfl⟩ σ' ⟨ρ', hρ', rfl⟩ t ht
      refine ⟨_, MartOT.Abs.optimizers_convex μ ν hμν ρ ρ' hρ hρ' t ht, ?_⟩
      rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul]
    have hfib : ∀ σ ∈ E, ∃ Γ : Set (ℝ × ℝ), σ Γᶜ = 0 ∧
        ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2 := by
      rintro σ ⟨ρ, hρ, rfl⟩
      obtain ⟨Γ', -, hΓ'0, hΓ'fib⟩ := MartOT.Abs.fibres_le_two μ ν hμν hμc ρ hρ
      refine ⟨Γ' ∩ Δᶜ, ?_, ?_⟩
      · rw [Measure.restrict_apply' hΔ.compl]
        refine measure_mono_null ?_ hΓ'0
        intro p hp hpΓ
        exact hp.1 ⟨hpΓ, hp.2⟩
      · intro x
        refine le_trans (Set.encard_le_encard ?_) (hΓ'fib x)
        intro y hy
        exact ⟨hy.1, fun h => hy.2 h.symm⟩
    obtain ⟨σ0, hσ0⟩ := MartOT.Abs.lemma_5_6 _ _ hcvx E hE hne hconv hfib
    have e1 : π.restrict Δᶜ ∈ E := ⟨π, hπ, rfl⟩
    have e2 : π'.restrict Δᶜ ∈ E := ⟨π', hπ', rfl⟩
    rw [hσ0] at e1 e2
    rw [hsplit π' hπ', hsplit π hπ, Set.mem_singleton_iff.mp e1, Set.mem_singleton_iff.mp e2]
  · -- fibres of size at most three
    refine ⟨Γ, hΓ0, fun x => ?_⟩
    have hsub : {y : ℝ | (x, y) ∈ Γ} ⊆ insert x {y : ℝ | (x, y) ∈ Γ ∧ y ≠ x} := by
      intro y hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hy, hyx⟩
    calc {y : ℝ | (x, y) ∈ Γ}.encard
        ≤ (insert x {y : ℝ | (x, y) ∈ Γ ∧ y ≠ x}).encard := Set.encard_le_encard hsub
      _ ≤ {y : ℝ | (x, y) ∈ Γ ∧ y ≠ x}.encard + 1 := Set.encard_insert_le _ _
      _ ≤ 2 + 1 := by gcongr; exact hΓfib x
      _ = 3 := rfl
  · -- the moving part lives on two graphs
    refine ⟨π.restrict Δᶜ, hsplit π hπ, ?_⟩
    choose T₁ T₂ hT using fun x => abs74_exists_pair _ (hΓfib x)
    refine ⟨T₁, T₂, ?_⟩
    rw [Measure.restrict_apply' hΔ.compl]
    refine measure_mono_null ?_ hΓ0
    intro p hp hpΓ
    obtain ⟨⟨h1, h2⟩, hpΔ⟩ := hp
    have hmem : p.2 ∈ {y : ℝ | (p.1, y) ∈ Γ ∧ y ≠ p.1} :=
      ⟨by simpa using hpΓ, fun h => hpΔ h.symm⟩
    rcases hT p.1 p.2 hmem with h | h
    · exact h1 h
    · exact h2 h
