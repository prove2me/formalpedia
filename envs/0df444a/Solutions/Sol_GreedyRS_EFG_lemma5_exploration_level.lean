-- Prove2me | solution 1 for GreedyRS.EFG.lemma5_exploration_level
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:20:14.555063+00:00
-- url     : https://prove2.me/submissions/a5ebdb46-58c9-43af-8709-37aa76c0c072

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i) :
    ∀ γ0 : ℝ, 0 < γ0 → ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∃ n0 : ℕ, 1 ≤ n0 ∧
      ENNReal.ofReal α ≤ P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)} := by
  intro γ0 hγ0 α hα
  have hint : Integrable (X 0 0) P := by
    have h1 : Integrable (id : ℝ → ℝ) (P.map (X 0 0)) := by
      rw [hX.law 0 0]
      exact (memLp_id_gaussianReal' (μ := μ 0) (v := v 0) 1 ENNReal.one_ne_top).integrable le_rfl
    exact (integrable_map_measure aestronglyMeasurable_id (hX.meas 0 0).aemeasurable).1 h1
  have hindep : Pairwise (fun i j => IndepFun (X 0 i) (X 0 j) P) := by
    intro i j hij
    exact hX.indep.indepFun (i := (0, i)) (j := (0, j)) (by simpa [Prod.ext_iff] using hij)
  have hident : ∀ i, IdentDistrib (X 0 i) (X 0 0) P P := fun i =>
    ⟨(hX.meas 0 i).aemeasurable, (hX.meas 0 0).aemeasurable, by rw [hX.law 0 i, hX.law 0 0]⟩
  have hmean : P[X 0 0] = μ 0 := by
    have := integral_map (μ := P) (φ := X 0 0) (f := fun x : ℝ => x) (hX.meas 0 0).aemeasurable
      aestronglyMeasurable_id
    rw [hX.law 0 0, integral_id_gaussianReal] at this
    exact this.symm
  have hslln := strong_law_ae_real (fun j ω => X 0 j ω) hint hindep hident
  set F : ℕ → Set Ω := fun N => {ω | ∀ n, N ≤ n →
    μ 0 - γ0 / 2 < GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 n} with hF
  have hmono : Monotone F := by
    intro N M hNM ω hω n hn
    exact hω n (le_trans hNM hn)
  have hU : (1 : ℝ≥0∞) ≤ P (⋃ N, F N) := by
    have hae : ∀ᵐ ω ∂P, ω ∈ ⋃ N, F N := by
      filter_upwards [hslln] with ω hω
      rw [hmean] at hω
      have hev := hω.eventually (lt_mem_nhds (show μ 0 - γ0 / 2 < μ 0 by linarith))
      obtain ⟨N, hN⟩ := eventually_atTop.1 hev
      exact Set.mem_iUnion.2 ⟨N, fun n hn => hN n hn⟩
    have h0 : P (⋃ N, F N)ᶜ = 0 := hae
    calc (1 : ℝ≥0∞) = P Set.univ := (measure_univ).symm
      _ = P ((⋃ N, F N) ∪ (⋃ N, F N)ᶜ) := by rw [Set.union_compl_self]
      _ ≤ P (⋃ N, F N) + P (⋃ N, F N)ᶜ := measure_union_le _ _
      _ = P (⋃ N, F N) := by rw [h0, add_zero]
  have hU1 : P (⋃ N, F N) = 1 := le_antisymm prob_le_one hU
  have hT := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU1] at hT
  have hα1 : ENNReal.ofReal α < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hα.2
  have hev := (tendsto_order.1 hT).1 _ hα1
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have h1 : ENNReal.ofReal α ≤ P (F (max N 1)) := le_of_lt (hN _ (le_max_left _ _))
  refine h1.trans (measure_mono ?_)
  intro ω hω
  show GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (max N 1) (μ 0 - γ0)
  have hb : BddBelow (Set.range fun n => GreedyRS.Greedy.runMean (fun i j => X i j ω) 0 (max N 1 + n)) :=
    ⟨μ 0 - γ0 / 2, by
      rintro _ ⟨n, rfl⟩
      exact (hω (max N 1 + n) (by omega)).le⟩
  refine ⟨hb, ?_⟩
  calc μ 0 - γ0 < μ 0 - γ0 / 2 := by linarith
    _ ≤ _ := le_ciInf fun n => (hω (max N 1 + n) (by omega)).le
