-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BlockZeroFiniteV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:07:47.617857+00:00
-- url     : https://prove2.me/submissions/bd32c9a6-b851-4024-a0e3-416dce9fb5df

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseBlockCountV5
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseCountLowerV5
import Theorems.Thm_Kyprianou_Ch04_exercise41FineCellsInjectiveV4
import Theorems.Thm_Kyprianou_Ch04_exercise41FloorCellV4
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteLiminfV2
import Theorems.Thm_Kyprianou_Ch04_exercise41LiminfTopV2
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (a δ : NNReal)
    (hδ : 0 < δ) (hd : 0 < L.drift)
    (hp : 0 < P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}) :
    ∀ᵐ ω ∂P, Set.Finite {s : NNReal | a ≤ s ∧ s < a + δ ∧ L.X s ω = 0} := by
  let q := TopologicalSpace.denseSeq NNReal
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq NNReal
  let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
    L.drift / 2 * (u : ℝ) ≤ L.X u ω}
  let h : ℕ → ℝ := fun n => (δ : ℝ) / ((n : ℝ) + 1)
  have hd' : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hw (n : ℕ) : ((n + 1 : ℕ) : ℝ) * h n = (δ : ℝ) := by
    simp only [h, Nat.cast_add, Nat.cast_one]
    exact mul_div_cancel₀ _ (by positivity)
  have ht : Tendsto h atTop (𝓝 0) := by
    have H := (tendsto_const_nhds (x := (δ : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [h, mul_zero, div_eq_mul_inv, one_mul] using H
  let A : ℕ → ℕ → ℕ → Set Ω := fun n m i =>
    {ω | ∃ k < m, (a : ℝ) + (i : ℝ) * h n ≤ (q k : ℝ) ∧
      (q k : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h n ∧
      |L.X (q k) ω| < L.drift * h n / 8}
  let N : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ⨆ m : ℕ, ∑ i ∈ Finset.range (n+1),
      (A n m i).indicator (fun _ : Ω => (1 : ℝ≥0∞)) ω
  have hN (n : ℕ) : Measurable (N n) ∧ (∫⁻ ω, N n ω ∂P) ≤ 2 / p :=
    exercise41DenseBlockCountV5 P F L a δ (h n) (n+1) q
      (hh n) hd (hw n).le hp
  have hfin := exercise41FiniteLiminfV2 P N (2 / p)
    (ENNReal.div_lt_top (by simp) (ne_of_gt hp))
    (fun n => (hN n).1) (fun n => (hN n).2)
  filter_upwards [hfin] with ω hω
  let Z : Set NNReal := {s | a ≤ s ∧ s < a + δ ∧ L.X s ω = 0}
  change Z.Finite
  by_contra hZ
  have hInf : Z.Infinite := hZ
  have htop : Filter.liminf (fun n => N n ω) atTop = ⊤ := by
    apply exercise41LiminfTopV2
    intro k
    obtain ⟨T, hTZ, hT, hcard⟩ := hInf.exists_subset_ncard_eq k
    let S := hT.toFinset
    have hSc : S.card = k := by
      rw [← Set.ncard_eq_toFinset_card T hT]
      exact hcard
    have hSZ (s : NNReal) (hs : s ∈ S) : s ∈ Z :=
      hTZ (hT.mem_toFinset.mp hs)
    let j : ℕ → NNReal → ℕ := fun n s => Nat.floor (((s : ℝ) - (a : ℝ)) / h n)
    have hc (n : ℕ) (s : NNReal) (hs : s ∈ S) :
        j n s ∈ Finset.range (n+1) ∧
        (a : ℝ) + (j n s : ℝ) * h n ≤ (s : ℝ) ∧
        (s : ℝ) < (a : ℝ) + ((j n s : ℝ) + 1) * h n := by
      have hsz := hSZ s hs
      apply exercise41FloorCellV4 (a : ℝ) (h n) (s : ℝ) (n+1) (hh n)
      · exact_mod_cast hsz.1
      · rw [hw n]
        exact_mod_cast hsz.2.1
    have hinj := exercise41FineCellsInjectiveV4 S (a : ℝ) h ht j
      (fun n s hs => (hc n s hs).2)
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp hinj
    refine ⟨m, fun n hn => ?_⟩
    have H := exercise41DenseCountLowerV5 (fun s => L.X s ω) q hq S
      (a : ℝ) (h n) (L.drift * h n / 8) (n+1)
      (by positivity) (j n) (hc n) (hm n hn)
      (fun s _ => L.rightCont ω s) (fun s hs => (hSZ s hs).2.2)
    rw [hSc] at H
    simpa only [N, A, Set.indicator_apply, Set.mem_setOf_eq] using H
  exact (lt_irrefl (⊤ : ℝ≥0∞)) (htop ▸ hω)
