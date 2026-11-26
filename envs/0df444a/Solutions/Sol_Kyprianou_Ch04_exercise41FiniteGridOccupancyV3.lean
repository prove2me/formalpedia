-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteGridOccupancyV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:13:13.86536+00:00
-- url     : https://prove2.me/submissions/cadc9fe5-ae7a-4fb7-9e84-9ea60cfd8f99

import Mathlib
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
import Theorems.Thm_Kyprianou_Ch04_exercise41GridRestartFactorV3
import Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstMemberV3
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulCellsV2
import Theorems.Thm_Kyprianou_Ch04_exercise41OccupancyFromCardV3
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (I : Finset ℕ) (D : ℕ → Finset NNReal) (b : ℕ → NNReal)
    (R : Finset NNReal) (δ : NNReal) (a h : ℝ)
    (hh : 0 < h) (hd : 0 < L.drift)
    (hD : ∀ i ∈ I, ∀ t ∈ D i, t ≤ b i)
    (hcell : ∀ i ∈ I, ∀ t ∈ D i,
      a + (i : ℝ) * h ≤ (t : ℝ) ∧
      (t : ℝ) < a + ((i : ℝ) + 1) * h)
    (hR : ∀ u ∈ R, 0 < u ∧ u ≤ δ)
    (hDiff : ∀ i ∈ I, ∀ j ∈ I, i < j →
      ∀ s ∈ D i, ∀ t ∈ D j, t - s ∈ R) :
    let C : NNReal → Set Ω := fun t => {ω | |L.X t ω| < L.drift * h / 8}
    let A : ℕ → Set Ω := fun i => {ω | ∃ t ∈ D i, ω ∈ C t}
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    (∀ i ∈ I, MeasurableSet (A i)) ∧
      p * ∑ i ∈ I, P (A i) ≤ 2 := by
  letI : IsProbabilityMeasure P := L.isProbability
  dsimp only
  let C : NNReal → Set Ω := fun t => {ω | |L.X t ω| < L.drift * h / 8}
  let A : ℕ → Set Ω := fun i => {ω | ∃ t ∈ D i, ω ∈ C t}
  let τ : ℕ → Ω → NNReal := fun i => exercise41GridFirstV2 (D i) C (b i)
  let G : Set (NNReal → ℝ) :=
    {y | ∀ u ∈ R, L.drift / 2 * (u : ℝ) ≤ y u}
  let B : ℕ → Set Ω := fun i =>
    A i ∩ {ω | (fun u => L.X (τ i ω + u) ω - L.X (τ i ω) ω) ∈ G}
  let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
    L.drift / 2 * (u : ℝ) ≤ L.X u ω}
  change (∀ i ∈ I, MeasurableSet (A i)) ∧ p * ∑ i ∈ I, P (A i) ≤ 2
  have hf (i : ℕ) (hi : i ∈ I) :
      MeasurableSet (A i) ∧ MeasurableSet (B i) ∧ p * P (A i) ≤ P (B i) :=
    exercise41GridRestartFactorV3 P F L (D i) R (b i) δ
      (L.drift * h / 8) (hD i hi) hR
  refine ⟨fun i hi => (hf i hi).1, ?_⟩
  apply exercise41OccupancyFromCardV3 P I A B p
    (fun i hi => (hf i hi).2.1) (fun i hi => (hf i hi).2.2)
  intro ω
  let S := I.filter fun i => ω ∈ B i
  rw [Finset.filter_congr_decidable I (fun i => ω ∈ B i) _]
  change S.card ≤ 2
  have hc (i : ℕ) (hi : i ∈ S) :
      i ∈ I ∧ τ i ω ∈ D i ∧ |L.X (τ i ω) ω| < L.drift * h / 8 := by
    have hi' := Finset.mem_filter.mp hi
    have hm := exercise41GridFirstMemberV3 (D i) C (b i) ω hi'.2.1
    exact ⟨hi'.1, hm.1, hm.2⟩
  apply exercise41SuccessfulCellsV2 S (fun i => (τ i ω : ℝ))
    (fun i => L.X (τ i ω) ω) a h L.drift hh hd
  · intro i hi
    exact hcell i (hc i hi).1 _ (hc i hi).2.1
  · intro i hi
    exact (hc i hi).2.2
  · intro i hi j hj hij
    have hi' := hc i hi
    have hj' := hc j hj
    have hci := hcell i hi'.1 _ hi'.2.1
    have hcj := hcell j hj'.1 _ hj'.2.1
    have hidx : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hlt : (τ i ω : ℝ) < (τ j ω : ℝ) := by nlinarith
    have ht : τ i ω ≤ τ j ω := by exact_mod_cast hlt.le
    have hr := hDiff i hi'.1 j hj'.1 hij _ hi'.2.1 _ hj'.2.1
    have hs := (Finset.mem_filter.mp hi).2.2 _ hr
    have hadd : τ i ω + (τ j ω - τ i ω) = τ j ω := by
      rw [add_comm, tsub_add_cancel_of_le ht]
    change L.drift / 2 * ((τ j ω - τ i ω : NNReal) : ℝ) ≤
      L.X (τ i ω + (τ j ω - τ i ω)) ω - L.X (τ i ω) ω at hs
    rw [hadd, NNReal.coe_sub ht] at hs
    exact hs
