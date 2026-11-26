-- Prove2me | solution 1 for Kyprianou.Ch04.ucpDiagonalGeometricV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:08:57.158161+00:00
-- url     : https://prove2.me/submissions/2632a787-1d2e-472e-b886-3b118aa66d02

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology UniformConvergence
set_option autoImplicit false

/-- Summable deviation events give eventual geometric increments on expanding horizons. -/
theorem solution {Ω E : Type} [MeasurableSpace Ω] [MetricSpace E] [CompleteSpace E]
    (P : Measure Ω) (X : ℕ → NNReal → Ω → E)
    (hc : ∀ i : ℕ, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n →
      P {w | ∃ t ≤ (i : NNReal), (2⁻¹ : ℝ)^i < dist (X m t w) (X n t w)} ≤
        (2⁻¹ : ENNReal)^i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ᵐ w ∂P,
      ∀ᶠ n : ℕ in atTop, ∀ t ≤ (n : NNReal),
        dist (X (k n) t w) (X (k (n+1)) t w) ≤ (2⁻¹ : ℝ)^n := by
  classical
  choose N hN using hc
  let k : ℕ → ℕ := fun n => n + ∑ i ∈ Finset.range (n+1), N i
  have hkN : ∀ n, N n ≤ k n := by
    intro n
    exact (Finset.single_le_sum (fun i _ => Nat.zero_le (N i))
      (Finset.mem_range.mpr (Nat.lt_succ_self n))).trans (Nat.le_add_left _ _)
  have hk : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro n
    dsimp only [k]
    rw [Finset.sum_range_succ (n := n+1)]
    omega
  let A : ℕ → Set Ω := fun n =>
    {w | ∃ t ≤ (n : NNReal), (2⁻¹ : ℝ)^n < dist (X (k n) t w) (X (k (n+1)) t w)}
  have hA (n : ℕ) : P (A n) ≤ (2⁻¹ : ENNReal)^n :=
    hN n (k n) (k (n+1)) (hkN n) ((hkN n).trans (hk.monotone (Nat.le_succ n)))
  have hsum : (∑' n : ℕ, (2⁻¹ : ENNReal)^n) ≠ ⊤ := by
    simpa only [ENNReal.tsum_geometric,ENNReal.one_sub_inv_two,inv_inv] using
      (ENNReal.ofNat_ne_top : (2 : ENNReal) ≠ ⊤)
  have hsumA : (∑' n, P (A n)) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hA)
  refine ⟨k,hk,?_⟩
  filter_upwards [ae_eventually_notMem hsumA] with w hw
  filter_upwards [hw] with n hn
  intro t ht
  exact le_of_not_gt (fun h => hn ⟨t,ht,h⟩)
