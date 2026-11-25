-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_actual_exp_grid_linearization_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:28:07.63277+00:00
-- url     : https://prove2.me/submissions/7e8c61fe-9aa9-4a7b-adf8-61b97662cf9d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_exp_grid_linearization_limit
import Theorems.Thm_Kyprianou_Ch04_kw47_reflected_exp_bounds
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The actual running-supremum exponent has vanishing first-order
grid error, using continuity and variation, without Lipschitzness. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (w : Ω) (a b : NNReal) (hab : a ≤ b)
    (u : Nat → Nat → NNReal) (N : Nat → Nat)
    (hu : ∀ n, Monotone (u n))
    (h0 : ∀ n, u n 0 = a) (hN : ∀ n, u n (N n) = b)
    (delta : Nat → Real) (hDelta : Tendsto delta atTop (nhds 0))
    (hMesh : ∀ n i, i < N n →
      (u n (i+1) : Real) - (u n i : Real) ≤ delta n) :
    let G : NNReal → Real := fun r =>
      -alpha * runningSup L r w + L.ψ alpha * (r:Real)
    let Z : NNReal → Real := fun r =>
      Real.exp (-alpha * (runningSup L r w - L.X r w))
    Tendsto (fun n =>
      (∑ i ∈ Finset.range (N n), Z (u n (i+1)) *
        (1 - Real.exp (-(G (u n (i+1)) - G (u n i))))) -
      (∑ i ∈ Finset.range (N n), Z (u n (i+1)) *
        (G (u n (i+1)) - G (u n i)))) atTop (nhds 0) := by
  dsimp only
  let U : NNReal → Real := fun r => runningSup L r w
  let G : Real → Real := fun r => -alpha * U r.toNNReal + L.ψ alpha * r
  let Z : Nat → Nat → Real := fun n i =>
    Real.exp (-alpha * (U (u n (i+1)) - L.X (u n (i+1)) w))
  have hUm : Monotone U := (runningSup_monotone_and_path_le L w).1
  have hGc : Continuous G :=
    (continuous_const.mul ((runningSup_continuous_actual L w).comp
      continuous_real_toNNReal)).add (continuous_const.mul continuous_id)
  have hmono (n : Nat) : Monotone (fun i => (u n i : Real)) :=
    fun i j hij => by exact_mod_cast hu n hij
  let C : Real := alpha * (U b - U a) +
    |L.ψ alpha| * ((b:Real)-(a:Real))
  have hba : (a:Real) ≤ (b:Real) := by exact_mod_cast hab
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg hAlpha (sub_nonneg.mpr (hUm hab)))
    (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hba))
  have hZ (n i : Nat) : |Z n i| ≤ 1 := by
    dsimp only [Z,U]
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Kyprianou.Ch04.kw47_reflected_exp_bounds L alpha hAlpha
      (u n (i+1)) w).2
  have hTel (f : Nat → Real) (k : Nat) :
      (∑ i ∈ Finset.range k, (f (i+1)-f i)) = f k - f 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; ring
  have hVar (n : Nat) :
      (∑ i ∈ Finset.range (N n),
        |G (u n (i+1):Real) - G (u n i:Real)|) ≤ C := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N n),
          (alpha * (U (u n (i+1))-U (u n i)) +
            |L.ψ alpha| * ((u n (i+1):Real)-(u n i:Real))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hU := sub_nonneg.mpr (hUm (hu n (Nat.le_succ i)))
        have ht := sub_nonneg.mpr (hmono n (Nat.le_succ i))
        simp only [G, Real.toNNReal_coe]
        rw [show -alpha * U (u n (i+1)) + L.ψ alpha * (u n (i+1):Real) -
          (-alpha * U (u n i) + L.ψ alpha * (u n i:Real)) =
          -alpha * (U (u n (i+1))-U (u n i)) +
            L.ψ alpha * ((u n (i+1):Real)-(u n i:Real)) by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hAlpha,
          abs_of_nonneg hU, abs_of_nonneg ht]
      _ = C := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hTel (fun i => U (u n i)), hTel (fun i => (u n i:Real)),
          hN n, h0 n]
  have h := Kyprianou.Ch04.kw47_exp_grid_linearization_limit
    (a:Real) (b:Real) G hGc.continuousOn
    (fun n i => (u n i:Real)) N hmono
    (fun n => by rw [h0 n]) (fun n => by rw [hN n])
    delta hDelta hMesh Z hZ C hC hVar
  simpa only [G,Z,U,Real.toNNReal_coe] using h
