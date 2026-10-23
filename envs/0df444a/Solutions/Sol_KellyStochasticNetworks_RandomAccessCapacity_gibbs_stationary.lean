-- Prove2me | solution 1 for KellyStochasticNetworks.RandomAccessCapacity.gibbs_stationary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:15:32.326844+00:00
-- url     : https://prove2.me/submissions/508440b9-cdd9-47cd-93a8-94b4f35cec71

import Definitions.Def_KellyStochasticNetworks_RandomAccessCapacity_Network

open KellyStochasticNetworks.RandomAccessCapacity
open Matrix
open scoped Norms.Operator

theorem g78g_expser {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ) (a b : m) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ • M ^ n) a b) (NormedSpace.exp M a b) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) M
  exact Pi.hasSum.1 (Pi.hasSum.1 h a) b

/-- a left null vector of `Q` is invariant under `exp (t Q)` -/
theorem g78g_inv {m : Type*} [Fintype m] [DecidableEq m] (Q : Matrix m m ℝ) (π : m → ℝ)
    (hπ : π ᵥ* Q = 0) (t : ℝ) (j : m) : ∑ i, π i * NormedSpace.exp (t • Q) i j = π j := by
  have hs : HasSum (fun n : ℕ => ∑ i, π i * ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) i j)
      (∑ i, π i * NormedSpace.exp (t • Q) i j) :=
    hasSum_sum fun i _ => (g78g_expser (t • Q) i j).mul_left (π i)
  have hz : ∀ n : ℕ, ∑ i, π i * ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) i j =
      if n = 0 then π j else 0 := by
    intro n
    have e : ∑ i, π i * ((n.factorial : ℝ)⁻¹ • (t • Q) ^ n) i j =
        ((n.factorial : ℝ)⁻¹ * t ^ n) * (π ᵥ* Q ^ n) j := by
      simp only [smul_pow, Matrix.smul_apply, smul_eq_mul, vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ' Q k, ← vecMul_vecMul, hπ, zero_vecMul]; simp
  rw [funext hz] at hs
  have h1 : HasSum (fun n : ℕ => if n = 0 then π j else 0) (π j) := hasSum_ite_eq 0 (π j)
  exact hs.unique h1

theorem solution {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj]
    (θ : Fin d → ℝ) :
    let S := {n : Fin d → Fin 2 // ∀ i j, G.Adj i j → n i = 0 ∨ n j = 0}
    let w : S → ℝ := fun n => Real.exp (∑ r, (n.val r : ℝ) * θ r)
    let π : S → ℝ := fun n => w n / ∑ m : S, w m
    let q : S → S → ℝ := fun n m =>
      ∑ r, if (∀ i, i ≠ r → m.val i = n.val i) ∧ m.val r ≠ n.val r
        then (if n.val r = 0 then Real.exp (θ r) else 1) else 0
    let Q : Matrix S S ℝ := fun n m =>
      if n = m then -(∑ k : S, q n k) else q n m
    (∀ n, 0 ≤ π n) ∧ (∑ n : S, π n) = 1 ∧
      ∀ t : ℝ, 0 ≤ t → ∀ m : S,
        (∑ n : S, π n * NormedSpace.exp (t • Q) n m) = π m := by
  intro S w π q Q
  have hw : ∀ n, 0 < w n := fun n => Real.exp_pos _
  have hne : Nonempty S := ⟨⟨fun _ => 0, fun i j _ => Or.inl rfl⟩⟩
  have hZ : 0 < ∑ m : S, w m := Finset.sum_pos (fun m _ => hw m) Finset.univ_nonempty
  -- detailed balance
  have hdb : ∀ n m : S, w n * q n m = w m * q m n := by
    intro n m
    simp only [q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hc : (∀ i, i ≠ r → m.val i = n.val i) ∧ m.val r ≠ n.val r
    · have hc' : (∀ i, i ≠ r → n.val i = m.val i) ∧ n.val r ≠ m.val r :=
        ⟨fun i hi => (hc.1 i hi).symm, fun h => hc.2 h.symm⟩
      rw [if_pos hc, if_pos hc']
      -- weights differ by the factor exp θ r
      have hsplit : ∀ x : S, ∑ i, (x.val i : ℝ) * θ i =
          (x.val r : ℝ) * θ r + ∑ i ∈ Finset.univ.erase r, (x.val i : ℝ) * θ i := fun x =>
        (Finset.add_sum_erase _ _ (Finset.mem_univ r)).symm
      have hrest : ∑ i ∈ Finset.univ.erase r, (m.val i : ℝ) * θ i =
          ∑ i ∈ Finset.univ.erase r, (n.val i : ℝ) * θ i :=
        Finset.sum_congr rfl fun i hi => by rw [hc.1 i (Finset.ne_of_mem_erase hi)]
      have hfin : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
      simp only [w]
      rw [hsplit n, hsplit m, hrest]
      rcases hfin _ _ hc.2 with ⟨hm, hn⟩ | ⟨hm, hn⟩
      · rw [hm, hn]
        simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_mul,
          one_mul, zero_add, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, mul_one]
        rw [Real.exp_add]; ring
      · rw [hm, hn]
        simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_mul,
          one_mul, zero_add, if_true, show (1 : Fin 2) ≠ 0 by decide, if_false, mul_one]
        rw [Real.exp_add]; ring
    · have hc' : ¬ ((∀ i, i ≠ r → n.val i = m.val i) ∧ n.val r ≠ m.val r) := fun h =>
        hc ⟨fun i hi => (h.1 i hi).symm, fun e => h.2 e.symm⟩
      rw [if_neg hc, if_neg hc']; ring
  have hqd : ∀ n : S, q n n = 0 := fun n => by
    simp only [q]; exact Finset.sum_eq_zero fun r _ => by rw [if_neg (fun h => h.2 rfl)]
  -- π Q = 0
  have hπQ : π ᵥ* Q = 0 := by
    funext m
    simp only [vecMul, dotProduct, Pi.zero_apply, Q, π]
    have : ∀ n : S, w n / (∑ k : S, w k) * (if n = m then -(∑ k : S, q n k) else q n m) =
        (w n * (if n = m then -(∑ k : S, q n k) else q n m)) / (∑ k : S, w k) := fun n => by ring
    rw [Finset.sum_congr rfl fun n _ => this n, ← Finset.sum_div, div_eq_zero_iff]
    left
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), if_pos rfl]
    have e2 : ∑ n ∈ Finset.univ.erase m, w n * (if n = m then -(∑ k : S, q n k) else q n m) =
        ∑ n ∈ Finset.univ.erase m, w m * q m n :=
      Finset.sum_congr rfl fun n hn => by rw [if_neg (Finset.ne_of_mem_erase hn), hdb]
    rw [e2, ← Finset.mul_sum, Finset.sum_erase _ (hqd m)]
    ring
  refine ⟨fun n => div_nonneg (hw n).le hZ.le, ?_, fun t _ m => g78g_inv Q π hπQ t m⟩
  simp only [π, ← Finset.sum_div]
  exact div_self hZ.ne'
