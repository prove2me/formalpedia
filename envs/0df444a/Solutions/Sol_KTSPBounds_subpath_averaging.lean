-- Prove2me | solution 1 for KTSPBounds.subpath_averaging
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:55:27.353794+00:00
-- url     : https://prove2.me/submissions/2f58e15d-6a5d-46f7-b643-e8608e8188ff

import Mathlib
import Definitions.Def_KTSPBounds_kTSPLength
import Definitions.Def_KTSPBounds_tourLength

open KTSPBounds MetricTSP Finset

lemma window_bound (m k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ m + 1) (x : Fin (m + 1) → Plane)
    (π : Equiv.Perm (Fin (m + 1))) :
    ((m + 1 : ℕ) : ℝ) * kTSPLength k x ≤ ((k : ℝ) - 1) * tourCost (fun i j => dist (x i) (x j)) π := by
  let ι : Fin k → Fin (m + 1) := fun i => Fin.castLE hkn i
  have hι : Function.Injective ι := Fin.castLE_injective hkn
  let σ : Fin (m + 1) → (Fin k ↪ Fin (m + 1)) := fun s =>
    ⟨fun i => π (s + ι i), fun a b h => Fin.castLE_injective hkn (add_left_cancel (π.injective h))⟩
  let d : Fin (m + 1) → ℝ := fun j => dist (x (π (j + 1))) (x (π j))
  let e : Fin (k - 1) → Fin (m + 1) := fun i => ⟨i.1, by have := i.2; omega⟩
  have hlen : ∀ s, ∑ i : Fin (k - 1), dist (x (σ s ⟨i.1 + 1, by have := i.2; omega⟩))
      (x (σ s ⟨i.1, by have := i.2; omega⟩)) = ∑ i : Fin (k - 1), d (s + e i) := by
    intro s
    apply sum_congr rfl; intro i _
    show dist (x (π (s + Fin.castLE hkn ⟨i.1 + 1, by have := i.2; omega⟩))) (x (π (s + Fin.castLE hkn ⟨i.1, by have := i.2; omega⟩))) = dist (x (π (s + e i + 1))) (x (π (s + e i)))
    have hi := i.2
    have h1 : s + Fin.castLE hkn ⟨i.1 + 1, by omega⟩ = s + (⟨i.1, by omega⟩ : Fin (m + 1)) + 1 := by
      rw [add_assoc]; congr 1
      apply Fin.ext
      simp only [Fin.coe_castLE, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [h1]; rfl
  have hle : ∀ s, kTSPLength k x ≤ ∑ i : Fin (k - 1), d (s + e i) := by
    intro s
    rw [← hlen s]
    exact ciInf_le (Finite.bddBelow_range _) (σ s)
  have hsum : ∑ s, ∑ i : Fin (k - 1), d (s + e i) = ((k : ℝ) - 1) * ∑ j, d j := by
    rw [sum_comm]
    have : ∀ i : Fin (k - 1), ∑ s, d (s + e i) = ∑ j, d j := fun i =>
      Fintype.sum_equiv (Equiv.addRight (e i)) _ _ (fun _ => rfl)
    rw [sum_congr rfl (fun i _ => this i), sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1; rw [Nat.cast_sub hk]; simp
  have htour : tourCost (fun i j => dist (x i) (x j)) π = ∑ j, d j := by
    unfold tourCost; apply sum_congr rfl; intro j _
    simp only [d, finRotate_apply, dist_comm]
  calc ((m + 1 : ℕ) : ℝ) * kTSPLength k x = ∑ _s : Fin (m + 1), kTSPLength k x := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ s, ∑ i : Fin (k - 1), d (s + e i) := sum_le_sum (fun s _ => hle s)
    _ = _ := by rw [hsum, htour]

theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (x : Fin n → Plane) :
    kTSPLength k x ≤ ((k : ℝ) - 1) / (n : ℝ) * tourLength x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set c : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j => dist (x i) (x j)
  have hset : {t : ℝ | ∃ π : Equiv.Perm (Fin (m + 1)), t = tourCost c π} = Set.range (tourCost c) := by
    ext t; simp [eq_comm]
  have hmem : tspOpt c ∈ Set.range (tourCost c) := by
    unfold tspOpt; rw [hset]
    exact (Set.range_nonempty _).csInf_mem (Set.finite_range _)
  obtain ⟨π, hπ⟩ := hmem
  have hw := window_bound m k hk hkn x π
  unfold tourLength
  rw [← hπ]
  have hn : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hn, mul_comm]
  exact hw
