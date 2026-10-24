-- Prove2me | solution 1 for ModernConvex.Spectral.spectral_function_sdr
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T22:15:45.598123+00:00
-- url     : https://prove2.me/submissions/12710ff1-65f3-41fb-b733-64c49ab3b0c9

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR
import Theorems.Thm_ModernConvex_Spectral_majorization_principle

open Matrix

namespace SPD98
open ModernConvex.Spectral

lemma eval_comb {m k N : ℕ} (S : EpiLMI m k N) (x y : Fin m → ℝ) (t : ℝ) (u v : Fin k → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    S.eval (a • x + b • y) t (a • u + b • v) = a • S.eval x t u + b • S.eval y t v := by
  obtain rfl : b = 1 - a := by linarith
  unfold EpiLMI.eval
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul, Finset.sum_add_distrib,
    ← Finset.smul_sum, smul_add]
  module

lemma sublevel_convex {m k N : ℕ} (g : (Fin m → ℝ) → EReal) (S : EpiLMI m k N)
    (hS : S.Represents g) (t : ℝ) : Convex ℝ {y | g y ≤ (t : EReal)} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨u, hu⟩ := (hS x t).1 hx
  obtain ⟨v, hv⟩ := (hS y t).1 hy
  refine (hS _ t).2 ⟨a • u + b • v, ?_⟩
  rw [eval_comb S x y t u v a b hab]
  exact (hu.smul ha).add (hv.smul hb)

lemma card_F {m : ℕ} (j : ℕ) (hj : j ≤ m) :
    (Finset.univ.filter (fun i : Fin m => (i : ℕ) < j)).card = j := by
  rw [Fin.card_filter_val_lt]; omega

lemma sum_le_partialSum {m : ℕ} (x : Fin m → ℝ) (hx : Antitone x) (j : ℕ) (hj : j ≤ m)
    (s : Finset (Fin m)) (hs : s.card = j) : ∑ i ∈ s, x i ≤ partialSum j x := by
  unfold partialSum
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [Finset.card_eq_zero.1 hs]; simp
  set c := x ⟨j - 1, by omega⟩
  set g : Fin m → ℝ := fun i => if (i : ℕ) < j then x i - c else 0
  have hfg : ∀ i, x i - c ≤ g i := by
    intro i; simp only [g]; split_ifs with h
    · exact le_rfl
    · have : x i ≤ c := hx (show (⟨j - 1, by omega⟩ : Fin m) ≤ i from by
        rw [Fin.le_def]; simp; omega)
      linarith
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i; simp only [g]; split_ifs with h
    · have : c ≤ x i := hx (show i ≤ (⟨j - 1, by omega⟩ : Fin m) from by
        rw [Fin.le_def]; simp; omega)
      linarith
    · exact le_rfl
  have h1 : ∑ i ∈ s, (x i - c) ≤ ∑ i, g i :=
    (Finset.sum_le_sum fun i _ => hfg i).trans
      (Finset.sum_le_univ_sum_of_nonneg (fun i => hg0 i))
  have h2 : ∑ i, g i = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), (x i - c) := by
    simp only [g]; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [h2, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    card_F j hj, hs] at h1
  linarith

end SPD98

open ModernConvex.Spectral in
theorem solution {m k N : ℕ} (g : (Fin m → ℝ) → EReal) (hg : ∀ x, g x ≠ ⊥)
    (hsym : IsSymmetricFn g) (S : EpiLMI m k N) (hS : S.Represents g)
    (X : Matrix (Fin m) (Fin m) ℝ) (hX : X.IsHermitian) (t : ℝ) :
    g (eigVec X) ≤ (t : EReal) ↔
      ∃ (x : Fin m → ℝ) (u : Fin k → ℝ),
        (S.eval x t u).PosSemidef ∧ Antitone x ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → sumLargestEig j X ≤ partialSum j x) ∧
        X.trace = ∑ i, x i := by
  have hev : eigVec X = fun i => hX.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm i) := by
    unfold eigVec; rw [dif_pos hX]
  have hanti : Antitone (eigVec X) := by
    rw [hev]; intro i j hij; exact hX.eigenvalues₀_antitone (by simpa using hij)
  have htr : X.trace = ∑ i, eigVec X i := by
    rw [hX.trace_eq_sum_eigenvalues, hev]
    simp only [RCLike.ofReal_real_eq_id, id]
    unfold IsHermitian.eigenvalues
    rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm (fun k => hX.eigenvalues₀ k)]
    exact (Equiv.sum_comp (finCongr (Fintype.card_fin m).symm) (fun k => hX.eigenvalues₀ k)).symm
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (hS _ t).1 h
    exact ⟨eigVec X, u, hu, hanti, fun j _ _ => le_rfl, htr⟩
  · rintro ⟨x, u, hu, hx, hj, hsum⟩
    have hgx : g x ≤ (t : EReal) := (hS x t).2 ⟨u, hu⟩
    have hmem : eigVec X ∈ permHull x := by
      rw [majorization_principle]
      refine ⟨fun j hj1 hjm => ?_, by rw [← htr, hsum]⟩
      have hne : Nonempty {s : Finset (Fin m) // s.card = j} := by
        obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m)))
          (n := j) (by simp; omega)
        exact ⟨⟨s, hs⟩⟩
      have hbdd : ∀ y : Fin m → ℝ, BddAbove (Set.range fun s : {s : Finset (Fin m) // s.card = j} =>
          ∑ i ∈ s.1, y i) := fun y => (Set.finite_range _).bddAbove
      unfold sumLargest
      refine ciSup_le fun s => ?_
      calc ∑ i ∈ s.1, eigVec X i ≤ partialSum j (eigVec X) := SPD98.sum_le_partialSum _ hanti j (by omega) s.1 s.2
        _ = sumLargestEig j X := rfl
        _ ≤ partialSum j x := hj j hj1 hjm
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < j), x i := rfl
        _ ≤ _ := by
          refine le_ciSup (f := fun s : {s : Finset (Fin m) // s.card = j} => ∑ i ∈ s.1, x i)
            (hbdd x) ⟨_, SPD98.card_F j (by omega)⟩
    have hconv := SPD98.sublevel_convex g S hS t
    have : permHull x ⊆ {y | g y ≤ (t : EReal)} := by
      refine convexHull_min ?_ hconv
      rintro _ ⟨σ, rfl⟩
      simp only [Set.mem_setOf_eq]; rw [hsym]; exact hgx
    exact this hmem
