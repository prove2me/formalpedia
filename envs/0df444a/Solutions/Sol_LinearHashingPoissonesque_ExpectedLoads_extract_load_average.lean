-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.extract_load_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:14:50.887093+00:00
-- url     : https://prove2.me/submissions/eefbe9c9-34d8-4554-bd1f-ec00546e8610

import Mathlib
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads

section
set_option autoImplicit false
namespace LinearHashingPoissonesque.Dev.Extract

lemma sum_affine (s : List ℕ) (a b : ℝ) :
    (s.map (fun x : ℕ => a + b * (x : ℝ))).sum = s.length * a + b * (s.map (fun x : ℕ => (x : ℝ))).sum := by
  induction s with
  | nil => simp
  | cons x t ih => simp [ih]; ring

lemma jensen (s : List ℕ) (hs : 0 < s.length) (lam mu : ℝ) :
    (s.length : ℝ) * Real.exp (lam * ((s.map (fun x : ℕ => (x : ℝ))).sum / s.length - mu))
      ≤ (s.map (fun x : ℕ => Real.exp (lam * ((x : ℝ) - mu)))).sum := by
  set c := lam * ((s.map (fun x : ℕ => (x : ℝ))).sum / s.length - mu) with hc
  have hlen : (s.length : ℝ) ≠ 0 := by positivity
  have h1 : (s.map (fun x : ℕ => Real.exp c * ((1 - c - lam * mu) + lam * (x : ℝ)))).sum
      ≤ (s.map (fun x : ℕ => Real.exp (lam * ((x : ℝ) - mu)))).sum := by
    apply List.Forall₂.sum_le_sum
    · simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      apply List.forall₂_same.2
      intro x _
      have := Real.add_one_le_exp (lam * ((x : ℝ) - mu) - c)
      rw [Real.exp_sub] at this
      have h2 : 0 < Real.exp c := Real.exp_pos c
      rw [le_div_iff₀ h2] at this
      nlinarith
  refine le_trans (le_of_eq ?_) h1
  have : (s.map (fun x : ℕ => Real.exp c * ((1 - c - lam * mu) + lam * (x : ℝ)))).sum
      = Real.exp c * (s.map (fun x : ℕ => ((1 - c - lam * mu) + lam * (x : ℝ)))).sum := by
    rw [List.sum_map_mul_left]
  rw [this, sum_affine]
  have : lam * (s.map (fun x : ℕ => (x : ℝ))).sum = s.length * (c + lam * mu) := by
    rw [hc]; field_simp; ring
  rw [mul_add, this]; ring_nf

lemma sum_eq_list {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) (F : ℕ → ℝ) :
    ∑ y : B, F (LinearHashingPoissonesque.ExpectedLoads.binLoad S f y)
      = ((LinearHashingPoissonesque.ExpectedLoads.sortedLoads S f).map F).sum := by
  unfold LinearHashingPoissonesque.ExpectedLoads.sortedLoads
  have h := Multiset.sort_eq (Finset.univ.val.map (LinearHashingPoissonesque.ExpectedLoads.binLoad S f)) (· ≤ ·)
  generalize (Multiset.map (LinearHashingPoissonesque.ExpectedLoads.binLoad S f) Finset.univ.val).sort (· ≤ ·) = l at h ⊢
  have h2 : (l.map F).sum = ((↑l : Multiset ℕ).map F).sum := by simp
  rw [h2, h]
  rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
  rfl

lemma core {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) (lam mu : ℝ) (s l : List ℕ)
    (hsl : s.Sublist l)
    (hl : l.Perm (LinearHashingPoissonesque.ExpectedLoads.sortedLoads S f)) (hs : 0 < s.length) :
    (s.length : ℝ) * Real.exp (lam * ((s.map (fun x : ℕ => (x : ℝ))).sum / s.length - mu))
      ≤ ∑ y : B, Real.exp (lam * ((LinearHashingPoissonesque.ExpectedLoads.binLoad S f y : ℝ) - mu)) := by
  rw [sum_eq_list S f (fun x : ℕ => Real.exp (lam * ((x : ℝ) - mu)))]
  refine le_trans (jensen s hs lam mu) ?_
  rw [← (hl.map _).sum_eq]
  exact (hsl.map _).sum_le_sum (by simp; intro a _; positivity)

end LinearHashingPoissonesque.Dev.Extract

namespace LinearHashingPoissonesque.ExpectedLoads
open LinearHashingPoissonesque.Dev.Extract in
theorem chk_extract_load_average {u ell : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell)
    (S : Finset (Fin u → ZMod 2)) (f : (Fin u → ZMod 2) → (Fin ell → ZMod 2))
    (lam : ℝ) (sign : Extreme) :
    lam * (extremeAverage S f r sign - (S.card : ℝ) / (2 : ℝ) ^ ell) -
      Real.log (((2 : ℝ) ^ ell) / (r : ℝ)) ≤ logPotential S f lam := by
  have hcard : (Fintype.card (Fin ell → ZMod 2) : ℝ) = (2 : ℝ) ^ ell := by simp
  have hlen : (sortedLoads S f).length = 2 ^ ell := by
    simp [sortedLoads]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hn0 : (0 : ℝ) < (2 : ℝ) ^ ell := by positivity
  have key : ∀ s l : List ℕ, s.Sublist l → l.Perm (sortedLoads S f) → s.length = r →
      lam * ((s.map (fun x : ℕ => (x : ℝ))).sum / r - (S.card : ℝ) / (2 : ℝ) ^ ell) -
        Real.log (((2 : ℝ) ^ ell) / (r : ℝ)) ≤ logPotential S f lam := by
    intro s l hsl hl hsr
    have h := core S f lam ((S.card : ℝ) / (2 : ℝ) ^ ell) s l hsl hl (by omega)
    rw [hsr] at h
    unfold logPotential
    rw [hcard]
    have hpos : 0 < (r : ℝ) * Real.exp (lam * ((s.map (fun x : ℕ => (x : ℝ))).sum / r - (S.card : ℝ) / (2 : ℝ) ^ ell)) := by positivity
    have h3 : Real.log ((r : ℝ) * Real.exp (lam * ((s.map (fun x : ℕ => (x : ℝ))).sum / r - (S.card : ℝ) / (2 : ℝ) ^ ell)) / (2 : ℝ) ^ ell)
        ≤ Real.log ((∑ y, Real.exp (lam * ((binLoad S f y : ℝ) - (S.card : ℝ) / (2 : ℝ) ^ ell))) / (2 : ℝ) ^ ell) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right h hn0.le)
    refine le_trans (le_of_eq ?_) h3
    rw [Real.log_div hpos.ne' hn0.ne', Real.log_mul hr0.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hn0.ne' hr0.ne']
    ring
  have hlr : r ≤ (sortedLoads S f).length := by omega
  cases sign with
  | lightest =>
    unfold extremeAverage lightestAverage
    simp only [Nat.cast_list_sum] 
    exact key _ _ (List.take_sublist _ _) (List.Perm.refl _) (by simp; omega)
  | heaviest =>
    unfold extremeAverage heaviestAverage
    simp only [Nat.cast_list_sum]
    exact key _ _ (List.take_sublist _ _) (List.reverse_perm _) (by simp; omega)

end LinearHashingPoissonesque.ExpectedLoads
end

theorem solution : type_of% @LinearHashingPoissonesque.ExpectedLoads.chk_extract_load_average := @LinearHashingPoissonesque.ExpectedLoads.chk_extract_load_average
