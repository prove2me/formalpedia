-- Prove2me | solution 1 for MDPFinance.BayesianModels.theorem_5_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:57:08.986366+00:00
-- url     : https://prove2.me/submissions/fcc9d5b9-b8ef-45e3-8f25-ca21e7fe8a42

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_OneKnownArmBandit

open MeasureTheory

namespace Band552Aux
open MDPFinance.BayesianModels

lemma pK_nonneg (mn : KnownArmState) : 0 ≤ pK mn := by
  unfold pK; positivity

lemma pK_le_one (mn : KnownArmState) : pK mn ≤ 1 := by
  unfold pK
  rw [div_le_one (by positivity)]
  have : (0:ℝ) ≤ mn.2 := by positivity
  linarith

lemma PK_mono {v w : KnownArmState → ℝ} (h : ∀ x, v x ≤ w x) (mn : KnownArmState) :
    PK v mn ≤ PK w mn := by
  unfold PK
  have h0 := pK_nonneg mn
  have h1 := pK_le_one mn
  have a := h (mn.1 + 1, mn.2)
  have b := h (mn.1, mn.2 + 1)
  nlinarith

lemma PK_pK (mn : KnownArmState) : PK pK mn = pK mn := by
  obtain ⟨m, n⟩ := mn
  unfold PK pK
  simp only [Nat.cast_add, Nat.cast_one]
  have h1 : (m:ℝ) + n + 2 ≠ 0 := by positivity
  have h2 : (m:ℝ) + 1 + n + 2 ≠ 0 := by positivity
  have h3 : (m:ℝ) + (n + 1) + 2 ≠ 0 := by positivity
  field_simp
  ring

lemma pK_mono {m n m' n' : ℕ} (hm : m ≤ m') (hn : n' ≤ n) : pK (m, n) ≤ pK (m', n') := by
  unfold pK
  simp only
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have a : (m:ℝ) ≤ m' := by exact_mod_cast hm
  have b : (n':ℝ) ≤ n := by exact_mod_cast hn
  have c : (0:ℝ) ≤ m := by positivity
  have d : (0:ℝ) ≤ n' := by positivity
  nlinarith [mul_le_mul a b d (by linarith)]

def Mono (v : KnownArmState → ℝ) : Prop :=
  ∀ m n m' n' : ℕ, m ≤ m' → n' ≤ n → v (m, n) ≤ v (m', n')

lemma PK_mono_order {w : KnownArmState → ℝ} (hw : Mono w) : Mono (PK w) := by
  intro m n m' n' hm hn
  unfold PK
  simp only
  have hp := pK_mono hm hn
  have p0 := pK_nonneg (m', n')
  have p1' := pK_le_one (m', n')
  have hA : w (m + 1, n) ≤ w (m' + 1, n') := hw _ _ _ _ (by omega) hn
  have hB : w (m, n + 1) ≤ w (m', n' + 1) := hw _ _ _ _ hm (by omega)
  have hAB : w (m, n + 1) ≤ w (m + 1, n) := hw _ _ _ _ (by omega) (by omega)
  nlinarith [mul_le_mul_of_nonneg_left hA p0, mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ 1 - pK (m', n')),
    mul_le_mul_of_nonneg_right hp (by linarith : (0:ℝ) ≤ w (m + 1, n) - w (m, n + 1))]

variable (p1 β : ℝ)

lemma JK_succ (k : ℕ) (mn : KnownArmState) :
    JK p1 β (k + 1) mn = p1 + β * JK p1 β k mn + max (dK p1 β (k + 1) mn) 0 := by
  simp only [JK, dK]
  rcases le_total (p1 + β * JK p1 β k mn) (pK mn + β * PK (JK p1 β k) mn) with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

lemma dK_one (mn : KnownArmState) : dK p1 β 1 mn = pK mn - p1 := by
  simp [dK, JK, PK]

lemma dK_rec (j : ℕ) (mn : KnownArmState) :
    dK p1 β (j + 2) mn = (1 - β) * (pK mn - p1)
      + β * PK (fun x => max (dK p1 β (j + 1) x) 0) mn + β * min (dK p1 β (j + 1) mn) 0 := by
  have hJ : JK p1 β (j + 1) = fun x => p1 + β * JK p1 β j x + max (dK p1 β (j + 1) x) 0 :=
    funext (JK_succ p1 β j)
  have hd : dK p1 β (j + 2) mn = pK mn + β * PK (JK p1 β (j + 1)) mn
      - (p1 + β * JK p1 β (j + 1) mn) := rfl
  have hd1 : dK p1 β (j + 1) mn = pK mn + β * PK (JK p1 β j) mn - (p1 + β * JK p1 β j mn) := rfl
  have hmin : min (dK p1 β (j + 1) mn) 0 = dK p1 β (j + 1) mn - max (dK p1 β (j + 1) mn) 0 := by
    rcases le_total (dK p1 β (j + 1) mn) 0 with h | h
    · rw [min_eq_left h, max_eq_right h]; ring
    · rw [min_eq_right h, max_eq_left h]; ring
  rw [hd, hmin, hJ]
  unfold PK at hd1 ⊢
  linear_combination (-β) * hd1

lemma dK_le_succ (hβ : 0 ≤ β) (j : ℕ) : ∀ mn, dK p1 β (j + 1) mn ≤ dK p1 β (j + 2) mn := by
  induction j with
  | zero =>
    intro mn
    have hf : (fun x => max (dK p1 β (0 + 1) x) 0) = fun x => max (pK x - p1) 0 :=
      funext fun x => by rw [dK_one]
    rw [dK_rec, hf, dK_one]
    have hP : PK (fun x => pK x - p1) mn = pK mn - p1 := by
      have := PK_pK mn; unfold PK at this ⊢; linarith
    have h1 : pK mn - p1 ≤ PK (fun x => max (pK x - p1) 0) mn := by
      rw [← hP]; exact PK_mono (fun x => le_max_left _ _) mn
    have h2 : 0 ≤ PK (fun x => max (pK x - p1) 0) mn := by
      have := PK_mono (v := fun _ => (0:ℝ)) (w := fun x => max (pK x - p1) 0)
        (fun x => le_max_right _ _) mn
      unfold PK at this ⊢; linarith
    rcases le_total (pK mn - p1) 0 with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  | succ j ih =>
    intro mn
    have e1 := dK_rec p1 β (j + 1) mn
    have e2 := dK_rec p1 β j mn
    have h1 : PK (fun x => max (dK p1 β (j + 1) x) 0) mn ≤ PK (fun x => max (dK p1 β (j + 1 + 1) x) 0) mn :=
      PK_mono (fun x => max_le_max (ih x) le_rfl) mn
    have h2 : min (dK p1 β (j + 1) mn) 0 ≤ min (dK p1 β (j + 1 + 1) mn) 0 := min_le_min (ih mn) le_rfl
    nlinarith

lemma dK_mono (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (j : ℕ) : Mono (dK p1 β (j + 1)) := by
  induction j with
  | zero =>
    intro m n m' n' hm hn
    rw [dK_one, dK_one]; linarith [pK_mono hm hn]
  | succ j ih =>
    intro m n m' n' hm hn
    rw [dK_rec, dK_rec]
    have hP := PK_mono_order (w := fun x => max (dK p1 β (j + 1) x) 0)
      (fun a b c d h1 h2 => max_le_max (ih a b c d h1 h2) le_rfl) m n m' n' hm hn
    have hmn := min_le_min (ih m n m' n' hm hn) (le_refl (0:ℝ))
    have hp := pK_mono hm hn
    nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : (0:ℝ) ≤ 1 - β)]

lemma dK_ge (hβ0 : 0 ≤ β) (j : ℕ) (mn : KnownArmState) : pK mn - p1 ≤ dK p1 β (j + 1) mn := by
  induction j with
  | zero => rw [dK_one]
  | succ j ih => exact ih.trans (dK_le_succ p1 β hβ0 j mn)

end Band552Aux

open MDPFinance.BayesianModels in
theorem solution (p1 β : ℝ) (hp1_0 : 0 < p1) (hp1_1 : p1 < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (N : ℕ) (f : ℕ → KnownArmState → Fin 2)
    (hf : ∀ k mn, f k mn = if 0 ≤ dK p1 β k mn then (1 : Fin 2) else 0) :
    (∀ mn, VpiK p1 β f N mn = JK p1 β N mn) ∧
      (∀ (g : ℕ → KnownArmState → Fin 2) (mn : KnownArmState), VpiK p1 β g N mn ≤ JK p1 β N mn) ∧
      (∀ k, 1 ≤ k → ∀ m n m' n', m ≤ m' → n' ≤ n → f k (m, n) ≤ f k (m', n')) ∧
      (∀ k, 1 ≤ k → ∀ m n, f (k + 1) (m, n) = 1 → f k (m + 1, n) = 1) ∧
      (∀ k, 1 ≤ k → ∀ m n, f (k + 1) (m, n) = 0 → f k (m, n) = 0) ∧
      (∀ k ≥ 1, ∀ mn, p1 ≤ pK mn → f k mn = 1) := by
  have hβ0' : 0 ≤ β := hβ0.le
  have hf1 : ∀ k mn, 0 ≤ dK p1 β k mn → f k mn = 1 := fun k mn h => by rw [hf]; simp [h]
  have hf0 : ∀ k mn, ¬ 0 ≤ dK p1 β k mn → f k mn = 0 := fun k mn h => by rw [hf]; simp [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · induction N with
    | zero => intro mn; simp [VpiK, JK]
    | succ k ih =>
      intro mn
      have hV : VpiK p1 β f k = JK p1 β k := funext ih
      have hd : dK p1 β (k + 1) mn = pK mn + β * PK (JK p1 β k) mn - (p1 + β * JK p1 β k mn) := rfl
      simp only [VpiK, JK]
      by_cases h : 0 ≤ dK p1 β (k + 1) mn
      · rw [hf1 _ _ h, hV, max_eq_right (by linarith)]; simp
      · rw [hf0 _ _ h, hV, max_eq_left (by linarith)]; simp
  · induction N with
    | zero => intro g mn; simp [VpiK, JK]
    | succ k ih =>
      intro g mn
      simp only [VpiK, JK]
      split_ifs
      · exact le_max_of_le_left (by nlinarith [ih g mn])
      · exact le_max_of_le_right (by nlinarith [Band552Aux.PK_mono (ih g) mn])
  · intro k hk m n m' n' hm hn
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have := Band552Aux.dK_mono p1 β hβ0' hβ1 j m n m' n' hm hn
    by_cases h : 0 ≤ dK p1 β (j + 1) (m, n)
    · rw [hf1 _ _ h, hf1 _ _ (h.trans this)]
    · rw [hf0 _ _ h]; exact Fin.zero_le _
  · intro k hk m n h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    by_contra hc
    have hneg : dK p1 β (j + 1) (m + 1, n) < 0 := by
      by_contra h'; exact hc (hf1 _ _ (not_lt.mp h'))
    have hmono := Band552Aux.dK_mono p1 β hβ0' hβ1 j
    have h1 : dK p1 β (j + 1) (m, n) ≤ dK p1 β (j + 1) (m + 1, n) := hmono _ _ _ _ (by omega) le_rfl
    have h2 : dK p1 β (j + 1) (m, n + 1) ≤ dK p1 β (j + 1) (m + 1, n) :=
      hmono _ _ _ _ (by omega) (by omega)
    have ha := Band552Aux.dK_ge p1 β hβ0' j (m, n)
    have e := Band552Aux.dK_rec p1 β j (m, n)
    have hP : PK (fun x => max (dK p1 β (j + 1) x) 0) (m, n) = 0 := by
      unfold PK
      simp only
      rw [max_eq_right hneg.le, max_eq_right (by linarith)]; ring
    rw [hP, min_eq_left (by linarith)] at e
    have hlt : dK p1 β (j + 1 + 1) (m, n) < 0 := by
      show dK p1 β (j + 2) (m, n) < 0
      rw [e]; nlinarith
    have := hf0 _ _ (not_le.mpr hlt)
    rw [this] at h; exact absurd h (by decide)
  · intro k hk m n h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    apply hf0
    intro h'
    have := hf1 _ _ (h'.trans (Band552Aux.dK_le_succ p1 β hβ0' j (m, n)))
    rw [this] at h; exact absurd h (by decide)
  · intro k hk mn h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact hf1 _ _ (by linarith [Band552Aux.dK_ge p1 β hβ0' j mn])
