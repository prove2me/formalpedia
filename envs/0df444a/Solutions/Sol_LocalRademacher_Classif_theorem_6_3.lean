-- Prove2me | solution 1 for LocalRademacher.Classif.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T06:33:03.458991+00:00
-- url     : https://prove2.me/submissions/2680d4af-a4b4-4608-9ace-6eda9e8431ac

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_LocalRademacher_Classif_Setting

set_option autoImplicit false

namespace A76222c0

open LocalRademacher.Classif UnderstandingML

lemma ell_pm {f y : ℝ} (hf : f = 1 ∨ f = -1) (hy : y = 1 ∨ y = -1) :
    ell f y = (1 - f * y) / 2 := by
  rcases hf with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [ell]

lemma abs_ell_sign {f : ℝ} (hf : f = 1 ∨ f = -1) (s : ℝ) :
    |s| * ell f (Real.sign s) = (|s| - f * s) / 2 := by
  rcases lt_trichotomy s 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]
    rcases hf with rfl | rfl <;> norm_num [ell] <;> ring
  · subst h; simp
  · rw [Real.sign_of_pos h, abs_of_pos h]
    rcases hf with rfl | rfl <;> norm_num [ell]

lemma key_i {f y : ℝ} (hf : f = 1 ∨ f = -1) (hy : y = 1 ∨ y = -1) (t μ : ℝ) :
    (-t * y) * ell f y + t * y / 2
      = μ * ell f y - μ / 2 + |t + μ * y| / 2
        - |t + μ * y| * ell f (Real.sign (t + μ * y)) := by
  rw [ell_pm hf hy, abs_ell_sign hf]
  rcases hy with rfl | rfl <;> ring

def flipW {n : ℕ} (w : Fin n → Bool) (τ : Fin n → Bool) : Fin n → Bool :=
  fun i => xor (w i) (τ i)

lemma flipW_inv {n : ℕ} (w : Fin n → Bool) : Function.Involutive (flipW w) := by
  intro τ; funext i; simp only [flipW]; cases w i <;> cases τ i <;> rfl

lemma signVec_flipW {n : ℕ} (w : Fin n → Bool) (τ : Fin n → Bool) (i : Fin n) :
    signVec (flipW w τ) i = if w i then -signVec τ i else signVec τ i := by
  unfold signVec flipW
  cases w i <;> cases τ i <;> norm_num

lemma sum_signVec_zero {n : ℕ} (i : Fin n) : ∑ τ : Fin n → Bool, signVec τ i = 0 := by
  have h := Equiv.sum_comp (Function.Involutive.toPerm _ (flipW_inv (fun j => decide (j = i))))
    (fun τ => signVec τ i)
  have h2 : ∀ τ, signVec (flipW (fun j => decide (j = i)) τ) i = -signVec τ i := by
    intro τ; rw [signVec_flipW]; simp
  simp only [Function.Involutive.coe_toPerm, h2, Finset.sum_neg_distrib] at h
  linarith

lemma sum_sum_zero {n : ℕ} (ys : Fin n → ℝ) :
    ∑ τ : Fin n → Bool, ∑ i, signVec τ i * ys i = 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Finset.sum_mul, sum_signVec_zero, zero_mul]

lemma signVec_flip_ys {n : ℕ} (ys : Fin n → ℝ) (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (τ : Fin n → Bool) (i : Fin n) :
    signVec (flipW (fun j => decide (ys j = 1)) τ) i = -signVec τ i * ys i := by
  rw [signVec_flipW]
  rcases hys i with h | h
  · simp [h]
  · have : ¬ ((-1 : ℝ) = 1) := by norm_num
    simp [h, this]

lemma key {X : Type*} {n : ℕ} (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1) (F : Set (X → ℝ))
    (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (f : X → ℝ) (hfF : f ∈ F) (hfb : empLoss xs ys f ≤ b) (τ : Fin n → Bool)
    (μ : ℝ) (hμ : 0 ≤ μ) :
    (∑ i, signVec (flipW (fun j => decide (ys j = 1)) τ) i * ell (f (xs i)) (ys i)
      + (∑ i, signVec τ i * ys i) / 2) / n
    ≤ (b - 1 / 2) * μ + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + μ * ys i|
        - J F xs ys τ μ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hJ : J F xs ys τ μ ≤ (1 / (n : ℝ)) * ∑ i, |signVec τ i + μ * ys i| *
      ell (f (xs i)) (Real.sign (signVec τ i + μ * ys i)) := by
    unfold J
    refine ciInf_le ⟨0, ?_⟩ (⟨f, hfF⟩ : F)
    rintro _ ⟨g, rfl⟩
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg; intro i _
    apply mul_nonneg (abs_nonneg _)
    unfold ell; split_ifs <;> norm_num
  have hL : ∑ i, ell (f (xs i)) (ys i) ≤ n * b := by
    unfold empLoss at hfb
    have := mul_le_mul_of_nonneg_left hfb hnpos.le
    rw [← mul_assoc, mul_one_div_cancel hnpos.ne', one_mul] at this
    exact this
  have hμL := mul_le_mul_of_nonneg_left hL hμ
  have hid : ∑ i, ((-signVec τ i * ys i) * ell (f (xs i)) (ys i) + signVec τ i * ys i / 2)
      = ∑ i, (μ * ell (f (xs i)) (ys i) - μ / 2 + |signVec τ i + μ * ys i| / 2
        - |signVec τ i + μ * ys i| * ell (f (xs i)) (Real.sign (signVec τ i + μ * ys i))) :=
    Finset.sum_congr rfl (fun i _ => key_i (hF f hfF (xs i)) (hys i) (signVec τ i) μ)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hid
  simp only [signVec_flip_ys ys hys]
  have hJn := mul_le_mul_of_nonneg_right hJ hnpos.le
  have e1 : (1 / (n : ℝ)) * (∑ i, |signVec τ i + μ * ys i| *
      ell (f (xs i)) (Real.sign (signVec τ i + μ * ys i))) * n
      = ∑ i, |signVec τ i + μ * ys i| *
      ell (f (xs i)) (Real.sign (signVec τ i + μ * ys i)) := by field_simp
  have e2 : (1 / (2 * (n : ℝ))) * (∑ i, |signVec τ i + μ * ys i|) * n
      = (∑ i, |signVec τ i + μ * ys i|) / 2 := by field_simp
  rw [div_le_iff₀ hnpos]
  nlinarith

lemma inner_bound {X : Type*} {n : ℕ} (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1) (F : Set (X → ℝ))
    (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (hb : ∃ f ∈ F, empLoss xs ys f ≤ b) :
    rademacher (lossVecs F xs ys b) ≤
      (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        ⨅ μ : Set.Ici (0 : ℝ),
          ((b - 1 / 2) * (μ : ℝ)
            + (1 / (2 * (n : ℝ))) * ∑ i, |signVec σ i + (μ : ℝ) * ys i|
            - J F xs ys σ μ) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨f0, hf0F, hf0b⟩ := hb
  set w : Fin n → Bool := fun j => decide (ys j = 1) with hw
  have hne : Nonempty (lossVecs F xs ys b) :=
    ⟨⟨fun i => ell (f0 (xs i)) (ys i), f0, hf0F, hf0b, rfl⟩⟩
  have : Nonempty (Set.Ici (0 : ℝ)) := ⟨⟨0, Set.mem_Ici.mpr le_rfl⟩⟩
  set S : (Fin n → Bool) → ℝ := fun σ =>
    ⨆ a : lossVecs F xs ys b, ∑ i, signVec σ i * (a : Fin n → ℝ) i with hS
  have hperm : ∑ σ, S σ = ∑ τ, S (flipW w τ) :=
    (Equiv.sum_comp (Function.Involutive.toPerm _ (flipW_inv w)) S).symm
  have hper : ∀ τ : Fin n → Bool, (1 / (n : ℝ)) * S (flipW w τ) ≤
      (⨅ μ : Set.Ici (0 : ℝ),
          ((b - 1 / 2) * (μ : ℝ)
            + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + (μ : ℝ) * ys i|
            - J F xs ys τ μ)) - (∑ i, signVec τ i * ys i) / 2 / n := by
    intro τ
    rw [le_sub_iff_add_le]
    apply le_ciInf
    rintro ⟨μ, hμ⟩
    have hsup : S (flipW w τ) ≤ n * ((b - 1 / 2) * μ
        + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + μ * ys i| - J F xs ys τ μ)
        - (∑ i, signVec τ i * ys i) / 2 := by
      apply ciSup_le
      rintro ⟨v, f, hfF, hfb, rfl⟩
      have := key hn xs ys hys F hF b f hfF hfb τ μ hμ
      rw [div_le_iff₀ hnpos] at this
      simp only
      linarith
    have : (1 / (n : ℝ)) * S (flipW w τ) ≤ (1 / (n : ℝ)) * (n * ((b - 1 / 2) * μ
        + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + μ * ys i| - J F xs ys τ μ)
        - (∑ i, signVec τ i * ys i) / 2) :=
      mul_le_mul_of_nonneg_left hsup (by positivity)
    have e : (1 / (n : ℝ)) * (n * ((b - 1 / 2) * μ
        + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + μ * ys i| - J F xs ys τ μ)
        - (∑ i, signVec τ i * ys i) / 2) = ((b - 1 / 2) * μ
        + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + μ * ys i| - J F xs ys τ μ)
        - (∑ i, signVec τ i * ys i) / 2 / n := by
      field_simp
    simp only
    linarith
  unfold rademacher
  change (1 / (n : ℝ)) * ((1 / 2 ^ n) * ∑ σ, S σ) ≤ _
  rw [hperm, mul_left_comm, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ τ, (1 / (n : ℝ)) * S (flipW w τ)
      ≤ ∑ τ : Fin n → Bool, ((⨅ μ : Set.Ici (0 : ℝ),
          ((b - 1 / 2) * (μ : ℝ)
            + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + (μ : ℝ) * ys i|
            - J F xs ys τ μ)) - (∑ i, signVec τ i * ys i) / 2 / n) :=
        Finset.sum_le_sum (fun τ _ => hper τ)
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, sum_sum_zero]
      simp

/-- Lower bound making the inner infimum bounded below. -/
lemma bdd_below {X : Type*} {n : ℕ} (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1) (F : Set (X → ℝ))
    (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (b : ℝ) (hb : ∃ f ∈ F, empLoss xs ys f ≤ b) (τ : Fin n → Bool) :
    BddBelow (Set.range fun μ : Set.Ici (0 : ℝ) =>
          ((b - 1 / 2) * (μ : ℝ)
            + (1 / (2 * (n : ℝ))) * ∑ i, |signVec τ i + (μ : ℝ) * ys i|
            - J F xs ys τ μ)) := by
  obtain ⟨f0, hf0F, hf0b⟩ := hb
  refine ⟨(∑ i, signVec (flipW (fun j => decide (ys j = 1)) τ) i * ell (f0 (xs i)) (ys i)
      + (∑ i, signVec τ i * ys i) / 2) / n, ?_⟩
  rintro _ ⟨⟨μ, hμ⟩, rfl⟩
  exact key hn xs ys hys F hF b f0 hf0F hf0b τ μ hμ

end A76222c0

open LocalRademacher.Classif in
theorem solution {X : Type*} (n : ℕ) (hn : 0 < n) (xs : Fin n → X) (ys : Fin n → ℝ)
    (hys : ∀ i, ys i = 1 ∨ ys i = -1)
    (F : Set (X → ℝ)) (hF : ∀ f ∈ F, ∀ z, f z = 1 ∨ f z = -1)
    (c x r : ℝ) (hc : 0 ≤ c) (hx : 0 < x) (hr : 0 < r) (hr2 : r ≤ 1 / 2)
    (hfeas : ∃ f ∈ F, empLoss xs ys f ≤ 2 * r) :
    psiHat c x r F xs ys ≤
      c * (⨆ α : Set.Icc (Real.sqrt (2 * r)) 1,
          (α : ℝ) * ((1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            ⨅ μ : Set.Ici (0 : ℝ),
              ((2 * r / (α : ℝ) ^ 2 - 1 / 2) * (μ : ℝ)
                + (1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + (μ : ℝ) * ys i|
                - J F xs ys σ μ)))
        + 26 * x / n := by
  obtain ⟨f0, hf0F, hf0b⟩ := hfeas
  have hsq : 0 < Real.sqrt (2 * r) := Real.sqrt_pos.mpr (by linarith)
  have hfb : ∀ α : Set.Icc (Real.sqrt (2 * r)) 1,
      ∃ f ∈ F, empLoss xs ys f ≤ 2 * r / (α : ℝ) ^ 2 := by
    rintro ⟨α, h1, h2⟩
    refine ⟨f0, hf0F, le_trans hf0b ?_⟩
    have hα : 0 < α := lt_of_lt_of_le hsq h1
    have hα2 : α ^ 2 ≤ 1 := pow_le_one₀ hα.le h2
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  set K : ℝ := (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
      ((1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + (0 : ℝ) * ys i|
        - J F xs ys σ 0) with hK
  have hRK : ∀ α : Set.Icc (Real.sqrt (2 * r)) 1,
      ((1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            ⨅ μ : Set.Ici (0 : ℝ),
              ((2 * r / (α : ℝ) ^ 2 - 1 / 2) * (μ : ℝ)
                + (1 / (2 * (n : ℝ))) * ∑ i, |UnderstandingML.signVec σ i + (μ : ℝ) * ys i|
                - J F xs ys σ μ)) ≤ K := by
    intro α
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro σ _
    refine (ciInf_le (A76222c0.bdd_below hn xs ys hys F hF _ (hfb α) σ)
      ⟨0, Set.mem_Ici.mpr le_rfl⟩).trans (le_of_eq ?_)
    simp
  unfold psiHat
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hc
  apply ciSup_mono
  · refine ⟨|K|, ?_⟩
    rintro _ ⟨α, rfl⟩
    have hα0 : 0 ≤ (α : ℝ) := hsq.le.trans α.2.1
    have hα1 : (α : ℝ) ≤ 1 := α.2.2
    have h1 := mul_le_mul_of_nonneg_left (hRK α) hα0
    have h2 : (α : ℝ) * K ≤ (α : ℝ) * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hα0
    have h3 : (α : ℝ) * |K| ≤ 1 * |K| := mul_le_mul_of_nonneg_right hα1 (abs_nonneg K)
    simp only
    linarith
  · intro α
    have hα0 : 0 ≤ (α : ℝ) := hsq.le.trans α.2.1
    exact mul_le_mul_of_nonneg_left
      (A76222c0.inner_bound hn xs ys hys F hF _ (hfb α)) hα0
