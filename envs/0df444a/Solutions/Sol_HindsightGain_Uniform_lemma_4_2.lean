-- Prove2me | solution 1 for HindsightGain.Uniform.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:53:16.775032+00:00
-- url     : https://prove2.me/submissions/c1ea4707-ae57-4069-9fbf-7f38698bfc86

import Mathlib
import Definitions.Def_HindsightGain_Uniform_model
import Definitions.Def_HindsightGain_Uniform_optima
import Theorems.Thm_HindsightGain_Uniform_corollary_4_1

section
set_option autoImplicit false

namespace HindsightGain.Uniform.Dev.Lem42
open HindsightGain.Uniform

variable {n : ℕ}

lemma filter_eq_image (U T : Finset (Fin n)) (hT : T ⊆ U) :
    U.powerset.filter (fun S => T ⊆ S) = (U \ T).powerset.image (fun R => T ∪ R) := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨hS, hTS⟩
    exact ⟨S \ T, Finset.sdiff_subset_sdiff hS (le_refl _), Finset.union_sdiff_of_subset hTS⟩
  · rintro ⟨R, hR, rfl⟩
    refine ⟨Finset.union_subset hT (hR.trans Finset.sdiff_subset), Finset.subset_union_left⟩

lemma sum_K (U T : Finset (Fin n)) (hT : T ⊆ U) (t x : ℝ) :
    ∑ S ∈ U.powerset.filter (fun S => T ⊆ S), t ^ S.card * (1 - t) ^ (U.card - S.card) * x ^ (S.card - T.card)
      = t ^ T.card * (t * x + (1 - t)) ^ (U.card - T.card) := by
  rw [filter_eq_image U T hT, Finset.sum_image]
  · have hc : (U \ T).card = U.card - T.card := Finset.card_sdiff_of_subset hT
    have : ∀ R ∈ (U \ T).powerset,
        t ^ (T ∪ R).card * (1 - t) ^ (U.card - (T ∪ R).card) * x ^ ((T ∪ R).card - T.card)
          = t ^ T.card * ((t * x) ^ R.card * (1 - t) ^ ((U \ T).card - R.card)) := by
      intro R hR
      have hd : Disjoint T R := Finset.disjoint_of_subset_right (Finset.mem_powerset.1 hR) Finset.disjoint_sdiff
      rw [Finset.card_union_of_disjoint hd, hc, Nat.add_sub_cancel_left, Nat.sub_sub, mul_pow]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow, hc]
  · intro R1 h1 R2 h2 h
    have hd1 : Disjoint T R1 := Finset.disjoint_of_subset_right (Finset.mem_powerset.1 h1) Finset.disjoint_sdiff
    have hd2 : Disjoint T R2 := Finset.disjoint_of_subset_right (Finset.mem_powerset.1 h2) Finset.disjoint_sdiff
    have := congrArg (fun S => S \ T) h
    simpa [Finset.union_sdiff_cancel_left hd1, Finset.union_sdiff_cancel_left hd2] using this


lemma mass_univ (S : Finset (Fin n)) (t : ℝ) :
    thinningMass Finset.univ S t = t ^ S.card * (1 - t) ^ (n - S.card) := by
  simp [thinningMass]

lemma sum_ind (A : Finset (Fin n)) (t : ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      thinningMass Finset.univ S t * (if A ⊆ S then (1 : ℝ) else 0) = t ^ A.card := by
  have h := sum_K (Finset.univ : Finset (Fin n)) A (Finset.subset_univ _) t 1
  simp only [one_pow, mul_one, add_sub_cancel, Finset.card_univ, Fintype.card_fin] at h
  simp_rw [mass_univ, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact h


lemma card_emb (S : Finset (Fin n)) (k : ℕ) :
    (S.card.descFactorial k : ℝ) =
      ∑ a : Fin k ↪ Fin n, if (Finset.univ.image a) ⊆ S then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype]
  have : Fintype.card {a : Fin k ↪ Fin n // (Finset.univ.image a) ⊆ S} = Fintype.card (Fin k ↪ S) := by
    refine Fintype.card_congr
      { toFun := fun a => a.1.codRestrict (· ∈ S) (fun i => a.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
        invFun := fun e => ⟨e.trans (Function.Embedding.subtype _), by
          intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
          exact (e i).2⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun e => by ext; rfl }
  rw [this, Fintype.card_embedding_eq]
  simp

lemma sum_desc (t : ℝ) (k : ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      thinningMass Finset.univ S t * (S.card.descFactorial k : ℝ) = t ^ k * (n.descFactorial k : ℝ) := by
  simp_rw [card_emb, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ a : Fin k ↪ Fin n, ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      thinningMass Finset.univ S t * (if (Finset.univ.image a) ⊆ S then (1 : ℝ) else 0) = t ^ k := by
    intro a
    rw [sum_ind, Finset.card_image_of_injective _ a.injective]
    simp
  simp_rw [this]
  simp [Fintype.card_embedding_eq, mul_comm]

lemma sum_frob {D r : ℕ} (M : Model n D r) (t : ℝ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      thinningMass Finset.univ S t * frobeniusSq (restrict M S) = t ^ r * frobeniusSq M := by
  have h1 : ∀ S : Finset (Fin n), frobeniusSq (restrict M S) =
      ∑ e : Edge n r, (if e.val ⊆ S then (1 : ℝ) else 0) * ∑ a : Fin r → Fin D, (M.A e a) ^ 2 := by
    intro S
    unfold frobeniusSq restrict
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : e.val ⊆ S <;> simp [h]
  rw [Finset.sum_congr rfl (fun S _ => by rw [h1 S, Finset.mul_sum])]
  rw [Finset.sum_comm]
  have : ∀ e : Edge n r, ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      thinningMass Finset.univ S t * ((if e.val ⊆ S then (1 : ℝ) else 0) * ∑ a : Fin r → Fin D, (M.A e a) ^ 2)
      = t ^ r * ∑ a : Fin r → Fin D, (M.A e a) ^ 2 := by
    intro e
    simp_rw [← mul_assoc, ← Finset.sum_mul, sum_ind, e.property]
  rw [Finset.sum_congr rfl (fun e _ => this e)]
  unfold frobeniusSq
  rw [Finset.mul_sum]


lemma tower {D r : ℕ} (M : Model n D r) (s t : ℝ) :
    retentionMean M (s * t) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, thinningMass Finset.univ S t * thinningMean M S s := by
  unfold retentionMean thinningMean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset (Fin n)).powerset)
    (s' := fun T => (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S))]
  · refine Finset.sum_congr rfl (fun T _ => ?_)
    have h := sum_K (Finset.univ : Finset (Fin n)) T (Finset.subset_univ _) t (1 - s)
    have e : ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => T ⊆ S),
        thinningMass Finset.univ S t * (thinningMass S T s * setVal M T) =
          (s ^ T.card * setVal M T) *
            (t ^ S.card * (1 - t) ^ ((Finset.univ : Finset (Fin n)).card - S.card) * (1 - s) ^ (S.card - T.card)) := by
      intro S hS
      have hTS : T ⊆ S := (Finset.mem_filter.1 hS).2
      rw [mass_univ, thinningMass, if_pos hTS, Finset.card_univ, Fintype.card_fin]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, h, mass_univ, Finset.card_univ, Fintype.card_fin]
    have : t * (1 - s) + (1 - t) = 1 - s * t := by ring
    rw [this, mul_pow]
    ring
  · intro S T
    simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_univ, true_and, and_true]


lemma sqrt_t (t : ℝ) (ht : 0 < t) (r : ℕ) (hr : 2 ≤ r) :
    Real.sqrt (t ^ (r - 1)) * Real.sqrt (t ^ r) = t ^ r * t ^ (-(1 : ℝ) / 2) := by
  rw [← Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast t r,
    ← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_mul ht.le]
  congr 1
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

lemma frob_sq_nonneg {D r : ℕ} (M : Model n D r) : 0 ≤ frobeniusSq M := by
  unfold frobeniusSq; positivity

lemma main {D r : ℕ} (M : Model n D r)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ compensated M (s * t) - compensated M t ∧
      compensated M (s * t) - compensated M t ≤
        (r : ℝ) * Real.sqrt 5 * (Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2)) *
          t ^ (-(1 : ℝ) / 2) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) *
            frobenius M := by
  have hm : ∀ S : Finset (Fin n), 0 ≤ thinningMass Finset.univ S t := by
    intro S; rw [mass_univ]
    have : 0 ≤ 1 - t := by linarith
    positivity
  have hD : retentionMean M (s * t) - s ^ r * retentionMean M t =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        thinningMass Finset.univ S t * (thinningMean M S s - s ^ r * setVal M S) := by
    rw [tower, retentionMean, thinningMean, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  have hdiv : compensated M (s * t) - compensated M t =
      (retentionMean M (s * t) - s ^ r * retentionMean M t) / (s * t) ^ r := by
    unfold compensated
    rw [mul_pow]
    field_simp
  have hpos : 0 < (s * t) ^ r := by positivity
  have hc := fun S : Finset (Fin n) => HindsightGain.Uniform.corollary_4_1 M S s hs0.le hs1
  refine ⟨?_, ?_⟩
  · rw [hdiv, hD]
    exact div_nonneg (Finset.sum_nonneg (fun S _ => mul_nonneg (hm S) (hc S).1)) hpos.le
  · rw [hdiv, hD, div_le_iff₀ hpos]
    set C0 : ℝ := (r : ℝ) * Real.sqrt 5 * s ^ ((r : ℝ) / 2) * Real.sqrt (1 - s) with hC0
    have hC0n : 0 ≤ C0 := by rw [hC0]; positivity
    have h1 : ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        thinningMass Finset.univ S t * (thinningMean M S s - s ^ r * setVal M S) ≤
        C0 * ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          thinningMass Finset.univ S t * (Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ) * frobenius (restrict M S)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun S _ => ?_)
      have := mul_le_mul_of_nonneg_left (hc S).2 (hm S)
      refine this.trans (le_of_eq ?_)
      rw [hC0]; ring
    have h2 : ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          thinningMass Finset.univ S t * (Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ) * frobenius (restrict M S))
        ≤ Real.sqrt (t ^ (r - 1) * (n.descFactorial (r - 1) : ℝ)) * Real.sqrt (t ^ r * frobeniusSq M) := by
      have cs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n)).powerset
        (fun S => Real.sqrt (thinningMass Finset.univ S t) * Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ))
        (fun S => Real.sqrt (thinningMass Finset.univ S t) * frobenius (restrict M S))
      have e1 : ∀ S : Finset (Fin n), thinningMass Finset.univ S t *
          (Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ) * frobenius (restrict M S)) =
          (Real.sqrt (thinningMass Finset.univ S t) * Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ)) *
          (Real.sqrt (thinningMass Finset.univ S t) * frobenius (restrict M S)) := by
        intro S
        have h := Real.mul_self_sqrt (hm S)
        calc _ = (Real.sqrt (thinningMass Finset.univ S t) * Real.sqrt (thinningMass Finset.univ S t)) *
            (Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ) * frobenius (restrict M S)) := by rw [h]
          _ = _ := by ring
      have e2 : ∀ S : Finset (Fin n), (Real.sqrt (thinningMass Finset.univ S t) * Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ)) ^ 2
          = thinningMass Finset.univ S t * (Nat.descFactorial S.card (r - 1) : ℝ) := by
        intro S
        rw [mul_pow, Real.sq_sqrt (hm S), Real.sq_sqrt (by positivity)]
      have e3 : ∀ S : Finset (Fin n), (Real.sqrt (thinningMass Finset.univ S t) * frobenius (restrict M S)) ^ 2
          = thinningMass Finset.univ S t * frobeniusSq (restrict M S) := by
        intro S
        rw [mul_pow, Real.sq_sqrt (hm S), frobenius, Real.sq_sqrt (frob_sq_nonneg _)]
      rw [Finset.sum_congr rfl (fun S _ => e1 S)]
      simp_rw [e2, e3, sum_desc, sum_frob] at cs
      exact cs
    have h3 : Real.sqrt (t ^ (r - 1) * (n.descFactorial (r - 1) : ℝ)) * Real.sqrt (t ^ r * frobeniusSq M)
        = (t ^ r * t ^ (-(1 : ℝ) / 2)) * Real.sqrt (n.descFactorial (r - 1) : ℝ) * frobenius M := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), frobenius, ← sqrt_t t ht0 r M.hr]
      ring
    have hA : 0 < s ^ ((r : ℝ) / 2) := Real.rpow_pos_of_pos hs0 _
    have hsr : (s * t) ^ r = s ^ ((r : ℝ) / 2) * s ^ ((r : ℝ) / 2) * t ^ r := by
      rw [mul_pow, ← Real.rpow_add hs0, ← Real.rpow_natCast s r]; congr 2; ring
    have hfin : C0 * ((t ^ r * t ^ (-(1 : ℝ) / 2)) * Real.sqrt (n.descFactorial (r - 1) : ℝ) * frobenius M) =
        (r : ℝ) * Real.sqrt 5 * (Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2)) *
          t ^ (-(1 : ℝ) / 2) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) * frobenius M * (s * t) ^ r := by
      rw [hsr, hC0]; field_simp
    calc _ ≤ C0 * ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          thinningMass Finset.univ S t * (Real.sqrt (Nat.descFactorial S.card (r - 1) : ℝ) * frobenius (restrict M S)) := h1
      _ ≤ C0 * ((t ^ r * t ^ (-(1 : ℝ) / 2)) * Real.sqrt (n.descFactorial (r - 1) : ℝ) * frobenius M) := by
        apply mul_le_mul_of_nonneg_left _ hC0n
        rw [← h3]; exact h2
      _ = _ := hfin

end HindsightGain.Uniform.Dev.Lem42

namespace HindsightGain.Uniform
open HindsightGain.Uniform.Dev.Lem42 in
theorem chk_lemma_4_2 {n D r : ℕ} (M : Model n D r)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ compensated M (s * t) - compensated M t ∧
      compensated M (s * t) - compensated M t ≤
        (r : ℝ) * Real.sqrt 5 * (Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2)) *
          t ^ (-(1 : ℝ) / 2) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) *
            frobenius M := main M s t hs0 hs1 ht0 ht1

end HindsightGain.Uniform
end

theorem solution : type_of% @HindsightGain.Uniform.chk_lemma_4_2 := @HindsightGain.Uniform.chk_lemma_4_2
