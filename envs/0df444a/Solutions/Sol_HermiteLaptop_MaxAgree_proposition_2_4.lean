-- Prove2me | solution 1 for HermiteLaptop.MaxAgree.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-18T15:44:58.970425+00:00
-- url     : https://prove2.me/submissions/0d0316d4-13d1-4c46-a0a3-bf95a6a3011c

import Theorems.Thm_HermiteLaptop_MaxAgree_eq_8_9
import Definitions.Def_HermiteLaptop_MaxAgree_TruncBounds

open HermiteLaptop.MaxAgree Finset

private theorem collision_at_one (k : ℕ) : collisionProb k 1 = 1 := by
  have h (x y : Fin k → ℝ) : corrPartner 1 x y = x := by ext i; simp [corrPartner]
  simp [collisionProb, h, gaussPi]

/-- At a negative correlation the finite polynomial bounds swap the endpoints in odd degrees. -/
private theorem finite_signed_bounds (c cl cu : ℕ → ℝ) (M : ℕ) {ρ : ℝ} (hρ : ρ ≤ 0)
    (hl : ∀ m ≤ M, cl m ≤ c m) (hu : ∀ m ≤ M, c m ≤ cu m) :
    (∑ m ∈ range (M+1), (if Even m then cl m else cu m) * ρ^m) ≤
        (∑ m ∈ range (M+1), c m * ρ^m) ∧
    (∑ m ∈ range (M+1), c m * ρ^m) ≤
        ∑ m ∈ range (M+1), (if Even m then cu m else cl m) * ρ^m := by
  constructor <;> apply sum_le_sum <;> intro m hm
  all_goals
    have hm' : m ≤ M := by simpa using hm
    by_cases he : Even m
    · simp only [if_pos he]
      first | exact mul_le_mul_of_nonneg_right (hl m hm') (he.pow_nonneg ρ)
            | exact mul_le_mul_of_nonneg_right (hu m hm') (he.pow_nonneg ρ)
    · simp only [if_neg he]
      have hpow := (Nat.not_even_iff_odd.mp he).pow_nonpos hρ
      first | exact mul_le_mul_of_nonpos_right (hu m hm') hpow
            | exact mul_le_mul_of_nonpos_right (hl m hm') hpow

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : ℕ) (cl cu : ℕ → ℝ)
    (hcl : ∀ m ≤ M, cl m ≤ coeffC k m) (hcu : ∀ m ≤ M, coeffC k m ≤ cu m) :
    ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      truncLower M cl cu ρ ≤ collisionProb k ρ ∧ collisionProb k ρ ≤ truncUpper M cl cu ρ := by
  intro ρ hρ
  let c := coeffC k
  have h := eq_8_9 k hk
  have hc (n : ℕ) : 0 ≤ c n := (h.2 n).2
  have hmass : HasSum c 1 := by
    simpa [c, collision_at_one] using (h.1 1 (by norm_num)).2.2
  have hseries : HasSum (fun m : ℕ => c m * ρ^m) (collisionProb k ρ) := (h.1 ρ hρ).2.2
  let B := |ρ|^(M+1)
  have hB : 0 ≤ B := pow_nonneg (abs_nonneg _) _
  have hshort : (∑ m ∈ range (M+1), cl m) ≤ ∑ m ∈ range (M+1), c m :=
    sum_le_sum (fun m hm => hcl m (by simpa using hm))
  have hgap := mul_le_mul_of_nonneg_left (sub_le_sub_left hshort 1) hB
  have hab (n : ℕ) : |ρ^(n+(M+1))| ≤ B := by
    rw [abs_pow]
    exact pow_le_pow_of_le_one (abs_nonneg _) (abs_le.mpr hρ) (by omega)
  have hm := (hasSum_nat_add_iff' (M+1)).mpr hmass
  have ht := (hasSum_nat_add_iff' (M+1)).mpr hseries
  have upper := hasSum_le (fun n : ℕ => show c (n+(M+1)) * ρ^(n+(M+1)) ≤ B * c (n+(M+1)) by
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_left ((abs_le.mp (hab n)).2) (hc _)) ht (hm.mul_left B)
  by_cases hp : 0 ≤ ρ
  · have htail := ht.nonneg (fun n => mul_nonneg (hc _) (pow_nonneg hp _))
    have hlow := sum_le_sum (s := range (M+1)) (fun m hm' => mul_le_mul_of_nonneg_right
      (hcl m (by simpa using hm')) (pow_nonneg hp m))
    have hhigh := sum_le_sum (s := range (M+1)) (fun m hm' => mul_le_mul_of_nonneg_right
      (hcu m (by simpa using hm')) (pow_nonneg hp m))
    dsimp [c] at htail upper hgap
    simp only [truncLower, truncUpper, if_pos hp]
    dsimp [B] at upper hgap
    rw [abs_of_nonneg hp] at upper hgap
    constructor <;> linarith
  · have lower := hasSum_le (fun n : ℕ => show -(B * c (n+(M+1))) ≤ c (n+(M+1)) * ρ^(n+(M+1)) by
      rw [← neg_mul, mul_comm (-B)]
      exact mul_le_mul_of_nonneg_left ((abs_le.mp (hab n)).1) (hc _)) (hm.mul_left B).neg ht
    have ⟨hlo, hhi⟩ := finite_signed_bounds c cl cu M (le_of_not_ge hp) hcl hcu
    simp only [truncLower, truncUpper, if_neg hp]
    dsimp [B, c] at lower upper hgap hlo hhi
    constructor <;> linarith
