-- Prove2me | solution 1 for MomentSearch.Supplement.theorem_27
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:17:55.338187+00:00
-- url     : https://prove2.me/submissions/86d0d3d0-fe3b-4f94-a6f9-67e815a36648

import Mathlib
import Definitions.Def_MomentSearch_Supplement_cdf
import Theorems.Thm_MomentSearch_Supplement_jl_near_orthogonal_labels
import Theorems.Thm_MomentSearch_Supplement_dyadic_prefix_gram_factorization

open MomentSearch.Supplement

private theorem simplex_error {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (V : Matrix (Fin k) (Fin n) ℝ) (δ : ℝ)
    (h : ∀ t j, |(U*V) t j - (if j ≤ t then 1 else 0)| ≤ δ)
    (p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) (t : Fin n) :
    |U.mulVec (V.mulVec p) t - cdf p t.val| ≤ δ := by
  rw [Matrix.mulVec_mulVec]
  have eq : cdf p t.val = ∑ j, (if j ≤ t then (1:ℝ) else 0)*p j := by
    unfold cdf
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ≤ t <;> simp [hj,show (j.val ≤ t.val) ↔ j ≤ t from Iff.rfl]
  rw [eq]
  change |(∑ j, (U*V) t j * p j) - _| ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    _ ≤ ∑ j, |((U*V) t j - (if j ≤ t then 1 else 0))*p j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, δ*p j := Finset.sum_le_sum fun j _ => by
      rw [abs_mul, abs_of_nonneg (hp.1 j)]
      exact mul_le_mul_of_nonneg_right (h t j) (hp.1 j)
    _ = δ := by rw [← Finset.mul_sum,hp.2,mul_one]

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C * Real.logb 2 n ^ 4 / δ ^ 2 ∧
          ∃ (U : Matrix (Fin n) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ),
            ∀ p ∈ stdSimplex ℝ (Fin n), ∀ t : Fin n,
              |Matrix.mulVec U (Matrix.mulVec V p) t - cdf p (t : ℕ)| ≤ δ := by

  obtain ⟨A,hA,labels⟩ := jl_near_orthogonal_labels
  refine ⟨27*A,by positivity,?_⟩
  intro n hn δ hδ hδ1
  let h := Nat.clog 2 n + 1
  let L := Real.logb 2 n
  have hL : 1 ≤ L := by
    simpa [L] using Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ n by exact_mod_cast hn)
  have height : (h:ℝ) ≤ 3*L := by
    have hc := Nat.ceil_lt_add_one (zero_le_one.trans hL)
    have e : ⌈L⌉₊ = Nat.clog 2 n := by simpa [L] using Real.natCeil_logb_natCast 2 n
    rw [e] at hc
    dsimp [h]; push_cast; linarith
  have hone : 1 ≤ (h:ℝ) := by exact_mod_cast (show 1 ≤ h from Nat.le_add_left 1 _)
  have hpos : 0 < (h:ℝ) := zero_lt_one.trans_le hone
  let η := δ/(h:ℝ)
  have ep : 0 < η := div_pos hδ hpos
  have elt : η < 1 := (div_lt_iff₀ hpos).mpr (by linarith)
  obtain ⟨R,hR,g,hg⟩ := labels n hn η ep elt
  obtain ⟨U,V,hUV⟩ := dyadic_prefix_gram_factorization hn ep.le g hg
  have err : (h:ℝ)*η = δ := by dsimp [η]; field_simp
  refine ⟨h*R,?_,U,V,fun p hp t => simplex_error U V δ (fun t j => (hUV t j).trans_eq err) p hp t⟩
  change ((h*R:ℕ):ℝ) ≤ 27*A*L^4/δ^2
  push_cast
  calc
    _ ≤ (h:ℝ)*(A*L/η^2) := mul_le_mul_of_nonneg_left hR hpos.le
    _ = A*L*(h:ℝ)^3/δ^2 := by dsimp [η]; field_simp
    _ ≤ A*L*(3*L)^3/δ^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le height _) (mul_nonneg hA.le (zero_le_one.trans hL))
    _ = _ := by ring
