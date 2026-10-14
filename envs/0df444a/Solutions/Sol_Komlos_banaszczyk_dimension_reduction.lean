-- Prove2me | solution 1 for Komlos.banaszczyk_dimension_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:24:16.652142+00:00
-- url     : https://prove2.me/submissions/9ed552ee-e1f6-49a5-b552-7a3201780645

import Definitions.Def_Komlos_model
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

namespace KomlosCoordinateSelection

lemma column_energy {n m : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin n) :
    ∑ j, (v i j)^2 ≤ 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq]
  nlinarith [hv i, norm_nonneg (v i)]

lemma total_energy {n m : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∑ j, ∑ i, (v i j)^2 ≤ (n : ℝ) := by
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => column_energy v hv i
    _ = _ := by simp

end KomlosCoordinateSelection

open KomlosCoordinateSelection

lemma coordinate_selection {n m : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ S : Finset (Fin m), S.card ≤ n^2 ∧
      ∀ j, j ∉ S → ∑ i, |v i j| ≤ 1 := by
  classical
  let S : Finset (Fin m) := Finset.univ.filter (fun j => 1 < (n : ℝ) * ∑ i, (v i j)^2)
  refine ⟨S, ?_, ?_⟩
  · have hs : (S.card : ℝ) ≤ (n : ℝ)^2 := by
      calc
        (S.card : ℝ) = ∑ _j ∈ S, (1 : ℝ) := by simp
        _ ≤ ∑ j ∈ S, (n : ℝ) * ∑ i, (v i j)^2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact le_of_lt (Finset.mem_filter.mp hj).2
        _ ≤ ∑ j : Fin m, (n : ℝ) * ∑ i, (v i j)^2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _
          positivity
        _ = (n : ℝ) * ∑ j, ∑ i, (v i j)^2 := by rw [Finset.mul_sum]
        _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left (total_energy v hv) (Nat.cast_nonneg _)
        _ = _ := by ring
    exact_mod_cast hs
  · intro j hj
    have he : (n : ℝ) * ∑ i, (v i j)^2 ≤ 1 := by
      simpa [S, not_lt] using hj
    have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i j|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hc
    nlinarith



namespace KomlosDimension

lemma restrict_norm_le {n m k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin m))
    (e : Fin k ↪ Fin m) (hv : ∀ i, ‖v i‖ ≤ 1) (i : Fin n) :
    ‖(WithLp.toLp 2 (fun j : Fin k => v i (e j)) : EuclideanSpace ℝ (Fin k))‖ ≤ 1 := by
  let w : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun j => v i (e j))
  change ‖w‖ ≤ 1
  have hs : ‖w‖^2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin k, (v i (e j))^2) ≤ 1
    calc
      _ = ∑ j ∈ Finset.univ.image e, (v i j)^2 := by rw [Finset.sum_image e.injective.injOn]
      _ ≤ ∑ j : Fin m, (v i j)^2 := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
      _ ≤ 1 := column_energy v hv i
  nlinarith [norm_nonneg w]

lemma sqrt_log_dimension {n k : ℕ} (hk : k ≤ n^2) :
    Real.sqrt (Real.log (k+2)) ≤ 2 * Real.sqrt (Real.log (n+2)) := by
  have hn : 0 ≤ Real.log (n+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n] : (1:ℝ) ≤ n+2)
  have hkn : (k:ℝ)+2 ≤ ((n:ℝ)+2)^2 := by
    have h : (k:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := Real.log_le_log (by positivity : (0:ℝ) < k+2) hkn
  rw [Real.log_pow] at hh
  have hs2 := Real.sq_sqrt hn
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · norm_num at hh
    nlinarith

lemma sign_abs {n : ℕ} {eps : Fin n → ℝ} (he : Komlos.IsSignVector eps) (i : Fin n) :
    |eps i| = 1 := by rcases he i with h | h <;> simp [h]

end KomlosDimension

open Komlos KomlosDimension

theorem solution
    (hCube : ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (m + 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (n + 2)) := by
  classical
  obtain ⟨C, hC, hCube⟩ := hCube
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2
  let D := 2*C + (Real.sqrt (Real.log 2))⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro n m v hv
  obtain ⟨S, hS, hsmall⟩ := coordinate_selection v hv
  let e : Fin S.card ≃ S := S.equivFin.symm
  let emb : Fin S.card ↪ Fin m := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let w : Fin n → EuclideanSpace ℝ (Fin S.card) := fun i => WithLp.toLp 2 (fun j => v i (emb j))
  obtain ⟨eps, heps, hbound⟩ := hCube n S.card w (restrict_norm_le v emb hv)
  refine ⟨eps, heps, ?_⟩
  intro j
  have hln : 0 < Real.log ((n:ℝ)+2) := Real.log_pos (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hsqrt := Real.sqrt_nonneg (Real.log ((n:ℝ)+2))
  by_cases hj : j ∈ S
  · let k : Fin S.card := e.symm ⟨j,hj⟩
    have hek : emb k = j := by simp [emb,k]
    have hh : |∑ i, eps i * v i j| ≤ C * Real.sqrt (Real.log ((S.card:ℝ)+2)) := by
      simpa [w,hek] using hbound k
    calc
      _ ≤ C * Real.sqrt (Real.log ((S.card:ℝ)+2)) := hh
      _ ≤ C * (2 * Real.sqrt (Real.log ((n:ℝ)+2))) :=
        mul_le_mul_of_nonneg_left (sqrt_log_dimension hS) hC.le
      _ ≤ D * Real.sqrt (Real.log ((n:ℝ)+2)) := by
        dsimp [D]
        nlinarith [inv_pos.mpr hs2]
  · have hrow : |∑ i, eps i * v i j| ≤ 1 := by
      calc
        _ ≤ ∑ i, |eps i * v i j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, |v i j| := by simp only [abs_mul,sign_abs heps,one_mul]
        _ ≤ 1 := hsmall j hj
    have hmon : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log ((n:ℝ)+2)) := by
      apply Real.sqrt_le_sqrt
      exact Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hone : 1 ≤ (Real.sqrt (Real.log 2))⁻¹ * Real.sqrt (Real.log ((n:ℝ)+2)) := by
      have hh := mul_le_mul_of_nonneg_left hmon (inv_nonneg.mpr hs2.le)
      simpa [inv_mul_cancel₀ hs2.ne'] using hh
    apply hrow.trans
    dsimp [D]
    nlinarith [mul_nonneg hC.le hsqrt]

#print axioms solution
