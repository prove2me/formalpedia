-- Prove2me | solution 1 for MasulloRH.factorial_grid_realizes_finite_rational_theta_sums
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T22:26:47.552642+00:00
-- url     : https://prove2.me/submissions/d83e66c6-36f2-4c40-bbe7-5aa3ca3929ce

import Definitions.Def_MasulloRH_RationalThetaGrid
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation

private lemma on_mesh (q : ℚ) (n : ℕ) (hd : q.den ≤ n) (ha : q.num.natAbs ≤ n) :
    ∃ i : Fin (gridCount n), mesh n i = q := by
  obtain ⟨t,ht⟩ := Nat.dvd_factorial q.den_pos hd
  have ht' : t ≤ n.factorial := by
    rw [ht]
    simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ q.den from q.den_pos)
  let z := q.num*(t:ℤ)
  let B := n*n.factorial
  have hab : z.natAbs ≤ B := by
    simpa [z,Int.natAbs_mul,B] using Nat.mul_le_mul ha ht'
  have hbInt : (z.natAbs:ℤ) ≤ (B:ℤ) := by exact_mod_cast hab
  have hab' : |z| ≤ (B:ℤ) := by simpa only [Int.natCast_natAbs] using hbInt
  obtain ⟨hlo,hhi⟩ := abs_le.mp hab'
  have hnon : 0 ≤ z+(B:ℤ) := by omega
  let u := (z+(B:ℤ)).toNat
  have hu : (u:ℤ) = z+B := Int.toNat_of_nonneg hnon
  have hsz : u < gridCount n := by
    change u < 2*B+1
    omega
  refine ⟨⟨u,hsz⟩,?_⟩
  have ene : (n.factorial:ℚ) ≠ 0 := by positivity
  have dnv : (q.den:ℚ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
  have ed : (n.factorial:ℚ) = (q.den:ℚ)*(t:ℚ) := by exact_mod_cast ht
  have eu : (u:ℚ) = (z:ℚ)+(B:ℚ) := by exact_mod_cast hu
  change ((u:ℚ)-(B:ℚ))/(n.factorial:ℚ) = q
  rw [eu,add_sub_cancel_right,← Rat.num_div_den q,div_eq_div_iff ene dnv,ed]
  simp only [z,Int.cast_mul,Int.cast_natCast]
  ring

private def toComplex : (ℚ × ℚ) →+ ℂ where
  toFun := asComplex
  map_zero' := by simp [asComplex]
  map_add' a b := by simp [asComplex];ring

private lemma repack {m n : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
    (g : Fin n → ℚ) (hy : ∀ i, ∃ j, g j = y i) :
    ∃ b : Fin n → ℚ × ℚ, residual 0 (fun i => asComplex (a i)) (fun i => (y i:ℝ)) =
      residual 0 (fun j => asComplex (b j)) (fun j => (g j:ℝ)) := by
  classical
  choose e he using hy
  let b (j : Fin n) : ℚ × ℚ := ∑ i, if e i = j then a i else 0
  refine ⟨b,?_⟩
  funext x
  unfold MasulloRH.GaussianApproximation.residual
  congr 1
  have co (j : Fin n) : asComplex (b j) = ∑ i, if e i = j then asComplex (a i) else 0 := by
    change toComplex (∑ i, if e i = j then a i else 0) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp [toComplex,asComplex])
  simp_rw [co,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul,← he i]

theorem solution :
    (∀ (m : ℕ) (y : Fin m → ℚ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ i : Fin m, ∃ j : Fin (gridCount n), mesh n j = y i) ∧
    (∀ {m n : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) (g : Fin n → ℚ),
      (∀ i, ∃ j, g j = y i) → ∃ b : Fin n → ℚ × ℚ,
      residual 0 (fun i => asComplex (a i)) (fun i => (y i:ℝ)) =
        residual 0 (fun j => asComplex (b j)) (fun j => (g j:ℝ))) := by
  refine ⟨?_,@repack⟩
  intro m y
  let f (i : Fin m) := (y i).den+(y i).num.natAbs
  refine ⟨∑ i, f i,?_⟩
  intro n hn i
  have hsum := (Finset.single_le_sum (f:=f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hn
  dsimp only [f] at hsum
  exact on_mesh (y i) n (by omega) (by omega)
