-- Prove2me | solution 1 for LewisTorczon.BoundPS.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:34:29.441649+00:00
-- url     : https://prove2.me/submissions/e82c5fc4-073f-44e6-a36f-38d38bf4bcb1

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (α β : ℕ) (hα : 0 < α) (hcop : Nat.Coprime α β)
    (hτ : P.τ = (β : ℚ) / (α : ℚ)) (r : ℕ → ℤ)
    (hr : ∀ k, R.Δ k = (P.τ : ℝ) ^ r k * R.Δ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : ℕ → (Fin n → ℤ),
      R.x N = R.x 0 +
        ((β : ℝ) ^ ((Finset.range N).inf' (Finset.nonempty_range_iff.mpr (by omega)) r) *
            (α : ℝ) ^ (-((Finset.range N).sup' (Finset.nonempty_range_iff.mpr (by omega)) r)) *
            R.Δ 0) •
          WithLp.toLp 2 (P.B.mulVec (fun i => (((∑ k ∈ Finset.range N, z k i : ℤ)) : ℝ))) := by
  classical
  set lb := (Finset.range N).inf' (Finset.nonempty_range_iff.mpr (by omega)) r with hlb
  set ub := (Finset.range N).sup' (Finset.nonempty_range_iff.mpr (by omega)) r with hub
  set C : ℝ := (β : ℝ) ^ lb * (α : ℝ) ^ (-ub) * R.Δ 0 with hC
  choose c hc hs using hR.step_mem
  have hβpos : (0:ℝ) < β := by
    have h1 := P.one_lt_τ
    rw [hτ] at h1
    have hα' : (0:ℚ) < α := by exact_mod_cast hα
    rw [lt_div_iff₀ hα', one_mul] at h1
    have : (0:ℚ) < β := lt_trans (by exact_mod_cast hα) h1
    exact_mod_cast this
  have hαpos : (0:ℝ) < α := by exact_mod_cast hα
  let mm : ℕ → ℤ := fun k => (β : ℤ) ^ (r k - lb).toNat * (α : ℤ) ^ (ub - r k).toNat
  have hmm : ∀ k < N, R.Δ k = C * (mm k : ℝ) := by
    intro k hk
    have h1 : lb ≤ r k := Finset.inf'_le _ (Finset.mem_range.mpr hk)
    have h2 : r k ≤ ub := Finset.le_sup' _ (Finset.mem_range.mpr hk)
    simp only [mm, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), hr k, hτ, hC]
    push_cast
    rw [div_zpow]
    have e1 : (β:ℝ) ^ (r k) = (β:ℝ) ^ lb * (β:ℝ) ^ (r k - lb) := by
      rw [← zpow_add₀ hβpos.ne']; congr 1; ring
    have e2 : ((α:ℝ) ^ (r k))⁻¹ = (α:ℝ) ^ (-ub) * (α:ℝ) ^ (ub - r k) := by
      rw [← zpow_add₀ hαpos.ne', ← zpow_neg]; congr 1; ring
    rw [div_eq_mul_inv, e1, e2]; ring
  let z : ℕ → Fin n → ℤ := fun k => if f (R.x k + R.s k) < f (R.x k) then mm k • c k else 0
  refine ⟨z, ?_⟩
  have key : ∀ j ≤ N, R.x j = R.x 0 + C • WithLp.toLp 2
      (P.B.mulVec (fun i => (((∑ k ∈ Finset.range j, z k i : ℤ)) : ℝ))) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Finset.range_zero, Finset.sum_empty, Int.cast_zero]
      rw [show (fun _ : Fin n => (0:ℝ)) = 0 from rfl, Matrix.mulVec_zero]
      simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      rw [hR.x_succ j]
      by_cases hsucc : f (R.x j + R.s j) < f (R.x j)
      · rw [if_pos hsucc, ih', hs j, hmm j (by omega)]
        have hsum : (fun i => (((∑ k ∈ Finset.range (j+1), z k i : ℤ)) : ℝ)) =
            (fun i => (((∑ k ∈ Finset.range j, z k i : ℤ)) : ℝ)) +
              (mm j : ℝ) • (fun i => (c j i : ℝ)) := by
          funext i
          simp [Finset.sum_range_succ, z, hsucc]
        rw [hsum, Matrix.mulVec_add, Matrix.mulVec_smul, WithLp.toLp_add, WithLp.toLp_smul,
          smul_add, add_assoc, smul_smul]
        unfold stepOf
        rw [WithLp.toLp_smul]
      · rw [if_neg hsucc, ih']
        congr 3
        funext i
        simp [Finset.sum_range_succ, z, hsucc]
  exact key N le_rfl
