-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.real_bound_of_fin_three
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-29T01:02:28.26421+00:00
-- url     : https://prove2.me/submissions/2a0c89fe-3f71-4e44-a84d-77bc70d70167

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Sparsification
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_WeightedCoordinates
import Definitions.Def_HlawkaSchatten_GapComparison
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_concaveOn_weightedNorm
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_sparse_concave_minimizer
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Reduction of a failed bound to three real coordinates

Common coordinate weights preserve the three pair power sums. The positive
part of the target inequality is concave in these weights, so the sparse
minimizer lemma reduces the question to at most three nonzero coordinates.
-/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Coordinate norms for the diagonal construction

The explicit finite power sum keeps coordinate arguments independent of
the exponent-indexed `PiLp` type. Its norm laws are inherited from `PiLp`.
-/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

































theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h



theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h





end HlawkaSchatten.DiagonalConstruction

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Concavity under common coordinate reweighting -/

namespace HlawkaSchatten.DiagonalConstruction

variable {ι : Type*} [Fintype ι]





omit [Fintype ι] in
theorem reweight_add (p : ℝ) (w x y : ι → ℝ) :
    reweight p w (x + y) = reweight p w x + reweight p w y := by
  ext i
  exact mul_add _ _ _

theorem lpNorm_reweight {p : ℝ} (hp : 0 < p) (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) : lpNorm p (reweight p w x) = weightedNorm p x w := by
  unfold lpNorm weightedNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [reweight, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw i) (1 / p))]
  rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (abs_nonneg _),
    ← Real.rpow_mul (hw i), one_div_mul_cancel hp.ne', Real.rpow_one]

theorem weightedNorm_one (p : ℝ) (x : ι → ℝ) :
    weightedNorm p x (fun _ ↦ 1) = lpNorm p x := by
  simp [weightedNorm, lpNorm, Real.norm_eq_abs]

theorem continuous_weightedNorm {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    Continuous (weightedNorm p x) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).mul continuous_const).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))





end HlawkaSchatten.DiagonalConstruction

private theorem pair_power_sum_pos {p a b c : ℝ} (hp : 0 < p)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    0 < |a + b| ^ p + |a + c| ^ p + |b + c| ^ p := by
  have h1 := Real.rpow_nonneg (abs_nonneg (a + b)) p
  have h2 := Real.rpow_nonneg (abs_nonneg (a + c)) p
  have h3 := Real.rpow_nonneg (abs_nonneg (b + c)) p
  by_contra hn
  have hn' : |a + b| ^ p + |a + c| ^ p + |b + c| ^ p ≤ 0 := le_of_not_gt hn
  have hab : a + b = 0 := abs_eq_zero.mp
    ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp (by linarith : |a + b| ^ p = 0))
  have hac : a + c = 0 := abs_eq_zero.mp
    ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp (by linarith : |a + c| ^ p = 0))
  have hbc : b + c = 0 := abs_eq_zero.mp
    ((Real.rpow_eq_zero (abs_nonneg _) hp.ne').mp (by linarith : |b + c| ^ p = 0))
  rcases h with h | h | h <;> apply h <;> linarith

private theorem bound_of_fin_three_active {p K : ℝ} (hp : 1 < p) (hK : 1 / 2 ≤ K)
    (h3 : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) K)
    (x y z : ι → ℝ) (hrow : ∀ i, x i ≠ 0 ∨ y i ≠ 0 ∨ z i ≠ 0) :
    tripleGap (lpNorm p) x y z ≤ K * pairGapSum (lpNorm p) x y z := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans hp
  let A : ι → Fin 3 → ℝ := fun i ↦ ![|x i + y i| ^ p, |x i + z i| ^ p, |y i + z i| ^ p]
  let b : Fin 3 → ℝ := fun k ↦ ∑ i, A i k
  let F : (ι → ℝ) → ℝ := fun w ↦
    (2 * K - 1) * (weightedNorm p x w + weightedNorm p y w + weightedNorm p z w) +
      weightedNorm p (x + y + z) w
  have hA : ∀ i k, 0 ≤ A i k := by
    intro i k
    fin_cases k <;> exact Real.rpow_nonneg (abs_nonneg _) p
  have hpos : ∀ i, 0 < ∑ k, A i k := by
    intro i
    simpa only [A, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
      pair_power_sum_pos hp0 (hrow i)
  have hF : Continuous F :=
    (continuous_const.mul (((continuous_weightedNorm hp0 x).add
      (continuous_weightedNorm hp0 y)).add (continuous_weightedNorm hp0 z))).add
        (continuous_weightedNorm hp0 (x + y + z))
  have hconc : ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} F := by
    exact (ConcaveOn.smul (by linarith : 0 ≤ 2 * K - 1)
      (((concaveOn_weightedNorm hp x).add (concaveOn_weightedNorm hp y)).add
        (concaveOn_weightedNorm hp z))).add (concaveOn_weightedNorm hp (x + y + z))
  have hseed : (fun _ : ι ↦ (1 : ℝ)) ∈ momentFiber A b := by
    exact ⟨fun _ ↦ zero_le_one, fun _ ↦ by simp [b]⟩
  obtain ⟨w, hw, hmin, hcard⟩ := exists_sparse_concave_minimizer A b hA hpos F hF hconc _ hseed
  let J := {i : ι // w i ≠ 0}
  let R : (ι → ℝ) → J → ℝ := fun v j ↦ reweight p w v j.1
  have hadd (u v : ι → ℝ) : R (u + v) = R u + R v := by
    ext j
    exact congrFun (reweight_add p w u v) j.1
  have hnorm (v : ι → ℝ) : lpNorm p (R v) = weightedNorm p v w := by
    change lpNorm p (fun j : J ↦ reweight p w v j.1) = _
    rw [lpNorm_subtype hp0 (reweight p w v) (fun i ↦ w i ≠ 0)]
    · exact lpNorm_reweight hp0 w v hw.1
    · intro i hi
      simp [reweight, not_ne_iff.mp hi, hp0.ne']
  have hxy : weightedNorm p (x + y) w = lpNorm p (x + y) := by
    unfold weightedNorm lpNorm
    congr 1
    simpa only [A, b, Pi.add_apply, Real.norm_eq_abs, Matrix.cons_val_zero] using hw.2 0
  have hxz : weightedNorm p (x + z) w = lpNorm p (x + z) := by
    unfold weightedNorm lpNorm
    congr 1
    simpa only [A, b, Pi.add_apply, Real.norm_eq_abs, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hw.2 1
  have hyz : weightedNorm p (y + z) w = lpNorm p (y + z) := by
    unfold weightedNorm lpNorm
    congr 1
    simpa only [A, b, Pi.add_apply, Real.norm_eq_abs, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] using hw.2 2
  have h := (hasHlawkaConstant_of_card_le_three hp0 hcard h3) (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd, hnorm, hxy, hxz, hyz] at h
  dsimp only [F] at hmin
  simp only [weightedNorm_one] at hmin
  dsimp only [tripleGap, pairGapSum, pairGap]
  nlinarith

theorem solution {p K : ℝ} (hp : 1 < p) (hK : 1 / 2 ≤ K)
    (h3 : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) K) :
    HasHlawkaConstant (lpNorm p : (ι → ℝ) → ℝ) K := by
  classical
  intro x y z
  have hp0 : 0 < p := zero_lt_one.trans hp
  let P := fun i ↦ x i ≠ 0 ∨ y i ≠ 0 ∨ z i ≠ 0
  let J := {i : ι // P i}
  let R : (ι → ℝ) → J → ℝ := fun v j ↦ v j.1
  have hadd (u v : ι → ℝ) : R (u + v) = R u + R v := rfl
  have hnorm (v : ι → ℝ) (hv : ∀ i, x i = 0 → y i = 0 → z i = 0 → v i = 0) :
      lpNorm p (R v) = lpNorm p v := by
    apply lpNorm_subtype hp0 v P
    intro i hi
    have hzero : x i = 0 ∧ y i = 0 ∧ z i = 0 := by simpa [P] using hi
    exact hv i hzero.1 hzero.2.1 hzero.2.2
  have h := bound_of_fin_three_active hp hK h3 (R x) (R y) (R z) (fun j ↦ j.2)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  rw [hnorm x (by intros; assumption), hnorm y (by intros; assumption),
    hnorm z (by intros; assumption),
    hnorm (x + y + z) (by intros; simp_all),
    hnorm (x + y) (by intros; simp_all),
    hnorm (x + z) (by intros; simp_all),
    hnorm (y + z) (by intros; simp_all)] at h
  exact h
