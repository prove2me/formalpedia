-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.infinite_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:27:48.643213+00:00
-- url     : https://prove2.me/submissions/61918059-646a-42d2-8508-98cf3e965078

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

open scoped BigOperators
open OAI.PiExponent.FinitePeriodCollision

namespace E103IC

theorem choose_le_sum (T : Finset ℕ) : T.card.choose 2 ≤ ∑ x ∈ T, x := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl _ (hlt a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (hlt x hx)
      simpa using Finset.card_le_card this
    have h2 : (s.card + 1).choose 2 = s.card.choose 1 + s.card.choose 2 := Nat.choose_succ_succ _ _
    rw [Nat.choose_one_right] at h2
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, h2]
    omega

theorem fiber_bound {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (d : ι → ℕ)
    (hinj : ∀ r r', r ≠ r' → group r = group r' → d r ≠ d r') :
    (∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card).choose 2) ≤
      ∑ r, d r := by
  rw [← Finset.sum_fiberwise Finset.univ group d]
  refine Finset.sum_le_sum fun a _ => ?_
  have hi : Set.InjOn d ((Finset.univ : Finset ι).filter (fun i => group i = a)) := by
    intro x hx y hy hxy
    by_contra hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    exact hinj x y hne (hx.trans hy.symm) hxy
  have := choose_le_sum (((Finset.univ : Finset ι).filter (fun i => group i = a)).image d)
  rw [Finset.card_image_of_injOn hi, Finset.sum_image hi] at this
  exact this

end E103IC

theorem solution
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (A : Matrix ι ι ℂ) (D s : ℝ) (bound : ι → ℝ)
    (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hbound : ∀ i, 0 ≤ bound i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ bound i * s ^ (d + d))
    (hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (A i j)) :
    ‖Matrix.det A‖ ≤
      (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι *
        (∏ i, bound i)) *
      s ^ (∑ a : κ,
        (((Finset.univ : Finset ι).filter (fun i => group i = a)).card).choose 2) *
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  set S := ∑ a : κ, (((Finset.univ : Finset ι).filter (fun i => group i = a)).card).choose 2
    with hS
  set K : ℝ := ((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι * (∏ i, bound i) with hK
  have hK0 : 0 ≤ K := by
    have := Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => hbound i
    positivity
  let AN : ℕ → Matrix ι ι ℂ := fun N i j => ∑ e ∈ Finset.range N, B i e * C (group i) e j
  have hlim : Filter.Tendsto (fun N => (AN N).det) Filter.atTop (nhds A.det) := by
    have : Filter.Tendsto AN Filter.atTop (nhds A) := by
      refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
      exact (hsum i j).tendsto_sum_nat
    exact ((continuous_id.matrix_det).tendsto A).comp this
  -- determinant of the "pure" matrices
  let M : (ι → ℕ) → Matrix ι ι ℂ := fun d => Matrix.of fun r j => C (group r) (d r) j
  have hexp : ∀ N, (AN N).det =
      ∑ d ∈ Fintype.piFinset (fun _ : ι => Finset.range N), (∏ r, B r (d r)) * (M d).det := by
    intro N
    have hrow : AN N = Matrix.of fun r => ∑ e ∈ Finset.range N, B r e • (fun j => C (group r) e j) := by
      ext i j; simp [AN, Finset.sum_apply]
    rw [hrow]
    have h := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum_finset
      (fun r e => B r e • fun j => C (group r) e j) (fun _ => Finset.range N)
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul] at h
    exact h
  have hterm : ∀ d : ι → ℕ, ‖(∏ r, B r (d r)) * (M d).det‖ ≤
      K * s ^ S * ∏ r, s ^ (d r) := by
    intro d
    have hRnn : 0 ≤ K * s ^ S * ∏ r, s ^ (d r) := by positivity
    by_cases hrep : ∃ r r', r ≠ r' ∧ group r = group r' ∧ d r = d r'
    · obtain ⟨r, r', hne, hg, hd⟩ := hrep
      have : (M d).det = 0 := Matrix.det_zero_of_row_eq hne (by ext j; simp [M, hg, hd])
      rw [this, mul_zero, norm_zero]; exact hRnn
    · push_neg at hrep
      have hinj : ∀ r r', r ≠ r' → group r = group r' → d r ≠ d r' :=
        fun r r' h1 h2 => hrep r r' h1 h2
      have hfb := E103IC.fiber_bound group d hinj
      have hdet : ‖(M d).det‖ ≤ ((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι := by
        have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ) (A := M d) (x := D)
          (fun i j => hC _ _ _)
        rw [nsmul_eq_mul] at this
        exact this
      have hprod : ‖∏ r, B r (d r)‖ ≤ (∏ r, bound r) * s ^ (∑ r, d r + ∑ r, d r) := by
        rw [norm_prod]
        calc ∏ r, ‖B r (d r)‖ ≤ ∏ r, (bound r * s ^ (d r + d r)) :=
              Finset.prod_le_prod (fun r _ => norm_nonneg _) fun r _ => hB r (d r)
          _ = (∏ r, bound r) * s ^ (∑ r, d r + ∑ r, d r) := by
            rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib]
      have hpow : s ^ (∑ r, d r + ∑ r, d r) ≤ s ^ S * ∏ r, s ^ (d r) := by
        rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
        exact pow_le_pow_of_le_one hs0 hs1.le (by omega)
      rw [norm_mul]
      calc ‖∏ r, B r (d r)‖ * ‖(M d).det‖
          ≤ ((∏ r, bound r) * (s ^ S * ∏ r, s ^ (d r))) *
              (((Fintype.card ι).factorial : ℝ) * D ^ Fintype.card ι) := by
            refine mul_le_mul (hprod.trans ?_) hdet (norm_nonneg _)
              (mul_nonneg (Finset.prod_nonneg fun i _ => hbound i) (by positivity))
            exact mul_le_mul_of_nonneg_left hpow
              (Finset.prod_nonneg fun i _ => hbound i)
        _ = K * s ^ S * ∏ r, s ^ (d r) := by rw [hK]; ring
  have hbnd : ∀ N, ‖(AN N).det‖ ≤ K * s ^ S * ((1 - s)⁻¹) ^ Fintype.card ι := by
    intro N
    rw [hexp]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun d _ => hterm d).trans ?_
    rw [← Finset.mul_sum, ← Finset.prod_univ_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod (fun r _ => Finset.sum_nonneg fun e _ => by positivity) fun r _ => ?_
    have := geom_sum_Ico_le_of_lt_one hs0 hs1 (m := 0) (n := N)
    rw [← Finset.range_eq_Ico, pow_zero, one_div] at this
    exact this
  exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall hbnd)
