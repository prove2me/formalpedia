-- Prove2me | solution 1 for ModernConvex.EllipsoidMethod.radius_decay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:13:20.522604+00:00
-- url     : https://prove2.me/submissions/973aa401-fb2e-46d9-8e58-f3f3e439b1c8

import Mathlib
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod

open Matrix ModernConvex.EllipsoidMethod

lemma g69el_log_le (v : ℝ) (hv : 0 ≤ v) : Real.log (1 + v) ≤ v - v ^ 2 / 2 + v ^ 3 / 3 := by
  let g : ℝ → ℝ := fun t => t - t ^ 2 / 2 + t ^ 3 / 3 - Real.log (1 + t)
  have hd : ∀ t, 0 ≤ t → HasDerivAt g (t ^ 3 / (1 + t)) t := by
    intro t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := ((((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
      ((hasDerivAt_pow 3 t).div_const 3)).sub (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log h1))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, id]
    field_simp; ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact (hd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht; rw [(hd t (le_of_lt ht)).deriv]
      have : (0:ℝ) < t := ht; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv) hv
  simp only [g] at this; simp at this; linarith

lemma g69el_log_ge (x : ℝ) (hx : 0 ≤ x) : x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ≤ Real.log (1 + x) := by
  let g : ℝ → ℝ := fun t => Real.log (1 + t) - (t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)
  have hd : ∀ t, 0 ≤ t → HasDerivAt g (t ^ 4 / (1 + t)) t := by
    intro t ht
    have h1 : (1 + t) ≠ 0 := by linarith
    have := (((hasDerivAt_const t (1:ℝ)).add (hasDerivAt_id t)).log h1).sub
      ((((hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 3 t).div_const 3)).sub ((hasDerivAt_pow 4 t).div_const 4))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply, id]
    field_simp; ring
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact (hd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht; rw [interior_Ici] at ht; rw [(hd t (le_of_lt ht)).deriv]
      have : (0:ℝ) < t := ht; positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only [g] at this; simp at this; linarith

/-- the rational inequality behind the volume decrease -/
lemma g69el_rat (n : ℝ) (hn : 2 ≤ n) :
    (n - 1) / 2 * (1 / (n ^ 2 - 1) - (1 / (n ^ 2 - 1)) ^ 2 / 2 + (1 / (n ^ 2 - 1)) ^ 3 / 3)
      - (1 / n - (1 / n) ^ 2 / 2 + (1 / n) ^ 3 / 3 - (1 / n) ^ 4 / 4) ≤ -1 / (2 * n) := by
  have h1 : 0 < n ^ 2 - 1 := by nlinarith
  have h2 : 0 < n := by linarith
  set P : ℝ := -n ^ 7 + 5 * n ^ 5 - 2 * n ^ 4 - 6 * n ^ 3 + 3 * n ^ 2 + 4 * n - 3 with hPdef
  have key : ((n - 1) / 2 * (1 / (n ^ 2 - 1) - (1 / (n ^ 2 - 1)) ^ 2 / 2 + (1 / (n ^ 2 - 1)) ^ 3 / 3)
      - (1 / n - (1 / n) ^ 2 / 2 + (1 / n) ^ 3 / 3 - (1 / n) ^ 4 / 4)) - (-1 / (2 * n))
      = P / (12 * (n ^ 2 - 1) ^ 3 * n ^ 4) := by
    rw [hPdef]; field_simp; ring
  have hP : P ≤ 0 := by
    have hm : 0 ≤ n - 2 := by linarith
    have e : P = -((n - 2) ^ 7 + 14 * (n - 2) ^ 6 + 79 * (n - 2) ^ 5 + 232 * (n - 2) ^ 4
      + 382 * (n - 2) ^ 3 + 353 * (n - 2) ^ 2 + 168 * (n - 2) + 31) := by rw [hPdef]; ring
    rw [e]; exact neg_nonpos.mpr (by positivity)
  have : P / (12 * (n ^ 2 - 1) ^ 3 * n ^ 4) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hP (by positivity)
  linarith

lemma g69el_bound (n : ℕ) (hn : 2 ≤ n) :
    ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) ≤
      Real.exp (-1 / (2 * (n:ℝ))) := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hκ : 0 < (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1) := div_pos (by linarith) hs
  have hl0 : 0 < (n:ℝ) / ((n:ℝ) + 1) := div_pos (by linarith) (by linarith)
  have hκ2 : ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ 2 = 1 + 1 / ((n:ℝ) ^ 2 - 1) := by
    rw [div_pow, Real.sq_sqrt hw.le]; field_simp; ring
  have hlogκ : Real.log ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) = Real.log (1 + 1 / ((n:ℝ) ^ 2 - 1)) / 2 := by
    rw [← hκ2, Real.log_pow]; push_cast; ring
  have hl : (n:ℝ) / ((n:ℝ) + 1) = (1 + 1 / (n:ℝ))⁻¹ := by field_simp
  have hlogl : Real.log ((n:ℝ) / ((n:ℝ) + 1)) = -Real.log (1 + 1 / (n:ℝ)) := by rw [hl, Real.log_inv]
  rw [← Real.log_le_iff_le_exp (mul_pos (pow_pos hκ _) hl0), Real.log_mul (pow_pos hκ _).ne' hl0.ne',
    Real.log_pow, hlogκ, hlogl]
  have h1 := g69el_log_le (1 / ((n:ℝ) ^ 2 - 1)) (by positivity)
  have h2 := g69el_log_ge (1 / (n:ℝ)) (by positivity)
  have h3 := g69el_rat (n:ℝ) hN
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hn1]
  have hN1 : 0 ≤ ((n:ℝ) - 1) / 2 := by linarith
  have := mul_le_mul_of_nonneg_left h1 hN1
  nlinarith

lemma g69el_det_aux {n : ℕ} (hn : 1 ≤ n) (κ μ : ℝ) (hκ : κ ≠ 0) (p : Fin n → ℝ) (hp : p ⬝ᵥ p = 1) :
    det (κ • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • vecMulVec p p) = κ ^ (n - 1) * (κ + μ) := by
  have e : κ • (1 : Matrix (Fin n) (Fin n) ℝ) + μ • vecMulVec p p =
      κ • (1 + vecMulVec ((μ / κ) • p) p) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    field_simp
  rw [e, det_smul, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin,
    dotProduct_smul, hp, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

lemma g69el_det_next {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    (nextMatrix B a).det = B.det * (((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1))) := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hκ : 0 < (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1) := div_pos (by linarith) hs
  set w := Bᵀ *ᵥ a with hwdef
  have hBt : IsUnit Bᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hB
  have hw0 : w ≠ 0 := by
    intro h
    apply ha
    have : (Bᵀ)⁻¹ *ᵥ w = a := by rw [hwdef, mulVec_mulVec, nonsing_inv_mul _ hBt, one_mulVec]
    rw [← this, h, mulVec_zero]
  have hq : a ⬝ᵥ ((B * Bᵀ) *ᵥ a) = w ⬝ᵥ w := by
    rw [← mulVec_mulVec, dotProduct_mulVec, hwdef, ← mulVec_transpose]
  have hqpos : 0 < w ⬝ᵥ w := by
    have h0 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
    exact lt_of_le_of_ne h0 (Ne.symm (fun h => hw0 (dotProduct_self_eq_zero.mp h)))
  have hp : cutDirection B a ⬝ᵥ cutDirection B a = 1 := by
    unfold cutDirection
    rw [hq, ← hwdef, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rw [one_div_mul_one_div, Real.mul_self_sqrt hqpos.le]
    field_simp
  have e : nextMatrix B a = B * (((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      ((n:ℝ) / ((n:ℝ) + 1) - (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) •
        vecMulVec (cutDirection B a) (cutDirection B a)) := by
    unfold nextMatrix
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, mul_vecMulVec]
  rw [e, det_mul, g69el_det_aux (by omega) _ _ hκ.ne' _ hp]
  ring

lemma g69el_step {n : ℕ} {X : Set (Fin n → ℝ)} {sep : (Fin n → ℝ) → Option (Fin n → ℝ)}
    (hsep : IsSeparationOracle X sep) (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R : ℝ) (s s' : State n)
    (h : step sep O R s = StepResult.next s') : ∃ a : Fin n → ℝ, a ≠ 0 ∧ s'.B = nextMatrix s.B a := by
  unfold step at h
  rcases hs : sep s.c with _ | a
  · rw [hs] at h
    simp only at h
    split_ifs at h with h0
    all_goals cases h
    exact ⟨(O s.c).2, h0, rfl⟩
  · rw [hs] at h
    simp only at h
    cases h
    exact ⟨a, ((hsep s.c).2 a hs).1, rfl⟩

lemma g69el_inv {n : ℕ} (hn : 2 ≤ n) {X : Set (Fin n → ℝ)} {sep : (Fin n → ℝ) → Option (Fin n → ℝ)}
    (hsep : IsSeparationOracle X sep) (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (R r ε : ℝ) (hR : 0 < R) :
    ∀ (t : ℕ) (s : State n), run sep O R r ε t = Outcome.running s →
      s.B.det ≠ 0 ∧ |s.B.det| ≤ (((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) *
        ((n:ℝ) / ((n:ℝ) + 1))) ^ t * R ^ n := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hc : 0 < ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) :=
    mul_pos (pow_pos (div_pos (by linarith) hs) _) (div_pos (by linarith) (by linarith))
  intro t
  induction t with
  | zero =>
    intro s h
    simp only [run] at h
    cases h
    simp only [initState, det_smul, det_one, Fintype.card_fin, mul_one, pow_zero, one_mul]
    exact ⟨(pow_pos hR n).ne', (abs_of_pos (pow_pos hR n)).le⟩
  | succ t ih =>
    intro s h
    simp only [run] at h
    rcases hr : run sep O R r ε t with s0 | x
    · rw [hr] at h
      simp only at h
      rcases hst : step sep O R s0 with x | s'
      · rw [hst] at h; simp only at h; cases h
      · rw [hst] at h
        simp only at h
        split_ifs at h
        all_goals cases h
        obtain ⟨a, ha, hB⟩ := g69el_step hsep O R s0 _ hst
        obtain ⟨h0, hle⟩ := ih s0 hr
        rw [hB, g69el_det_next hn _ h0 a ha, abs_mul, abs_of_pos hc, pow_succ]
        refine ⟨mul_ne_zero h0 hc.ne', ?_⟩
        calc |s0.B.det| * _ ≤ (_ ^ t * R ^ n) * _ := mul_le_mul_of_nonneg_right hle hc.le
          _ = _ := by ring
    · rw [hr] at h; simp only at h; cases h


open Matrix MeasureTheory
open ModernConvex.EllipsoidMethod
/-- Ben-Tal–Nemirovski, p. 350, Eq. (5.2.21), in the proof of Theorem 5.2.1. Let the ellipsoid
method with accuracy `ε > 0` be applied to (5.2.9) of dimension `n ≥ 2` under assumption A,
with a separation oracle for `X` and a first order oracle for `f`. If the method is still
running after `t` steps and step `t + 1` performs rule 3 (it does not stop by rule 2), the
new ellipsoid `E_{t+1} = {c_{t+1} + B_{t+1}u | uᵀu ≤ 1}` satisfies
`ρ_{t+1} = |Det B_{t+1}|^{1/n} ≤ exp{−(t+1)/(2n²)} R`. -/
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (r R : ℝ) (hP : IsBlackBoxProgram f X r R)
    (sep : (Fin n → ℝ) → Option (Fin n → ℝ)) (hsep : IsSeparationOracle X sep)
    (O : (Fin n → ℝ) → ℝ × (Fin n → ℝ)) (hO : IsFirstOrderOracle f O)
    (ε : ℝ) (hε : 0 < ε)
    (t : ℕ) (s s' : State n) (hrun : run sep O R r ε t = Outcome.running s)
    (hstep : step sep O R s = StepResult.next s') :
    radius s'.B ≤ Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) * R := by
  have hR : 0 < R := hP.2.2.2.2.2.2.1
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  set c := ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) with hcdef
  have hc : 0 < c := mul_pos (pow_pos (div_pos (by linarith) hs) _) (div_pos (by linarith) (by linarith))
  obtain ⟨h0, hle⟩ := g69el_inv hn hsep O R r ε hR t s hrun
  obtain ⟨a, ha, hB⟩ := g69el_step hsep O R s s' hstep
  have hdet : |s'.B.det| ≤ Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) * R ^ n := by
    rw [hB, g69el_det_next hn _ h0 a ha, abs_mul, abs_of_pos hc]
    have hcb : c ≤ Real.exp (-1 / (2 * (n:ℝ))) := g69el_bound n hn
    have h1 : c ^ (t + 1) ≤ Real.exp (-1 / (2 * (n:ℝ))) ^ (t + 1) := pow_le_pow_left₀ hc.le hcb _
    have h2 : Real.exp (-1 / (2 * (n:ℝ))) ^ (t + 1) = Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc |s.B.det| * c ≤ (c ^ t * R ^ n) * c := mul_le_mul_of_nonneg_right hle hc.le
      _ = c ^ (t + 1) * R ^ n := by ring
      _ ≤ Real.exp (-1 / (2 * (n:ℝ))) ^ (t + 1) * R ^ n :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hR.le _)
      _ = _ := by rw [h2]
  unfold radius
  calc |s'.B.det| ^ ((1:ℝ) / n) ≤ (Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) * R ^ n) ^ ((1:ℝ) / n) :=
        Real.rpow_le_rpow (abs_nonneg _) hdet (by positivity)
    _ = Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ))) ^ ((1:ℝ) / n) * (R ^ n) ^ ((1:ℝ) / n) :=
        Real.mul_rpow (Real.exp_pos _).le (pow_nonneg hR.le _)
    _ = Real.exp (-((t : ℝ) + 1) / (2 * (n : ℝ) ^ 2)) * R := by
        rw [← Real.exp_mul, one_div, Real.pow_rpow_inv_natCast hR.le (by omega)]
        congr 1; congr 1; field_simp


