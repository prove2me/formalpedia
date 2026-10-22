-- Prove2me | solution 1 for ModernConvex.EllipsoidMethod.half_ellipsoid_cover
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T13:20:27.486989+00:00
-- url     : https://prove2.me/submissions/a513f844-828e-4f15-912c-ef22651285da

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

lemma g69el_vol {n : ℕ} (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    MeasureTheory.volume (ellipsoid c B) =
      ENNReal.ofReal |B.det| * MeasureTheory.volume {u : Fin n → ℝ | u ⬝ᵥ u ≤ 1} := by
  have : ellipsoid c B = (fun x => c + x) '' (Matrix.toLin' B '' {u | u ⬝ᵥ u ≤ 1}) := by
    ext x
    simp only [ellipsoid, Set.mem_setOf_eq, Set.mem_image, Matrix.toLin'_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨B *ᵥ u, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
  rw [this, Set.image_add_left, MeasureTheory.measure_preimage_add,
    MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin']

lemma g69el_unit {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (a : Fin n → ℝ) (ha : a ≠ 0) :
    cutDirection B a ⬝ᵥ cutDirection B a = 1 ∧
      Bᵀ *ᵥ a = Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) • cutDirection B a ∧
      0 < Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a)) := by
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
  have hsq : 0 < Real.sqrt (w ⬝ᵥ w) := Real.sqrt_pos.2 hqpos
  refine ⟨?_, ?_, by rw [hq]; exact hsq⟩
  · unfold cutDirection
    rw [hq, ← hwdef, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    rw [one_div_mul_one_div, Real.mul_self_sqrt hqpos.le]
    field_simp
  · unfold cutDirection
    rw [hq, ← hwdef, smul_smul, mul_one_div_cancel hsq.ne', one_smul]

lemma g69el_half {n : ℕ} (hn : 1 < n) (c : Fin n → ℝ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    halfEllipsoid c B a ⊆ ellipsoid (nextCenter c B a) (nextMatrix B a) := by
  obtain ⟨hp, hBa, hsq⟩ := g69el_unit B hB a ha
  set p := cutDirection B a with hpdef
  set q := Real.sqrt (a ⬝ᵥ ((B * Bᵀ) *ᵥ a))
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  set κ := (n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1) with hκdef
  set l := (n:ℝ) / ((n:ℝ) + 1) with hldef
  have hκ : 0 < κ := div_pos (by linarith) hs
  have hl : 0 < l := div_pos (by linarith) (by linarith)
  rintro x ⟨⟨u, hu, rfl⟩, hcut⟩
  set s := p ⬝ᵥ u with hsdef
  set δ := 1 / ((n:ℝ) + 1) with hδdef
  -- s ≤ 0
  have hs0 : s ≤ 0 := by
    have h1 : a ⬝ᵥ (B *ᵥ u) ≤ 0 := by
      rw [dotProduct_add] at hcut; linarith
    have h2 : a ⬝ᵥ (B *ᵥ u) = q * s := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hBa, smul_dotProduct, smul_eq_mul]
    rw [h2] at h1
    by_contra hc; push Not at hc
    have := mul_pos hsq hc; linarith
  -- |u - s p|² = u⬝u - s²
  have hperp : (u - s • p) ⬝ᵥ (u - s • p) = u ⬝ᵥ u - s ^ 2 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hp]
    rw [dotProduct_comm u p]; ring
  have hp_perp : p ⬝ᵥ (u - s • p) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hp, smul_eq_mul]; ring
  have hnn : 0 ≤ (u - s • p) ⬝ᵥ (u - s • p) := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsge : -1 ≤ s := by nlinarith
  refine ⟨κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p), ?_, ?_⟩
  · -- norm bound
    have e : (κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p)) ⬝ᵥ (κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p))
        = κ⁻¹ ^ 2 * (u ⬝ᵥ u - s ^ 2) + l⁻¹ ^ 2 * (s + δ) ^ 2 := by
      simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, hperp, hp]
      rw [dotProduct_comm (u - s • p) p, hp_perp]; ring
    rw [e]
    have hκ2 : κ⁻¹ ^ 2 = ((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2 := by
      rw [hκdef, inv_div, div_pow, Real.sq_sqrt hw.le]
    have hl2 : l⁻¹ ^ 2 = ((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2 := by rw [hldef, inv_div, div_pow]
    rw [hκ2, hl2, hδdef]
    have hn0 : (0:ℝ) < (n:ℝ) ^ 2 := by positivity
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
    have key : ((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2 * (u ⬝ᵥ u - s ^ 2) +
        ((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2 * (s + 1 / ((n:ℝ) + 1)) ^ 2 =
        (((n:ℝ) ^ 2 - 1) * (u ⬝ᵥ u - s ^ 2) + (((n:ℝ) + 1) * s + 1) ^ 2) / (n:ℝ) ^ 2 := by
      field_simp
    rw [key, div_le_one hn0]
    have h1 := mul_le_mul_of_nonneg_left hu hw.le
    have h2 := mul_nonneg hn1.le (mul_nonneg (neg_nonneg.mpr hs0) (show 0 ≤ s + 1 by linarith))
    nlinarith
  · -- the point
    have hvm : ∀ v w z : Fin n → ℝ, vecMulVec (B *ᵥ v) w *ᵥ z = (w ⬝ᵥ z) • (B *ᵥ v) := by
      intro v w z; ext i; simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    unfold nextCenter nextMatrix
    rw [← hpdef, add_mulVec, smul_mulVec, smul_mulVec, hvm]
    have hdot : p ⬝ᵥ (κ⁻¹ • (u - s • p) + l⁻¹ • ((s + δ) • p)) = l⁻¹ * (s + δ) := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, hp_perp, dotProduct_smul, hp]; simp
    rw [hdot]
    simp only [mulVec_add, mulVec_smul, mulVec_sub]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hκdef, hldef, hδdef]
    have hn0 : (n:ℝ) ≠ 0 := by positivity
    have hn1 : (n:ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring


open Matrix MeasureTheory
open ModernConvex.EllipsoidMethod
/-- Ben-Tal–Nemirovski, p. 344, statement (∗), case `n > 1`, with (5.2.13) and (5.2.14).
Let `E = {x = c + Bu | uᵀu ≤ 1}` with `Det B ≠ 0` and `Ê = {x ∈ E | aᵀx ≤ aᵀc}`, `a ≠ 0`.
With `p = Bᵀa/√(aᵀBBᵀa)`, `c⁺ = c − (1/(n+1))Bp` and
`B⁺ = B((n/√(n²−1))(Iₙ − ppᵀ) + (n/(n+1))ppᵀ) = (n/√(n²−1))B + (n/(n+1) − n/√(n²−1))(Bp)pᵀ`,
the half-ellipsoid `Ê` lies in `E⁺ = {c⁺ + B⁺u | uᵀu ≤ 1}` and
`Vol(E⁺) = (n/√(n²−1))^{n−1} (n/(n+1)) Vol(E) ≤ exp{−1/(2n)} Vol(E)` (Lebesgue measure). -/
theorem solution {n : ℕ} (hn : 1 < n) (c : Fin n → ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (a : Fin n → ℝ) (ha : a ≠ 0) :
    B * (((n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) •
          (1 - vecMulVec (cutDirection B a) (cutDirection B a)) +
        ((n : ℝ) / ((n : ℝ) + 1)) • vecMulVec (cutDirection B a) (cutDirection B a)) =
      nextMatrix B a ∧
    halfEllipsoid c B a ⊆ ellipsoid (nextCenter c B a) (nextMatrix B a) ∧
    volume (ellipsoid (nextCenter c B a) (nextMatrix B a)) =
      ENNReal.ofReal (((n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) ^ (n - 1) *
        ((n : ℝ) / ((n : ℝ) + 1))) * volume (ellipsoid c B) ∧
    volume (ellipsoid (nextCenter c B a) (nextMatrix B a)) ≤
      ENNReal.ofReal (Real.exp (-1 / (2 * (n : ℝ)))) * volume (ellipsoid c B) := by
  have hn2 : 2 ≤ n := by omega
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn2
  have hw : 0 < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt ((n:ℝ) ^ 2 - 1) := Real.sqrt_pos.2 hw
  have hC : 0 ≤ ((n:ℝ) / Real.sqrt ((n:ℝ) ^ 2 - 1)) ^ (n - 1) * ((n:ℝ) / ((n:ℝ) + 1)) :=
    mul_nonneg (pow_nonneg (div_pos (by linarith) hs).le _) (div_pos (by linarith) (by linarith)).le
  have hvol : MeasureTheory.volume (ellipsoid (nextCenter c B a) (nextMatrix B a)) =
      ENNReal.ofReal (((n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 - 1)) ^ (n - 1) *
        ((n : ℝ) / ((n : ℝ) + 1))) * MeasureTheory.volume (ellipsoid c B) := by
    rw [g69el_vol, g69el_vol, g69el_det_next hn2 B hB a ha, abs_mul, abs_of_nonneg hC,
      ENNReal.ofReal_mul (abs_nonneg _)]
    ring
  refine ⟨?_, g69el_half hn c B hB a ha, hvol, ?_⟩
  · unfold nextMatrix
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec]
    simp only [smul_sub, sub_smul]
    abel
  · rw [hvol]
    gcongr
    exact g69el_bound n hn2


