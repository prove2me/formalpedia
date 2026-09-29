-- Prove2me | solution 1 for LewisTorczon.BoundPS.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:39:01.73222+00:00
-- url     : https://prove2.me/submissions/b75ea972-d217-4058-9b39-b575cf35709a

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

theorem aux_p42_mem {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ box lo hi := by
  intro k
  induction k with
  | zero => exact hR.x_zero_mem
  | succ k ih =>
    rw [hR.x_succ k]
    split_ifs
    · exact hR.step_feasible k
    · exact ih

theorem aux_p42_clamp (a b : EReal) (x t : ℝ) (ha : a ≤ (x : EReal)) (hb : (x : EReal) ≤ b) :
    a ≤ ((clampCoord a b t : ℝ) : EReal) ∧ ((clampCoord a b t : ℝ) : EReal) ≤ b ∧
      (clampCoord a b t < x → t ≤ clampCoord a b t) ∧
      (x < clampCoord a b t → clampCoord a b t ≤ t) := by
  have hV : ((clampCoord a b t : ℝ) : EReal) = max a (min b (t : EReal)) := by
    unfold clampCoord
    apply EReal.coe_toReal
    · exact (max_lt (ha.trans_lt (EReal.coe_lt_top x))
        ((min_le_right _ _).trans_lt (EReal.coe_lt_top t))).ne
    · have h1 : (⊥ : EReal) < min b (t : EReal) :=
        lt_min ((EReal.bot_lt_coe x).trans_le hb) (EReal.bot_lt_coe t)
      exact (h1.trans_le (le_max_right _ _)).ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hV]; exact le_max_left _ _
  · rw [hV]; exact max_le (ha.trans hb) (min_le_left _ _)
  · intro h
    have h' : ((clampCoord a b t : ℝ) : EReal) < (x : EReal) := EReal.coe_lt_coe_iff.mpr h
    rw [← EReal.coe_le_coe_iff, hV]
    rw [hV] at h'
    rcases le_total b (t : EReal) with hbt | htb
    · exfalso
      rw [min_eq_left hbt] at h'
      exact absurd (hb.trans (le_max_right a b)) (not_le.mpr h')
    · rw [min_eq_right htb]; exact le_max_right _ _
  · intro h
    have h' : (x : EReal) < ((clampCoord a b t : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr h
    rw [← EReal.coe_le_coe_iff, hV]
    rw [hV] at h'
    rcases le_total a (min b (t : EReal)) with hat | hta
    · rw [max_eq_right hat]; exact min_le_right _ _
    · exfalso
      rw [max_eq_left hta] at h'
      exact absurd ha (not_le.mpr h')

theorem aux_p42_step {n m : ℕ} (P : GPSParams n) (R : GPSRun n m) (k : ℕ)
    (hdiag : (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))).IsDiag) (Δ : ℝ) (j : Fin n) :
    stepOf P Δ ((R.M k).transpose j) =
      EuclideanSpace.single j (Δ * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j) := by
  ext r
  have key : (P.B.mulVec (fun l => (((R.M k).transpose j) l : ℝ))) r =
      (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) r j := by
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  simp only [stepOf, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul, key,
    PiLp.single_apply]
  split_ifs with h
  · subst h; rfl
  · rw [hdiag h, mul_zero]

theorem aux_p42_step_neg {n : ℕ} (P : GPSParams n) (Δ : ℝ) (c : Fin n → ℤ) :
    stepOf P Δ (-c) = stepOf P (-Δ) c := by
  ext r
  simp only [stepOf, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul]
  have : (fun r => (((-c) r : ℤ) : ℝ)) = -(fun r => (c r : ℝ)) := by ext; simp
  rw [this, Matrix.mulVec_neg]; simp

theorem aux_p42_diag_ne {n m : ℕ} (P : GPSParams n) (R : GPSRun n m) (k : ℕ)
    (hM : R.M k ∈ P.𝕄)
    (hdiag : (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))).IsDiag) (j : Fin n) :
    (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j ≠ 0 := by
  have hdet : (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))).det ≠ 0 := by
    rw [Matrix.det_mul, ← Int.cast_det]
    exact mul_ne_zero P.B_det_ne_zero (Int.cast_ne_zero.mpr (P.𝕄_det_ne_zero _ hM))
  rw [← (Matrix.isDiag_iff_diagonal_diag _).mp hdiag, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet j (Finset.mem_univ j)

theorem aux_p42_core {n m : ℕ} (P : GPSParams n) (R : GPSRun n m) (k : ℕ)
    (hdiag : (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))).IsDiag) (Δ : ℝ) (hΔ : 0 < Δ)
    (j : Fin n) (ε : ℝ)
    (hε : |ε| = Δ * |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j|) :
    ∃ c ∈ coreCols R k, stepOf P Δ c = EuclideanSpace.single j ε := by
  have h1 : |ε| = |Δ * (P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| := by
    rw [abs_mul, abs_of_pos hΔ, hε]
  rcases abs_eq_abs.mp h1 with h | h
  · exact ⟨(R.M k).transpose j, ⟨j, Or.inl rfl⟩, by rw [aux_p42_step P R k hdiag Δ j, h]⟩
  · refine ⟨-((R.M k).transpose j), ⟨j, Or.inr rfl⟩, ?_⟩
    rw [aux_p42_step_neg, aux_p42_step P R k hdiag (-Δ) j, h, neg_mul]

theorem aux_p42_finish {n : ℕ} (lo hi : Fin n → EReal) (x g : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ box lo hi) (j : Fin n) (ε a b : ℝ)
    (hlo : lo j ≤ ((x j + ε : ℝ) : EReal)) (hhi : ((x j + ε : ℝ) : EReal) ≤ hi j)
    (hin : g j * ε ≤ -(a * b) * |ε|) :
    x + EuclideanSpace.single j ε ∈ box lo hi ∧
      inner ℝ g (EuclideanSpace.single j ε) ≤ -a * b * ‖EuclideanSpace.single j ε‖ := by
  refine ⟨?_, ?_⟩
  · intro r
    by_cases hr : r = j
    · subst hr
      simp only [PiLp.add_apply, PiLp.single_apply, if_true]
      exact ⟨hlo, hhi⟩
    · simp only [PiLp.add_apply, PiLp.single_apply, if_neg hr, add_zero]
      exact hx r
  · rw [EuclideanSpace.inner_single_right, PiLp.norm_single]
    simp only [conj_trivial, Real.norm_eq_abs]
    linarith [mul_comm (g j) ε, neg_mul a b]

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R) (k : ℕ)
    (hq : projQ lo hi f (R.x k) ≠ 0) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ Δ : ℝ, 0 < Δ → Δ < ν →
      ∃ c ∈ coreCols R k, R.x k + stepOf P Δ c ∈ box lo hi ∧
        inner ℝ (gradient f (R.x k)) (stepOf P Δ c) ≤
          -(1 / Real.sqrt n) * ‖projQ lo hi f (R.x k)‖ * ‖stepOf P Δ c‖ := by
  classical
  have hxmem : R.x k ∈ box lo hi := aux_p42_mem P lo hi f R hR k
  have hex : ∃ j, projQ lo hi f (R.x k) j ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    ext j
    simp [h j]
  obtain ⟨j0, hj0⟩ := hex
  obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => |projQ lo hi f (R.x k) i|) ⟨j0, Finset.mem_univ _⟩
  have hqpos : 0 < |projQ lo hi f (R.x k) j| :=
    (abs_pos.mpr hj0).trans_le (hjmax j0 (Finset.mem_univ _))
  have hn : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast j.pos)
  have hnorm : ‖projQ lo hi f (R.x k)‖ ≤ Real.sqrt n * |projQ lo hi f (R.x k) j| := by
    rw [EuclideanSpace.norm_eq]
    rw [show Real.sqrt n * |projQ lo hi f (R.x k) j| =
        Real.sqrt (n * (projQ lo hi f (R.x k) j) ^ 2) by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs]]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖projQ lo hi f (R.x k) i‖ ^ 2
        ≤ ∑ _i : Fin n, (projQ lo hi f (R.x k) j) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          exact sq_le_sq.mpr (hjmax i (Finset.mem_univ _))
      _ = n * (projQ lo hi f (R.x k) j) ^ 2 := by simp
  have hA : 1 / Real.sqrt n * ‖projQ lo hi f (R.x k)‖ ≤ |projQ lo hi f (R.x k) j| := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn]
    linarith [mul_comm (Real.sqrt n) |projQ lo hi f (R.x k) j|]
  have hd0 := aux_p42_diag_ne P R k (hR.M_mem k) (hR.diag k) j
  have hdpos : 0 < |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| := abs_pos.mpr hd0
  refine ⟨|projQ lo hi f (R.x k) j| / |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j|,
    div_pos hqpos hdpos, ?_⟩
  intro Δ hΔ hΔν
  have hΔd : Δ * |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| <
      |projQ lo hi f (R.x k) j| := (lt_div_iff₀ hdpos).mp hΔν
  have hΔd0 : 0 < Δ * |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j| := mul_pos hΔ hdpos
  have hqj_eq : projQ lo hi f (R.x k) j =
      clampCoord (lo j) (hi j) (R.x k j - gradient f (R.x k) j) - R.x k j := by
    simp [projQ, boxProj]
  obtain ⟨hvlo, hvhi, hlt, hgt⟩ :=
    aux_p42_clamp (lo j) (hi j) (R.x k j) (R.x k j - gradient f (R.x k) j) (hxmem j).1 (hxmem j).2
  rcases lt_or_gt_of_ne (abs_pos.mp hqpos) with hneg | hpos
  · -- q_j < 0
    obtain ⟨c, hc, hcs⟩ := aux_p42_core P R k (hR.diag k) Δ hΔ j
      (-(Δ * |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j|))
      (by rw [abs_neg, abs_of_pos hΔd0])
    refine ⟨c, hc, ?_⟩
    rw [hcs]
    rw [abs_of_neg hneg] at hΔd hA
    have hv : clampCoord (lo j) (hi j) (R.x k j - gradient f (R.x k) j) < R.x k j := by linarith
    have hg := hlt hv
    apply aux_p42_finish lo hi (R.x k) (gradient f (R.x k)) hxmem j
    · exact hvlo.trans (EReal.coe_le_coe_iff.mpr (by linarith))
    · exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans (hxmem j).2
    · rw [abs_neg, abs_of_pos hΔd0]
      nlinarith
  · -- q_j > 0
    obtain ⟨c, hc, hcs⟩ := aux_p42_core P R k (hR.diag k) Δ hΔ j
      (Δ * |(P.B * (R.M k).map (fun a : ℤ => (a : ℝ))) j j|)
      (by rw [abs_of_pos hΔd0])
    refine ⟨c, hc, ?_⟩
    rw [hcs]
    rw [abs_of_pos hpos] at hΔd hA
    have hv : R.x k j < clampCoord (lo j) (hi j) (R.x k j - gradient f (R.x k) j) := by linarith
    have hg := hgt hv
    apply aux_p42_finish lo hi (R.x k) (gradient f (R.x k)) hxmem j
    · exact (hxmem j).1.trans (EReal.coe_le_coe_iff.mpr (by linarith))
    · exact (EReal.coe_le_coe_iff.mpr (by linarith)).trans hvhi
    · rw [abs_of_pos hΔd0]
      nlinarith
