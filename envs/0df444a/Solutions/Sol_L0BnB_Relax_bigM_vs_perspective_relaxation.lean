-- Prove2me | solution 1 for L0BnB.Relax.bigM_vs_perspective_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T01:09:40.335194+00:00
-- url     : https://prove2.me/submissions/b7fd55a4-a2f2-47a5-9e11-6704c5ed86b5

import Mathlib
import Definitions.Def_L0BnB_Relax_VB
import Definitions.Def_L0BnB_Relax_VPRinf
import Definitions.Def_L0BnB_Relax_Lset

set_option autoImplicit false

namespace L0BnB.Relax.A5709

/-- Coordinate step for (10): a Big-M feasible coordinate `(b, z)` with `M ≤ c/2` yields the
perspective-feasible coordinate `(b, |b|/c, c|b|)` whose penalty is at most `lam0 * z`. -/
lemma coord10 (lam2 c M b z : ℝ) (h2 : 0 < lam2) (hc : 0 < c) (hM : M ≤ c / 2)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hb1 : -(M * z) ≤ b) (hb2 : b ≤ M * z) :
    0 ≤ |b| / c ∧ |b| / c ≤ 1 ∧ 0 ≤ c * |b| ∧ b ^ 2 ≤ (c * |b|) * (|b| / c) ∧
      (lam2 * c ^ 2) * (|b| / c) + lam2 * (c * |b|) ≤ (lam2 * c ^ 2) * z := by
  have hbz : |b| ≤ M * z := abs_le.mpr ⟨by linarith, hb2⟩
  have hMz : M * z ≤ c / 2 * z := mul_le_mul_of_nonneg_right hM hz0
  have hab : 0 ≤ |b| := abs_nonneg b
  have hbc : 2 * |b| ≤ c * z := by linarith
  have hbc1 : |b| ≤ c := by nlinarith
  have hcne : c ≠ 0 := ne_of_gt hc
  refine ⟨div_nonneg hab hc.le, (div_le_one hc).mpr hbc1, mul_nonneg hc.le hab, ?_, ?_⟩
  · have : (c * |b|) * (|b| / c) = |b| ^ 2 := by field_simp
    rw [this, sq_abs]
  · have e : (lam2 * c ^ 2) * (|b| / c) = lam2 * c * |b| := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hbc (mul_nonneg h2.le hc.le)
    nlinarith

/-- Coordinate step for (11): a perspective-feasible coordinate `(b, zs, ss)` with `|b| ≤ M` and
`c ≤ M` yields a Big-M feasible `z` with penalty at most the perspective penalty. -/
lemma coord11 (lam2 c M b zs ss : ℝ) (h2 : 0 < lam2) (hc : 0 < c) (hcM : c ≤ M)
    (hbM : |b| ≤ M) (hz0 : 0 ≤ zs) (hz1 : zs ≤ 1) (hs0 : 0 ≤ ss) (hbs : b ^ 2 ≤ ss * zs) :
    ∃ z : ℝ, (0 ≤ z ∧ z ≤ 1 ∧ -(M * z) ≤ b ∧ b ≤ M * z) ∧
      (lam2 * c ^ 2) * z + lam2 * b ^ 2 ≤ (lam2 * c ^ 2) * zs + lam2 * ss := by
  have hMpos : 0 < M := lt_of_lt_of_le hc hcM
  have hab : 0 ≤ |b| := abs_nonneg b
  have hb2 : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
  by_cases hbc : |b| ≤ c
  · refine ⟨|b| / M, ⟨div_nonneg hab hMpos.le, (div_le_one hMpos).mpr hbM, ?_, ?_⟩, ?_⟩
    · have : M * (|b| / M) = |b| := by field_simp
      rw [this]; exact neg_abs_le b
    · have : M * (|b| / M) = |b| := by field_simp
      rw [this]; exact le_abs_self b
    · -- LHS ≤ 2 lam2 c |b| ≤ RHS
      have e1 : (lam2 * c ^ 2) * (|b| / M) ≤ lam2 * c * |b| := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hMpos]
        have := mul_le_mul_of_nonneg_left hcM (mul_nonneg (mul_nonneg h2.le hc.le) hab)
        nlinarith
      have e2 : lam2 * b ^ 2 ≤ lam2 * c * |b| := by
        rw [hb2]
        have := mul_le_mul_of_nonneg_left hbc (mul_nonneg h2.le hab)
        nlinarith
      set q := (lam2 * c ^ 2) * zs + lam2 * ss with hq
      have hq0 : 0 ≤ q := by positivity
      have hA : 0 ≤ 2 * (lam2 * c * |b|) := by positivity
      have hsq : (2 * (lam2 * c * |b|)) ^ 2 ≤ q ^ 2 := by
        have h4 : q ^ 2 - 4 * (lam2 * c ^ 2) * lam2 * (zs * ss)
            = ((lam2 * c ^ 2) * zs - lam2 * ss) ^ 2 := by rw [hq]; ring
        have h5 : 0 ≤ ((lam2 * c ^ 2) * zs - lam2 * ss) ^ 2 := sq_nonneg _
        have h6 : |b| ^ 2 ≤ zs * ss := by rw [← hb2]; linarith [mul_comm ss zs]
        have h7 : 0 ≤ 4 * (lam2 * c ^ 2) * lam2 := by positivity
        have h8 := mul_le_mul_of_nonneg_left h6 h7
        have h9 : (2 * (lam2 * c * |b|)) ^ 2 = 4 * (lam2 * c ^ 2) * lam2 * |b| ^ 2 := by ring
        rw [h9]; linarith
      have hfin : 2 * (lam2 * c * |b|) ≤ q := by nlinarith
      linarith
  · push_neg at hbc
    have hb1 : -M ≤ b ∧ b ≤ M := abs_le.mp hbM
    refine ⟨1, ⟨zero_le_one, le_rfl, by linarith, by linarith⟩, ?_⟩
    have hcb : c ^ 2 ≤ b ^ 2 := by rw [hb2]; nlinarith
    have hpos : 0 < b ^ 2 := by nlinarith
    have hzs : 0 < zs := by
      rcases lt_or_eq_of_le hz0 with h | h
      · exact h
      · rw [← h] at hbs; linarith
    have hK : 0 ≤ lam2 * b ^ 2 - lam2 * c ^ 2 := by nlinarith
    have m1 : 0 ≤ (1 - zs) * (lam2 * b ^ 2 - lam2 * c ^ 2) := mul_nonneg (by linarith) hK
    have m2 : 0 ≤ lam2 * (ss * zs - b ^ 2) := mul_nonneg h2.le (by linarith)
    have m3 : 0 ≤ (lam2 * c ^ 2) * (zs - 1) ^ 2 := by positivity
    have key : 0 ≤ zs * ((lam2 * c ^ 2) * zs + lam2 * ss - ((lam2 * c ^ 2) * 1 + lam2 * b ^ 2)) := by
      nlinarith
    have : 0 ≤ (lam2 * c ^ 2) * zs + lam2 * ss - ((lam2 * c ^ 2) * 1 + lam2 * b ^ 2) := by
      by_contra hneg
      push_neg at hneg
      have := mul_neg_of_pos_of_neg hzs hneg
      linarith
    linarith

lemma rss_nonneg' {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (β : Fin p → ℝ) :
    0 ≤ rss X y β := by
  unfold rss; positivity

lemma prObj_nonneg' {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 : ℝ)
    (h0 : 0 < lam0) (h2 : 0 < lam2) (β z s : Fin p → ℝ) (hf : prFeasible β z s) :
    0 ≤ prObj X y lam0 lam2 β z s := by
  unfold prObj
  have a := rss_nonneg' X y β
  have b : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => (hf i).1)
  have c : 0 ≤ ∑ i, s i := Finset.sum_nonneg (fun i _ => (hf i).2.2.1)
  have := mul_nonneg h0.le b
  have := mul_nonneg h2.le c
  linarith

lemma bigMObj_nonneg' {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (lam0 lam2 M : ℝ)
    (h0 : 0 < lam0) (h2 : 0 < lam2) (β z : Fin p → ℝ) (hf : bigMFeasible M β z) :
    0 ≤ bigMObj X y lam0 lam2 β z := by
  unfold bigMObj
  have a := rss_nonneg' X y β
  have b : 0 ≤ ∑ i, z i := Finset.sum_nonneg (fun i _ => (hf i).1)
  have c : 0 ≤ ∑ i, β i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have := mul_nonneg h0.le b
  have := mul_nonneg h2.le c
  linarith

theorem main {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 ≤ M) :
    (M ≤ 1 / 2 * Real.sqrt (lam0 / lam2) → VPRinf X y lam0 lam2 ≤ VB X y lam0 lam2 M) ∧
    (Real.sqrt (lam0 / lam2) ≤ M → lam2 ∈ Lset X y lam0 M →
      VB X y lam0 lam2 M ≤ VPRinf X y lam0 lam2) := by
  set c := Real.sqrt (lam0 / lam2) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (div_pos h0 h2)
  have hlam0 : lam0 = lam2 * c ^ 2 := by
    rw [hcdef, Real.sq_sqrt (div_pos h0 h2).le]; field_simp
  have bddP : BddBelow {v | ∃ β z s : Fin p → ℝ, prFeasible β z s ∧
      prObj X y lam0 lam2 β z s = v} := by
    refine ⟨0, ?_⟩
    rintro w ⟨β, z, s, hf, rfl⟩
    exact prObj_nonneg' X y lam0 lam2 h0 h2 β z s hf
  have bddB : BddBelow {v | ∃ β z : Fin p → ℝ, bigMFeasible M β z ∧
      bigMObj X y lam0 lam2 β z = v} := by
    refine ⟨0, ?_⟩
    rintro w ⟨β, z, hf, rfl⟩
    exact bigMObj_nonneg' X y lam0 lam2 M h0 h2 β z hf
  refine ⟨?_, ?_⟩
  · intro hMc
    have hMc' : M ≤ c / 2 := by linarith
    unfold VPRinf VB
    apply le_csInf
    · refine ⟨_, 0, 0, fun i => ?_, rfl⟩
      simp
    · rintro v ⟨β, z, hf, rfl⟩
      have co := fun i => coord10 lam2 c M (β i) (z i) h2 hc hMc' (hf i).1 (hf i).2.1
        (hf i).2.2.1 (hf i).2.2.2
      refine le_trans (csInf_le bddP ⟨β, fun i => |β i| / c, fun i => c * |β i|,
        fun i => ⟨(co i).1, (co i).2.1, (co i).2.2.1, (co i).2.2.2.1⟩, rfl⟩) ?_
      unfold prObj bigMObj
      have hs : lam0 * ∑ i, |β i| / c + lam2 * ∑ i, c * |β i| ≤ lam0 * ∑ i, z i := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [hlam0]; exact (co i).2.2.2.2
      have hq : 0 ≤ lam2 * ∑ i, β i ^ 2 :=
        mul_nonneg h2.le (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      linarith
  · intro hcM hL
    simp only [Lset, solSet, Set.mem_setOf_eq] at hL
    obtain ⟨_, β, ⟨zs, ss, hfeas, hopt⟩, hbM⟩ := hL
    unfold VB VPRinf
    apply le_csInf
    · refine ⟨_, 0, 0, 0, fun i => ?_, rfl⟩
      simp
    · rintro w ⟨β', z', s', hf', rfl⟩
      refine le_trans ?_ (hopt β' z' s' hf')
      have co : ∀ i, ∃ z : ℝ, (0 ≤ z ∧ z ≤ 1 ∧ -(M * z) ≤ β i ∧ β i ≤ M * z) ∧
          (lam2 * c ^ 2) * z + lam2 * β i ^ 2 ≤ (lam2 * c ^ 2) * zs i + lam2 * ss i :=
        fun i => coord11 lam2 c M (β i) (zs i) (ss i) h2 hc hcM (hbM i) (hfeas i).1
          (hfeas i).2.1 (hfeas i).2.2.1 (hfeas i).2.2.2
      choose zf hzf using co
      refine le_trans (csInf_le bddB ⟨β, zf, fun i => (hzf i).1, rfl⟩) ?_
      unfold prObj bigMObj
      have hs : lam0 * ∑ i, zf i + lam2 * ∑ i, β i ^ 2 ≤
          lam0 * ∑ i, zs i + lam2 * ∑ i, ss i := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [hlam0]; exact (hzf i).2
      linarith

end L0BnB.Relax.A5709

open L0BnB.Relax in
theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ)
    (y : Fin n → ℝ) (lam0 lam2 M : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 ≤ M) :
    (M ≤ 1 / 2 * Real.sqrt (lam0 / lam2) → VPRinf X y lam0 lam2 ≤ VB X y lam0 lam2 M) ∧
    (Real.sqrt (lam0 / lam2) ≤ M → lam2 ∈ Lset X y lam0 M →
      VB X y lam0 lam2 M ≤ VPRinf X y lam0 lam2) := by
  exact L0BnB.Relax.A5709.main X y lam0 lam2 M h0 h2 hM
