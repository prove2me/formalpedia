-- Prove2me | solution 1 for NonsmoothQN.ExactNorm.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T08:41:56.982997+00:00
-- url     : https://prove2.me/submissions/2cd2529f-4046-4055-88f3-e1d579351483

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

set_option autoImplicit false

open Matrix Filter Topology

namespace NQN841

open NonsmoothQN.ExactNorm

lemma dot2 (u v : Fin 2 → ℝ) : u ⬝ᵥ v = u 0 * v 0 + u 1 * v 1 := by
  simp [dotProduct, Fin.sum_univ_two]

lemma mulVec2 (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    (A *ᵥ v) i = A i 0 * v 0 + A i 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

lemma eucNorm_sq' (x : Fin 2 → ℝ) : eucNorm x ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  unfold eucNorm
  rw [Real.sq_sqrt (by rw [dot2]; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]), dot2]
  ring

lemma eucNorm_nonneg' (x : Fin 2 → ℝ) : 0 ≤ eucNorm x := Real.sqrt_nonneg _

lemma ne_zero_coords {x : Fin 2 → ℝ} (hx : x ≠ 0) : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  funext i
  fin_cases i <;> simp [h.1, h.2]

lemma eucNorm_pos' {x : Fin 2 → ℝ} (hx : x ≠ 0) : 0 < eucNorm x := by
  have h2 : 0 < eucNorm x ^ 2 := by
    rw [eucNorm_sq']
    rcases ne_zero_coords hx with h | h
    · have := lt_of_le_of_ne (sq_nonneg (x 0)) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg (x 1)]
    · have := lt_of_le_of_ne (sq_nonneg (x 1)) (Ne.symm (pow_ne_zero 2 h))
      nlinarith [sq_nonneg (x 0)]
  rcases (eucNorm_nonneg' x).lt_or_eq with h | h
  · exact h
  · rw [← h] at h2; simp at h2

lemma sq_le_of_eucNorm_le {u v : Fin 2 → ℝ} (h : eucNorm u ≤ eucNorm v) :
    u 0 ^ 2 + u 1 ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 := by
  rw [← eucNorm_sq', ← eucNorm_sq']
  exact pow_le_pow_left₀ (eucNorm_nonneg' u) h 2

lemma exact_orth (x p : Fin 2 → ℝ) (t : ℝ)
    (h : ∀ τ : ℝ, eucNorm (x + t • p) ≤ eucNorm (x + τ • p)) :
    (x 0 + t * p 0) * p 0 + (x 1 + t * p 1) * p 1 = 0 := by
  obtain ⟨D, hD⟩ : ∃ D, D = (x 0 + t * p 0) * p 0 + (x 1 + t * p 1) * p 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = p 0 ^ 2 + p 1 ^ 2 := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  obtain ⟨e, he⟩ : ∃ e, e = D / (P + 1) := ⟨_, rfl⟩
  have hDe : D = e * (P + 1) := by rw [he]; field_simp
  have h1 := sq_le_of_eucNorm_le (h (t - e))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
  have key : (x 0 + (t - e) * p 0) ^ 2 + (x 1 + (t - e) * p 1) ^ 2
      - ((x 0 + t * p 0) ^ 2 + (x 1 + t * p 1) ^ 2) = -(e ^ 2 * (P + 2)) := by
    linear_combination (2 * e) * hD - (2 * e) * hDe - e ^ 2 * hP
  have h3 : e ^ 2 * (P + 2) ≤ 0 := by linarith
  have h4 : e ^ 2 ≤ 0 := by nlinarith [sq_nonneg e]
  have h5 : e = 0 := by nlinarith [sq_nonneg e]
  rw [← hD, hDe, h5]; ring

/-- The core planar step: unit vectors `a, b, d` with `d ∥ b - a`, `d · b > 0`, `a · b < 1`. -/
lemma core (a0 a1 b0 b1 d0 d1 : ℝ) (ha : a0 ^ 2 + a1 ^ 2 = 1) (hb : b0 ^ 2 + b1 ^ 2 = 1)
    (hd : d0 ^ 2 + d1 ^ 2 = 1) (hcr : d0 * (b1 - a1) - d1 * (b0 - a0) = 0)
    (hdb : 0 < d0 * b0 + d1 * b1) (hab : a0 * b0 + a1 * b1 < 1) :
    (d0 * b0 + d1 * b1) ^ 2 = (1 - (a0 * b0 + a1 * b1)) / 2 ∧
      ∃ l : ℝ, 0 < l ∧ b0 * d1 - b1 * d0 = l * (a0 * b1 - a1 * b0) := by
  obtain ⟨c, hc⟩ : ∃ c, c = a0 * b0 + a1 * b1 := ⟨_, rfl⟩
  rw [← hc] at hab ⊢
  have hW : (b0 - a0) ^ 2 + (b1 - a1) ^ 2 = 2 - 2 * c := by
    linear_combination ha + hb + 2 * hc
  have hWpos : 0 < (b0 - a0) ^ 2 + (b1 - a1) ^ 2 := by rw [hW]; linarith
  obtain ⟨e, he⟩ : ∃ e, e = d0 * (b0 - a0) + d1 * (b1 - a1) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = e / ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) := ⟨_, rfl⟩
  have hWl : l * ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) = e := by
    rw [hl]; field_simp
  have hd0 : d0 = l * (b0 - a0) := by
    have h1 : ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) * d0 = e * (b0 - a0) := by
      linear_combination (b1 - a1) * hcr - (b0 - a0) * he
    have h2 : ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) * (d0 - l * (b0 - a0)) = 0 := by
      linear_combination h1 - (b0 - a0) * hWl
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith
  have hd1 : d1 = l * (b1 - a1) := by
    have h1 : ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) * d1 = e * (b1 - a1) := by
      linear_combination -(b0 - a0) * hcr - (b1 - a1) * he
    have h2 : ((b0 - a0) ^ 2 + (b1 - a1) ^ 2) * (d1 - l * (b1 - a1)) = 0 := by
      linear_combination h1 - (b1 - a1) * hWl
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · linarith
  have hdb' : d0 * b0 + d1 * b1 = l * (1 - c) := by
    rw [hd0, hd1]; linear_combination l * hb + l * hc
  have hlpos : 0 < l := by
    rw [hdb'] at hdb
    by_contra hneg
    push Not at hneg
    nlinarith
  have hl2 : l ^ 2 * (2 - 2 * c) = 1 := by
    rw [← hW, ← hd, hd0, hd1]; ring
  refine ⟨?_, l, hlpos, ?_⟩
  · rw [hdb']
    linear_combination ((1 - c) / 2) * hl2
  · rw [hd0, hd1]; ring

lemma L_g (v : Fin 2 → ℝ) (i : Fin 2) : gradNorm v i = v i / eucNorm v := by
  simp [gradNorm, div_eq_inv_mul]

lemma unit_g {v : Fin 2 → ℝ} (hv : v ≠ 0) : gradNorm v 0 ^ 2 + gradNorm v 1 ^ 2 = 1 := by
  have hN := eucNorm_pos' hv
  rw [L_g, L_g, div_pow, div_pow, ← add_div, ← eucNorm_sq']
  field_simp

lemma x_eq (v : Fin 2 → ℝ) (hv : v ≠ 0) (i : Fin 2) : v i = eucNorm v * gradNorm v i := by
  rw [L_g]; field_simp [(eucNorm_pos' hv).ne']

lemma L_qn (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    qnDir A v i = -(A i 0 * gradNorm v 0 + A i 1 * gradNorm v 1) := by
  simp only [qnDir, Pi.neg_apply]; rw [mulVec2]

noncomputable def cc (x : ℕ → Fin 2 → ℝ) (k : ℕ) : ℝ :=
  gradNorm (x k) 0 * gradNorm (x (k + 1)) 0 + gradNorm (x k) 1 * gradNorm (x (k + 1)) 1

noncomputable def cr (x : ℕ → Fin 2 → ℝ) (k : ℕ) : ℝ :=
  gradNorm (x k) 0 * gradNorm (x (k + 1)) 1 - gradNorm (x k) 1 * gradNorm (x (k + 1)) 0

section Run

variable {x : ℕ → Fin 2 → ℝ} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ} {t : ℕ → ℝ}

lemma L_next (hrun : IsExactNormRun x H t) (k : ℕ) (i : Fin 2) :
    x (k + 1) i = x k i + t k * qnDir (H k) (x k) i := by
  rw [hrun.next k]; simp

lemma L_orth (hrun : IsExactNormRun x H t) (k : ℕ) :
    x (k + 1) 0 * qnDir (H k) (x k) 0 + x (k + 1) 1 * qnDir (H k) (x k) 1 = 0 := by
  have := exact_orth (x k) (qnDir (H k) (x k)) (t k) (hrun.exact k)
  rw [← L_next hrun k 0, ← L_next hrun k 1] at this
  exact this

lemma L_desc (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) (k : ℕ) :
    qnDir (H k) (x k) 0 * gradNorm (x k) 0 + qnDir (H k) (x k) 1 * gradNorm (x k) 1 < 0 := by
  have hg0 : gradNorm (x k) ≠ 0 := by
    unfold gradNorm
    exact smul_ne_zero (inv_ne_zero (eucNorm_pos' (hnt k)).ne') (hnt k)
  have h := (hrun.posDef k).dotProduct_mulVec_pos hg0
  simp only [star_trivial] at h
  rw [dot2, mulVec2, mulVec2] at h
  rw [L_qn, L_qn]
  nlinarith [h]

lemma L_symm (hrun : IsExactNormRun x H t) (k : ℕ) : H k 0 1 = H k 1 0 := by
  have := (hrun.posDef k).isHermitian.apply 0 1
  simp at this
  linarith

lemma L_sec (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) (k : ℕ) :
    qnDir (H (k + 1)) (x (k + 1)) 0 * (gradNorm (x (k + 1)) 0 - gradNorm (x k) 0) +
      qnDir (H (k + 1)) (x (k + 1)) 1 * (gradNorm (x (k + 1)) 1 - gradNorm (x k) 1) = 0 := by
  have hs := hrun.secant k (hnt (k + 1))
  have hs0 := congrFun hs 0
  have hs1 := congrFun hs 1
  rw [mulVec2] at hs0 hs1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs0 hs1
  have hH := L_symm hrun (k + 1)
  have hGp : gradNorm (x (k + 1)) 0 * qnDir (H k) (x k) 0 +
      gradNorm (x (k + 1)) 1 * qnDir (H k) (x k) 1 = 0 := by
    rw [L_g, L_g, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, L_orth hrun k, zero_div]
  rw [L_qn, L_qn]
  linear_combination (-(gradNorm (x (k + 1)) 0)) * hs0 + (-(gradNorm (x (k + 1)) 1)) * hs1 +
    (gradNorm (x (k + 1)) 0 * (gradNorm (x (k + 1)) 1 - gradNorm (x k) 1) -
      gradNorm (x (k + 1)) 1 * (gradNorm (x (k + 1)) 0 - gradNorm (x k) 0)) * hH - t k * hGp

lemma L_cross (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) (k : ℕ) :
    x (k + 2) 0 * (gradNorm (x (k + 1)) 1 - gradNorm (x k) 1) -
      x (k + 2) 1 * (gradNorm (x (k + 1)) 0 - gradNorm (x k) 0) = 0 := by
  have ho := L_orth hrun (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at ho
  have hs := L_sec hrun hnt k
  have hd := L_desc hrun hnt (k + 1)
  generalize qnDir (H (k + 1)) (x (k + 1)) 0 = p0 at ho hs hd
  generalize qnDir (H (k + 1)) (x (k + 1)) 1 = p1 at ho hs hd
  generalize gradNorm (x (k + 1)) 0 - gradNorm (x k) 0 = y0 at hs ⊢
  generalize gradNorm (x (k + 1)) 1 - gradNorm (x k) 1 = y1 at hs ⊢
  generalize x (k + 2) 0 = u0 at ho ⊢
  generalize x (k + 2) 1 = u1 at ho ⊢
  have e0 : p0 * (u0 * y1 - u1 * y0) = 0 := by linear_combination y1 * ho - u1 * hs
  have e1 : p1 * (u0 * y1 - u1 * y0) = 0 := by linear_combination u0 * hs - y0 * ho
  by_cases h0 : p0 = 0
  · have h1 : p1 ≠ 0 := by
      rintro h1; rw [h0, h1] at hd; simp at hd
    exact (mul_eq_zero.mp e1).resolve_left h1
  · exact (mul_eq_zero.mp e0).resolve_left h0

lemma L_S1 (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) (k : ℕ) :
    eucNorm (x (k + 1)) = cc x k * eucNorm (x k) ∧ 0 < cc x k ∧ cc x k < 1 := by
  have hN := eucNorm_pos' (hnt k)
  have hN' := eucNorm_pos' (hnt (k + 1))
  have hv0 := L_next hrun k 0
  have hv1 := L_next hrun k 1
  have ho := L_orth hrun k
  have hd := L_desc hrun hnt k
  have ht := hrun.step_pos k
  rw [L_g, L_g, mul_div_assoc', mul_div_assoc', ← add_div] at hd
  have hd' : qnDir (H k) (x k) 0 * x k 0 + qnDir (H k) (x k) 1 * x k 1 < 0 := by
    have := mul_neg_of_neg_of_pos hd hN
    rwa [div_mul_cancel₀ _ hN.ne'] at this
  have hvv : x (k + 1) 0 ^ 2 + x (k + 1) 1 ^ 2 = x k 0 * x (k + 1) 0 + x k 1 * x (k + 1) 1 := by
    linear_combination (x (k + 1) 0) * hv0 + (x (k + 1) 1) * hv1 + t k * ho
  have hid : x k 0 * x (k + 1) 0 + x k 1 * x (k + 1) 1 =
      x k 0 ^ 2 + x k 1 ^ 2 + t k * (qnDir (H k) (x k) 0 * x k 0 + qnDir (H k) (x k) 1 * x k 1) := by
    linear_combination (x k 0) * hv0 + (x k 1) * hv1
  have htp := mul_neg_of_pos_of_neg ht hd'
  have e1 : cc x k = (x k 0 * x (k + 1) 0 + x k 1 * x (k + 1) 1) /
      (eucNorm (x k) * eucNorm (x (k + 1))) := by
    unfold cc; simp only [L_g]; ring
  have hsq : eucNorm (x (k + 1)) ^ 2 < eucNorm (x k) ^ 2 := by
    rw [eucNorm_sq', eucNorm_sq']; linarith
  have hlt : eucNorm (x (k + 1)) < eucNorm (x k) := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, ← hvv, ← eucNorm_sq' (x (k + 1)), div_mul_eq_mul_div, eq_div_iff (by positivity)]
    ring
  · rw [e1]
    apply div_pos _ (mul_pos hN hN')
    rw [← hvv, ← eucNorm_sq']; positivity
  · rw [e1, div_lt_one (mul_pos hN hN'), ← hvv, ← eucNorm_sq']
    nlinarith

lemma L_S2 (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) (k : ℕ) :
    cc x (k + 1) ^ 2 = (1 - cc x k) / 2 ∧ ∃ l : ℝ, 0 < l ∧ cr x (k + 1) = l * cr x k := by
  have h1 := L_S1 hrun hnt k
  have h2 := L_S1 hrun hnt (k + 1)
  have hc := L_cross hrun hnt k
  have hcr : gradNorm (x (k + 2)) 0 * (gradNorm (x (k + 1)) 1 - gradNorm (x k) 1) -
      gradNorm (x (k + 2)) 1 * (gradNorm (x (k + 1)) 0 - gradNorm (x k) 0) = 0 := by
    rw [L_g (x (k + 2)) 0, L_g (x (k + 2)) 1, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_div,
      hc, zero_div]
  have hpos2 := h2.2.1
  unfold cc at hpos2
  rw [show k + 1 + 1 = k + 2 by ring] at hpos2
  have hdb : 0 < gradNorm (x (k + 2)) 0 * gradNorm (x (k + 1)) 0 +
      gradNorm (x (k + 2)) 1 * gradNorm (x (k + 1)) 1 := by
    linarith [mul_comm (gradNorm (x (k + 1)) 0) (gradNorm (x (k + 2)) 0),
      mul_comm (gradNorm (x (k + 1)) 1) (gradNorm (x (k + 2)) 1)]
  have hab := h1.2.2
  unfold cc at hab
  obtain ⟨hsq, l, hl, hcrl⟩ := core (gradNorm (x k) 0) (gradNorm (x k) 1)
    (gradNorm (x (k + 1)) 0) (gradNorm (x (k + 1)) 1) (gradNorm (x (k + 2)) 0)
    (gradNorm (x (k + 2)) 1) (unit_g (hnt k)) (unit_g (hnt (k + 1))) (unit_g (hnt (k + 2)))
    hcr hdb hab
  refine ⟨?_, l, hl, ?_⟩
  · unfold cc
    rw [show k + 1 + 1 = k + 2 by ring, ← hsq]
    ring
  · unfold cr
    rw [show k + 1 + 1 = k + 2 by ring]
    linear_combination hcrl

end Run

lemma seq_conv (c : ℕ → ℝ) (hpos : ∀ k, 0 < c k) (hlt : ∀ k, c k < 1)
    (hrec : ∀ k, c (k + 1) ^ 2 = (1 - c k) / 2) : Tendsto c atTop (𝓝 (1 / 2)) := by
  have hup : ∀ k, c (k + 1) < 3 / 4 := by
    intro k; nlinarith [hrec k, hpos k, hpos (k + 1)]
  have hlow : ∀ k, 1 / 4 < c (k + 2) := by
    intro k; nlinarith [hup k, hrec (k + 1), hpos (k + 2)]
  have hcon : ∀ k, |c (k + 3) - 1 / 2| ≤ (2 / 3) * |c (k + 2) - 1 / 2| := by
    intro k
    have e : (c (k + 3) - 1 / 2) * (2 * c (k + 3) + 1) = -(c (k + 2) - 1 / 2) := by
      linear_combination 2 * hrec (k + 2)
    have hl := hlow (k + 1)
    have hpos3 : 0 < 2 * c (k + 3) + 1 := by linarith
    have := congrArg abs e
    rw [abs_mul, abs_neg, abs_of_pos hpos3] at this
    nlinarith [abs_nonneg (c (k + 3) - 1 / 2), abs_nonneg (c (k + 2) - 1 / 2)]
  have hgeo : ∀ n, |c (n + 2) - 1 / 2| ≤ (2 / 3) ^ n * |c 2 - 1 / 2| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hcon n
      calc |c (n + 1 + 2) - 1 / 2| = |c (n + 3) - 1 / 2| := by ring_nf
        _ ≤ (2 / 3) * |c (n + 2) - 1 / 2| := this
        _ ≤ (2 / 3) * ((2 / 3) ^ n * |c 2 - 1 / 2|) := by gcongr
        _ = (2 / 3) ^ (n + 1) * |c 2 - 1 / 2| := by ring
  rw [← Filter.tendsto_add_atTop_iff_nat 2, tendsto_iff_norm_sub_tendsto_zero]
  have hz : Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n * |c 2 - 1 / 2|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (2 / 3 : ℝ) < 1)).mul_const
      (|c 2 - 1 / 2|)
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hgeo n) hz

lemma norm_conv (N c : ℕ → ℝ) (hN : ∀ k, 0 < N k) (hrel : ∀ k, N (k + 1) = c k * N k)
    (hc : ∀ k, 0 < c k) (hup : ∀ k, c (k + 1) < 3 / 4) : Tendsto N atTop (𝓝 0) := by
  have hgeo : ∀ n, N (n + 1) ≤ (3 / 4) ^ n * N 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hrel (n + 1)
      have h2 := hup n
      have h3 := hN (n + 1)
      calc N (n + 1 + 1) = c (n + 1) * N (n + 1) := h1
        _ ≤ (3 / 4) * N (n + 1) := by nlinarith
        _ ≤ (3 / 4) * ((3 / 4) ^ n * N 1) := by gcongr
        _ = (3 / 4) ^ (n + 1) * N 1 := by ring
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  have hz : Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ n * N 1) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (3 / 4 : ℝ) < 1)).mul_const
      (N 1)
  exact squeeze_zero (fun n => (hN _).le) hgeo hz

end NQN841

open Matrix Filter Topology NonsmoothQN.ExactNorm in
theorem solution (x : ℕ → Fin 2 → ℝ) (H : ℕ → Matrix (Fin 2) (Fin 2) ℝ) (t : ℕ → ℝ)
    (hrun : IsExactNormRun x H t) (hnt : ∀ k, x k ≠ 0) :
    IsQLinear (fun k => eucNorm (x k)) 0 (1 / 2) ∧
      Tendsto (fun k => turnAngle (x k) (x (k + 1))) atTop (𝓝 (Real.pi / 3)) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ᶠ k in atTop, 0 < σ * cross (x k) (x (k + 1)) := by
  have S1 := NQN841.L_S1 hrun hnt
  have S2 := NQN841.L_S2 hrun hnt
  have hpos : ∀ k, 0 < NQN841.cc x k := fun k => (S1 k).2.1
  have hlt : ∀ k, NQN841.cc x k < 1 := fun k => (S1 k).2.2
  have hrec : ∀ k, NQN841.cc x (k + 1) ^ 2 = (1 - NQN841.cc x k) / 2 := fun k => (S2 k).1
  have hcc : Tendsto (NQN841.cc x) atTop (𝓝 (1 / 2)) := NQN841.seq_conv _ hpos hlt hrec
  have hup : ∀ k, NQN841.cc x (k + 1) < 3 / 4 := fun k => by nlinarith [hrec k, hpos k, hpos (k + 1)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact NQN841.norm_conv (fun k => eucNorm (x k)) (NQN841.cc x) (fun k => NQN841.eucNorm_pos' (hnt k))
      (fun k => (S1 k).1) hpos hup
  · show Tendsto (fun k => |eucNorm (x (k + 1)) - 0| / |eucNorm (x k) - 0|) atTop (𝓝 (1 / 2))
    have e : (fun k => |eucNorm (x (k + 1)) - 0| / |eucNorm (x k) - 0|) = NQN841.cc x := by
      funext k
      rw [sub_zero, sub_zero, abs_of_pos (NQN841.eucNorm_pos' (hnt _)), abs_of_pos (NQN841.eucNorm_pos' (hnt _)),
        (S1 k).1]
      field_simp [(NQN841.eucNorm_pos' (hnt k)).ne']
    rw [e]; exact hcc
  · have hta : (fun k => turnAngle (x k) (x (k + 1))) = fun k => Real.arccos (NQN841.cc x k) := by
      funext k
      unfold turnAngle
      congr 1
      rw [NQN841.dot2]; unfold NQN841.cc; simp only [NQN841.L_g]; ring
    rw [hta]
    have h3 : Real.arccos (1 / 2) = Real.pi / 3 := by
      rw [show (1 / 2 : ℝ) = Real.cos (Real.pi / 3) by rw [Real.cos_pi_div_three]]
      exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
    rw [← h3]
    exact (Real.continuous_arccos.tendsto _).comp hcc
  · have hcr0 : NQN841.cr x 0 ≠ 0 := by
      intro h0
      have hu0 := NQN841.unit_g (hnt 0)
      have hu1 := NQN841.unit_g (hnt (0 + 1))
      have lag : NQN841.cc x 0 ^ 2 + NQN841.cr x 0 ^ 2 = 1 := by
        unfold NQN841.cc NQN841.cr
        linear_combination (gradNorm (x (0 + 1)) 0 ^ 2 + gradNorm (x (0 + 1)) 1 ^ 2) * hu0 + hu1
      rw [h0] at lag
      have := hpos 0
      have := hlt 0
      nlinarith
    obtain ⟨σ, hσ, hσpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < σ * NQN841.cr x 0 := by
      rcases lt_or_gt_of_ne hcr0 with h | h
      · exact ⟨-1, Or.inr rfl, by linarith⟩
      · exact ⟨1, Or.inl rfl, by linarith⟩
    have hall : ∀ k, 0 < σ * NQN841.cr x k := by
      intro k
      induction k with
      | zero => exact hσpos
      | succ n ih =>
        obtain ⟨l, hl, he⟩ := (S2 n).2
        rw [he, show σ * (l * NQN841.cr x n) = l * (σ * NQN841.cr x n) by ring]
        exact mul_pos hl ih
    refine ⟨σ, hσ, Filter.Eventually.of_forall fun k => ?_⟩
    have hxk : cross (x k) (x (k + 1)) = eucNorm (x k) * eucNorm (x (k + 1)) * NQN841.cr x k := by
      unfold cross NQN841.cr
      rw [NQN841.x_eq (x k) (hnt k) 0, NQN841.x_eq (x k) (hnt k) 1, NQN841.x_eq (x (k + 1)) (hnt (k + 1)) 0,
        NQN841.x_eq (x (k + 1)) (hnt (k + 1)) 1]
      ring
    rw [hxk, show σ * (eucNorm (x k) * eucNorm (x (k + 1)) * NQN841.cr x k) =
      (eucNorm (x k) * eucNorm (x (k + 1))) * (σ * NQN841.cr x k) by ring]
    exact mul_pos (mul_pos (NQN841.eucNorm_pos' (hnt k)) (NQN841.eucNorm_pos' (hnt (k + 1)))) (hall k)
