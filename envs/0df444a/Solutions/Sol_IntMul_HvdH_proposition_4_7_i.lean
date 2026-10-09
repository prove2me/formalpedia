-- Prove2me | solution 1 for IntMul.HvdH.proposition_4_7_i
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T11:45:49.148193+00:00
-- url     : https://prove2.me/submissions/5715d524-2ecf-4dfe-b934-b4a848035eed

import Definitions.Def_IntMul_HvdH_Resampling
import Theorems.Thm_IntMul_HvdH_theorem_4_2
import Theorems.Thm_IntMul_HvdH_lemma_4_5
import Theorems.Thm_IntMul_HvdH_lemma_4_6
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open IntMul.HvdH
open scoped BigOperators

private noncomputable def pull (s t : ℕ) [NeZero s] [NeZero t]
    (f : ZMod t → ZMod s) : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ f)

private lemma pull_apply (s t : ℕ) [NeZero s] [NeZero t]
    (f : ZMod t → ZMod s) (u : ZMod s → ℂ) (j : ZMod t) :
    pull s t f u j = u (f j) := rfl

private lemma pull_norm (s t : ℕ) [NeZero s] [NeZero t] (f : ZMod t → ZMod s) :
    ‖pull s t f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro j
  exact norm_le_pi_norm u (f j)

private lemma rowDel_apply (s t : ℕ) [NeZero s] [NeZero t]
    (u : ZMod t → ℂ) (j : ZMod s) :
    rowDel s t u j = u ((nearest ((t : ℝ) * j.val / s) : ℤ) : ZMod t) := by
  classical
  simp [rowDel, toCLM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

private lemma rowDel_norm (s t : ℕ) [NeZero s] [NeZero t] : ‖rowDel s t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro j
  rw [rowDel_apply]
  exact norm_le_pi_norm u _

private lemma diagD_apply (s t : ℕ) [NeZero s] (a : ℝ)
    (u : ZMod s → ℂ) (j : ZMod s) :
    diagD s t a u j = (Real.exp (Real.pi * a ^ 2 * beta s t j.val ^ 2) : ℂ) * u j := by
  classical
  simp [diagD, toCLM, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

private lemma beta_sq_le (s t : ℕ) (j : ℤ) : beta s t j ^ 2 ≤ (1 / 4 : ℝ) := by
  let x : ℝ := (t : ℝ) * j / s
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  have hlo : -(1 / 2 : ℝ) ≤ beta s t j := by dsimp [beta, nearest, x] at *; linarith
  have hhi : beta s t j ≤ (1 / 2 : ℝ) := by dsimp [beta, nearest, x] at *; linarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ beta s t j + 1 / 2)
    (by linarith : 0 ≤ 1 / 2 - beta s t j)]

private lemma diagD_norm (s t : ℕ) [NeZero s] (a : ℝ) :
    ‖diagD s t a‖ ≤ Real.exp (Real.pi * a ^ 2 / 4) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro u
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg u))).mpr
  intro j
  rw [diagD_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (beta_sq_le s t (j.val : ℤ))
      (mul_nonneg Real.pi_pos.le (sq_nonneg a))
    nlinarith
  · exact norm_le_pi_norm u j
  · exact norm_nonneg _
  · exact (Real.exp_pos _).le

private lemma diagD_surjective (s t : ℕ) [NeZero s] (a : ℝ) :
    Function.Surjective (diagD s t a) := by
  intro u
  refine ⟨fun j => (Real.exp (Real.pi * a ^ 2 * beta s t j.val ^ 2) : ℂ)⁻¹ * u j, ?_⟩
  funext j
  rw [diagD_apply, ← mul_assoc, mul_inv_cancel₀, one_mul]
  apply Complex.ofReal_ne_zero.mpr
  exact Real.exp_ne_zero _

-- A uniform diagonal bound leaves enough room for both factors of 2.
private lemma diagonal_scale_bound (a : ℕ) (ha : 2 ≤ a) :
    4 * Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) ≤ (2 : ℝ) ^ (2 * a ^ 2) := by
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha2 : 4 ≤ (a : ℝ) ^ 2 := by nlinarith
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_nonneg (by nlinarith : 0 ≤ 2 * (a : ℝ) ^ 2 - 2)
    (sub_nonneg.mpr hlog)
  have hpi := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (sq_nonneg (a : ℝ))
  have he : 2 * Real.log 2 + Real.pi * (a : ℝ) ^ 2 / 4 ≤
      (2 * (a : ℝ) ^ 2) * Real.log 2 := by nlinarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_mul (x := (2 : ℝ)) (y := 2) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  calc
    4 * Real.exp (Real.pi * (a : ℝ) ^ 2 / 4) =
        Real.exp (2 * Real.log 2 + Real.pi * (a : ℝ) ^ 2 / 4) := by
      rw [← h4, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ Real.exp ((2 * (a : ℝ) ^ 2) * Real.log 2) := Real.exp_le_exp.mpr he
    _ = (2 : ℝ) ^ (2 * a ^ 2) := by
      have hpow : (2 : ℝ) ^ (2 * a ^ 2) =
          Real.exp (Real.log 2 * ((2 * a ^ 2 : ℕ) : ℝ)) := by
        calc
          (2 : ℝ) ^ (2 * a ^ 2) = (2 : ℝ) ^ ((2 * a ^ 2 : ℕ) : ℝ) :=
            (Real.rpow_natCast 2 (2 * a ^ 2)).symm
          _ = _ := Real.rpow_def_of_pos (by norm_num) _
      rw [hpow]
      congr 1
      push_cast
      ring

private lemma near_identity_inverse (s : ℕ) [NeZero s]
    (N : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hN : ‖N - 1‖ < (1 / 2 : ℝ)) :
    ∃ J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ),
      ‖J‖ ≤ 2 ∧ ∀ u, J (N u) = u := by
  let E := N - 1
  have hE : ‖-E‖ < 1 := by simpa only [norm_neg] using (lt_trans hN (by norm_num : (1 / 2 : ℝ) < 1))
  let J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) := ∑' k : ℕ, (-E) ^ k
  have hinv : J * N = 1 := by
    have h := geom_series_mul_neg (-E) hE
    have hNN : 1 - -E = N := by dsimp [E]; abel
    rw [hNN] at h
    exact h
  refine ⟨J, ?_, ?_⟩
  · have h := tsum_geometric_le_of_norm_lt_one (-E) hE
    have hden : 0 < 1 - ‖E‖ := by dsimp [E]; linarith
    have hprod := mul_inv_cancel₀ hden.ne'
    have hmul : 0 ≤ (1 - ‖E‖ - 1 / 2) * (1 - ‖E‖)⁻¹ :=
      mul_nonneg (by dsimp [E]; linarith) (inv_nonneg.mpr hden.le)
    have hi : (1 - ‖E‖)⁻¹ ≤ 2 := by nlinarith
    have hJ : ‖J‖ ≤ (1 - ‖E‖)⁻¹ := by simpa only [norm_one, norm_neg, sub_self, zero_add] using h
    exact hJ.trans hi
  · intro u
    have h := congrArg (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) => f u) hinv
    change J (N u) = u at h
    exact h

private lemma comp_norm_le (s t r : ℕ) [NeZero s] [NeZero t] [NeZero r]
    (f : (ZMod t → ℂ) →L[ℂ] (ZMod r → ℂ))
    (g : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ)) (F G : ℝ)
    (hF : 0 ≤ F) (hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ G) :
    ‖f.comp g‖ ≤ F * G :=
  (f.opNorm_comp_le g).trans (mul_le_mul hf hg (norm_nonneg g) hF)

theorem solution (p s t : ℕ) [NeZero s] [NeZero t] (hp : 100 ≤ p) (hs : 2 ≤ s)
    (hst : s < t) (htp : t < 2 ^ p) (hcop : Nat.Coprime s t) (α : ℕ) (hα : 2 ≤ α)
    (hαp : (α : ℝ) < Real.sqrt p) (hθ : (p : ℝ) / α ^ 4 ≤ theta s t) :
    ∃ A : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ), ∃ B : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ),
      ‖A‖ ≤ 1 ∧ ‖B‖ ≤ 1 ∧ dft s = ((2 : ℂ) ^ (2 * α ^ 2)) •
        (B.comp ((dft t).comp A)) := by
  have ha2 : (2 : ℝ) ≤ α := by exact_mod_cast hα
  have ha : (0 : ℝ) < α := by linarith
  have hasq : (α : ℝ) ^ 2 < p := (Real.lt_sqrt ha.le).mp hαp
  have hlarge : (p : ℝ) ≤ (α : ℝ) ^ 4 * theta s t := by
    have h := (div_le_iff₀ (pow_pos ha 4)).mp hθ
    nlinarith
  have htheta : 1 ≤ (α : ℝ) ^ 2 * theta s t := by
    by_contra h
    have hh : (α : ℝ) ^ 2 * theta s t < 1 := lt_of_not_ge h
    have hm := mul_lt_mul_of_pos_left hh (pow_pos ha 2)
    nlinarith [sq_nonneg ((α : ℝ) ^ 2)]
  obtain ⟨hE, hE'⟩ := lemma_4_6 s t hst hcop (α : ℝ) ha htheta
  have hrpow : (2 : ℝ) ^ (-((α : ℝ) ^ 2 * theta s t)) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by norm_num [Real.rpow_neg, Real.rpow_one]
  have hN : ‖normN s t (α : ℝ) - 1‖ < (1 / 2 : ℝ) := by
    exact (show ‖errE s t (α : ℝ)‖ < (1 / 2 : ℝ) from
      (hE.trans hE').trans_le hrpow)
  obtain ⟨J, hJn, hJ⟩ := near_identity_inverse s (normN s t (α : ℝ)) hN
  have hLT (u : ZMod s → ℂ) :
      diagD s t (α : ℝ) (J (rowDel s t (resT s t (α : ℝ) u))) = u := by
    obtain ⟨v, hv⟩ := diagD_surjective s t (α : ℝ) u
    rw [← hv]
    exact congrArg (diagD s t (α : ℝ)) (hJ v)
  let P := pull s s (fun j : ZMod s => (t : ZMod s)⁻¹ * j)
  have hPn : ‖P‖ ≤ 1 := pull_norm s s _
  have hP (u : ZMod s → ℂ) : P (permS s t u) = u := by
    funext j
    change u ((t : ZMod s) * ((t : ZMod s)⁻¹ * j)) = u j
    rw [← mul_assoc, ZMod.coe_mul_inv_eq_one t hcop.symm, one_mul]
  have hPtn : ‖permT s t‖ ≤ 1 := pull_norm t t _
  let Q := P.comp ((diagD s t (α : ℝ)).comp
    (J.comp ((rowDel s t).comp (permT s t))))
  have hQ : Q.comp ((dft t).comp (resS s t (α : ℝ))) = dft s := by
    apply ContinuousLinearMap.ext
    intro u
    have hid := congrArg
      (fun f : (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) => f u)
      (theorem_4_2 s t hst hcop (α : ℝ) ha)
    change resT s t (α : ℝ) (permS s t (dft s u)) =
      permT s t (dft t (resS s t (α : ℝ) u)) at hid
    change P (diagD s t (α : ℝ) (J
      (rowDel s t (permT s t (dft t (resS s t (α : ℝ) u)))))) = dft s u
    rw [← hid, hLT, hP]
  have hQn : ‖Q‖ ≤ 2 * Real.exp (Real.pi * (α : ℝ) ^ 2 / 4) := by
    have hC := comp_norm_le t t s (rowDel s t) (permT s t) 1 1
      zero_le_one (rowDel_norm s t) hPtn
    have hJC := comp_norm_le t s s J ((rowDel s t).comp (permT s t)) 2 (1 * 1)
      (by norm_num) hJn hC
    have hDJC := comp_norm_le t s s (diagD s t (α : ℝ))
      (J.comp ((rowDel s t).comp (permT s t)))
      (Real.exp (Real.pi * (α : ℝ) ^ 2 / 4)) (2 * (1 * 1))
      (Real.exp_pos _).le (diagD_norm s t (α : ℝ)) hJC
    have hPQ := comp_norm_le t s s P
      ((diagD s t (α : ℝ)).comp (J.comp ((rowDel s t).comp (permT s t))))
      1 (Real.exp (Real.pi * (α : ℝ) ^ 2 / 4) * (2 * (1 * 1)))
      zero_le_one hPn hDJC
    simpa only [one_mul, mul_one, mul_comm] using hPQ
  have hSn : ‖resS s t (α : ℝ)‖ ≤ 2 := by
    have hS := lemma_4_5 s t hst hcop (α : ℝ) ha
    have hprod := mul_inv_cancel₀ ha.ne'
    have hm := mul_nonneg (by linarith : 0 ≤ (α : ℝ) - 1)
      (inv_nonneg.mpr ha.le)
    have hi : (α : ℝ)⁻¹ ≤ 1 := by nlinarith
    linarith
  let c : ℝ := (2 : ℝ) ^ (2 * α ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbudget : 2 * ‖Q‖ ≤ c := by
    have hb := diagonal_scale_bound α hα
    dsimp [c]
    linarith
  let A := (1 / 2 : ℂ) • resS s t (α : ℝ)
  let B := ((2 / c : ℝ) : ℂ) • Q
  refine ⟨A, B, ?_, ?_, ?_⟩
  · change ‖(1 / 2 : ℂ) • resS s t (α : ℝ)‖ ≤ 1
    rw [norm_smul]
    norm_num
    linarith
  · change ‖((2 / c : ℝ) : ℂ) • Q‖ ≤ 1
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (by norm_num) hc)]
    have hfrac : (2 / c) * ‖Q‖ = (2 * ‖Q‖) / c := by ring
    rw [hfrac]
    exact (div_le_iff₀ hc).mpr (by simpa using hbudget)
  · have hcast : (2 : ℂ) ^ (2 * α ^ 2) = (c : ℂ) := by
      dsimp [c]
      push_cast
      rfl
    have hscalar : (2 : ℂ) ^ (2 * α ^ 2) *
        (((2 / c : ℝ) : ℂ) * (1 / 2 : ℂ)) = 1 := by
      rw [hcast]
      push_cast
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      field_simp
    change dft s = ((2 : ℂ) ^ (2 * α ^ 2)) •
      ((((2 / c : ℝ) : ℂ) • Q).comp
        ((dft t).comp ((1 / 2 : ℂ) • resS s t (α : ℝ))))
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, smul_smul, smul_smul, mul_assoc,
      hscalar, one_smul, hQ]
