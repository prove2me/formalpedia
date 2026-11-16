-- Prove2me | solution 1 for IAFTRL.lemma_C_10
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T10:27:03.443559+00:00
-- url     : https://prove2.me/submissions/ca30a305-dfb5-435e-b857-4b47448f1a8d

import Mathlib
import Definitions.Def_IAFTRL_cR
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_actionNorm
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_IsFeasibleAlloc
import Definitions.Def_IAFTRL_allocMass
import Definitions.Def_IAFTRL_IsFeasible2_3
import Definitions.Def_IAFTRL_chi
import Theorems.Thm_IAFTRL_lemma_J_4

open Matrix IAFTRL

namespace C3A

lemma gram_bil {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) (β v : Fin r → ℝ) :
    ((∑ c, n c • vecMulVec (X c) (X c)) *ᵥ β) ⬝ᵥ v = ∑ c, n c * (X c ⬝ᵥ β) * (X c ⬝ᵥ v) := by
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, sum_dotProduct,
    smul_dotProduct, smul_eq_mul, op_smul_eq_smul]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma gram_qf {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) (v : Fin r → ℝ) :
    v ⬝ᵥ ((∑ c, n c • vecMulVec (X c) (X c)) *ᵥ v) = ∑ c, n c * (X c ⬝ᵥ v) ^ 2 := by
  rw [dotProduct_comm, gram_bil]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma gram_herm {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) :
    (∑ c, n c • vecMulVec (X c) (X c)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

/-- Cauchy–Schwarz for a positive definite matrix. -/
lemma cs_pd {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosDef) (a w : Fin r → ℝ) :
    (a ⬝ᵥ w) ^ 2 ≤ (a ⬝ᵥ H⁻¹ *ᵥ a) * (w ⬝ᵥ H *ᵥ w) := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  have hT : Hᵀ = H := by
    have := hH.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set v := H⁻¹ *ᵥ a with hv
  have hHv : H *ᵥ v = a := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  -- symmetry of the bilinear form
  have hsym : ∀ x y : Fin r → ℝ, x ⬝ᵥ H *ᵥ y = y ⬝ᵥ H *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have haw : a ⬝ᵥ w = v ⬝ᵥ H *ᵥ w := by rw [← hHv, hsym, dotProduct_comm]
  have hav : a ⬝ᵥ v = v ⬝ᵥ H *ᵥ v := by rw [hHv, dotProduct_comm]
  rw [haw, hav]
  by_cases hw : w = 0
  · subst hw; simp
  have hww : 0 < w ⬝ᵥ H *ᵥ w := by
    have := hH.dotProduct_mulVec_pos hw
    rwa [star_trivial] at this
  set t := (v ⬝ᵥ H *ᵥ w) / (w ⬝ᵥ H *ᵥ w)
  have hpsd : 0 ≤ (v - t • w) ⬝ᵥ H *ᵥ (v - t • w) := by
    by_cases h0 : v - t • w = 0
    · rw [h0]; simp
    · have := hH.dotProduct_mulVec_pos h0
      rw [star_trivial] at this
      exact this.le
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, smul_eq_mul] at hpsd
  rw [hsym w v] at hpsd
  have ht : t * (w ⬝ᵥ H *ᵥ w) = v ⬝ᵥ H *ᵥ w := by
    simp only [t]; field_simp
  nlinarith [ht]

/-- A quadratic-form bound gives the inverse-form bound. -/
lemma inv_le_of_qf {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) (hH : H.PosDef) (a : Fin r → ℝ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hqf : ∀ w, (a ⬝ᵥ w) ^ 2 ≤ κ * (w ⬝ᵥ H *ᵥ w)) :
    a ⬝ᵥ H⁻¹ *ᵥ a ≤ κ := by
  have hdet : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det H).mp hH.isUnit
  set v := H⁻¹ *ᵥ a with hv
  have hHv : H *ᵥ v = a := by rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
    Matrix.one_mulVec]
  have h := hqf v
  rw [hHv, dotProduct_comm v a] at h
  by_cases hp : a ⬝ᵥ v ≤ 0
  · linarith
  · have hp' : 0 < a ⬝ᵥ v := lt_of_not_ge hp
    nlinarith

/-- Vectors orthogonal to a spanning family vanish. -/
lemma eq_zero_of_orth {K d : ℕ} (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) (w : Fin d → ℝ)
    (h : ∀ c, arms c ⬝ᵥ w = 0) : w = 0 := by
  have : ∀ v ∈ Submodule.span ℝ (Set.range arms), v ⬝ᵥ w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact h c
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have hw := this w (by rw [hspan]; trivial)
  exact dotProduct_self_eq_zero.mp hw

end C3A

namespace GE

lemma sum_inv_sq_le (T : ℕ) :
    ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((T : ℝ) + 1) := by
  induction T with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have key : 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    push_cast
    linarith

lemma sum_inv_sq_le_two (T : ℕ) : ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 ≤ 2 := by
  have := sum_inv_sq_le T
  have : (0 : ℝ) ≤ 2 / ((T : ℝ) + 1) := by positivity
  linarith

/-- fourth roots -/
lemma qr_pow (s : ℝ) (hs : 0 ≤ s) (n : ℕ) : (s ^ ((1 : ℝ) / 4)) ^ n = s ^ ((n : ℝ) / 4) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  ring_nf

lemma qr_four (s : ℝ) (hs : 0 ≤ s) : (s ^ ((1 : ℝ) / 4)) ^ 4 = s := by
  rw [qr_pow s hs 4]; norm_num

lemma qr_two (s : ℝ) (hs : 0 ≤ s) : (s ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt s := by
  rw [qr_pow s hs 2, Real.sqrt_eq_rpow]; norm_num

lemma qr_three (s : ℝ) (hs : 0 ≤ s) : (s ^ ((1 : ℝ) / 4)) ^ 3 = s ^ ((3 : ℝ) / 4) := by
  rw [qr_pow s hs 3]; norm_num

lemma qr_ge_one (s : ℝ) (hs : 1 ≤ s) : 1 ≤ s ^ ((1 : ℝ) / 4) :=
  Real.one_le_rpow hs (by norm_num)

lemma exp_neg_le (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ (Nat.factorial 12 : ℝ) / y ^ 12 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 12
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h
  linarith

/-- (C.172): the time envelope is summable, uniformly in the horizon. -/
lemma tail_sum (Cb : ℝ) (hCb : 0 < Cb) (T : ℕ) :
    ∑ t ∈ Finset.range T, Real.sqrt ((t : ℝ) + 1) *
        Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) ≤
      2 * ((Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12) := by
  have hterm : ∀ t : ℕ, Real.sqrt ((t : ℝ) + 1) *
      Real.exp (-(2 * ((t : ℝ) + 1) ^ ((1 : ℝ) / 4) / Cb)) ≤
      (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * (1 / ((t : ℝ) + 1) ^ 2) := by
    intro t
    set s : ℝ := (t : ℝ) + 1 with hs
    have hs1 : 1 ≤ s := by simp only [s]; linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    set u := s ^ ((1 : ℝ) / 4) with hu
    have hu1 : 1 ≤ u := qr_ge_one s hs1
    have hu0 : 0 < u := by linarith
    have hy : 0 < 2 * u / Cb := by positivity
    have h1 := exp_neg_le (2 * u / Cb) hy
    rw [← qr_two s (by linarith)]
    have hs2 : s ^ 2 = u ^ 8 := by rw [← qr_four s (by linarith)]; ring
    rw [hs2]
    calc u ^ 2 * Real.exp (-(2 * u / Cb))
        ≤ u ^ 2 * ((Nat.factorial 12 : ℝ) / (2 * u / Cb) ^ 12) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * (1 / u ^ 10) := by
          field_simp
      _ ≤ (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * (1 / u ^ 8) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_right₀ hu1 (by norm_num)
  calc _ ≤ ∑ t ∈ Finset.range T, (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 *
        (1 / ((t : ℝ) + 1) ^ 2) := Finset.sum_le_sum fun t _ => hterm t
    _ = (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 *
        ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12 * 2 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le_two T) (by positivity)
    _ = 2 * ((Nat.factorial 12 : ℝ) * (Cb / 2) ^ 12) := by ring

/-- the learning-rate schedule `β_s = 16d + √(d s / L)`, `L = 1 + log K` -/
lemma beta_eq (d K s : ℕ) (hK : 1 ≤ K) :
    IAFTRL.beta d K s = 16 * d + Real.sqrt (d / (1 + Real.log K)) * Real.sqrt s := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hnn : (0 : ℝ) ≤ d / (1 + Real.log K) := by positivity
  unfold IAFTRL.beta
  rw [show (d : ℝ) * s / (1 + Real.log K) = d / (1 + Real.log K) * s by ring,
    Real.sqrt_mul hnn]

lemma beta_le (d K s : ℕ) (hK : 1 ≤ K) (hs : 1 ≤ s) :
    IAFTRL.beta d K s ≤ (16 * d + Real.sqrt (d / (1 + Real.log K))) * Real.sqrt s := by
  rw [beta_eq d K s hK]
  have h1 : 1 ≤ Real.sqrt (s : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
  have : (0 : ℝ) ≤ 16 * d := by positivity
  nlinarith

lemma beta_ge (d K s : ℕ) (hK : 1 ≤ K) :
    Real.sqrt (d / (1 + Real.log K)) * Real.sqrt s ≤ IAFTRL.beta d K s := by
  rw [beta_eq d K s hK]; have : (0 : ℝ) ≤ 16 * d := by positivity
  linarith

lemma cR_eq (d K : ℕ) (hK : 1 ≤ K) :
    IAFTRL.cR d K = Real.sqrt (d / (1 + Real.log K)) * (1 + Real.log K) := by
  have hL : 0 < 1 + Real.log K := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK); linarith
  unfold IAFTRL.cR
  rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  rw [show (d : ℝ) * (1 + Real.log K) = (1 + Real.log K) ^ 2 * (d / (1 + Real.log K)) by
    field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL.le]
  ring

/-- (C.170a): `(β_{t+1} − β_t) log K ≤ c_R / √(t+1)` and `β_{t+1} − β_t ≤ c_β` -/
lemma beta_diff (d K t : ℕ) (hK : 1 ≤ K) :
    0 ≤ IAFTRL.beta d K (t + 1) - IAFTRL.beta d K t ∧
    IAFTRL.beta d K (t + 1) - IAFTRL.beta d K t ≤ Real.sqrt (d / (1 + Real.log K)) ∧
    (IAFTRL.beta d K (t + 1) - IAFTRL.beta d K t) * Real.log K ≤
      IAFTRL.cR d K / Real.sqrt ((t : ℝ) + 1) := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  rw [beta_eq d K (t + 1) hK, beta_eq d K t hK, cR_eq d K hK]
  set c := Real.sqrt (d / (1 + Real.log K))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  push_cast
  set a := Real.sqrt ((t : ℝ) + 1)
  set b := Real.sqrt (t : ℝ)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = t + 1 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = t := Real.sq_sqrt (by positivity)
  have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hd : a - b ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    nlinarith
  have hd1 : a - b ≤ 1 := by
    have : 1 ≤ a := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by
      have := (Nat.cast_nonneg t : (0 : ℝ) ≤ t); linarith)
    calc a - b ≤ 1 / a := hd
      _ ≤ 1 := by rw [div_le_one ha]; exact this
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have e : 16 * (d : ℝ) + c * a - (16 * d + c * b) = c * (a - b) := by ring
  rw [e]
  calc c * (a - b) * Real.log K ≤ c * (1 / a) * (1 + Real.log K) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hd hc) (by linarith) hlogK
        exact mul_nonneg hc (by positivity)
    _ = c * (1 + Real.log K) / a := by ring

/-- (C.170b): `2d / β_{t+1} ≤ 2 c_R / √(t+1)` -/
lemma two_d_div_beta (d K t : ℕ) (hK : 1 ≤ K) (hd : 1 ≤ d) :
    2 * (d : ℝ) / IAFTRL.beta d K (t + 1) ≤ 2 * IAFTRL.cR d K / Real.sqrt ((t : ℝ) + 1) := by
  have hlogK := Real.log_nonneg (show (1 : ℝ) ≤ K by exact_mod_cast hK)
  have hL : 0 < 1 + Real.log K := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hge := beta_ge d K (t + 1) hK
  rw [cR_eq d K hK]
  set c := Real.sqrt (d / (1 + Real.log K)) with hcdef
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = d / (1 + Real.log K) := Real.sq_sqrt (by positivity)
  set a := Real.sqrt ((t : ℝ) + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  push_cast at hge
  have hβ : 0 < IAFTRL.beta d K (t + 1) := by unfold IAFTRL.beta; positivity
  calc 2 * (d : ℝ) / IAFTRL.beta d K (t + 1) ≤ 2 * d / (c * a) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    _ = 2 * (c * (1 + Real.log K)) / a := by
        field_simp
        rw [hc2]
        field_simp

end GE


namespace GE

variable {d K : ℕ}

lemma qSoft_norm (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K)
    (a : Fin K) :
    qSoft β arms S a = Real.exp (-((arms a - arms jstar) ⬝ᵥ S / β)) /
      ∑ b, Real.exp (-((arms b - arms jstar) ⬝ᵥ S / β)) := by
  unfold qSoft
  have hfac : ∀ c, Real.exp (-(arms c ⬝ᵥ S) / β) = Real.exp (-(arms jstar ⬝ᵥ S) / β) *
      Real.exp (-((arms c - arms jstar) ⬝ᵥ S / β)) := by
    intro c; rw [← Real.exp_add]; congr 1; rw [sub_dotProduct]; ring
  rw [Finset.sum_congr rfl fun c _ => hfac c, hfac a, ← Finset.mul_sum,
    mul_div_mul_left _ _ (Real.exp_pos _).ne']

lemma Z_ge_one (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) :
    1 ≤ ∑ b, Real.exp (-((arms b - arms jstar) ⬝ᵥ S / β)) := by
  have h := Finset.single_le_sum (f := fun b => Real.exp (-((arms b - arms jstar) ⬝ᵥ S / β)))
    (fun b _ => (Real.exp_pos _).le) (Finset.mem_univ jstar)
  simpa using h

lemma q_le (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) (a : Fin K) :
    qSoft β arms S a ≤ Real.exp (-((arms a - arms jstar) ⬝ᵥ S / β)) := by
  rw [qSoft_norm β arms S jstar a]
  exact div_le_self (Real.exp_pos _).le (Z_ge_one β arms S jstar)

lemma q_pos (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) (a : Fin K) :
    0 < qSoft β arms S a := by
  rw [qSoft_norm β arms S jstar a]
  exact div_pos (Real.exp_pos _) (lt_of_lt_of_le one_pos (Z_ge_one β arms S jstar))

lemma q_sum (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) :
    ∑ a, qSoft β arms S a = 1 := by
  simp_rw [qSoft_norm β arms S jstar]
  rw [← Finset.sum_div]
  exact div_self (lt_of_lt_of_le one_pos (Z_ge_one β arms S jstar)).ne'

lemma one_add_mul_exp_neg (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have h := Real.add_one_le_exp (x / 2)
  have e1 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-(x / 2))
  rw [e1]
  nlinarith

/-- (C.168): entropy envelope under separation. -/
lemma entropy_env (β : ℝ) (hβ : 0 < β) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ)
    (jstar : Fin K) (hsep : ∀ a, a ≠ jstar → 0 ≤ (arms a - arms jstar) ⬝ᵥ S) :
    -∑ a, qSoft β arms S a * Real.log (qSoft β arms S a) ≤
      2 * ∑ a ∈ Finset.univ.erase jstar,
        Real.exp (-((arms a - arms jstar) ⬝ᵥ S / (2 * β))) := by
  classical
  set x : Fin K → ℝ := fun a => (arms a - arms jstar) ⬝ᵥ S / β with hx
  have hx0 : x jstar = 0 := by simp [x]
  have hxnn : ∀ a, 0 ≤ x a := by
    intro a
    by_cases h : a = jstar
    · rw [h, hx0]
    · exact div_nonneg (hsep a h) hβ.le
  set Z := ∑ b, Real.exp (-x b) with hZ
  have hZ1 : 1 ≤ Z := Z_ge_one β arms S jstar
  have hZpos : 0 < Z := by linarith
  have hq : ∀ a, qSoft β arms S a = Real.exp (-x a) / Z := fun a => qSoft_norm β arms S jstar a
  have hlog : ∀ a, Real.log (qSoft β arms S a) = -x a - Real.log Z := by
    intro a; rw [hq a, Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hsum1 := q_sum β arms S jstar
  have hH : -∑ a, qSoft β arms S a * Real.log (qSoft β arms S a) =
      ∑ a, qSoft β arms S a * x a + Real.log Z := by
    simp_rw [hlog]
    have : ∑ a, qSoft β arms S a * (-x a - Real.log Z) =
        -(∑ a, qSoft β arms S a * x a) - Real.log Z * ∑ a, qSoft β arms S a := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hsum1]; ring
  rw [hH]
  have hlogZ : Real.log Z ≤ ∑ a ∈ Finset.univ.erase jstar, Real.exp (-x a) := by
    have h1 := Real.log_le_sub_one_of_pos hZpos
    have h2 : Z = Real.exp (-x jstar) + ∑ a ∈ Finset.univ.erase jstar, Real.exp (-x a) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ jstar)).symm
    rw [h2, hx0] at h1 ⊢
    simp only [neg_zero, Real.exp_zero] at h1 ⊢
    linarith
  have hqx : ∑ a, qSoft β arms S a * x a ≤
      ∑ a ∈ Finset.univ.erase jstar, x a * Real.exp (-x a) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jstar), hx0, mul_zero, zero_add]
    exact Finset.sum_le_sum fun a _ => by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (q_le β arms S jstar a) (hxnn a)
  have hfinal : ∑ a ∈ Finset.univ.erase jstar, (Real.exp (-x a) + x a * Real.exp (-x a)) ≤
      ∑ a ∈ Finset.univ.erase jstar, 2 * Real.exp (-(x a / 2)) :=
    Finset.sum_le_sum fun a _ => by
      have := one_add_mul_exp_neg (x a); nlinarith
  have hx2 : ∀ a, x a / 2 = (arms a - arms jstar) ⬝ᵥ S / (2 * β) := by
    intro a; simp only [x]; field_simp
  rw [Finset.mul_sum]
  simp_rw [← hx2]
  rw [Finset.sum_add_distrib] at hfinal
  linarith

/-- the reference action is `a*` when `a*` is the strict minimizer -/
lemma refArm_eq (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K)
    (hmin : ∀ a, a ≠ jstar → arms jstar ⬝ᵥ S < arms a ⬝ᵥ S) : refArm arms S = arms jstar := by
  classical
  unfold refArm
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty := by
    refine ⟨jstar, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => ?_⟩⟩
    by_cases hi : i = jstar
    · rw [hi]
    · exact (hmin i hi).le
  rw [dif_pos hne]
  have hmem := (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  congr 1
  by_contra hj
  exact absurd (hmem jstar) (not_le.mpr (hmin _ hj))

lemma chi_le_exp_abs (x : ℝ) : chi x ≤ Real.exp |x| := by
  unfold chi
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    have : Real.exp (-x) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith
  · rw [abs_of_neg h]
    have : Real.exp x ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    linarith

/-- centering inequality, finite form of Lemma J.4 (J.6) -/
lemma centering (q f : Fin K → ℝ) (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) :
    ∑ a, q a * chi (f a - ∑ c, q c * f c) ≤ ∑ a, q a * chi (2 * f a) := by
  set m := ∑ c, q c * f c with hm
  set A := ∑ a, q a * Real.exp (f a) with hA
  set B := ∑ a, q a * Real.exp (-f a) with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun a _ => mul_nonneg (hq0 a) (Real.exp_pos _).le
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun a _ => mul_nonneg (hq0 a) (Real.exp_pos _).le
  have hJ1 : Real.exp m ≤ A := by
    have := convexOn_exp.map_sum_le (t := Finset.univ) (w := q) (p := f)
      (fun a _ => hq0 a) hq1 (fun a _ => Set.mem_univ _)
    simpa [smul_eq_mul] using this
  have hJ2 : Real.exp (-m) ≤ B := by
    have := convexOn_exp.map_sum_le (t := Finset.univ) (w := q) (p := fun a => -f a)
      (fun a _ => hq0 a) hq1 (fun a _ => Set.mem_univ _)
    have e : ∑ a, q a • (-f a) = -m := by
      simp only [smul_eq_mul, mul_neg, Finset.sum_neg_distrib, m]
    simpa [smul_eq_mul, e] using this
  have hA2 : A ^ 2 ≤ ∑ a, q a * Real.exp (2 * f a) := by
    have := (convexOn_pow 2).map_sum_le (t := Finset.univ) (w := q)
      (p := fun a => Real.exp (f a)) (fun a _ => hq0 a) hq1
      (fun a _ => Set.mem_Ici.mpr (Real.exp_pos _).le)
    have e : ∀ a, Real.exp (f a) ^ 2 = Real.exp (2 * f a) := by
      intro a; rw [sq, ← Real.exp_add]; ring_nf
    simpa [smul_eq_mul, e] using this
  have hB2 : B ^ 2 ≤ ∑ a, q a * Real.exp (-(2 * f a)) := by
    have := (convexOn_pow 2).map_sum_le (t := Finset.univ) (w := q)
      (p := fun a => Real.exp (-f a)) (fun a _ => hq0 a) hq1
      (fun a _ => Set.mem_Ici.mpr (Real.exp_pos _).le)
    have e : ∀ a, Real.exp (-f a) ^ 2 = Real.exp (-(2 * f a)) := by
      intro a; rw [sq, ← Real.exp_add]; ring_nf
    simpa [smul_eq_mul, e] using this
  have hL : ∑ a, q a * chi (f a - m) = Real.exp (-m) * A + Real.exp m * B - 2 := by
    unfold chi
    have : ∀ a, q a * (Real.exp (f a - m) + Real.exp (-(f a - m)) - 2) =
        Real.exp (-m) * (q a * Real.exp (f a)) + Real.exp m * (q a * Real.exp (-f a)) - 2 * q a := by
      intro a
      rw [show f a - m = f a + -m by ring, Real.exp_add,
        show -(f a + -m) = -f a + m by ring, Real.exp_add]
      ring
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hq1]
    ring
  have hR : ∑ a, q a * chi (2 * f a) =
      ∑ a, q a * Real.exp (2 * f a) + ∑ a, q a * Real.exp (-(2 * f a)) - 2 := by
    unfold chi
    have : ∑ a, q a * (Real.exp (2 * f a) + Real.exp (-(2 * f a)) - 2) =
        ∑ a, q a * Real.exp (2 * f a) + ∑ a, q a * Real.exp (-(2 * f a)) - 2 * ∑ a, q a := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hq1, mul_one]
  rw [hL, hR]
  have h1 : Real.exp (-m) * A ≤ B * A := mul_le_mul_of_nonneg_right hJ2 hA0
  have h2 : Real.exp m * B ≤ A * B := mul_le_mul_of_nonneg_right hJ1 hB0
  nlinarith [sq_nonneg (A - B)]

end GE



namespace C10

/-- root extraction: `c^n ≤ t ⟹ c ≤ t^{1/n}` -/
lemma root_ge (c t : ℝ) (hc : 0 ≤ c) (n : ℕ) (hn : n ≠ 0) (h : c ^ n ≤ t) :
    c ≤ t ^ ((1 : ℝ) / n) := by
  have h1 : (c ^ n) ^ ((1 : ℝ) / n) ≤ t ^ ((1 : ℝ) / n) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  rw [one_div, Real.pow_rpow_inv_natCast hc hn] at h1
  rw [one_div]; exact h1

/-- (C.59)–(C.61), (C.75): the time thresholds give `e^{-t^{1/4}/(2C_β)} ≤ 1/(Kt)`. -/
lemma threshold (Cb t : ℝ) (K : ℕ) (hK : 1 ≤ K) (hCb : 0 < Cb)
    (hT1 : (32 * Cb) ^ 8 ≤ t) (hT2 : (4 * Cb * (1 + Real.log K)) ^ 4 ≤ t) :
    Real.exp (-(t ^ ((1 : ℝ) / 4) / (2 * Cb))) ≤ 1 / (K * t) := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast hK)
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hT1
  set x := t ^ ((1 : ℝ) / 8) with hx
  have hx1 : 32 * Cb ≤ x := by
    have := root_ge (32 * Cb) t (by positivity) 8 (by norm_num) hT1
    rw [hx]; convert this using 2; norm_num
  have hxpos : 0 < x := by linarith
  have hx2 : x ^ 2 = t ^ ((1 : ℝ) / 4) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hx8 : x ^ 8 = t := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hlogt : Real.log t = 8 * Real.log x := by
    rw [← hx8, Real.log_pow]; norm_num
  have hlogx : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hxpos; linarith
  have h1 : Real.log t ≤ x ^ 2 / (4 * Cb) := by
    rw [hlogt, le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : Real.log K ≤ x ^ 2 / (4 * Cb) := by
    have h4 := root_ge (4 * Cb * (1 + Real.log K)) t (by positivity) 4 (by norm_num) hT2
    have h4' : 4 * Cb * (1 + Real.log K) ≤ x ^ 2 := by
      rw [hx2]; convert h4 using 2; norm_num
    have := h4'
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  rw [← hx2]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  calc Real.exp (-(x ^ 2 / (2 * Cb))) ≤ Real.exp (-(Real.log t + Real.log K)) := by
        apply Real.exp_le_exp.mpr
        have : x ^ 2 / (2 * Cb) = x ^ 2 / (4 * Cb) + x ^ 2 / (4 * Cb) := by field_simp; ring
        linarith
    _ = 1 / (K * t) := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log ht0, Real.exp_log hKpos]
        field_simp

/-- separation to exponent: `X ≥ 4t^{3/4}`, `0 < β ≤ C_β √t` give `X/β ≥ 4t^{1/4}/C_β`. -/
lemma sep_ratio (Cb t β X : ℝ) (hCb : 0 < Cb) (ht : 1 ≤ t) (hβ : 0 < β)
    (hβle : β ≤ Cb * Real.sqrt t) (hX : 4 * t ^ ((3 : ℝ) / 4) ≤ X) :
    4 * t ^ ((1 : ℝ) / 4) / Cb ≤ X / β := by
  set u := t ^ ((1 : ℝ) / 4) with hu
  have ht0 : 0 ≤ t := by linarith
  have hu1 : 1 ≤ u := Real.one_le_rpow ht (by norm_num)
  have hu2 : u ^ 2 = Real.sqrt t := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0, Real.sqrt_eq_rpow]; norm_num
  have hu3 : u ^ 3 = t ^ ((3 : ℝ) / 4) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul ht0]; norm_num
  rw [← hu2] at hβle
  rw [← hu3] at hX
  rw [div_le_div_iff₀ hCb hβ]
  have : 0 < u := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hβle (show (0 : ℝ) ≤ 4 * u by positivity)]

end C10

namespace C10

/-- (C.58a) -/
lemma rhoN_le (B Cb L N d t β : ℝ) (hB : 0 < B) (hCb : 0 < Cb) (hd : 0 < d) (ht : 0 < t)
    (hβ : 0 < β) (hβle : β ≤ Cb * Real.sqrt t) (hN0 : 0 ≤ N)
    (hLn : L ^ 2 ≤ Real.sqrt t / max 1 (4 * B * Cb * N / d)) :
    16 * B * L ^ 2 / t * N ≤ 4 * d / β := by
  set an := max 1 (4 * B * Cb * N / d) with han
  have han1 : 1 ≤ an := le_max_left _ _
  have hanN : 4 * B * Cb * N / d ≤ an := le_max_right _ _
  have hN : N ≤ an * d / (4 * B * Cb) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hd] at hanN
    linarith
  set s := Real.sqrt t with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr ht
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : 16 * B * L ^ 2 * N ≤ 4 * d * s / Cb := by
    have e1 : 16 * B * L ^ 2 * N ≤ 16 * B * (s / an) * (an * d / (4 * B * Cb)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hLn (by positivity)) hN hN0 (by positivity)
    have e2 : 16 * B * (s / an) * (an * d / (4 * B * Cb)) = 4 * d * s / Cb := by
      field_simp; ring
    linarith
  have h2 : 16 * B * L ^ 2 / t * N = 16 * B * L ^ 2 * N / t := by ring
  rw [h2, div_le_div_iff₀ ht hβ]
  have h3 : 4 * d * s / Cb * β ≤ 4 * d * t := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hCb]
    calc 4 * d * s * β ≤ 4 * d * s * (Cb * s) :=
          mul_le_mul_of_nonneg_left hβle (by positivity)
      _ = 4 * d * t * Cb := by rw [← hs2]; ring
  nlinarith [mul_le_mul_of_nonneg_right h1 hβ.le]

/-- (C.58b) -/
lemma rho_le (B L t Δ₀ : ℝ) (hB : 0 < B) (ht : 0 < t) (hΔ₀ : 0 < Δ₀)
    (hLΔ : L ^ 2 ≤ t / (64 * B / Δ₀ ^ 2)) : 4 * (16 * B * L ^ 2 / t) ≤ Δ₀ ^ 2 := by
  rw [le_div_iff₀ (by positivity)] at hLΔ
  rw [show 4 * (16 * B * L ^ 2 / t) = 64 * B * L ^ 2 / t by ring, div_le_iff₀ ht]
  have : L ^ 2 * (64 * B / Δ₀ ^ 2) * Δ₀ ^ 2 = 64 * B * L ^ 2 := by field_simp
  nlinarith [sq_nonneg Δ₀]

/-- (C.81e)–(C.81f): the row budgets -/
lemma row_alg (Δ X L t ρ B β : ℝ) (hΔ : 0 ≤ Δ) (hX : 0 ≤ X) (hL : 1 ≤ L) (ht : 0 < t)
    (hρ : 0 < ρ) (hρt : ρ * t = 16 * B * L ^ 2) (hB : 1 ≤ B) (hβ : 0 < β)
    (hLX : t * Δ ≤ L * X) :
    2 * Δ / ρ ≤ β + X / B ∧ 2 * Δ ^ 2 / ρ ≤ β + X ^ 2 / (B * t) := by
  have hBpos : 0 < B := by linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hLX2 : t * Δ ≤ L ^ 2 * X := by
    have := mul_le_mul_of_nonneg_right hLL hX; linarith
  constructor
  · have h1 : 2 * Δ / ρ ≤ X / B := by
      rw [div_le_div_iff₀ hρ hBpos]
      have : 2 * Δ * B * t ≤ X * ρ * t := by
        rw [mul_assoc X, hρt]
        have e1 := mul_le_mul_of_nonneg_left hLX2 (show (0 : ℝ) ≤ 2 * B by positivity)
        have e2 : 0 ≤ X * B * L ^ 2 := by positivity
        nlinarith
      nlinarith
    have : 0 ≤ β := hβ.le
    linarith
  · have h1 : 2 * Δ ^ 2 / ρ ≤ X ^ 2 / (B * t) := by
      rw [div_le_div_iff₀ hρ (by positivity)]
      have hsq : (t * Δ) ^ 2 ≤ (L * X) ^ 2 := pow_le_pow_left₀ (by positivity) hLX 2
      have : 2 * Δ ^ 2 * (B * t) * t ≤ X ^ 2 * ρ * t := by
        rw [mul_assoc (X ^ 2), hρt]; nlinarith
      nlinarith
    have : 0 ≤ β := hβ.le
    linarith

/-- (C.83a): the proxy exponent -/
lemma exp_alg (Δ X L t ρ B β : ℝ) (hΔ : 0 ≤ Δ) (hX : 0 ≤ X) (hL : 1 ≤ L) (ht : 0 < t)
    (hρ : 0 < ρ) (hρt : ρ * t = 16 * B * L ^ 2) (hB : 1 ≤ B) (hβ : 0 < β)
    (hLX : t * Δ ≤ L * X) : -(X / β) + 2 * (2 * Δ / ρ) / β ≤ -(X / (2 * β)) := by
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hLX2 : t * Δ ≤ L ^ 2 * X := by
    have := mul_le_mul_of_nonneg_right hLL hX; linarith
  have h1 : 2 * (2 * Δ / ρ) ≤ X / 2 := by
    rw [show 2 * (2 * Δ / ρ) = 4 * Δ / ρ by ring, div_le_div_iff₀ hρ (by norm_num)]
    have : 4 * Δ * 2 * t ≤ X * ρ * t := by
      rw [mul_assoc X, hρt]
      have e1 := mul_le_mul_of_nonneg_left hLX2 (show (0 : ℝ) ≤ 8 by norm_num)
      have e2 : 0 ≤ X * L ^ 2 := by positivity
      have e3 : X * L ^ 2 * 8 ≤ X * L ^ 2 * (16 * B) :=
        mul_le_mul_of_nonneg_left (by linarith) e2
      nlinarith
    nlinarith
  have h2 : 2 * (2 * Δ / ρ) / β ≤ X / 2 / β := div_le_div_of_nonneg_right h1 hβ.le
  have h3 : X / 2 / β = X / β - X / (2 * β) := by field_simp; ring
  linarith

end C10

namespace C10

open Matrix IAFTRL

/-- The comparison design: positive definiteness, `V_a ≤ 2Δ(a)²/ρ`, row bounds, and the
row-variance identity. -/
lemma comparison_matrix {d K : ℕ} (arms : Fin K → Fin d → ℝ) (jstar : Fin K)
    (n p Δ : Fin K → ℝ) (ρ Δ₀ : ℝ) (hρ : 0 < ρ) (hρΔ : 4 * ρ ≤ Δ₀ ^ 2) (hρ1 : ρ ≤ 1)
    (hΔ₀ : 0 < Δ₀) (hΔge : ∀ a, a ≠ jstar → Δ₀ ≤ Δ a) (hΔ2 : ∀ a, Δ a ≤ 2)
    (hΔnn : ∀ a, 0 ≤ Δ a)
    (hn0 : ∀ b, 0 ≤ n b) (hHpd : (BanditAlgorithm.linearAllocationMatrix arms n).PosDef)
    (hnf : ∀ a, a ≠ jstar → arms a ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms n)⁻¹ *ᵥ
      arms a ≤ Δ a ^ 2 / 2)
    (hp0 : ∀ b, 0 ≤ p b) (hpρ : ∀ b, ρ * n b ≤ p b) (hpstar : 1 / 2 ≤ p jstar) :
    (BanditAlgorithm.linearAllocationMatrix arms p).PosDef ∧
    (∀ a, a ≠ jstar → (arms a - arms jstar) ⬝ᵥ
        (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ (arms a - arms jstar) ≤
          2 * Δ a ^ 2 / ρ) ∧
    (∀ a, a ≠ jstar → ∀ b, |(arms a - arms jstar) ⬝ᵥ
        (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ arms b| ≤ 2 * Δ a / ρ) ∧
    (∀ x : Fin d → ℝ, ∑ b, p b * (x ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ
        arms b) ^ 2 = x ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ x) := by
  set M := BanditAlgorithm.linearAllocationMatrix arms p with hMdef
  set H := BanditAlgorithm.linearAllocationMatrix arms n with hHdef
  have hMqf : ∀ v, v ⬝ᵥ M *ᵥ v = ∑ b, p b * (arms b ⬝ᵥ v) ^ 2 := fun v => by
    simp only [M]; unfold BanditAlgorithm.linearAllocationMatrix; exact C3A.gram_qf arms p v
  have hHqf : ∀ v, v ⬝ᵥ H *ᵥ v = ∑ b, n b * (arms b ⬝ᵥ v) ^ 2 := fun v => by
    simp only [H]; unfold BanditAlgorithm.linearAllocationMatrix; exact C3A.gram_qf arms n v
  have hMH : ∀ v, ρ * (v ⬝ᵥ H *ᵥ v) ≤ v ⬝ᵥ M *ᵥ v := by
    intro v
    rw [hMqf, hHqf, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hpρ b) (sq_nonneg _)
  have hMstar : ∀ v, (1 / 2) * (arms jstar ⬝ᵥ v) ^ 2 ≤ v ⬝ᵥ M *ᵥ v := by
    intro v
    rw [hMqf]
    calc (1 / 2) * (arms jstar ⬝ᵥ v) ^ 2 ≤ p jstar * (arms jstar ⬝ᵥ v) ^ 2 :=
          mul_le_mul_of_nonneg_right hpstar (sq_nonneg _)
      _ ≤ ∑ b, p b * (arms b ⬝ᵥ v) ^ 2 :=
          Finset.single_le_sum (f := fun b => p b * (arms b ⬝ᵥ v) ^ 2)
            (fun b _ => mul_nonneg (hp0 b) (sq_nonneg _)) (Finset.mem_univ _)
  have hHnn : ∀ v, 0 ≤ v ⬝ᵥ H *ᵥ v := fun v => by
    rw [hHqf]; exact Finset.sum_nonneg fun b _ => mul_nonneg (hn0 b) (sq_nonneg _)
  have hMnn : ∀ v, 0 ≤ v ⬝ᵥ M *ᵥ v := fun v => by
    rw [hMqf]; exact Finset.sum_nonneg fun b _ => mul_nonneg (hp0 b) (sq_nonneg _)
  have hMpd : M.PosDef := by
    have hherm : M.IsHermitian := by
      simp only [M]; unfold BanditAlgorithm.linearAllocationMatrix; exact C3A.gram_herm arms p
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun v hv => ?_
    rw [star_trivial]
    have h := hHpd.dotProduct_mulVec_pos hv
    rw [star_trivial] at h
    have := hMH v
    nlinarith
  have hdetM : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMpd.isUnit
  have hinvnn : ∀ x, 0 ≤ x ⬝ᵥ M⁻¹ *ᵥ x := by
    intro x
    have hz : x ⬝ᵥ M⁻¹ *ᵥ x = (M⁻¹ *ᵥ x) ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetM, Matrix.one_mulVec,
        dotProduct_comm]
    rw [hz]; exact hMnn _
  have hlam : ∀ a, a ≠ jstar → arms a ⬝ᵥ M⁻¹ *ᵥ arms a ≤ Δ a ^ 2 / (2 * ρ) := by
    intro a ha
    refine C3A.inv_le_of_qf M hMpd (arms a) _ (by positivity) fun v => ?_
    have h1 := C3A.cs_pd H hHpd (arms a) v
    have h2 := hnf a ha
    have h3 := hMH v
    have h4 := hHnn v
    calc (arms a ⬝ᵥ v) ^ 2 ≤ (arms a ⬝ᵥ H⁻¹ *ᵥ arms a) * (v ⬝ᵥ H *ᵥ v) := h1
      _ ≤ Δ a ^ 2 / 2 * (v ⬝ᵥ H *ᵥ v) := mul_le_mul_of_nonneg_right h2 h4
      _ ≤ Δ a ^ 2 / (2 * ρ) * (v ⬝ᵥ M *ᵥ v) := by
          rw [show Δ a ^ 2 / (2 * ρ) * (v ⬝ᵥ M *ᵥ v) = Δ a ^ 2 / 2 * ((v ⬝ᵥ M *ᵥ v) / ρ) by
            field_simp]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ hρ]; linarith
  have hlamstar : arms jstar ⬝ᵥ M⁻¹ *ᵥ arms jstar ≤ 2 :=
    C3A.inv_le_of_qf M hMpd (arms jstar) 2 (by norm_num) fun v => by
      have := hMstar v; linarith
  have hlamb : ∀ b, arms b ⬝ᵥ M⁻¹ *ᵥ arms b ≤ 2 / ρ := by
    intro b
    by_cases hb : b = jstar
    · rw [hb]; refine hlamstar.trans ?_
      rw [le_div_iff₀ hρ]; nlinarith
    · refine (hlam b hb).trans ?_
      rw [div_le_div_iff₀ (by positivity) hρ]
      have h4 : Δ b ^ 2 ≤ 4 := by nlinarith [hΔ2 b, hΔnn b]
      nlinarith [mul_le_mul_of_nonneg_right h4 hρ.le]
  have hV : ∀ a, a ≠ jstar →
      (arms a - arms jstar) ⬝ᵥ M⁻¹ *ᵥ (arms a - arms jstar) ≤ 2 * Δ a ^ 2 / ρ := by
    intro a ha
    refine C3A.inv_le_of_qf M hMpd _ _ (by positivity) fun v => ?_
    have h1 := C3A.cs_pd M hMpd (arms a) v
    have h2 := C3A.cs_pd M hMpd (arms jstar) v
    have hMv := hMnn v
    have e1 : (arms a ⬝ᵥ v) ^ 2 ≤ Δ a ^ 2 / (2 * ρ) * (v ⬝ᵥ M *ᵥ v) :=
      h1.trans (mul_le_mul_of_nonneg_right (hlam a ha) hMv)
    have e2 : (arms jstar ⬝ᵥ v) ^ 2 ≤ 2 * (v ⬝ᵥ M *ᵥ v) :=
      h2.trans (mul_le_mul_of_nonneg_right hlamstar hMv)
    have e3 : 4 ≤ Δ a ^ 2 / ρ := by
      rw [le_div_iff₀ hρ]
      have : Δ₀ ^ 2 ≤ Δ a ^ 2 := pow_le_pow_left₀ hΔ₀.le (hΔge a ha) 2
      linarith
    have e4 : Δ a ^ 2 / (2 * ρ) = (Δ a ^ 2 / ρ) / 2 := by field_simp
    rw [sub_dotProduct]
    have e5 : (arms a ⬝ᵥ v - arms jstar ⬝ᵥ v) ^ 2 ≤
        2 * (arms a ⬝ᵥ v) ^ 2 + 2 * (arms jstar ⬝ᵥ v) ^ 2 := by
      nlinarith [sq_nonneg (arms a ⬝ᵥ v + arms jstar ⬝ᵥ v)]
    rw [e4] at e1
    have e6 : 2 * Δ a ^ 2 / ρ = 2 * (Δ a ^ 2 / ρ) := by ring
    rw [e6]
    set m := v ⬝ᵥ M *ᵥ v
    set r := Δ a ^ 2 / ρ
    nlinarith
  have hcsinv : ∀ x y : Fin d → ℝ,
      (x ⬝ᵥ M⁻¹ *ᵥ y) ^ 2 ≤ (x ⬝ᵥ M⁻¹ *ᵥ x) * (y ⬝ᵥ M⁻¹ *ᵥ y) := by
    intro x y
    have h := C3A.cs_pd M hMpd x (M⁻¹ *ᵥ y)
    have e : (M⁻¹ *ᵥ y) ⬝ᵥ M *ᵥ (M⁻¹ *ᵥ y) = y ⬝ᵥ M⁻¹ *ᵥ y := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetM, Matrix.one_mulVec,
        dotProduct_comm]
    rwa [e] at h
  have hMinvT : M⁻¹ᵀ = M⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    have := hMpd.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨hMpd, hV, ?_, ?_⟩
  · intro a ha b
    have h := hcsinv (arms a - arms jstar) (arms b)
    have hsq : ((arms a - arms jstar) ⬝ᵥ M⁻¹ *ᵥ arms b) ^ 2 ≤ (2 * Δ a / ρ) ^ 2 := by
      calc _ ≤ _ := h
        _ ≤ (2 * Δ a ^ 2 / ρ) * (2 / ρ) :=
            mul_le_mul (hV a ha) (hlamb b) (hinvnn _) (by positivity)
        _ = (2 * Δ a / ρ) ^ 2 := by field_simp
    have hc : 0 ≤ 2 * Δ a / ρ := by have := hΔnn a; positivity
    exact abs_le_of_sq_le_sq' hsq hc |> fun h => abs_le.mpr ⟨h.1, h.2⟩
  · intro x
    set z := M⁻¹ *ᵥ x with hz
    have hrow : ∀ b, x ⬝ᵥ M⁻¹ *ᵥ arms b = arms b ⬝ᵥ z := by
      intro b
      rw [hz, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hMinvT, dotProduct_comm]
    simp_rw [hrow]
    rw [← hMqf z]
    rw [show M *ᵥ z = x by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetM, Matrix.one_mulVec],
      dotProduct_comm]

end C10

namespace C10

open Matrix IAFTRL

/-- (C.82): proxy bound for a law with controlled reconstruction rows. -/
lemma proxy_generic {d K : ℕ} (arms : Fin K → Fin d → ℝ) (t : ℕ) (S : Fin d → ℝ)
    (p : Fin K → ℝ) (jstar : Fin K) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∑ b, p b = 1)
    (hβ : 0 < beta d K t) (R V : Fin K → ℝ) (E : ℝ) (hE0 : 0 ≤ E)
    (hrow : ∀ a, a ≠ jstar → ∀ b, |(arms a - arms jstar) ⬝ᵥ vCoef arms p b| ≤ R a)
    (hV : ∀ a, a ≠ jstar → ∑ b, p b * ((arms a - arms jstar) ⬝ᵥ vCoef arms p b) ^ 2 ≤ V a)
    (hE : ∀ a, a ≠ jstar → qSoft (beta d K t) arms S a * Real.exp (2 * R a / beta d K t) ≤ E)
    (hchi : ∀ x, chi x ≤ x ^ 2 * Real.exp |x|) :
    proxyC arms t S p ≤ 4 / beta d K t * E * ∑ a ∈ Finset.univ.erase jstar, V a := by
  classical
  set β := beta d K t with hβdef
  set q := qSoft β arms S with hqdef
  have hq0 : ∀ a, 0 ≤ q a := fun a => (GE.q_pos β arms S jstar a).le
  have hq1 : ∑ a, q a = 1 := GE.q_sum β arms S jstar
  set bb : Fin K → Fin K → ℝ := fun a b => (arms a - arms jstar) ⬝ᵥ vCoef arms p b with hbb
  have hinner : ∀ b, ∑ a, q a * chi ((arms a - abar arms q) ⬝ᵥ vCoef arms p b / β) ≤
      ∑ a ∈ Finset.univ.erase jstar, 4 / β ^ 2 * E * bb a b ^ 2 := by
    intro b
    set v := vCoef arms p b
    set f : Fin K → ℝ := fun a => (arms a - arms jstar) ⬝ᵥ v / β with hfdef
    have habar : ∀ a, (arms a - abar arms q) ⬝ᵥ v / β = f a - ∑ c, q c * f c := by
      intro a
      simp only [f, abar, sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul]
      have : ∑ c, q c * ((arms c ⬝ᵥ v - arms jstar ⬝ᵥ v) / β) =
          (∑ c, q c * arms c ⬝ᵥ v) / β - (∑ c, q c) * (arms jstar ⬝ᵥ v) / β := by
        rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by ring
      rw [this, hq1]
      ring
    simp_rw [habar]
    refine (GE.centering q f hq0 hq1).trans ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jstar)]
    have hf0 : f jstar = 0 := by simp [f]
    rw [hf0, mul_zero, show chi 0 = 0 by norm_num [chi], mul_zero, zero_add]
    refine Finset.sum_le_sum fun a ha => ?_
    have haj : a ≠ jstar := Finset.ne_of_mem_erase ha
    have hra := hrow a haj b
    have habs : |2 * f a| ≤ 2 * R a / β := by
      rw [abs_mul, abs_two, show f a = bb a b / β from rfl, abs_div, abs_of_pos hβ]
      rw [show 2 * (|bb a b| / β) = 2 * |bb a b| / β by ring]
      exact div_le_div_of_nonneg_right (by linarith) hβ.le
    have hsq : (2 * f a) ^ 2 = 4 / β ^ 2 * bb a b ^ 2 := by
      simp only [f]; field_simp; ring
    calc q a * chi (2 * f a) ≤ q a * ((2 * f a) ^ 2 * Real.exp |2 * f a|) :=
          mul_le_mul_of_nonneg_left (hchi _) (hq0 a)
      _ ≤ q a * ((2 * f a) ^ 2 * Real.exp (2 * R a / β)) := by
          apply mul_le_mul_of_nonneg_left _ (hq0 a)
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr habs) (sq_nonneg _)
      _ = 4 / β ^ 2 * bb a b ^ 2 * (q a * Real.exp (2 * R a / β)) := by rw [hsq]; ring
      _ ≤ 4 / β ^ 2 * bb a b ^ 2 * E :=
          mul_le_mul_of_nonneg_left (hE a haj) (by positivity)
      _ = 4 / β ^ 2 * E * bb a b ^ 2 := by ring
  unfold proxyC
  rw [← hβdef, ← hqdef]
  calc β * ∑ b, p b * ∑ a, q a * chi ((arms a - abar arms q) ⬝ᵥ vCoef arms p b / β)
      ≤ β * ∑ b, p b * ∑ a ∈ Finset.univ.erase jstar, 4 / β ^ 2 * E * bb a b ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hβ.le
        exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hinner b) (hp0 b)
    _ = β * (4 / β ^ 2 * E) * ∑ a ∈ Finset.univ.erase jstar, ∑ b, p b * bb a b ^ 2 := by
        have key : ∑ b, p b * ∑ a ∈ Finset.univ.erase jstar, 4 / β ^ 2 * E * bb a b ^ 2 =
            4 / β ^ 2 * E * ∑ a ∈ Finset.univ.erase jstar, ∑ b, p b * bb a b ^ 2 := by
          rw [Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
        rw [key]; ring
    _ ≤ β * (4 / β ^ 2 * E) * ∑ a ∈ Finset.univ.erase jstar, V a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun a ha => hV a (Finset.ne_of_mem_erase ha)
    _ = 4 / β * E * ∑ a ∈ Finset.univ.erase jstar, V a := by
        field_simp

end C10

namespace C10

open IAFTRL

lemma exp_small (Cb t β X : ℝ) (K : ℕ) (hK : 1 ≤ K) (hCb : 0 < Cb) (ht : 1 ≤ t) (hβ : 0 < β)
    (hβle : β ≤ Cb * Real.sqrt t) (hX : 4 * t ^ ((3 : ℝ) / 4) ≤ X)
    (hT1 : (32 * Cb) ^ 8 ≤ t) (hT2 : (4 * Cb * (1 + Real.log K)) ^ 4 ≤ t) :
    Real.exp (-(X / (2 * β))) ≤ 1 / (K * t) := by
  have hr4 := sep_ratio Cb t β X hCb ht hβ hβle hX
  have hth := threshold Cb t K hK hCb hT1 hT2
  refine le_trans (Real.exp_le_exp.mpr ?_) hth
  set u := t ^ ((1 : ℝ) / 4)
  have hu0 : 0 ≤ u := by positivity
  have e1 : X / (2 * β) = (X / β) / 2 := by field_simp
  have e2 : (4 * u / Cb) / 2 = 4 * (u / (2 * Cb)) := by field_simp
  have e3 : 0 ≤ u / (2 * Cb) := by positivity
  rw [e1]
  linarith

lemma q_star_ge {d K : ℕ} (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (jstar : Fin K) (β t : ℝ)
    (ht : 4 ≤ t) (hqsub : ∀ a, a ≠ jstar → qSoft β arms S a ≤ 1 / (K * t)) :
    3 / 4 ≤ qSoft β arms S jstar := by
  classical
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have htpos : (0 : ℝ) < t := by linarith
  have hs := GE.q_sum β arms S jstar
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jstar)] at hs
  have hrest : ∑ a ∈ Finset.univ.erase jstar, qSoft β arms S a ≤ K * (1 / (K * t)) := by
    calc _ ≤ ∑ a ∈ Finset.univ.erase jstar, 1 / ((K : ℝ) * t) :=
          Finset.sum_le_sum fun a ha => hqsub a (Finset.ne_of_mem_erase ha)
      _ ≤ ∑ _a : Fin K, 1 / ((K : ℝ) * t) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => by positivity)
      _ = K * (1 / (K * t)) := by simp
  have e : (K : ℝ) * (1 / (K * t)) = 1 / t := by field_simp
  have h1t : 1 / t ≤ 1 / 4 := by
    rw [div_le_div_iff₀ htpos (by norm_num)]; linarith
  linarith

end C10

namespace C10

lemma final_num (β ρ t K B L d : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (ht : 0 < t) (hK : 0 < K)
    (hρt : ρ * t = 16 * B * L ^ 2) (hB : 1 ≤ B) (hL : 1 ≤ L) (hd : 1 ≤ d) :
    4 / β * (1 / (K * t)) * (K * (8 / ρ)) ≤ 2 * d / β := by
  have e : 4 / β * (1 / (K * t)) * (K * (8 / ρ)) = 32 / (β * (ρ * t)) := by field_simp; ring
  rw [e, hρt, div_le_div_iff₀ (by positivity) hβ]
  have h1 : 1 ≤ L ^ 2 := by nlinarith
  have h16 : 16 ≤ 16 * B * L ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h16 hβ.le]

end C10

open Matrix IAFTRL

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (hA : IsActionSet arms)
    (θ : Fin d → ℝ) (hθ : actionNorm arms θ ≤ 1) (jstar : Fin K) (hu : IsUniqueMin arms θ jstar)
    (Δ₀ : ℝ) (hΔ₀ : 0 < Δ₀) (hΔ₀1 : Δ₀ ≤ 1)
    (hgap : ∀ j, j ≠ jstar → Δ₀ ≤ (arms j - arms jstar) ⬝ᵥ θ)
    (n : Fin K → ℝ) (hn : IsFeasibleAlloc arms θ jstar n)
    (t : ℕ) (S : Fin d → ℝ) (L : ℝ)
    (hT1 : (32 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)))) ^ 8 ≤ t)
    (hT2 : (4 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))) * (1 + Real.log K)) ^ 4 ≤ t)
    (hsep : ∀ a, a ≠ jstar → 4 * (t : ℝ) ^ ((3 : ℝ) / 4) ≤ (arms a - arms jstar) ⬝ᵥ S)
    (hL1 : 1 ≤ L)
    (hLX : ∀ a, a ≠ jstar →
      t * ((arms a - arms jstar) ⬝ᵥ θ) ≤ L * ((arms a - arms jstar) ⬝ᵥ S))
    (hLn : L ^ 2 ≤ Real.sqrt t / max 1
      (4 * Bc K * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))) * allocMass n / d))
    (hLΔ : L ^ 2 ≤ t / (64 * Bc K / Δ₀ ^ 2)) :
    IsFeasible2_3 arms t S (fun a =>
      (1 - ∑ b, (if b = jstar then 0 else 16 * Bc K * L ^ 2 / t * n b)) *
          qSoft (beta d K t) arms S a +
        (if a = jstar then 0 else 16 * Bc K * L ^ 2 / t * n a)) := by
  classical
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hKR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  -- constants
  have hCb16 : 16 ≤ 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)) := by
    have := Real.sqrt_nonneg (d / (1 + Real.log K)); linarith
  have hCbpos : 0 < 16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)) := by linarith
  have ht4 : (4 : ℝ) ≤ t := by
    have h32 : (1 : ℝ) ≤ 32 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))) := by linarith
    have : 32 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K))) ≤
        (32 * (16 * (d : ℝ) + Real.sqrt (d / (1 + Real.log K)))) ^ 8 :=
      le_self_pow₀ h32 (by norm_num)
    linarith
  have htpos : (0 : ℝ) < t := by linarith
  have htN : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by linarith)
  have hB4 : 4 ≤ Bc K := by
    unfold Bc
    have h1 : (256 : ℝ) ≤ ⌈256 + Real.log (2 * (K : ℝ))⌉ := by
      have := Int.le_ceil (256 + Real.log (2 * (K : ℝ)))
      have h2 : 0 ≤ Real.log (2 * (K : ℝ)) := Real.log_nonneg (by linarith)
      linarith
    nlinarith
  have hBpos : 0 < Bc K := by linarith
  have hβpos : 0 < beta d K t := by unfold beta; positivity
  have hβle := GE.beta_le d K t hK htN
  have hβ16 : 16 * (d : ℝ) < beta d K t := by
    rw [GE.beta_eq d K t hK]
    have h1 : 0 < Real.sqrt (d / (1 + Real.log K)) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
    nlinarith [mul_pos h1 h2]
  -- gaps and cumulative differences
  have hΔstar : (arms jstar - arms jstar) ⬝ᵥ θ = 0 := by simp
  have hΔ2 : ∀ a, (arms a - arms jstar) ⬝ᵥ θ ≤ 2 := by
    intro a
    have h1 : |arms a ⬝ᵥ θ| ≤ 1 :=
      (le_ciSup (f := fun j => |arms j ⬝ᵥ θ|) (Set.finite_range _).bddAbove a).trans hθ
    have h2 : |arms jstar ⬝ᵥ θ| ≤ 1 :=
      (le_ciSup (f := fun j => |arms j ⬝ᵥ θ|) (Set.finite_range _).bddAbove jstar).trans hθ
    rw [sub_dotProduct]
    linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]
  have hΔnn : ∀ a, 0 ≤ (arms a - arms jstar) ⬝ᵥ θ := by
    intro a; by_cases h : a = jstar
    · rw [h, hΔstar]
    · linarith [hgap a h]
  have hXpos : ∀ a, a ≠ jstar → 0 < (arms a - arms jstar) ⬝ᵥ S := by
    intro a ha
    have := hsep a ha
    have : 0 < 4 * (t : ℝ) ^ ((3 : ℝ) / 4) := by positivity
    linarith
  have hr : refArm arms S = arms jstar := by
    refine GE.refArm_eq arms S jstar fun a ha => ?_
    have := hXpos a ha
    rw [sub_dotProduct] at this; linarith
  have hZ : ∀ a, Zd arms S a = (arms a - arms jstar) ⬝ᵥ S := by
    intro a; unfold Zd; rw [hr, sub_dotProduct]
  -- the exploration scale
  have hL0 : 0 < L := by linarith
  have hρpos : 0 < 16 * Bc K * L ^ 2 / t := by positivity
  have hρt : 16 * Bc K * L ^ 2 / t * t = 16 * Bc K * L ^ 2 := by field_simp
  have hρΔ := C10.rho_le (Bc K) L t Δ₀ hBpos htpos hΔ₀ hLΔ
  have hρ14 : 16 * Bc K * L ^ 2 / t ≤ 1 / 4 := by
    have : Δ₀ ^ 2 ≤ 1 := pow_le_one₀ hΔ₀.le hΔ₀1
    linarith
  have hn0 : ∀ b, 0 ≤ n b := hn.1
  have hN0 : 0 ≤ allocMass n := Finset.sum_nonneg fun b _ => hn0 b
  have hρN := C10.rhoN_le (Bc K) _ L (allocMass n) d t (beta d K t) hBpos hCbpos hdpos htpos
    hβpos hβle hN0 hLn
  have hΓ : 4 * (d : ℝ) / beta d K t < 1 / 4 := by
    rw [div_lt_iff₀ hβpos]; linarith
  -- the comparison weights and law
  set ρ := 16 * Bc K * L ^ 2 / t with hρdef
  set w : Fin K → ℝ := fun a => if a = jstar then 0 else ρ * n a with hwdef
  have hw0 : ∀ a, 0 ≤ w a := fun a => by
    simp only [w]; split_ifs; exacts [le_rfl, mul_nonneg hρpos.le (hn0 a)]
  have hγN : ∑ b, w b ≤ ρ * allocMass n := by
    simp only [allocMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    simp only [w]; split_ifs; exacts [mul_nonneg hρpos.le (hn0 b), le_rfl]
  have hγ0 : 0 ≤ ∑ b, w b := Finset.sum_nonneg fun b _ => hw0 b
  have hq0 : ∀ a, 0 ≤ qSoft (beta d K t) arms S a :=
    fun a => (GE.q_pos _ arms S jstar a).le
  have hq1 : ∑ a, qSoft (beta d K t) arms S a = 1 := GE.q_sum _ arms S jstar
  -- exponential weights of suboptimal actions are tiny
  have hexpX : ∀ a, a ≠ jstar →
      Real.exp (-((arms a - arms jstar) ⬝ᵥ S / (2 * beta d K t))) ≤ 1 / (K * t) :=
    fun a ha => C10.exp_small _ t (beta d K t) _ K hK hCbpos (by linarith) hβpos hβle
      (hsep a ha) hT1 hT2
  have hqsub : ∀ a, a ≠ jstar → qSoft (beta d K t) arms S a ≤ 1 / (K * t) := by
    intro a ha
    refine (GE.q_le _ arms S jstar a).trans ?_
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexpX a ha)
    have := hXpos a ha
    have : (arms a - arms jstar) ⬝ᵥ S / (2 * beta d K t) ≤
        (arms a - arms jstar) ⬝ᵥ S / beta d K t :=
      div_le_div_of_nonneg_left this.le hβpos (by linarith)
    linarith
  have hqstar : 3 / 4 ≤ qSoft (beta d K t) arms S jstar :=
    C10.q_star_ge arms S jstar _ t ht4 hqsub
  set p : Fin K → ℝ := fun a => (1 - ∑ b, w b) * qSoft (beta d K t) arms S a + w a with hpdef
  show IsFeasible2_3 arms t S p
  have h1γ : 0 ≤ 1 - ∑ b, w b := by linarith
  have hp0 : ∀ a, 0 ≤ p a := fun a => by
    simp only [p]; exact add_nonneg (mul_nonneg h1γ (hq0 a)) (hw0 a)
  have hp1 : ∑ a, p a = 1 := by
    simp only [p]; rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq1]; ring
  have hwj : w jstar = 0 := by simp [w]
  have hpstar : 1 / 2 ≤ p jstar := by
    have hpj : p jstar = (1 - ∑ b, w b) * qSoft (beta d K t) arms S jstar + w jstar := rfl
    rw [hpj, hwj, add_zero]
    have h1 : 3 / 4 ≤ 1 - ∑ b, w b := by linarith
    have h2 : 3 / 4 * (3 / 4) ≤ (1 - ∑ b, w b) * qSoft (beta d K t) arms S jstar :=
      mul_le_mul h1 hqstar (by norm_num) h1γ
    linarith
  have hpρ : ∀ b, ρ * n b ≤ p b := by
    intro b
    by_cases hb : b = jstar
    · rw [hb]
      have : n jstar ≤ allocMass n :=
        Finset.single_le_sum (f := n) (fun b _ => hn0 b) (Finset.mem_univ _)
      have h2 : ρ * n jstar ≤ ρ * allocMass n := mul_le_mul_of_nonneg_left this hρpos.le
      linarith
    · have hwb : w b = ρ * n b := by simp [w, hb]
      have hpb : p b = (1 - ∑ c, w c) * qSoft (beta d K t) arms S b + w b := rfl
      rw [hpb, hwb]
      have := mul_nonneg h1γ (hq0 b)
      linarith
  -- the comparison design
  obtain ⟨hMpd, hV, hrowb, hid⟩ := C10.comparison_matrix arms jstar n p
    (fun a => (arms a - arms jstar) ⬝ᵥ θ) ρ Δ₀ hρpos hρΔ (by linarith) hΔ₀ hgap hΔ2 hΔnn hn0
    hn.2.1 hn.2.2 hp0 hpρ hpstar
  have hchi : ∀ x, chi x ≤ x ^ 2 * Real.exp |x| := (lemma_J_4.{0}).2.2.2.2.2.1
  refine ⟨hp0, hp1, ⟨w, hw0, ?_, rfl⟩, ?_, ?_, ?_⟩
  · -- mixture constraint (2.3b)–(2.3c)
    show ∑ b, w b ≤ 4 * d / beta d K t
    linarith
  · -- update magnitude (2.3d)
    intro a b
    rw [hr, hZ]
    unfold vCoef
    by_cases ha : a = jstar
    · rw [ha]
      have hz : arms jstar - arms jstar = 0 := sub_self _
      rw [hz]
      simp <;> linarith [hβpos]
    · refine (hrowb a ha b).trans ?_
      exact (C10.row_alg _ _ L t ρ (Bc K) (beta d K t) (hΔnn a) (hXpos a ha).le hL1 htpos
        hρpos hρt (by linarith) hβpos (hLX a ha)).1
  · -- second moment (2.3e)
    intro a
    rw [hr, hZ]
    by_cases ha : a = jstar
    · rw [ha]
      have hz : arms jstar - arms jstar = 0 := sub_self _
      rw [hz]
      simp <;> linarith [hβpos]
    · refine (hV a ha).trans ?_
      exact (C10.row_alg _ _ L t ρ (Bc K) (beta d K t) (hΔnn a) (hXpos a ha).le hL1 htpos
        hρpos hρt (by linarith) hβpos (hLX a ha)).2
  · -- the exponential proxy constraint (2.3f)
    have hE : ∀ a, a ≠ jstar → qSoft (beta d K t) arms S a *
        Real.exp (2 * (2 * ((arms a - arms jstar) ⬝ᵥ θ) / ρ) / beta d K t) ≤ 1 / (K * t) := by
      intro a ha
      have h1 := GE.q_le (beta d K t) arms S jstar a
      have h2 := C10.exp_alg _ _ L t ρ (Bc K) (beta d K t) (hΔnn a) (hXpos a ha).le hL1 htpos
        hρpos hρt (by linarith) hβpos (hLX a ha)
      calc qSoft (beta d K t) arms S a *
            Real.exp (2 * (2 * ((arms a - arms jstar) ⬝ᵥ θ) / ρ) / beta d K t)
          ≤ Real.exp (-((arms a - arms jstar) ⬝ᵥ S / beta d K t)) *
            Real.exp (2 * (2 * ((arms a - arms jstar) ⬝ᵥ θ) / ρ) / beta d K t) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = Real.exp (-((arms a - arms jstar) ⬝ᵥ S / beta d K t) +
            2 * (2 * ((arms a - arms jstar) ⬝ᵥ θ) / ρ) / beta d K t) := (Real.exp_add _ _).symm
        _ ≤ Real.exp (-((arms a - arms jstar) ⬝ᵥ S / (2 * beta d K t))) := Real.exp_le_exp.mpr h2
        _ ≤ 1 / (K * t) := hexpX a ha
    have hP := C10.proxy_generic arms t S p jstar hp0 hp1 hβpos
      (fun a => 2 * ((arms a - arms jstar) ⬝ᵥ θ) / ρ)
      (fun a => 2 * ((arms a - arms jstar) ⬝ᵥ θ) ^ 2 / ρ) (1 / (K * t)) (by positivity)
      (fun a ha b => by unfold vCoef; exact hrowb a ha b)
      (fun a ha => by unfold vCoef; rw [hid]; exact hV a ha) hE hchi
    refine hP.trans ?_
    have hsumV : ∑ a ∈ Finset.univ.erase jstar, 2 * ((arms a - arms jstar) ⬝ᵥ θ) ^ 2 / ρ ≤
        K * (8 / ρ) := by
      calc _ ≤ ∑ a ∈ Finset.univ.erase jstar, 8 / ρ :=
            Finset.sum_le_sum fun a _ => by
              apply div_le_div_of_nonneg_right _ hρpos.le
              have h := mul_le_mul (hΔ2 a) (hΔ2 a) (hΔnn a) (by norm_num : (0 : ℝ) ≤ 2)
              rw [← pow_two] at h
              linarith
        _ ≤ ∑ _a : Fin K, 8 / ρ :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun _ _ _ => by positivity)
        _ = K * (8 / ρ) := by simp
    have hKpos : (0 : ℝ) < K := by linarith
    calc 4 / beta d K t * (1 / (K * t)) *
          ∑ a ∈ Finset.univ.erase jstar, 2 * ((arms a - arms jstar) ⬝ᵥ θ) ^ 2 / ρ
        ≤ 4 / beta d K t * (1 / (K * t)) * (K * (8 / ρ)) :=
          mul_le_mul_of_nonneg_left hsumV (by positivity)
      _ ≤ 2 * d / beta d K t :=
          C10.final_num _ ρ t K (Bc K) L d hβpos hρpos htpos hKpos hρt (by linarith) hL1 hdR
