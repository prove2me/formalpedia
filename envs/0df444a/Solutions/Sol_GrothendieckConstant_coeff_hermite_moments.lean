-- Prove2me | solution 1 for GrothendieckConstant.coeff_hermite_moments
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T01:26:43.668731+00:00
-- url     : https://prove2.me/submissions/d05f2b67-b8c5-4c04-acba-d0afcad1ba7b

import Mathlib
import Definitions.Def_KrivineSchemeDefs

/-!
# Gaussian moments on `Fin k → ℝ` (module 1 of the Grothendieck lane)
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace KG

/-- Standard Gaussian density on `Fin k → ℝ`. -/
noncomputable def phiK (k : ℕ) (x : Fin k → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma phiK_nonneg (k : ℕ) (x : Fin k → ℝ) : 0 ≤ phiK k x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

lemma measurable_phiK (k : ℕ) : Measurable (phiK k) := by
  unfold phiK
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

end KG

/-! # An elementary polynomial-versus-exponential bound -/

namespace KG

/-- Polynomial times `exp (-A/4)` is dominated by a multiple of `exp (-A/8)`. -/
lemma poly_exp_le (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4))
      ≤ 2000 * ((1 + k) ^ 3 + 3072) * Real.exp (-(A / 8)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcube : (1 + A + k) ^ 3 ≤ 4 * ((1 + k) ^ 3 + A ^ 3) := by
    nlinarith [sq_nonneg (1 + k - A), mul_nonneg (add_nonneg zero_le_one hk) hA,
      mul_nonneg (mul_nonneg (add_nonneg zero_le_one hk) hA) (sq_nonneg (1 + k - A))]
  have hA3 : A ^ 3 ≤ 3072 * Real.exp (A / 8) := by
    have := Real.pow_div_factorial_le_exp (A / 8) (by positivity) 3
    norm_num [Nat.factorial] at this
    nlinarith
  have he1 : 1 ≤ Real.exp (A / 8) := Real.one_le_exp (by positivity)
  have hsplit : Real.exp (-(A / 4)) = (Real.exp (A / 8))⁻¹ * Real.exp (-(A / 8)) := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  have hpos : 0 < Real.exp (-(A / 8)) := Real.exp_pos _
  have key : (1 + A + k) ^ 3 * (Real.exp (A / 8))⁻¹ ≤ 4 * ((1 + k) ^ 3 + 3072) := by
    rw [mul_inv_le_iff₀ (Real.exp_pos _)]
    have : (0:ℝ) ≤ (1 + k) ^ 3 := by positivity
    nlinarith
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right key hpos.le
  nlinarith

end KG

/-!
# Closed form and `t`-derivatives of the Gaussian pair density (module 2)
-/

open Real
set_option linter.unusedSimpArgs false

namespace KG

variable (k : ℕ) (A B : ℝ)

noncomputable def cpref (t : ℝ) : ℝ := 1 / (2 * π * Real.sqrt (1 - t ^ 2))
noncomputable def Eexp (t : ℝ) : ℝ := -(A - 2 * t * B) / (2 * (1 - t ^ 2))
noncomputable def Rho (t : ℝ) : ℝ := cpref t ^ k * Real.exp (Eexp A B t)

noncomputable def ell1 (t : ℝ) : ℝ := (B * (1 + t ^ 2) - A * t + k * t * (1 - t ^ 2)) / (1 - t ^ 2) ^ 2
noncomputable def ell2 (t : ℝ) : ℝ :=
  (-3 * A * t ^ 2 - A + 2 * B * t ^ 3 + 6 * B * t - k * t ^ 4 + k) / (1 - t ^ 2) ^ 3
noncomputable def ell3 (t : ℝ) : ℝ :=
  (-12 * A * t ^ 3 - 12 * A * t + 6 * B * t ^ 4 + 36 * B * t ^ 2 + 6 * B - 2 * k * t ^ 5
    - 4 * k * t ^ 3 + 6 * k * t) / (1 - t ^ 2) ^ 4

noncomputable def D1 (t : ℝ) : ℝ := Rho k A B t * ell1 k A B t
noncomputable def D2 (t : ℝ) : ℝ := Rho k A B t * (ell2 k A B t + ell1 k A B t ^ 2)
noncomputable def D3 (t : ℝ) : ℝ :=
  Rho k A B t * (ell3 k A B t + 3 * ell1 k A B t * ell2 k A B t + ell1 k A B t ^ 3)

lemma natCast_mul_pow_pred (c : ℝ) (k : ℕ) : (k : ℝ) * c ^ (k - 1) * c = k * c ^ k := by
  rcases k with _ | k
  · simp
  · simp [pow_succ, mul_assoc]

section derivs
variable {k A B}
variable {t : ℝ} (ht : 0 < 1 - t ^ 2)
include ht

lemma hasDerivAt_ell1 : HasDerivAt (ell1 k A B) (ell2 k A B t) t := by
  have hu : (1 - t ^ 2) ≠ 0 := ht.ne'
  have h1 := (((hasDerivAt_pow 2 t).const_add 1).const_mul B).sub ((hasDerivAt_id' t).const_mul A)
  have h2 := ((hasDerivAt_id' t).const_mul (k : ℝ)).mul ((hasDerivAt_pow 2 t).const_sub 1)
  have hd := ((hasDerivAt_pow 2 t).const_sub 1).pow 2
  have := (h1.add h2).div hd (pow_ne_zero 2 hu)
  show HasDerivAt (fun t => (B * (1 + t ^ 2) - A * t + k * t * (1 - t ^ 2)) / (1 - t ^ 2) ^ 2) _ t
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  unfold ell2
  field_simp
  push_cast
  ring

lemma hasDerivAt_ell2 : HasDerivAt (ell2 k A B) (ell3 k A B t) t := by
  have hu : (1 - t ^ 2) ≠ 0 := ht.ne'
  have h1 := (hasDerivAt_pow 2 t).const_mul (-3 * A)
  have h2 := (hasDerivAt_pow 3 t).const_mul (2 * B)
  have h3 := (hasDerivAt_id' t).const_mul (6 * B)
  have h4 := (hasDerivAt_pow 4 t).const_mul (k : ℝ)
  have hn := ((((h1.sub_const A).add h2).add h3).sub h4).add_const (k : ℝ)
  have hd := ((hasDerivAt_pow 2 t).const_sub 1).pow 3
  have := hn.div hd (pow_ne_zero 3 hu)
  show HasDerivAt (fun t => (-3 * A * t ^ 2 - A + 2 * B * t ^ 3 + 6 * B * t - k * t ^ 4 + k)
    / (1 - t ^ 2) ^ 3) _ t
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  unfold ell3
  field_simp
  push_cast
  ring

lemma hasDerivAt_cpref : HasDerivAt cpref (cpref t * (t / (1 - t ^ 2))) t := by
  have hs := ((hasDerivAt_pow 2 t).const_sub 1).sqrt ht.ne'
  have hpos : 0 < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr ht
  have := (hs.const_mul (2 * π)).inv (by positivity)
  have hc : cpref = fun t => (2 * π * Real.sqrt (1 - t ^ 2))⁻¹ := by
    funext s; simp [cpref]
  rw [hc]
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  have hsq : Real.sqrt (1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt ht.le
  field_simp
  rw [hsq]
  push_cast
  ring

lemma hasDerivAt_Eexp : HasDerivAt (Eexp A B) ((B * (1 + t ^ 2) - A * t) / (1 - t ^ 2) ^ 2) t := by
  have hu : (1 - t ^ 2) ≠ 0 := ht.ne'
  have hn := ((((hasDerivAt_id' t).const_mul 2).mul_const B).const_sub A).neg
  have hd := ((hasDerivAt_pow 2 t).const_sub 1).const_mul 2
  have := hn.div hd (by positivity)
  show HasDerivAt (fun t => -(A - 2 * t * B) / (2 * (1 - t ^ 2))) _ t
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  field_simp
  push_cast
  ring

lemma hasDerivAt_Rho : HasDerivAt (Rho k A B) (D1 k A B t) t := by
  have hc := (hasDerivAt_cpref ht).pow k
  have he := (hasDerivAt_Eexp (A := A) (B := B) ht).exp
  have := hc.mul he
  show HasDerivAt (fun t => cpref t ^ k * Real.exp (Eexp A B t)) _ t
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  have hu : (1 - t ^ 2) ≠ 0 := ht.ne'
  have key : (k : ℝ) * cpref t ^ (k - 1) * (cpref t * (t / (1 - t ^ 2)))
      = k * cpref t ^ k * (t / (1 - t ^ 2)) := by
    rw [← mul_assoc, natCast_mul_pow_pred]
  unfold D1 Rho ell1
  rw [key]
  field_simp
  ring

lemma hasDerivAt_D1 : HasDerivAt (D1 k A B) (D2 k A B t) t := by
  have := (hasDerivAt_Rho (k := k) (A := A) (B := B) ht).mul (hasDerivAt_ell1 (k := k) (A := A) (B := B) ht)
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  unfold D2 D1
  ring

lemma hasDerivAt_D2 : HasDerivAt (D2 k A B) (D3 k A B t) t := by
  have h1 := hasDerivAt_ell1 (k := k) (A := A) (B := B) ht
  have h2 := hasDerivAt_ell2 (k := k) (A := A) (B := B) ht
  have := (hasDerivAt_Rho (k := k) (A := A) (B := B) ht).mul (h2.add (h1.pow 2))
  refine this.congr_deriv ?_
  try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Pi.neg_apply]
  unfold D3 D1
  push_cast
  ring

end derivs

/-- Values at `t = 0`. -/
lemma ell1_zero : ell1 k A B 0 = B := by simp [ell1]
lemma ell2_zero : ell2 k A B 0 = k - A := by simp [ell2]; ring
lemma ell3_zero : ell3 k A B 0 = 6 * B := by simp [ell3]

end KG

open Real

namespace KG

noncomputable def sqA {k : ℕ} (x y : Fin k → ℝ) : ℝ := ∑ i, (x i ^ 2 + y i ^ 2)
noncomputable def dotB {k : ℕ} (x y : Fin k → ℝ) : ℝ := ∑ i, x i * y i

lemma gaussianPairDensity_eq (k : ℕ) (t : ℝ) (x y : Fin k → ℝ) :
    GrothendieckConstant.gaussianPairDensity k t x y = Rho k (sqA x y) (dotB x y) t := by
  unfold GrothendieckConstant.gaussianPairDensity Rho Eexp sqA dotB
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  rw [← Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end KG

/-!
# Uniform bounds on the density derivatives for `|t| ≤ 1/2` (module 3a)
-/

open Real

namespace KG

section
variable {t : ℝ} (ht : |t| ≤ 1 / 2)
include ht

lemma tp (n : ℕ) (X : ℝ) : -|X| ≤ t ^ n * X ∧ t ^ n * X ≤ |X| := by
  have h1 : |t| ≤ 1 := by linarith
  have : |t ^ n * X| ≤ |X| := by
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) h1)
  exact abs_le.mp this

lemma u_ge : 3 / 4 ≤ 1 - t ^ 2 := by
  have : t ^ 2 ≤ 1 / 4 := by
    have := sq_abs t ▸ pow_le_pow_left₀ (abs_nonneg t) ht 2
    nlinarith
  linarith

omit ht in
lemma u_le : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]

variable {A B k : ℝ} (hA : 0 ≤ A) (hB : |B| ≤ A / 2) (hk : 0 ≤ k)
include hA hB hk

lemma abs_ell1 (k' : ℕ) (hk' : (k' : ℝ) = k) : |ell1 k' A B t| ≤ 4 * (1 + A + k) := by
  have hu := u_ge ht
  unfold ell1
  have hd : 0 < (1 - t ^ 2) ^ 2 := pow_pos (by linarith) 2
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, hk']
  have e : B * (1 + t ^ 2) - A * t + k * t * (1 - t ^ 2)
      = B + t ^ 2 * B - t ^ 1 * A + t ^ 1 * k - t ^ 3 * k := by ring
  rw [e]
  have hBA := abs_le.mp hB
  have := tp ht 2 B; have := tp ht 1 A; have := tp ht 1 k; have := tp ht 3 k
  rw [abs_of_nonneg hA] at *; rw [abs_of_nonneg hk] at *
  have hnum : |B + t ^ 2 * B - t ^ 1 * A + t ^ 1 * k - t ^ 3 * k| ≤ 2 * (1 + A + k) := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg B, le_abs_self B, neg_abs_le B]
  have h2 : (9 / 16 : ℝ) ≤ (1 - t ^ 2) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 1 + A + k)]

lemma abs_ell2 (k' : ℕ) (hk' : (k' : ℝ) = k) : |ell2 k' A B t| ≤ 20 * (1 + A + k) := by
  have hu := u_ge ht
  unfold ell2
  have hd : 0 < (1 - t ^ 2) ^ 3 := pow_pos (by linarith) 3
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, hk']
  have e : -3 * A * t ^ 2 - A + 2 * B * t ^ 3 + 6 * B * t - k * t ^ 4 + k
      = -3 * (t ^ 2 * A) - A + 2 * (t ^ 3 * B) + 6 * (t ^ 1 * B) - t ^ 4 * k + k := by ring
  rw [e]
  have := tp ht 2 A; have := tp ht 3 B; have := tp ht 1 B; have := tp ht 4 k
  rw [abs_of_nonneg hA] at *; rw [abs_of_nonneg hk] at *
  have hnum : |-3 * (t ^ 2 * A) - A + 2 * (t ^ 3 * B) + 6 * (t ^ 1 * B) - t ^ 4 * k + k|
      ≤ 8 * (1 + A + k) := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg B]
  have h3 : (27 / 64 : ℝ) ≤ (1 - t ^ 2) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hu 3
    linarith [show ((3:ℝ) / 4) ^ 3 = 27 / 64 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 1 + A + k)]

lemma abs_ell3 (k' : ℕ) (hk' : (k' : ℝ) = k) : |ell3 k' A B t| ≤ 160 * (1 + A + k) := by
  have hu := u_ge ht
  unfold ell3
  have hd : 0 < (1 - t ^ 2) ^ 4 := pow_pos (by linarith) 4
  rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, hk']
  have e : -12 * A * t ^ 3 - 12 * A * t + 6 * B * t ^ 4 + 36 * B * t ^ 2 + 6 * B - 2 * k * t ^ 5
      - 4 * k * t ^ 3 + 6 * k * t
      = -12 * (t ^ 3 * A) - 12 * (t ^ 1 * A) + 6 * (t ^ 4 * B) + 36 * (t ^ 2 * B) + 6 * B
        - 2 * (t ^ 5 * k) - 4 * (t ^ 3 * k) + 6 * (t ^ 1 * k) := by ring
  rw [e]
  have := tp ht 3 A; have := tp ht 1 A; have := tp ht 4 B; have := tp ht 2 B
  have := tp ht 5 k; have := tp ht 3 k; have := tp ht 1 k
  have hBA := abs_le.mp hB
  rw [abs_of_nonneg hA] at *; rw [abs_of_nonneg hk] at *
  have hnum : |-12 * (t ^ 3 * A) - 12 * (t ^ 1 * A) + 6 * (t ^ 4 * B) + 36 * (t ^ 2 * B) + 6 * B
        - 2 * (t ^ 5 * k) - 4 * (t ^ 3 * k) + 6 * (t ^ 1 * k)| ≤ 48 * (1 + A + k) := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg B]
  have h4 : (81 / 256 : ℝ) ≤ (1 - t ^ 2) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num) hu 4
    linarith [show ((3:ℝ) / 4) ^ 4 = 81 / 256 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 1 + A + k)]

lemma Rho_le (k' : ℕ) : 0 < Rho k' A B t ∧ Rho k' A B t ≤ Real.exp (-(A / 4)) := by
  have hu := u_ge ht
  have hu1 := u_le (t := t)
  have hsq : 1 / 2 ≤ Real.sqrt (1 - t ^ 2) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hc0 : 0 < cpref t := by unfold cpref; have := Real.pi_pos; positivity
  have hc1 : cpref t ≤ 1 := by
    unfold cpref
    rw [div_le_one (by have := Real.pi_pos; positivity)]
    nlinarith [Real.pi_gt_three]
  have htB : |t * B| ≤ A / 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg t, abs_nonneg B]
  have hE : Eexp A B t ≤ -(A / 4) := by
    unfold Eexp
    rw [div_le_iff₀ (by linarith), neg_mul, neg_le_neg_iff]
    have := (abs_le.mp htB).2; have := (abs_le.mp htB).1
    nlinarith
  refine ⟨by unfold Rho; positivity, ?_⟩
  unfold Rho
  calc cpref t ^ k' * Real.exp (Eexp A B t) ≤ 1 * Real.exp (-(A / 4)) := by
        gcongr
        · exact pow_le_one₀ hc0.le hc1
    _ = _ := one_mul _

/-- One dominating bound for `Rho`, `D1`, `D2`, `D3` on `|t| ≤ 1/2`. -/
lemma abs_D_le (k' : ℕ) (hk' : (k' : ℝ) = k) :
    |Rho k' A B t| ≤ 500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4)) ∧
    |D1 k' A B t| ≤ 500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4)) ∧
    |D2 k' A B t| ≤ 500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4)) ∧
    |D3 k' A B t| ≤ 500 * (1 + A + k) ^ 3 * Real.exp (-(A / 4)) := by
  obtain ⟨hR0, hR⟩ := Rho_le ht hA hB hk k'
  have h1 := abs_ell1 ht hA hB hk k' hk'
  have h2 := abs_ell2 ht hA hB hk k' hk'
  have h3 := abs_ell3 ht hA hB hk k' hk'
  set M := 1 + A + k with hM
  have hM1 : 1 ≤ M := by linarith
  set e := Real.exp (-(A / 4))
  have he : 0 < e := Real.exp_pos _
  have hRe : |Rho k' A B t| ≤ e := by rw [abs_of_pos hR0]; exact hR
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hM23 : M ^ 2 ≤ M ^ 3 := by
    rw [pow_succ]; nlinarith
  have hM3 : M ≤ M ^ 3 := hM2.trans hM23
  set l1 := ell1 k' A B t; set l2 := ell2 k' A B t; set l3 := ell3 k' A B t
  have hp2 : |l2 + l1 ^ 2| ≤ 36 * M ^ 3 := by
    calc |l2 + l1 ^ 2| ≤ |l2| + |l1| ^ 2 := by
          rw [← abs_pow]; exact abs_add_le _ _
      _ ≤ 20 * M + (4 * M) ^ 2 := by gcongr
      _ ≤ 36 * M ^ 3 := by nlinarith
  have hp3 : |l3 + 3 * l1 * l2 + l1 ^ 3| ≤ 464 * M ^ 3 := by
    calc |l3 + 3 * l1 * l2 + l1 ^ 3| ≤ |l3| + 3 * |l1| * |l2| + |l1| ^ 3 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_pow]
          gcongr
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
      _ ≤ 160 * M + 3 * (4 * M) * (20 * M) + (4 * M) ^ 3 := by gcongr
      _ ≤ 464 * M ^ 3 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · unfold D1; rw [abs_mul]
    calc |Rho k' A B t| * |l1| ≤ e * (4 * M) := by gcongr
      _ ≤ _ := by nlinarith
  · unfold D2; rw [abs_mul]
    calc |Rho k' A B t| * |l2 + l1 ^ 2| ≤ e * (36 * M ^ 3) := by gcongr
      _ ≤ _ := by nlinarith
  · unfold D3; rw [abs_mul]
    calc |Rho k' A B t| * |l3 + 3 * l1 * l2 + l1 ^ 3| ≤ e * (464 * M ^ 3) := by gcongr
      _ ≤ _ := by nlinarith

end

end KG

/-!
# Differentiation of the correlation function under the integral sign (module 3b)
-/

open Real MeasureTheory Filter Topology GrothendieckConstant

set_option linter.unusedSectionVars false

namespace KG

/-- The density and its first three `t`-derivatives. -/
noncomputable def DD (j : ℕ) (k : ℕ) (A B t : ℝ) : ℝ :=
  match j with
  | 0 => Rho k A B t
  | 1 => D1 k A B t
  | 2 => D2 k A B t
  | _ => D3 k A B t

lemma hasDerivAt_DD (j : ℕ) (hj : j < 3) (k : ℕ) (A B : ℝ) {t : ℝ} (ht : 0 < 1 - t ^ 2) :
    HasDerivAt (DD j k A B) (DD (j + 1) k A B t) t := by
  interval_cases j
  · exact hasDerivAt_Rho ht
  · exact hasDerivAt_D1 ht
  · exact hasDerivAt_D2 ht

lemma sqA_nonneg {k : ℕ} (x y : Fin k → ℝ) : 0 ≤ sqA x y :=
  Finset.sum_nonneg fun i _ => by positivity

lemma abs_dotB_le {k : ℕ} (x y : Fin k → ℝ) : |dotB x y| ≤ sqA x y / 2 := by
  unfold dotB sqA
  rw [Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + y i), sq_nonneg (x i - y i)]

lemma abs_DD_le (j : ℕ) (k : ℕ) {t : ℝ} (ht : |t| ≤ 1 / 2) (x y : Fin k → ℝ) :
    |DD j k (sqA x y) (dotB x y) t|
      ≤ 500 * (1 + sqA x y + k) ^ 3 * Real.exp (-(sqA x y / 4)) := by
  obtain ⟨h0, h1, h2, h3⟩ := abs_D_le ht (sqA_nonneg x y) (abs_dotB_le x y) (Nat.cast_nonneg k) k rfl
  match j with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | _ + 3 => exact h3

lemma integrable_exp_sqA (k : ℕ) :
    Integrable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => Real.exp (-(sqA p.1 p.2 / 8))) := by
  have h1 : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (-(1 / 8) * x i ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ s => Real.exp (-(1 / 8) * s ^ 2))
      fun _ => integrable_exp_neg_mul_sq (by norm_num)
  have := h1.mul_prod h1
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, sqA, ← Finset.sum_add_distrib, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section scheme

variable {k : ℕ} (S : KrivineScheme k)

/-- The integrand: `f(x) g(y) ∂ʲρ_t(x, y)`. -/
noncomputable def GG (j : ℕ) (t : ℝ) (p : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  S.f p.1 * S.g p.2 * DD j k (sqA p.1 p.2) (dotB p.1 p.2) t

noncomputable def FF (j : ℕ) (t : ℝ) : ℝ := ∫ p, GG S j t p

noncomputable def domB (k : ℕ) (p : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  2000 * ((1 + k) ^ 3 + 3072) * Real.exp (-(sqA p.1 p.2 / 8))

lemma integrable_domB : Integrable (domB k) :=
  (integrable_exp_sqA k).const_mul _

lemma abs_fg (p : (Fin k → ℝ) × (Fin k → ℝ)) : |S.f p.1 * S.g p.2| = 1 := by
  rcases S.f_sign p.1 with h | h <;> rcases S.g_sign p.2 with h' | h' <;> simp [h, h']

lemma norm_GG_le (j : ℕ) {t : ℝ} (ht : |t| ≤ 1 / 2) (p) : ‖GG S j t p‖ ≤ domB k p := by
  rw [Real.norm_eq_abs, GG, abs_mul, abs_fg, one_mul]
  exact (abs_DD_le j k ht p.1 p.2).trans (poly_exp_le k (sqA_nonneg _ _))

lemma measurable_GG (j : ℕ) (t : ℝ) : Measurable (GG S j t) := by
  have hf : Measurable fun p : (Fin k → ℝ) × (Fin k → ℝ) => S.f p.1 :=
    S.measurable_f.comp measurable_fst
  have hg : Measurable fun p : (Fin k → ℝ) × (Fin k → ℝ) => S.g p.2 :=
    S.measurable_g.comp measurable_snd
  have hA : Measurable fun p : (Fin k → ℝ) × (Fin k → ℝ) => sqA p.1 p.2 := by
    unfold sqA; fun_prop
  have hB : Measurable fun p : (Fin k → ℝ) × (Fin k → ℝ) => dotB p.1 p.2 := by
    unfold dotB; fun_prop
  have hD : ∀ j, Measurable fun q : ℝ × ℝ => DD j k q.1 q.2 t := by
    intro j
    match j with
    | 0 => simp only [DD]; unfold Rho Eexp; fun_prop
    | 1 => simp only [DD]; unfold D1 Rho Eexp ell1; fun_prop
    | 2 => simp only [DD]; unfold D2 Rho Eexp ell1 ell2; fun_prop
    | _ + 3 => simp only [DD]; unfold D3 Rho Eexp ell1 ell2 ell3; fun_prop
  exact (hf.mul hg).mul ((hD j).comp (hA.prodMk hB))

lemma integrable_GG (j : ℕ) {t : ℝ} (ht : |t| ≤ 1 / 2) : Integrable (GG S j t) :=
  (integrable_domB (k := k)).mono' (measurable_GG S j t).aestronglyMeasurable
    (Eventually.of_forall (norm_GG_le S j ht))

lemma hasDerivAt_FF (j : ℕ) (hj : j < 3) {t₀ : ℝ} (ht₀ : |t₀| < 1 / 4) :
    HasDerivAt (FF S j) (FF S (j + 1) t₀) t₀ := by
  have hs : Metric.ball t₀ (1 / 4) ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ (by norm_num)
  have hsub : ∀ t ∈ Metric.ball t₀ (1 / 4), |t| ≤ 1 / 2 := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    linarith
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (bound := domB k)
    (F := fun t p => GG S j t p) (F' := fun t p => GG S (j + 1) t p) hs
    (Eventually.of_forall fun t => (measurable_GG S j t).aestronglyMeasurable)
    (integrable_GG S j (by linarith))
    (measurable_GG S (j + 1) t₀).aestronglyMeasurable
    (Eventually.of_forall fun p t ht => norm_GG_le S (j + 1) (hsub t ht) p)
    integrable_domB
    (Eventually.of_forall fun p t ht => by
      have h := hsub t ht
      have hu : 0 < 1 - t ^ 2 := by
        have : t ^ 2 ≤ 1 / 4 := by
          have := sq_abs t ▸ pow_le_pow_left₀ (abs_nonneg t) h 2
          nlinarith
        linarith
      exact (hasDerivAt_DD j hj k _ _ hu).const_mul _)
  exact this.2

/-- On `|t| ≤ 1/2` the iterated integral defining `correlationFunction` equals a
product-space integral. -/
lemma correlationFunction_eq {t : ℝ} (ht : |t| ≤ 1 / 2) :
    correlationFunction S t = (π / 2) * FF S 0 t := by
  unfold correlationFunction FF
  congr 1
  rw [Measure.volume_eq_prod, integral_prod _ (by
    rw [← Measure.volume_eq_prod]; exact integrable_GG S 0 ht)]
  simp only [GG, DD, gaussianPairDensity_eq]

lemma correlationFunction_eventuallyEq :
    correlationFunction S =ᶠ[𝓝 0] fun t => (π / 2) * FF S 0 t := by
  have : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  filter_upwards [this] with t ht
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  exact correlationFunction_eq S ht.le

lemma coeffLinear_eq : coeffLinear S = (π / 2) * FF S 1 0 := by
  unfold coeffLinear
  rw [(correlationFunction_eventuallyEq S).deriv_eq]
  exact ((hasDerivAt_FF S 0 (by norm_num) (by norm_num)).const_mul _).deriv

lemma coeffCubic_eq : coeffCubic S = (π / 2) * FF S 3 0 / 6 := by
  unfold coeffCubic
  congr 1
  have hball : Metric.ball (0 : ℝ) (1 / 4) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hin : ∀ t ∈ Metric.ball (0 : ℝ) (1 / 4), |t| < 1 / 4 := by
    intro t ht; rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  -- first derivative near 0
  have hd1 : deriv (correlationFunction S) =ᶠ[𝓝 0] fun t => (π / 2) * FF S 1 t := by
    filter_upwards [hball] with t ht
    have hev : correlationFunction S =ᶠ[𝓝 t] fun t => (π / 2) * FF S 0 t := by
      have : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 t :=
        Metric.isOpen_ball.mem_nhds (by
          rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith [hin t ht])
      filter_upwards [this] with s hs
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact correlationFunction_eq S hs.le
    rw [hev.deriv_eq]
    exact ((hasDerivAt_FF S 0 (by norm_num) (hin t ht)).const_mul _).deriv
  have hd2 : deriv (deriv (correlationFunction S)) =ᶠ[𝓝 0] fun t => (π / 2) * FF S 2 t := by
    filter_upwards [hball] with t ht
    have hev : deriv (correlationFunction S) =ᶠ[𝓝 t] fun t => (π / 2) * FF S 1 t := by
      have : Metric.ball (0 : ℝ) (1 / 4) ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
      filter_upwards [this] with s hs
      have hev' : correlationFunction S =ᶠ[𝓝 s] fun t => (π / 2) * FF S 0 t := by
        have : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 s :=
          Metric.isOpen_ball.mem_nhds (by
            rw [Metric.mem_ball, Real.dist_eq, sub_zero]; linarith [hin s hs])
        filter_upwards [this] with r hr
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hr
        exact correlationFunction_eq S hr.le
      rw [hev'.deriv_eq]
      exact ((hasDerivAt_FF S 0 (by norm_num) (hin s hs)).const_mul _).deriv
    rw [hev.deriv_eq]
    exact ((hasDerivAt_FF S 1 (by norm_num) (hin t ht)).const_mul _).deriv
  rw [iteratedDeriv_eq_iterate]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  show deriv (deriv (deriv (correlationFunction S))) 0 = _
  rw [hd2.deriv_eq]
  exact ((hasDerivAt_FF S 2 (by norm_num) (by norm_num)).const_mul _).deriv

end scheme

end KG

/-!
# Third-order Hermite tensors (module 4a, pure algebra)
-/

namespace KG

open Finset

/-- `H3 x i j l = x_i x_j x_l - δ_ij x_l - δ_il x_j - δ_jl x_i`. -/
def H3 {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) : ℝ :=
  x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
    - (if j = l then x i else 0)

lemma sum_H3_mul_H3 {k : ℕ} (x y : Fin k → ℝ) :
    ∑ i, ∑ j, ∑ l, H3 x i j l * H3 y i j l
      = (∑ i, x i * y i) ^ 3
        - 3 * (∑ i, (x i ^ 2 + y i ^ 2)) * (∑ i, x i * y i)
        + (3 * k + 6) * (∑ i, x i * y i) := by
  simp only [H3, sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, sum_sub_distrib,
    sum_ite_eq, sum_ite_eq', mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, if_true, sum_sub_distrib]
  set B := ∑ i, x i * y i
  set X := ∑ i, x i ^ 2
  set Y := ∑ i, y i ^ 2
  have s3 : ∑ a, ∑ b, ∑ c, x a * x b * x c * (y a * y b * y c) = B ^ 3 := by
    simp only [B, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring
  have two : ∀ F G : Fin k → ℝ, ∀ T : Fin k → Fin k → ℝ, (∀ a b, T a b = F a * G b) →
      ∑ a, ∑ b, T a b = (∑ a, F a) * ∑ b, G b := by
    intro F G T h
    simp only [h]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have p1 : ∑ a, ∑ b, x b * (y a * y a * y b) = Y * B :=
    two (fun a => y a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have p2 : ∑ a, ∑ b, x b * (y a * y b * y a) = Y * B :=
    two (fun a => y a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have p3 : ∑ a, ∑ b, x a * (y a * y b * y b) = B * Y :=
    two (fun a => x a * y a) (fun b => y b ^ 2) _ (fun a b => by ring)
  have q1 : ∑ a, ∑ b, x a * x a * x b * y b = X * B :=
    two (fun a => x a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have q2 : ∑ a, ∑ b, x a * x b * x a * y b = X * B :=
    two (fun a => x a ^ 2) (fun b => x b * y b) _ (fun a b => by ring)
  have q3 : ∑ a, ∑ b, x a * x b * x b * y a = B * X :=
    two (fun a => x a * y a) (fun b => x b ^ 2) _ (fun a b => by ring)
  have c1 : ∑ _a : Fin k, ∑ b, x b * y b = k * B := by
    simp [B]
  have c2 : ∑ a, ∑ _b : Fin k, x a * y a = k * B := by
    simp [B, Finset.mul_sum]
  have hXY : ∑ i, (x i ^ 2 + y i ^ 2) = X + Y := sum_add_distrib
  rw [s3, p1, p2, p3, q1, q2, q3, c1, c2, hXY]
  ring

lemma sum_H3_mul_cube {k : ℕ} (x v : Fin k → ℝ) :
    ∑ i, ∑ j, ∑ l, H3 x i j l * (v i * v j * v l)
      = (∑ i, v i * x i) ^ 3 - 3 * (∑ i, v i ^ 2) * (∑ i, v i * x i) := by
  have h := sum_H3_mul_H3 x v
  simp only [H3, sub_mul, ite_mul, zero_mul, sum_sub_distrib, sum_ite_eq, mem_univ, if_true,
    Finset.sum_ite_irrel, sum_const_zero]
  set s := ∑ i, v i * x i
  set V := ∑ i, v i ^ 2
  have two : ∀ F G : Fin k → ℝ, ∀ T : Fin k → Fin k → ℝ, (∀ a b, T a b = F a * G b) →
      ∑ a, ∑ b, T a b = (∑ a, F a) * ∑ b, G b := by
    intro F G T h
    simp only [h]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have s3 : ∑ a, ∑ b, ∑ c, x a * x b * x c * (v a * v b * v c) = s ^ 3 := by
    simp only [s, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    ring
  have p1 : ∑ a, ∑ b, x b * (v a * v a * v b) = V * s :=
    two (fun a => v a ^ 2) (fun b => v b * x b) _ (fun a b => by ring)
  have p2 : ∑ a, ∑ b, x b * (v a * v b * v a) = V * s :=
    two (fun a => v a ^ 2) (fun b => v b * x b) _ (fun a b => by ring)
  have p3 : ∑ a, ∑ b, x a * (v a * v b * v b) = s * V :=
    two (fun a => v a * x a) (fun b => v b ^ 2) _ (fun a b => by ring)
  rw [s3, p1, p2, p3]
  ring

/-- Cauchy–Schwarz for triple sums. -/
lemma sq_sum3_le {k : ℕ} (T W : Fin k → Fin k → Fin k → ℝ) :
    (∑ i, ∑ j, ∑ l, T i j l * W i j l) ^ 2
      ≤ (∑ i, ∑ j, ∑ l, T i j l ^ 2) * (∑ i, ∑ j, ∑ l, W i j l ^ 2) := by
  have e : ∀ F : Fin k → Fin k → Fin k → ℝ,
      ∑ i, ∑ j, ∑ l, F i j l = ∑ p : Fin k × Fin k × Fin k, F p.1 p.2.1 p.2.2 := by
    intro F
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
  rw [e (fun i j l => T i j l * W i j l), e (fun i j l => T i j l ^ 2), e (fun i j l => W i j l ^ 2)]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma sum_cube_sq {k : ℕ} (v : Fin k → ℝ) :
    ∑ i, ∑ j, ∑ l, (v i * v j * v l) ^ 2 = (∑ i, v i ^ 2) ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
  ring

end KG

/-!
# Hermite moments and their integrability (module 4b)
-/

open Real MeasureTheory Filter ProbabilityTheory GrothendieckConstant Finset

set_option linter.unusedSectionVars false

namespace KG

lemma gaussianPDFReal_std (s : ℝ) :
    gaussianPDFReal 0 1 s = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(s ^ 2 / 2)) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

lemma phiK_le_exp {k : ℕ} (x : Fin k → ℝ) : phiK k x ≤ Real.exp (-((∑ i, x i ^ 2) / 2)) := by
  unfold phiK
  rw [show -((∑ i, x i ^ 2) / 2) = ∑ i, -(x i ^ 2 / 2) by rw [sum_div, sum_neg_distrib],
    Real.exp_sum]
  refine prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) fun i _ => ?_
  rw [gaussianPDFReal_std]
  have : 1 ≤ Real.sqrt (2 * π) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x i ^ 2 / 2)) ≤ 1 * Real.exp (-(x i ^ 2 / 2)) := by
        gcongr; exact inv_le_one_of_one_le₀ this
    _ = _ := one_mul _

lemma integrable_exp_Q (k : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Fin k → ℝ => Real.exp (-(b * ∑ i, x i ^ 2))) := by
  have h1 : Integrable (fun x : Fin k → ℝ => ∏ i, Real.exp (-b * x i ^ 2)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun _ s => Real.exp (-b * s ^ 2))
      fun _ => integrable_exp_neg_mul_sq hb
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [← Real.exp_sum, mul_sum, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

/-- A bounded function times a cubic-growth weight times the Gaussian density is integrable. -/
lemma integrable_poly_phi {k : ℕ} (h p : (Fin k → ℝ) → ℝ) (hh : Measurable h)
    (hb : ∀ x, |h x| ≤ 1) (hp : Measurable p) (C : ℝ) (hC : 0 ≤ C)
    (hpC : ∀ x, |p x| ≤ C * (1 + ∑ i, x i ^ 2) ^ 3) :
    Integrable (fun x => h x * p x * phiK k x) := by
  refine ((integrable_exp_Q k (1 / 4) (by norm_num)).const_mul (C * (2000 * 3073 / 500))).mono'
    ((hh.mul hp).mul (measurable_phiK k)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  set Q := ∑ i, x i ^ 2
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have hphi := phiK_le_exp x
  have hphi0 := phiK_nonneg k x
  have key := poly_exp_le 0 (A := 2 * Q) (by positivity)
  simp only [Nat.cast_zero, add_zero] at key
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hphi0]
  have h1 : (1 + Q) ^ 3 ≤ (1 + 2 * Q) ^ 3 := by gcongr; linarith
  have e1 : -(2 * Q / 4) = -(Q / 2) := by ring
  have e2 : -(2 * Q / 8) = -(1 / 4 * Q) := by ring
  rw [e1, e2] at key
  calc |h x| * |p x| * phiK k x ≤ 1 * (C * (1 + Q) ^ 3) * Real.exp (-(Q / 2)) := by
        gcongr
        · exact hb x
        · exact hpC x
    _ ≤ C * ((1 + 2 * Q) ^ 3 * Real.exp (-(Q / 2))) := by
        rw [one_mul, mul_assoc]; gcongr
    _ ≤ C * (2000 * (1 + 3072) / 500 * Real.exp (-(1 / 4 * Q))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        norm_num at key ⊢; linarith
    _ = _ := by norm_num; ring

lemma abs_coord_le {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 + ∑ j, x j ^ 2 := by
  have : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x i + 1 / 2), sq_nonneg (x i - 1 / 2)]

lemma one_le_oneQ {k : ℕ} (x : Fin k → ℝ) : 1 ≤ 1 + ∑ j, x j ^ 2 := by
  have := sum_nonneg (s := univ) fun j _ => sq_nonneg (x j); linarith

lemma abs_coord_le3 {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ 1 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  have h1 := one_le_oneQ x
  have := abs_coord_le x i
  nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 3 by norm_num), pow_one (1 + ∑ j, x j ^ 2)]

lemma abs_H3_le {k : ℕ} (x : Fin k → ℝ) (i j l : Fin k) :
    |H3 x i j l| ≤ 4 * (1 + ∑ j, x j ^ 2) ^ 3 := by
  set M := 1 + ∑ j, x j ^ 2
  have h1 : 1 ≤ M := one_le_oneQ x
  have hi := abs_coord_le x i; have hj := abs_coord_le x j; have hl := abs_coord_le x l
  have hM3 : M ≤ M ^ 3 := by nlinarith [pow_le_pow_right₀ h1 (show 1 ≤ 3 by norm_num)]
  have hprod : |x i * x j * x l| ≤ M ^ 3 := by
    rw [abs_mul, abs_mul, pow_succ, pow_succ, pow_one]
    gcongr
  have hite : ∀ (P : Prop) [Decidable P] (z : ℝ), |z| ≤ M → |(if P then z else 0)| ≤ M ^ 3 := by
    intro P _ z hz
    split_ifs
    · exact hz.trans hM3
    · simp; positivity
  unfold H3
  calc _ ≤ |x i * x j * x l| + |(if i = j then x l else 0)| + |(if i = l then x j else 0)|
        + |(if j = l then x i else 0)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ M ^ 3 + M ^ 3 + M ^ 3 + M ^ 3 := by
        gcongr
        · exact hite _ _ hl
        · exact hite _ _ hj
        · exact hite _ _ hi
    _ = _ := by ring

section scheme
variable {k : ℕ}

/-- First moments `E[h(X) X_i]`. -/
noncomputable def mom1 (h : (Fin k → ℝ) → ℝ) (i : Fin k) : ℝ := ∫ x, h x * x i * phiK k x

/-- Third Hermite moments `E[h(X) H3(X)_{ijl}]`. -/
noncomputable def mom3 (h : (Fin k → ℝ) → ℝ) (i j l : Fin k) : ℝ :=
  ∫ x, h x * H3 x i j l * phiK k x

lemma measurable_H3 (i j l : Fin k) : Measurable fun x : Fin k → ℝ => H3 x i j l := by
  have hite : ∀ (P : Prop) [Decidable P] (m : Fin k),
      Measurable fun x : Fin k → ℝ => if P then x m else 0 := by
    intro P _ m
    by_cases hP : P <;> simp [hP]; fun_prop
  unfold H3
  exact ((((measurable_pi_apply i).mul (measurable_pi_apply j)).mul
    (measurable_pi_apply l)).sub (hite _ l)).sub (hite _ j) |>.sub (hite _ i)

lemma integrable_mom1 (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i : Fin k) : Integrable (fun x => h x * x i * phiK k x) :=
  integrable_poly_phi h (fun x => x i) hh hb (measurable_pi_apply i) 1 zero_le_one
    fun x => abs_coord_le3 x i

lemma integrable_mom3 (h : (Fin k → ℝ) → ℝ) (hh : Measurable h) (hb : ∀ x, |h x| ≤ 1)
    (i j l : Fin k) : Integrable (fun x => h x * H3 x i j l * phiK k x) :=
  integrable_poly_phi h (fun x => H3 x i j l) hh hb (measurable_H3 i j l) 4 (by norm_num)
    fun x => abs_H3_le x i j l

variable (S : KrivineScheme k)

lemma abs_f_le (x : Fin k → ℝ) : |S.f x| ≤ 1 := by
  rcases S.f_sign x with h | h <;> simp [h]

lemma abs_g_le (x : Fin k → ℝ) : |S.g x| ≤ 1 := by
  rcases S.g_sign x with h | h <;> simp [h]

end scheme

end KG

/-!
# The coefficients at `t = 0` as Hermite moment sums (module 4c)
-/

open Real MeasureTheory Filter ProbabilityTheory GrothendieckConstant Finset

set_option linter.unusedSectionVars false

namespace KG

lemma Rho_zero {k : ℕ} (x y : Fin k → ℝ) :
    Rho k (sqA x y) (dotB x y) 0 = phiK k x * phiK k y := by
  unfold Rho cpref Eexp phiK sqA
  rw [← prod_mul_distrib]
  simp only [gaussianPDFReal_std]
  have h2 : Real.sqrt (2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have : ∀ i : Fin k, (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x i ^ 2 / 2)) *
      ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(y i ^ 2 / 2)))
      = (1 / (2 * π)) * Real.exp (-(x i ^ 2 + y i ^ 2) / 2) := by
    intro i
    rw [show -(x i ^ 2 + y i ^ 2) / 2 = -(x i ^ 2 / 2) + -(y i ^ 2 / 2) by ring, Real.exp_add]
    field_simp
    rw [h2]
  rw [prod_congr rfl fun i _ => this i, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  · norm_num
  · rw [← sum_div, sum_neg_distrib]; ring

section scheme
variable {k : ℕ} (S : KrivineScheme k)

lemma FF1_zero : FF S 1 0 = ∑ i, mom1 S.f i * mom1 S.g i := by
  have hpt : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), GG S 1 0 p
      = ∑ i, (S.f p.1 * p.1 i * phiK k p.1) * (S.g p.2 * p.2 i * phiK k p.2) := by
    intro p
    simp only [GG, DD, D1, Rho_zero, ell1_zero]
    unfold dotB
    simp only [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  unfold FF
  simp_rw [hpt]
  have hint : ∀ i, Integrable (fun p : (Fin k → ℝ) × (Fin k → ℝ) =>
      (S.f p.1 * p.1 i * phiK k p.1) * (S.g p.2 * p.2 i * phiK k p.2)) := by
    intro i
    rw [Measure.volume_eq_prod]
    exact (integrable_mom1 _ S.measurable_f (abs_f_le S) i).mul_prod
      (integrable_mom1 _ S.measurable_g (abs_g_le S) i)
  rw [integral_finsetSum _ fun i _ => hint i]
  refine sum_congr rfl fun i _ => ?_
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => S.f x * x i * phiK k x) (fun y => S.g y * y i * phiK k y)

lemma FF3_zero : FF S 3 0 = ∑ i, ∑ j, ∑ l, mom3 S.f i j l * mom3 S.g i j l := by
  have hpt : ∀ p : (Fin k → ℝ) × (Fin k → ℝ), GG S 3 0 p
      = ∑ i, ∑ j, ∑ l, (S.f p.1 * H3 p.1 i j l * phiK k p.1)
          * (S.g p.2 * H3 p.2 i j l * phiK k p.2) := by
    intro p
    have hid := sum_H3_mul_H3 p.1 p.2
    simp only [GG, DD, D3, Rho_zero, ell1_zero, ell2_zero, ell3_zero]
    have e : ∑ i, ∑ j, ∑ l, (S.f p.1 * H3 p.1 i j l * phiK k p.1)
          * (S.g p.2 * H3 p.2 i j l * phiK k p.2)
        = S.f p.1 * S.g p.2 * (phiK k p.1 * phiK k p.2)
          * ∑ i, ∑ j, ∑ l, H3 p.1 i j l * H3 p.2 i j l := by
      simp only [mul_sum]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
      ring
    rw [e, hid]
    unfold sqA dotB
    ring
  unfold FF
  simp_rw [hpt]
  have hint : ∀ i j l, Integrable (fun p : (Fin k → ℝ) × (Fin k → ℝ) =>
      (S.f p.1 * H3 p.1 i j l * phiK k p.1) * (S.g p.2 * H3 p.2 i j l * phiK k p.2)) := by
    intro i j l
    rw [Measure.volume_eq_prod]
    exact (integrable_mom3 _ S.measurable_f (abs_f_le S) i j l).mul_prod
      (integrable_mom3 _ S.measurable_g (abs_g_le S) i j l)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun l _ => hint i j l]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint i j l]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun l _ => hint i j l]
  refine sum_congr rfl fun l _ => ?_
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun x => S.f x * H3 x i j l * phiK k x)
    (fun y => S.g y * H3 y i j l * phiK k y)

/-- **Moment formulas.** `b₁ = (π/2) ⟨a_f, a_g⟩`, `b₃ = (π/12) ⟨T_f, T_g⟩`. -/
theorem coeffLinear_eq_moments : coeffLinear S = (π / 2) * ∑ i, mom1 S.f i * mom1 S.g i := by
  rw [coeffLinear_eq, FF1_zero]

theorem coeffCubic_eq_moments :
    coeffCubic S = (π / 12) * ∑ i, ∑ j, ∑ l, mom3 S.f i j l * mom3 S.g i j l := by
  rw [coeffCubic_eq, FF3_zero]; ring

end scheme

end KG

open MeasureTheory ProbabilityTheory Real GrothendieckConstant

theorem solution (k : ℕ) (S : KrivineScheme k) :
    coeffLinear S = (π / 2) * ∑ i : Fin k,
        (∫ x, S.f x * x i * ∏ m, gaussianPDFReal 0 1 (x m)) *
        (∫ y, S.g y * y i * ∏ m, gaussianPDFReal 0 1 (y m)) ∧
    coeffCubic S = (π / 12) * ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k,
        (∫ x, S.f x * (x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
            - (if j = l then x i else 0)) * ∏ m, gaussianPDFReal 0 1 (x m)) *
        (∫ y, S.g y * (y i * y j * y l - (if i = j then y l else 0) - (if i = l then y j else 0)
            - (if j = l then y i else 0)) * ∏ m, gaussianPDFReal 0 1 (y m)) :=
  ⟨KG.coeffLinear_eq_moments S, KG.coeffCubic_eq_moments S⟩
