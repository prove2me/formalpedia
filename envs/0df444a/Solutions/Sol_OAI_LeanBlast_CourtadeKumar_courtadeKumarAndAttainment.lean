-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.courtadeKumarAndAttainment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T22:07:05.281798+00:00
-- url     : https://prove2.me/submissions/7c3ee175-b38a-411b-b446-53e4a7bd5505

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_mostInformativeBooleanFunction

universe u v

section
section
namespace OAI

/-!
# Polynomial thresholds and average sensitivity

The Boolean cube encodes the sign cube `{−1,1}^n`:
`false` represents `−1` and `true` represents `1`. The public statement
quantifies directly over real multilinear polynomials and uses uniform counting
probability, the convention `sign(0) = 1`, and the exact constant `8`.

`GotsmanLinialStatement` is a proposition definition, not a proof of the bound.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial


/-- Interpret a Boolean cube coordinate as the corresponding real sign. -/
def cubeCoord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

/-- Reverse one coordinate of a cube vertex. -/
def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

/-- The threshold convention assigns `1` at zero. -/
noncomputable def thresholdSign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else -1

end LeanBlast.GotsmanLinial

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar


end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

@[simp] theorem flip_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

@[simp] theorem cubeCoord_flip_same {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord (flip i x) i = -cubeCoord x i := by
  cases hxi : x i <;> simp [cubeCoord, flip, hxi]

@[simp] theorem cubeCoord_sq {n : ℕ} (x : Cube n) (i : Fin n) :
    (cubeCoord x i) ^ 2 = 1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem thresholdSign_zero : thresholdSign 0 = 1 := by
  simp [thresholdSign]

theorem thresholdSign_cases (t : ℝ) : thresholdSign t = 1 ∨ thresholdSign t = -1 := by
  unfold thresholdSign
  split <;> simp

@[simp] theorem thresholdSign_sq (t : ℝ) : thresholdSign t ^ 2 = 1 := by
  rcases thresholdSign_cases t with h | h <;> simp [h]

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

end LeanBlast.GotsmanLinial

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

def noiseKernel {n : ℕ} (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then (1 + u) / 2 else (1 - u) / 2

def noiseOperator {n : ℕ} (u : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, noiseKernel u x y * g y

abbrev flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  LeanBlast.GotsmanLinial.flip i x

def cubeDerivative {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (g x - g (flip i x)) / 2

def psi (v : ℝ) : ℝ :=
  (1 + v) / 2 * Real.log (1 + v) + (1 - v) / 2 * Real.log (1 - v)

def entropy (v : ℝ) : ℝ := ell - psi v

def entropyAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => entropy (g x))

def informationDeficit {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  entropy (cubeAverage g) - entropyAverage g

def dissipation {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  ∑ i, cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i g x)

def signEncoding {n : ℕ} (f : Cube n → Bool) (x : Cube n) : ℝ :=
  if f x then 1 else -1

def restrict {n : ℕ} (g : Cube (n + 1) → ℝ) (b : Bool) (x : Cube n) : ℝ :=
  g (Fin.cases b x)

def pairMean {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x + restrict g false x) / 2

def pairHalfDifference {n : ℕ} (g : Cube (n + 1) → ℝ) (x : Cube n) : ℝ :=
  (restrict g true x - restrict g false x) / 2

def pairEntropyGap (a b : ℝ) : ℝ :=
  entropy a - (entropy (a + b) + entropy (a - b)) / 2

def pairDissipation (a b : ℝ) : ℝ :=
  b / 2 * (Real.artanh (a + b) - Real.artanh (a - b))

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open scoped BigOperators

noncomputable section


namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n :=
  LeanBlast.GotsmanLinial.card_cube n

theorem cube_denominator_pos (n : ℕ) : 0 < (2 : ℝ) ^ n := by positivity

@[simp] theorem cubeAverage_const (n : ℕ) (c : ℝ) :
    cubeAverage (fun _ : Cube n => c) = c := by
  simp [cubeAverage]

theorem cubeAverage_add (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x + h x) = cubeAverage g + cubeAverage h := by
  simp [cubeAverage, Finset.sum_add_distrib, add_div]

theorem cubeAverage_sub (g h : Cube n → ℝ) :
    cubeAverage (fun x => g x - h x) = cubeAverage g - cubeAverage h := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]

theorem cubeAverage_neg (g : Cube n → ℝ) :
    cubeAverage (fun x => -g x) = -cubeAverage g := by
  simp [cubeAverage, neg_div]

theorem cubeAverage_smul (c : ℝ) (g : Cube n → ℝ) :
    cubeAverage (fun x => c * g x) = c * cubeAverage g := by
  simp [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

theorem cubeAverage_nonneg {g : Cube n → ℝ} (hg : ∀ x, 0 ≤ g x) :
    0 ≤ cubeAverage g :=
  div_nonneg (Finset.sum_nonneg fun x _ => hg x) (le_of_lt (cube_denominator_pos n))

theorem noiseKernel_symm (u : ℝ) (x y : Cube n) :
    noiseKernel u x y = noiseKernel u y x := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : x i = y i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem noiseKernel_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel u x y := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem noiseKernel_row_sum (u : ℝ) (x : Cube n) :
    ∑ y, noiseKernel u x y = 1 := by
  unfold noiseKernel
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if x i = b then (1 + u) / 2 else (1 - u) / 2)]
  have hfactor : ∀ i : Fin n,
      (∑ b : Bool, if x i = b then (1 + u) / 2 else (1 - u) / 2) = 1 := by
    intro i
    cases x i <;> simp <;> ring
  simp_rw [hfactor]
  simp

theorem noiseKernel_col_sum (u : ℝ) (y : Cube n) :
    ∑ x, noiseKernel u x y = 1 := by
  simp_rw [noiseKernel_symm u]
  exact noiseKernel_row_sum u y

@[simp] theorem noiseOperator_const (u c : ℝ) (x : Cube n) :
    noiseOperator u (fun _ => c) x = c := by
  rw [noiseOperator, ← Finset.sum_mul, noiseKernel_row_sum, one_mul]

theorem noiseOperator_add (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y + h y) x = noiseOperator u g x + noiseOperator u h x := by
  simp [noiseOperator, mul_add, Finset.sum_add_distrib]

theorem noiseOperator_sub (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y - h y) x = noiseOperator u g x - noiseOperator u h x := by
  simp [noiseOperator, mul_sub, Finset.sum_sub_distrib]

theorem noiseOperator_neg (u : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => -g y) x = -noiseOperator u g x := by
  simp [noiseOperator]

theorem noiseOperator_smul (u c : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => c * g y) x = c * noiseOperator u g x := by
  simp [noiseOperator, Finset.mul_sum, mul_left_comm]

theorem cubeAverage_noiseOperator (u : ℝ) (g : Cube n → ℝ) :
    cubeAverage (noiseOperator u g) = cubeAverage g := by
  unfold cubeAverage noiseOperator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, noiseKernel_col_sum, one_mul]

theorem noiseOperator_prod (u : ℝ) (f : Fin n → Bool → ℝ) (x : Cube n) :
    noiseOperator u (fun y => ∏ i, f i (y i)) x =
      ∏ i, ∑ b : Bool, (if x i = b then (1 + u) / 2 else (1 - u) / 2) * f i b := by
  unfold noiseOperator noiseKernel
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if x i = b then (1 + u) / 2 else (1 - u) / 2) * f i b)).symm

@[simp] theorem noiseKernel_zero (x y : Cube n) :
    noiseKernel 0 x y = 1 / (2 : ℝ) ^ n := by
  simp [noiseKernel, one_div]

@[simp] theorem noiseOperator_zero_correlation (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator 0 g x = cubeAverage g := by
  simp only [noiseOperator, noiseKernel_zero, ← Finset.mul_sum]
  unfold cubeAverage
  ring

@[simp] theorem noiseKernel_one (x y : Cube n) :
    noiseKernel 1 x y = if x = y then 1 else 0 := by
  simp only [noiseKernel, add_self_div_two, sub_self, zero_div]
  rw [Fintype.prod_boole]
  simp only [← funext_iff]

@[simp] theorem noiseOperator_one (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator 1 g x = g x := by
  simp [noiseOperator]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, xlogx]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, xlogx]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem ell_pos : 0 < ell := Real.log_pos (by norm_num)

@[simp] theorem psi_zero : psi 0 = 0 := by norm_num [psi]
@[simp] theorem psi_one : psi 1 = ell := by norm_num [psi, ell]

@[simp] theorem psi_neg (v : ℝ) : psi (-v) = psi v := by
  simp only [psi, sub_eq_add_neg, neg_neg]
  ring

@[simp] theorem psi_neg_one : psi (-1) = ell := by rw [psi_neg, psi_one]

@[simp] theorem entropy_zero : entropy 0 = ell := by simp [entropy]
@[simp] theorem entropy_one : entropy 1 = 0 := by simp [entropy]
@[simp] theorem entropy_neg (v : ℝ) : entropy (-v) = entropy v := by simp [entropy]
@[simp] theorem entropy_neg_one : entropy (-1) = 0 := by simp

theorem entropy_eq_binEntropy (v : ℝ) :
    entropy v = Real.binEntropy ((1 + v) / 2) := by
  have hs (t : ℝ) : Real.negMulLog (t / 2) =
      -(t / 2) * Real.log t + (t / 2) * ell := by
    calc
      _ = (2 : ℝ)⁻¹ * Real.negMulLog t + t * Real.negMulLog ((2 : ℝ)⁻¹) := by
        simpa [div_eq_mul_inv] using Real.negMulLog_mul t ((2 : ℝ)⁻¹)
      _ = _ := by simp [Real.negMulLog, ell, Real.log_inv]; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show 1 - (1 + v) / 2 = (1 - v) / 2 by ring, hs, hs]
  unfold entropy psi
  ring

theorem strictMonoOn_psi : StrictMonoOn psi (Icc 0 1) := by
  intro x hx y hy hxy
  have h := Real.binEntropy_strictAntiOn
    (show (1 + x) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hx.1, hx.2])
    (show (1 + y) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hy.1, hy.2])
    (show (1 + x) / 2 < (1 + y) / 2 by linarith)
  rw [← entropy_eq_binEntropy, ← entropy_eq_binEntropy] at h
  unfold entropy at h
  linarith

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators


namespace LeanBlast.CourtadeKumar

theorem xlogx_mul (a b : ℝ) :
    xlogx (a * b) = a * xlogx b + b * xlogx a := by
  by_cases ha : a = 0
  · simp [ha, xlogx]
  by_cases hb : b = 0
  · simp [hb, xlogx]
  simp only [xlogx, Real.log_mul ha hb]
  ring

theorem finite_kl_eq_entropy_sums {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (j : A → B → ℝ) (hj : ∀ a b, 0 ≤ j a b) :
    (∑ a : A, ∑ b : B,
      if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      (∑ a : A, ∑ b : B, xlogx (j a b)) -
        (∑ a : A, xlogx (∑ b : B, j a b)) -
        (∑ b : B, xlogx (∑ a : A, j a b)) := by
  classical
  have hterm (a : A) (b : B) :
      (if 0 < j a b then j a b * Real.log
        (j a b / ((∑ z : B, j a z) * (∑ z : A, j z b))) else 0) =
      xlogx (j a b) - j a b * Real.log (∑ z : B, j a z) -
        j a b * Real.log (∑ z : A, j z b) := by
    by_cases hp : 0 < j a b
    · have hr : 0 < ∑ z : B, j a z := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj a z) (Finset.mem_univ b))
      have hc : 0 < ∑ z : A, j z b := lt_of_lt_of_le hp
        (Finset.single_le_sum (fun z _ => hj z b) (Finset.mem_univ a))
      rw [if_pos hp, Real.log_div (ne_of_gt hp) (ne_of_gt (mul_pos hr hc)),
        Real.log_mul (ne_of_gt hr) (ne_of_gt hc)]
      unfold xlogx
      ring
    · have hz : j a b = 0 := le_antisymm (le_of_not_gt hp) (hj a b)
      simp [hz, xlogx]
  have hrow : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : B, j a z)) =
      ∑ a : A, xlogx (∑ b : B, j a b) := by
    simp only [xlogx, Finset.sum_mul]
  have hcol : (∑ a : A, ∑ b : B, j a b * Real.log (∑ z : A, j z b)) =
      ∑ b : B, xlogx (∑ a : A, j a b) := by
    rw [Finset.sum_comm]
    simp only [xlogx, Finset.sum_mul]
  simp_rw [hterm, Finset.sum_sub_distrib]
  rw [hrow, hcol]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def signProbability (v : ℝ) (b : Bool) : ℝ :=
  if b then (1 + v) / 2 else (1 - v) / 2

theorem sum_signProbability (v : ℝ) : (∑ b : Bool, signProbability v b) = 1 := by
  simp only [Fintype.sum_bool, signProbability, Bool.false_eq_true, ite_false, ite_true]
  ring

theorem signProbability_signEncoding (f : Cube n → Bool) (x : Cube n) (b : Bool) :
    signProbability (signEncoding f x) b = if f x = b then 1 else 0 := by
  cases b <;> cases hfx : f x <;> simp [signProbability, signEncoding, hfx]

theorem noiseOperator_signProbability (u : ℝ) (g : Cube n → ℝ) (b : Bool) (x : Cube n) :
    noiseOperator u (fun y => signProbability (g y) b) x =
      signProbability (noiseOperator u g x) b := by
  cases b
  · change noiseOperator u (fun y => (1 - g y) / 2) x = (1 - noiseOperator u g x) / 2
    have hfun : (fun y => (1 - g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 - g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_sub, noiseOperator_const]
    ring
  · change noiseOperator u (fun y => (1 + g y) / 2) x = (1 + noiseOperator u g x) / 2
    have hfun : (fun y => (1 + g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 + g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_add, noiseOperator_const]
    ring

theorem cubeAverage_signProbability (g : Cube n → ℝ) (b : Bool) :
    cubeAverage (fun x => signProbability (g x) b) = signProbability (cubeAverage g) b := by
  cases b
  · change cubeAverage (fun y => (1 - g y) / 2) = (1 - cubeAverage g) / 2
    have hfun : (fun y => (1 - g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 - g y)) := by
      funext y
      ring
    rw [hfun, cubeAverage_smul, cubeAverage_sub, cubeAverage_const]
    ring
  · change cubeAverage (fun y => (1 + g y) / 2) = (1 + cubeAverage g) / 2
    have hfun : (fun y => (1 + g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 + g y)) := by
      funext y
      ring
    rw [hfun, cubeAverage_smul, cubeAverage_add, cubeAverage_const]
    ring

theorem bitFlipKernel_eq_noiseKernel (ε : ℝ) (x y : Cube n) :
    bitFlipKernel ε x y = noiseKernel (1 - 2 * ε) x y := by
  unfold bitFlipKernel noiseKernel
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> ring

theorem bitFlipKernel_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2)
    (x y : Cube n) : 0 ≤ bitFlipKernel ε x y := by
  rw [bitFlipKernel_eq_noiseKernel]
  exact noiseKernel_nonneg (by linarith) (by linarith) x y

theorem jointProbability_eq_posterior (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    jointProbability ε f b y =
      signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b / (2 : ℝ) ^ n := by
  have hterm (x : Cube n) :
      (if f x = b then bitFlipKernel ε x y else 0) =
        noiseKernel (1 - 2 * ε) y x * signProbability (signEncoding f x) b := by
    rw [signProbability_signEncoding]
    by_cases h : f x = b
    · simp only [h, ite_true, mul_one, bitFlipKernel_eq_noiseKernel]
      exact noiseKernel_symm _ x y
    · simp [h]
  unfold jointProbability cubeAverage
  simp_rw [hterm]
  change noiseOperator (1 - 2 * ε) (fun x => signProbability (signEncoding f x) b) y /
    (2 : ℝ) ^ n = _
  rw [noiseOperator_signProbability]

theorem functionMarginal_eq_signProbability (ε : ℝ) (f : Cube n → Bool) (b : Bool) :
    functionMarginal ε f b = signProbability (cubeAverage (signEncoding f)) b := by
  unfold functionMarginal
  simp_rw [jointProbability_eq_posterior]
  rw [← Finset.sum_div]
  change cubeAverage (fun y => signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b) = _
  rw [cubeAverage_signProbability, cubeAverage_noiseOperator]

theorem observationMarginal_eq_uniform (ε : ℝ) (f : Cube n → Bool) (y : Cube n) :
    observationMarginal ε f y = 1 / (2 : ℝ) ^ n := by
  unfold observationMarginal
  simp_rw [jointProbability_eq_posterior]
  rw [← Finset.sum_div, sum_signProbability]

theorem jointProbability_nonneg (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) (b : Bool) (y : Cube n) :
    0 ≤ jointProbability ε f b y := by
  apply cubeAverage_nonneg
  intro x
  split_ifs
  · exact bitFlipKernel_nonneg hε0 hεhalf x y
  · exact le_refl 0

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem sum_xlogx_signProbability (v : ℝ) :
    (∑ b : Bool, xlogx (signProbability v b)) = -entropy v := by
  rw [entropy_eq_binEntropy]
  have hhalf : 1 - (1 + v) / 2 = (1 - v) / 2 := by ring
  simp only [Fintype.sum_bool, signProbability, Bool.false_eq_true, ite_false, ite_true]
  rw [Real.binEntropy, hhalf]
  simp only [Real.log_inv, xlogx]
  ring

theorem binaryEntropy_eq_binEntropy (ε : ℝ) :
    binaryEntropy ε = Real.binEntropy ε / ell := by
  unfold binaryEntropy xlogx Real.binEntropy
  simp only [Real.log_inv]
  ring

theorem one_sub_binaryEntropy_eq_psi (ε : ℝ) :
    1 - binaryEntropy ε = psi (1 - 2 * ε) / ell := by
  rw [binaryEntropy_eq_binEntropy]
  have h := entropy_eq_binEntropy (1 - 2 * ε)
  rw [show (1 + (1 - 2 * ε)) / 2 = 1 - ε by ring, Real.binEntropy_one_sub] at h
  rw [← h]
  unfold entropy
  field_simp [ne_of_gt ell_pos]
  ring

theorem joint_xlogx_sum_bool (ε : ℝ) (f : Cube n → Bool) (y : Cube n) :
    (∑ b : Bool, xlogx (jointProbability ε f b y)) =
      xlogx (((2 : ℝ) ^ n)⁻¹) -
        entropy (noiseOperator (1 - 2 * ε) (signEncoding f) y) / (2 : ℝ) ^ n := by
  simp_rw [jointProbability_eq_posterior, div_eq_mul_inv, xlogx_mul]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_signProbability, sum_xlogx_signProbability]
  ring

theorem joint_xlogx_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ b : Bool, ∑ y : Cube n, xlogx (jointProbability ε f b y)) =
      (2 : ℝ) ^ n * xlogx (((2 : ℝ) ^ n)⁻¹) -
        entropyAverage (noiseOperator (1 - 2 * ε) (signEncoding f)) := by
  rw [Finset.sum_comm]
  simp_rw [joint_xlogx_sum_bool]
  simp [Finset.sum_sub_distrib, entropyAverage, cubeAverage, Finset.sum_div]

theorem functionMarginal_xlogx_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ b : Bool, xlogx (functionMarginal ε f b)) =
      -entropy (cubeAverage (signEncoding f)) := by
  simp_rw [functionMarginal_eq_signProbability]
  exact sum_xlogx_signProbability _

theorem observationMarginal_xlogx_sum (ε : ℝ) (f : Cube n → Bool) :
    (∑ y : Cube n, xlogx (observationMarginal ε f y)) =
      (2 : ℝ) ^ n * xlogx (((2 : ℝ) ^ n)⁻¹) := by
  simp [observationMarginal_eq_uniform, one_div]

theorem mutualInformation_eq_informationDeficit (ε : ℝ) (f : Cube n → Bool)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) :
    mutualInformation ε f =
      informationDeficit (noiseOperator (1 - 2 * ε) (signEncoding f)) / ell := by
  unfold mutualInformation functionMarginal observationMarginal
  rw [finite_kl_eq_entropy_sums (jointProbability ε f)
    (jointProbability_nonneg ε f hε0 hεhalf)]
  change ((∑ b : Bool, ∑ y : Cube n, xlogx (jointProbability ε f b y)) -
    (∑ b : Bool, xlogx (functionMarginal ε f b)) -
    (∑ y : Cube n, xlogx (observationMarginal ε f y))) / ell = _
  rw [joint_xlogx_sum, functionMarginal_xlogx_sum, observationMarginal_xlogx_sum]
  unfold informationDeficit
  rw [cubeAverage_noiseOperator]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseOperator_dictator (u : ℝ) (i : Fin n) (x : Cube n) :
    noiseOperator u (signEncoding (dictator i)) x =
      u * signEncoding (dictator i) x := by
  let a : Fin n → Bool → ℝ :=
    fun j b => if j = i then (if b then 1 else -1) else 1
  have hprod : (fun y : Cube n => ∏ j, a j (y j)) = signEncoding (dictator i) := by
    funext y
    simp [a, signEncoding, dictator]
    rfl
  have hfactor (j : Fin n) :
      (∑ b : Bool, (if x j = b then (1 + u) / 2 else (1 - u) / 2) * a j b) =
        if j = i then u * signEncoding (dictator i) x else 1 := by
    by_cases hji : j = i
    · subst j
      cases hx : x i <;> simp [a, hx, signEncoding, dictator] <;> ring
    · cases hx : x j <;> simp [a, hji] <;> ring
  calc
    _ = noiseOperator u (fun y => ∏ j, a j (y j)) x := by rw [hprod]
    _ = ∏ j, ∑ b : Bool,
        (if x j = b then (1 + u) / 2 else (1 - u) / 2) * a j b :=
      noiseOperator_prod u a x
    _ = u * signEncoding (dictator i) x := by simp_rw [hfactor]; simp

theorem cubeAverage_dictator (i : Fin n) : cubeAverage (signEncoding (dictator i)) = 0 := by
  simpa only [noiseOperator_zero_correlation, zero_mul] using
    noiseOperator_dictator 0 i (fun _ => false)

theorem signEncoding_complementDictator (i : Fin n) :
    signEncoding (complementDictator i) = fun x => -signEncoding (dictator i) x := by
  funext x
  cases hx : x i <;> simp [signEncoding, complementDictator, dictator, hx]

@[simp] theorem entropyAverage_const (c : ℝ) :
    entropyAverage (fun _ : Cube n => c) = entropy c :=
  cubeAverage_const n (entropy c)

@[simp] theorem informationDeficit_const (c : ℝ) :
    informationDeficit (fun _ : Cube n => c) = 0 := by
  simp [informationDeficit]

theorem entropyAverage_neg (g : Cube n → ℝ) :
    entropyAverage (fun x => -g x) = entropyAverage g := by
  simp [entropyAverage]

theorem informationDeficit_neg (g : Cube n → ℝ) :
    informationDeficit (fun x => -g x) = informationDeficit g := by
  simp only [informationDeficit, cubeAverage_neg, entropy_neg, entropyAverage_neg]

@[simp] theorem informationDeficit_noise_const (u c : ℝ) :
    informationDeficit (noiseOperator u (fun _ : Cube n => c)) = 0 := by
  have h : noiseOperator u (fun _ : Cube n => c) = fun _ => c := by
    funext x
    exact noiseOperator_const u c x
  rw [h, informationDeficit_const]

@[simp] theorem informationDeficit_noise_zero (g : Cube n → ℝ) :
    informationDeficit (noiseOperator 0 g) = 0 := by
  have h : noiseOperator 0 g = fun _ => cubeAverage g := by
    funext x
    exact noiseOperator_zero_correlation g x
  rw [h, informationDeficit_const]

theorem informationDeficit_noise_dictator (u : ℝ) (i : Fin n) :
    informationDeficit (noiseOperator u (signEncoding (dictator i))) = psi u := by
  have he : entropyAverage (noiseOperator u (signEncoding (dictator i))) = entropy u := by
    have hpoint :
        (fun x => entropy (noiseOperator u (signEncoding (dictator i)) x)) =
          fun _ : Cube n => entropy u := by
      funext x
      rw [noiseOperator_dictator]
      cases hx : x i <;> simp [signEncoding, dictator, hx]
    unfold entropyAverage
    rw [hpoint, cubeAverage_const]
  rw [informationDeficit, cubeAverage_noiseOperator, cubeAverage_dictator,
    entropy_zero, he]
  simp [entropy]

theorem informationDeficit_noise_complementDictator (u : ℝ) (i : Fin n) :
    informationDeficit (noiseOperator u (signEncoding (complementDictator i))) = psi u := by
  rw [signEncoding_complementDictator]
  have h : noiseOperator u (fun x => -signEncoding (dictator i) x) =
      fun x => -noiseOperator u (signEncoding (dictator i)) x := by
    funext x
    exact noiseOperator_neg u (signEncoding (dictator i)) x
  rw [h, informationDeficit_neg, informationDeficit_noise_dictator]

theorem mutualInformation_dictator (ε : ℝ) (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2)
    (i : Fin n) : mutualInformation ε (dictator i) = 1 - binaryEntropy ε := by
  rw [mutualInformation_eq_informationDeficit ε (dictator i) hε0 hεhalf,
    informationDeficit_noise_dictator, one_sub_binaryEntropy_eq_psi]

theorem mutualInformation_complementDictator (ε : ℝ) (hε0 : 0 ≤ ε)
    (hεhalf : ε ≤ (1 : ℝ) / 2) (i : Fin n) :
    mutualInformation ε (complementDictator i) = 1 - binaryEntropy ε := by
  rw [mutualInformation_eq_informationDeficit ε (complementDictator i) hε0 hεhalf,
    informationDeficit_noise_complementDictator, one_sub_binaryEntropy_eq_psi]

theorem dictatorAttainment : DictatorAttainmentStatement := by
  intro n _ ε hε0 hεhalf i
  exact ⟨mutualInformation_dictator ε hε0 hεhalf i,
    mutualInformation_complementDictator ε hε0 hεhalf i⟩

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def setBit (i : Fin n) (b : Bool) (x : Cube n) : Cube n := Function.update x i b

@[simp] theorem setBit_apply_same (i : Fin n) (b : Bool) (x : Cube n) :
    setBit i b x i = b := Function.update_self _ _ _

@[simp] theorem setBit_self (i : Fin n) (x : Cube n) : setBit i (x i) x = x :=
  Function.update_eq_self _ _

@[simp] theorem setBit_setBit (i : Fin n) (a b : Bool) (x : Cube n) :
    setBit i b (setBit i a x) = setBit i b x := Function.update_idem _ _ _

def sortCoordinate (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  if x i then max (F (setBit i false x)) (F (setBit i true x))
  else min (F (setBit i false x)) (F (setBit i true x))

@[simp] theorem sortCoordinate_false (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    sortCoordinate i F (setBit i false x) =
      min (F (setBit i false x)) (F (setBit i true x)) := by
  simp [sortCoordinate]

@[simp] theorem sortCoordinate_true (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    sortCoordinate i F (setBit i true x) =
      max (F (setBit i false x)) (F (setBit i true x)) := by
  simp [sortCoordinate]

def coordinatePairMean (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i false x) + F (setBit i true x)) / 2

def coordinatePairDifference (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i true x) - F (setBit i false x)) / 2

@[simp] theorem coordinatePairMean_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    coordinatePairMean i (sortCoordinate i F) = coordinatePairMean i F := by
  funext x
  simp only [coordinatePairMean, sortCoordinate_false, sortCoordinate_true, min_add_max]

@[simp] theorem coordinatePairDifference_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    coordinatePairDifference i (sortCoordinate i F) =
      fun x => |coordinatePairDifference i F x| := by
  funext x
  simp only [coordinatePairDifference, sortCoordinate_false, sortCoordinate_true]
  rcases le_total (F (setBit i false x)) (F (setBit i true x)) with h | h
  · rw [min_eq_left h, max_eq_right h, abs_of_nonneg (div_nonneg (sub_nonneg.mpr h) (by norm_num))]
  · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr h) (by norm_num))]
    ring

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def psiInv (s : ℝ) : ℝ := Function.invFunOn psi (Set.Icc 0 1) s

def r (s : ℝ) : ℝ := psiInv s * Real.artanh (psiInv s)

def rDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 2 else
    1 + psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s))

def rSecondDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 4 / 3 else
    (((1 + (psiInv s) ^ 2) * Real.artanh (psiInv s) - psiInv s) /
      ((1 - (psiInv s) ^ 2) ^ 2 * (Real.artanh (psiInv s)) ^ 3))

def rGap (s : ℝ) : ℝ := r s - 2 * s

def s0 : ℝ := psi (1 / 5)

def K (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rGap s else rGap s0 + (rDeriv s0 - 2) * (s - s0)

def KDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rDeriv s - 2 else rDeriv s0 - 2

@[simp] theorem rDeriv_zero : rDeriv 0 = 2 := by simp [rDeriv]
@[simp] theorem rSecondDeriv_zero : rSecondDeriv 0 = 4 / 3 := by simp [rSecondDeriv]
@[simp] theorem K_zero : K 0 = 0 := by simp [K]
@[simp] theorem KDeriv_zero : KDeriv 0 = 0 := by simp [KDeriv]

theorem psiInv_psi {u : ℝ} (hu : u ∈ Icc 0 1) : psiInv (psi u) = u :=
  strictMonoOn_psi.injOn.leftInvOn_invFunOn hu

@[simp] theorem psiInv_zero : psiInv 0 = 0 := by
  simpa only [psi_zero] using psiInv_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem psiInv_ell : psiInv ell = 1 := by
  simpa only [psi_one] using psiInv_psi (show (1 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem r_zero : r 0 = 0 := by simp [r]
@[simp] theorem rGap_zero : rGap 0 = 0 := by simp [rGap]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Filter Set
open scoped Topology

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiCoeff (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1))

@[simp] theorem psiCoeff_zero : psiCoeff 0 = 1 / 2 := by norm_num [psiCoeff]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def noiseFlow (F : Cube n → ℝ) (t : ℝ) : Cube n → ℝ :=
  noiseOperator (Real.exp (-t)) F

@[simp]
theorem noiseFlow_zero (F : Cube n → ℝ) : noiseFlow F 0 = F := by
  funext x
  simp [noiseFlow]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def cubeSplitEquiv (n : ℕ) : Bool × Cube n ≃ Cube (n + 1) where
  toFun z := Fin.cases z.1 z.2
  invFun x := (x 0, fun i => x i.succ)
  left_inv z := by cases z; rfl
  right_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem sum_cube_split (g : Cube (n + 1) → ℝ) :
    (∑ x, g x) = (∑ x, restrict g true x) + ∑ x, restrict g false x := by
  rw [← (cubeSplitEquiv n).sum_comp g, Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

theorem cubeAverage_split (g : Cube (n + 1) → ℝ) :
    cubeAverage g = (cubeAverage (restrict g true) + cubeAverage (restrict g false)) / 2 := by
  unfold cubeAverage
  rw [sum_cube_split, pow_succ]
  have hN : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (cube_denominator_pos n)
  field_simp

theorem cubeAverage_div (g : Cube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => g x / c) = cubeAverage g / c := by
  simp only [cubeAverage, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  ring

theorem cubeAverage_half_sum (g h : Cube n → ℝ) :
    cubeAverage (fun x => (g x + h x) / 2) = (cubeAverage g + cubeAverage h) / 2 := by
  rw [cubeAverage_div, cubeAverage_add]

theorem cubeAverage_split_pair (g : Cube (n + 1) → ℝ) :
    cubeAverage g = cubeAverage (fun x => (restrict g true x + restrict g false x) / 2) := by
  rw [cubeAverage_half_sum, cubeAverage_split]

@[simp] theorem pairMean_add_halfDifference (g : Cube (n + 1) → ℝ) (x : Cube n) :
    pairMean g x + pairHalfDifference g x = restrict g true x := by
  unfold pairMean pairHalfDifference
  ring

@[simp] theorem pairMean_sub_halfDifference (g : Cube (n + 1) → ℝ) (x : Cube n) :
    pairMean g x - pairHalfDifference g x = restrict g false x := by
  unfold pairMean pairHalfDifference
  ring

@[simp] theorem cubeAverage_pairMean (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) = cubeAverage g := by
  exact (cubeAverage_split_pair g).symm

theorem cubeAverage_dim_zero (g : Cube 0 → ℝ) :
    cubeAverage g = g (fun i => Fin.elim0 i) := by
  have heq : g = fun _ => g (fun i => Fin.elim0 i) := by
    funext x
    congr 1
    exact Subsingleton.elim _ _
  rw [heq, cubeAverage_const]

@[simp] theorem informationDeficit_dim_zero (g : Cube 0 → ℝ) : informationDeficit g = 0 := by
  simp only [informationDeficit, entropyAverage, cubeAverage_dim_zero]
  ring

@[simp] theorem dissipation_dim_zero (g : Cube 0 → ℝ) : dissipation g = 0 := by
  simp [dissipation]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

@[simp] theorem pairEntropyGap_zero (a : ℝ) : pairEntropyGap a 0 = 0 := by
  simp [pairEntropyGap]

@[simp] theorem pairDissipation_zero (a : ℝ) : pairDissipation a 0 = 0 := by
  simp [pairDissipation]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def lambda (z : ℝ) : ℝ := if z = 0 then 1 else -Real.log (1 - z) / z

@[simp] theorem lambda_zero : lambda 0 = 1 := by simp [lambda]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators


namespace LeanBlast.CourtadeKumar

section Weighted

variable {ι : Type u} [Fintype ι]

end Weighted

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter


namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

noncomputable def rawPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  (1 + a) / 2 * (b / (1 + a)) ^ (2 * j) +
    (1 - a) / 2 * (b / (1 - a)) ^ (2 * j)

noncomputable def normalizedPairMoment (a b : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else rawPairMoment a b j / (1 - a ^ 2)

@[simp]
theorem normalizedPairMoment_zero (a b : ℝ) : normalizedPairMoment a b 0 = 1 := by
  simp [normalizedPairMoment]

@[simp]
theorem normalizedPairMoment_succ (a b : ℝ) (j : ℕ) :
    normalizedPairMoment a b (j + 1) = rawPairMoment a b (j + 1) / (1 - a ^ 2) := by
  simp [normalizedPairMoment]

end LeanBlast.CourtadeKumar

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def logBarrier (b : ℝ) : ℝ := -Real.log (1 - b)

@[simp] theorem logBarrier_zero : logBarrier 0 = 0 := by simp [logBarrier]

def lambdaAuxiliary (b : ℝ) : ℝ :=
  3 * logBarrier (b ^ 4) - b ^ 3 * logBarrier b - b ^ 2 * logBarrier (b ^ 2)

@[simp] theorem lambdaAuxiliary_zero : lambdaAuxiliary 0 = 0 := by
  simp [lambdaAuxiliary]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

open Set

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end OAI

end
end

section
section
namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def comparisonKernel (s : ℝ) : ℝ := 1 / (s ^ 2 * Real.artanh s)

@[simp] theorem comparisonKernel_one : comparisonKernel 1 = 0 := by
  norm_num [comparisonKernel, Real.artanh]

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

end LeanBlast.CourtadeKumar

end

end OAI

end
end

section
section
/-! Transfer of OpenAI's Courtade–Kumar bound (OpenAI Math Release, https://github.com/openai/math,
`OAI.LeanBlast.CourtadeKumar.courtadeKumar_bound`, the bound behind
`courtadeKumarAndAttainment`) to the published `GeneralCK.GeneralCourtadeKumar`.

* For `0 ≤ p ≤ 1/2` the published mutual information `H(f(X)) + H(Y) - H(f(X),Y)` equals
  OpenAI's Kullback–Leibler form `∑ J log (J / (P Q)) / log 2` (`finite_kl_eq_entropy_sums`),
  and the two binary entropies agree.
* For `1/2 < p ≤ 1`, relabelling `Y ↦ ¬Y` turns crossover `p` into `1 - p` and leaves the
  mutual information unchanged, while `H (1 - p) = H p`. -/

namespace GeneralCK.OAIBridge

open scoped BigOperators

/-- The published joint mass is OpenAI's `jointProbability`. -/
theorem jointMass_eq {n : ℕ} (f : Cube n → Bool) (p : ℝ) (b : Bool) (y : Cube n) :
    jointMass f p b y = OAI.LeanBlast.CourtadeKumar.jointProbability p f b y := by
  unfold jointMass OAI.LeanBlast.CourtadeKumar.jointProbability
    OAI.LeanBlast.CourtadeKumar.cubeAverage
  rw [zpow_neg, zpow_natCast, div_eq_inv_mul]
  rfl

/-- For `0 ≤ p ≤ 1/2` the published mutual information is OpenAI's. -/
theorem mutualInformation_eq_oai {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    mutualInformation f p = OAI.LeanBlast.CourtadeKumar.mutualInformation p f := by
  have hJ : ∀ b y, 0 ≤ OAI.LeanBlast.CourtadeKumar.jointProbability p f b y :=
    OAI.LeanBlast.CourtadeKumar.jointProbability_nonneg p f hp0 hp
  have hkl := OAI.LeanBlast.CourtadeKumar.finite_kl_eq_entropy_sums
    (fun b y => OAI.LeanBlast.CourtadeKumar.jointProbability p f b y) hJ
  unfold OAI.LeanBlast.CourtadeKumar.mutualInformation
    OAI.LeanBlast.CourtadeKumar.functionMarginal OAI.LeanBlast.CourtadeKumar.observationMarginal
    OAI.LeanBlast.CourtadeKumar.ell
  rw [hkl]
  unfold mutualInformation entropy
  simp only [jointMass_eq, Fintype.sum_prod_type, Real.negMulLog,
    OAI.LeanBlast.CourtadeKumar.xlogx]
  rw [← add_div, ← sub_div]
  congr 1
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

/-- OpenAI's binary entropy is the published one. -/
theorem H_eq_oai (p : ℝ) : H p = OAI.LeanBlast.CourtadeKumar.binaryEntropy p := by
  rw [OAI.LeanBlast.CourtadeKumar.binaryEntropy_eq_binEntropy]
  rfl

end GeneralCK.OAIBridge

end
end

section
section
/-! OpenAI's `FullStatement` (Courtade–Kumar bound plus dictator attainment), with the bound taken
from the published `GeneralCK.mostInformativeBooleanFunction`. -/

namespace CKReduce

open OAI.LeanBlast.CourtadeKumar

theorem courtadeKumar_of_general : CourtadeKumarStatement := by
  intro n _ ε hε0 hεhalf f
  rw [← GeneralCK.OAIBridge.mutualInformation_eq_oai f hε0 hεhalf,
    ← GeneralCK.OAIBridge.H_eq_oai]
  exact GeneralCK.mostInformativeBooleanFunction n f ε hε0 (by linarith)

theorem fullStatement_of_general : FullStatement :=
  ⟨courtadeKumar_of_general, dictatorAttainment⟩

end CKReduce

end
end


open OAI.LeanBlast.CourtadeKumar in
theorem solution : FullStatement :=
  CKReduce.fullStatement_of_general
