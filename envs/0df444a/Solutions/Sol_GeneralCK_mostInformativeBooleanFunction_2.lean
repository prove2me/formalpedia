-- Prove2me | solution 2 for GeneralCK.mostInformativeBooleanFunction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T09:51:56.029116+00:00
-- url     : https://prove2.me/submissions/50d279eb-1b6c-41f3-a245-96afaa689e52

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Set.Function
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_GeneralCK_statement
universe u v

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

/-- The sign cube `{−1,1}^n`, with Boolean coordinates encoding the signs. -/
abbrev Cube (n : ℕ) := Fin n → Bool

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

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

abbrev Cube (n : ℕ) := LeanBlast.GotsmanLinial.Cube n

def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n

def ell : ℝ := Real.log 2

def bitFlipKernel {n : ℕ} (ε : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - ε else ε

def jointProbability {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) : ℝ :=
  cubeAverage (fun x => if f x = b then bitFlipKernel ε x y else 0)

def functionMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (b : Bool) : ℝ :=
  ∑ y, jointProbability ε f b y

def observationMarginal {n : ℕ} (ε : ℝ) (f : Cube n → Bool) (y : Cube n) : ℝ :=
  ∑ b : Bool, jointProbability ε f b y

def xlogx (t : ℝ) : ℝ := t * Real.log t

def binaryEntropy (ε : ℝ) : ℝ :=
  -(xlogx ε + xlogx (1 - ε)) / ell

def mutualInformation {n : ℕ} (ε : ℝ) (f : Cube n → Bool) : ℝ :=
  (∑ b : Bool, ∑ y : Cube n,
    if 0 < jointProbability ε f b y then
      jointProbability ε f b y *
        Real.log (jointProbability ε f b y /
          (functionMarginal ε f b * observationMarginal ε f y))
    else 0) / ell

end LeanBlast.CourtadeKumar

end

end OAI
end

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

theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) :=
  flip_flip i

theorem flip_bijective {n : ℕ} (i : Fin n) : Function.Bijective (flip i) :=
  (flip_involutive i).bijective

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

def meanVariance {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  1 - (cubeAverage g) ^ 2

def dissipation {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  ∑ i, cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i g x)

def IsInterior {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, -1 < g x ∧ g x < 1

def IsSignValued {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x, g x = 1 ∨ g x = -1

def IsIncreasing {n : ℕ} (g : Cube n → ℝ) : Prop :=
  ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y

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

theorem cubeAverage_zeroDim (g : Cube 0 → ℝ) :
    cubeAverage g = g (fun _ => false) := by
  simp only [cubeAverage, pow_zero, div_one, Fintype.sum_unique]
  exact congrArg g (Subsingleton.elim _ _)

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

theorem cubeAverage_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x) :
    cubeAverage g ≤ cubeAverage h := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hgh x)
    (le_of_lt (cube_denominator_pos n))

theorem cubeAverage_strict_mono {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x)
    (hlt : ∃ x, g x < h x) : cubeAverage g < cubeAverage h := by
  apply (div_lt_div_iff_of_pos_right (cube_denominator_pos n)).2
  apply Finset.sum_lt_sum (fun x _ => hgh x)
  obtain ⟨x, hx⟩ := hlt
  exact ⟨x, Finset.mem_univ x, hx⟩

theorem cubeAverage_lt {g h : Cube n → ℝ} (hgh : ∀ x, g x < h x) :
    cubeAverage g < cubeAverage h := by
  exact cubeAverage_strict_mono (fun x => (hgh x).le) ⟨fun _ => false, hgh _⟩

theorem IsInterior.cubeAverage {g : Cube n → ℝ} (hg : IsInterior g) :
    -1 < cubeAverage g ∧ cubeAverage g < 1 := by
  constructor
  · simpa using cubeAverage_lt (fun x => (hg x).1)
  · simpa using cubeAverage_lt (fun x => (hg x).2)

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

theorem noiseKernel_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (x y : Cube n) : 0 < noiseKernel u x y := by
  apply Finset.prod_pos
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

theorem noiseKernel_split_coord (u : ℝ) (x y : Cube n) (i : Fin n) :
    noiseKernel u x y =
      (if x i = y i then (1 + u) / 2 else (1 - u) / 2) *
        ∏ j ∈ Finset.univ.erase i, if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

@[simp] theorem noiseOperator_const (u c : ℝ) (x : Cube n) :
    noiseOperator u (fun _ => c) x = c := by
  rw [noiseOperator, ← Finset.sum_mul, noiseKernel_row_sum, one_mul]

theorem noiseOperator_add (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y + h y) x = noiseOperator u g x + noiseOperator u h x := by
  simp [noiseOperator, mul_add, Finset.sum_add_distrib]

theorem noiseOperator_sub (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y - h y) x = noiseOperator u g x - noiseOperator u h x := by
  simp [noiseOperator, mul_sub, Finset.sum_sub_distrib]

theorem noiseOperator_smul (u c : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => c * g y) x = c * noiseOperator u g x := by
  simp [noiseOperator, Finset.mul_sum, mul_left_comm]

theorem cubeAverage_noiseOperator (u : ℝ) (g : Cube n → ℝ) :
    cubeAverage (noiseOperator u g) = cubeAverage g := by
  unfold cubeAverage noiseOperator
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, noiseKernel_col_sum, one_mul]

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

theorem noiseOperator_mono {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (x : Cube n) :
    noiseOperator u g x ≤ noiseOperator u h x := by
  exact Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (hgh y) (noiseKernel_nonneg hu0 hu1 x y)

theorem noiseOperator_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    {g : Cube n → ℝ} (hg : ∀ y, -1 ≤ g y ∧ g y ≤ 1) (x : Cube n) :
    -1 ≤ noiseOperator u g x ∧ noiseOperator u g x ≤ 1 := by
  constructor
  · simpa using noiseOperator_mono hu0 hu1 (fun y => (hg y).1) x
  · simpa using noiseOperator_mono hu0 hu1 (fun y => (hg y).2) x

theorem noiseOperator_strict_mono {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (hlt : ∃ y, g y < h y) (x : Cube n) :
    noiseOperator u g x < noiseOperator u h x := by
  apply Finset.sum_lt_sum
  · intro y _
    exact mul_le_mul_of_nonneg_left (hgh y) (le_of_lt (noiseKernel_pos hu0 hu1 x y))
  · obtain ⟨y, hy⟩ := hlt
    exact ⟨y, Finset.mem_univ y, mul_lt_mul_of_pos_left hy (noiseKernel_pos hu0 hu1 x y)⟩

theorem exists_signs_of_nonconstant {g : Cube n → ℝ} (hg : IsSignValued g)
    (hne : ∃ x y, g x ≠ g y) : (∃ x, g x = 1) ∧ (∃ y, g y = -1) := by
  obtain ⟨x, y, hxy⟩ := hne
  rcases hg x with hx | hx <;> rcases hg y with hy | hy
  · exact False.elim (hxy (hx.trans hy.symm))
  · exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exact ⟨⟨y, hy⟩, ⟨x, hx⟩⟩
  · exact False.elim (hxy (hx.trans hy.symm))

theorem noiseOperator_isInterior_of_exists_signs {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {g : Cube n → ℝ} (hg : IsSignValued g)
    (hpos : ∃ x, g x = 1) (hneg : ∃ y, g y = -1) :
    IsInterior (noiseOperator u g) := by
  have hb : ∀ y, -1 ≤ g y ∧ g y ≤ 1 := by
    intro y
    rcases hg y with h | h <;> rw [h] <;> norm_num
  intro x
  constructor
  · have hs : ∃ y, (-1 : ℝ) < g y := by
      obtain ⟨y, hy⟩ := hpos
      exact ⟨y, by rw [hy]; norm_num⟩
    simpa using noiseOperator_strict_mono hu0 hu1 (fun y => (hb y).1) hs x
  · have hs : ∃ y, g y < (1 : ℝ) := by
      obtain ⟨y, hy⟩ := hneg
      exact ⟨y, by rw [hy]; norm_num⟩
    simpa using noiseOperator_strict_mono hu0 hu1 (fun y => (hb y).2) hs x

theorem noiseOperator_isInterior {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    {g : Cube n → ℝ} (hg : IsSignValued g) (hne : ∃ x y, g x ≠ g y) :
    IsInterior (noiseOperator u g) := by
  obtain ⟨hp, hn⟩ := exists_signs_of_nonconstant hg hne
  exact noiseOperator_isInterior_of_exists_signs hu0 hu1 hg hp hn

theorem cubeAverage_mem_Ioo_of_signValued_nonconstant {g : Cube n → ℝ}
    (hg : IsSignValued g) (hne : ∃ x y, g x ≠ g y) :
    -1 < cubeAverage g ∧ cubeAverage g < 1 := by
  simpa using noiseOperator_isInterior (u := 0) (by norm_num) (by norm_num) hg hne
    (fun _ => false)

theorem meanVariance_pos_of_signValued_nonconstant {g : Cube n → ℝ}
    (hg : IsSignValued g) (hne : ∃ x y, g x ≠ g y) : 0 < meanVariance g := by
  obtain ⟨hlo, hhi⟩ := cubeAverage_mem_Ioo_of_signValued_nonconstant hg hne
  unfold meanVariance
  nlinarith [sq_nonneg (cubeAverage g), mul_pos (by linarith : 0 < 1 - cubeAverage g)
    (by linarith : 0 < 1 + cubeAverage g)]

end LeanBlast.CourtadeKumar

end

end OAI
end

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

theorem continuous_entropy : Continuous entropy := by
  have h : entropy = fun v => Real.binEntropy ((1 + v) / 2) :=
    funext entropy_eq_binEntropy
  rw [h]
  fun_prop

theorem continuous_psi : Continuous psi := by
  have h : psi = fun v => ell - entropy v := by ext v; simp [entropy]
  rw [h]
  exact continuous_const.sub continuous_entropy

theorem psi_nonneg (v : ℝ) : 0 ≤ psi v := by
  have h := Real.binEntropy_le_log_two (p := (1 + v) / 2)
  rw [← entropy_eq_binEntropy] at h
  unfold entropy ell at *
  linarith

theorem entropy_le_ell (v : ℝ) : entropy v ≤ ell := by
  exact sub_le_self _ (psi_nonneg v)

theorem entropy_nonneg {v : ℝ} (hv : v ∈ Icc (-1) 1) : 0 ≤ entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg (by linarith [hv.1]) (by linarith [hv.2])

theorem entropy_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith [hv.1]) (by linarith [hv.2])

theorem psi_lt_ell {v : ℝ} (hv : v ∈ Ioo (-1) 1) : psi v < ell := by
  have := entropy_pos hv
  unfold entropy at this
  linarith

theorem strictMonoOn_psi : StrictMonoOn psi (Icc 0 1) := by
  intro x hx y hy hxy
  have h := Real.binEntropy_strictAntiOn
    (show (1 + x) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hx.1, hx.2])
    (show (1 + y) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hy.1, hy.2])
    (show (1 + x) / 2 < (1 + y) / 2 by linarith)
  rw [← entropy_eq_binEntropy, ← entropy_eq_binEntropy] at h
  unfold entropy at h
  linarith

theorem concaveOn_entropy : ConcaveOn ℝ (Icc (-1) 1) entropy := by
  refine ⟨convex_Icc (-1) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 + y) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [entropy_eq_binEntropy, entropy_eq_binEntropy, entropy_eq_binEntropy]
  convert h using 1
  congr 1
  nlinarith

theorem convexOn_psi : ConvexOn ℝ (Icc (-1) 1) psi := by
  have h := concaveOn_entropy.neg.add (convexOn_const ell (convex_Icc (-1 : ℝ) 1))
  convert h using 1 <;> try with_reducible_and_instances rfl
  ext v
  simp [entropy]

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

theorem hasDerivAt_psi {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt psi (Real.artanh v) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have h1 := ((Real.hasDerivAt_mul_log hp).comp v
    ((hasDerivAt_id v).const_add 1)).div_const 2
  have h2 := ((Real.hasDerivAt_mul_log hm).comp v
    ((hasDerivAt_id v).const_sub 1)).div_const 2
  convert h1.add h2 using 1 <;> try with_reducible_and_instances rfl
  · ext u
    dsimp [psi]
    ring
  · rw [artanh_eq_log_sub hv]
    ring

theorem hasDerivAt_entropy {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt entropy (-Real.artanh v) v := by
  exact (hasDerivAt_psi hv).const_sub ell

theorem hasDerivAt_artanh {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - v ^ 2)) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have hq : 1 - v ^ 2 ≠ 0 := by
    have hp' : 0 < 1 + v := by linarith [hv.1]
    have hm' : 0 < 1 - v := by linarith [hv.2]
    nlinarith [mul_pos hp' hm']
  have h := ((((hasDerivAt_id v).const_add 1).log hp).sub
    (((hasDerivAt_id v).const_sub 1).log hm)).div_const 2
  have he : Real.artanh =ᶠ[𝓝 v]
      (fun u => (Real.log (1 + u) - Real.log (1 - u)) / 2) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with u hu
    exact artanh_eq_log_sub hu
  apply (h.congr_of_eventuallyEq he).congr_deriv
  change (1 / (1 + v) - -1 / (1 - v)) / 2 = 1 / (1 - v ^ 2)
  field_simp [hp, hm, hq]
  ring

end LeanBlast.CourtadeKumar

end

end OAI
end

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

section
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem isSignValued_signEncoding (f : Cube n → Bool) : IsSignValued (signEncoding f) := by
  intro x
  cases hx : f x <;> simp [signEncoding, hx]

@[simp] theorem entropyAverage_const (c : ℝ) :
    entropyAverage (fun _ : Cube n => c) = entropy c :=
  cubeAverage_const n (entropy c)

@[simp] theorem informationDeficit_const (c : ℝ) :
    informationDeficit (fun _ : Cube n => c) = 0 := by
  simp [informationDeficit]

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

theorem informationDeficit_noise_one_le (g : Cube n → ℝ) (hg : IsSignValued g) :
    informationDeficit (noiseOperator 1 g) ≤ psi 1 := by
  have hnoise : noiseOperator 1 g = g := by
    funext x
    exact noiseOperator_one g x
  have he : entropyAverage g = 0 := by
    have hpoint : (fun x => entropy (g x)) = fun _ : Cube n => 0 := by
      funext x
      rcases hg x with h | h <;> simp [h]
    unfold entropyAverage
    rw [hpoint, cubeAverage_const]
  rw [hnoise, informationDeficit, he, sub_zero, psi_one]
  exact entropy_le_ell _

end LeanBlast.CourtadeKumar

end

end OAI
end

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

def IsIncreasingIn (i : Fin n) (F : Cube n → ℝ) : Prop :=
  ∀ x, F (setBit i false x) ≤ F (setBit i true x)

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

theorem sortCoordinate_signValued (i : Fin n) {F : Cube n → ℝ}
    (hF : IsSignValued F) : IsSignValued (sortCoordinate i F) := by
  intro x
  rcases hF (setBit i false x) with h0 | h0 <;>
    rcases hF (setBit i true x) with h1 | h1 <;>
    cases hx : x i <;> simp [sortCoordinate, hx, h0, h1]

theorem sortCoordinate_increasingIn (i : Fin n) (F : Cube n → ℝ) :
    IsIncreasingIn i (sortCoordinate i F) := by
  intro x
  simp only [sortCoordinate_false, sortCoordinate_true]
  exact min_le_max

theorem sortCoordinate_preserves_increasingIn (i j : Fin n) {F : Cube n → ℝ}
    (hF : IsIncreasingIn j F) : IsIncreasingIn j (sortCoordinate i F) := by
  by_cases hij : i = j
  · subst j
    exact sortCoordinate_increasingIn i F
  · intro x
    have h0 := hF (setBit i false x)
    have h1 := hF (setBit i true x)
    simp only [sortCoordinate, setBit, Function.update_of_ne hij,
      Function.update_comm (Ne.symm hij)]
    cases hx : x i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact min_le_min h0 h1
    · exact max_le_max h0 h1

theorem increasingIn_setBit_mono {F : Cube n → ℝ} {i : Fin n}
    (hF : IsIncreasingIn i F) (x : Cube n) (a b : Bool) (hab : a ≤ b) :
    F (setBit i a x) ≤ F (setBit i b x) := by
  cases a <;> cases b
  · exact le_rfl
  · exact hF x
  · exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hab)
  · exact le_rfl

theorem isIncreasing_of_forall_increasingIn {F : Cube n → ℝ}
    (hF : ∀ i, IsIncreasingIn i F) : IsIncreasing F := by
  intro x y hxy
  let fill (s : Finset (Fin n)) : Cube n := fun i => if i ∈ s then y i else x i
  have hfill : ∀ s : Finset (Fin n), F x ≤ F (fill s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [fill]
    | @insert i s hi ih =>
      have hstep : F (fill s) ≤ F (setBit i (y i) (fill s)) := by
        have horder : fill s i ≤ y i := by simp [fill, hi, hxy i]
        simpa only [setBit_self] using
          increasingIn_setBit_mono (hF i) (fill s) (fill s i) (y i) horder
      have heq : setBit i (y i) (fill s) = fill (insert i s) := by
        funext j
        by_cases hji : j = i
        · subst j; simp [fill]
        · simp [setBit, fill, hji]
      exact ih.trans (heq ▸ hstep)
  simpa [fill] using hfill Finset.univ

theorem isIncreasing_increasingIn {F : Cube n → ℝ} (hF : IsIncreasing F)
    (i : Fin n) : IsIncreasingIn i F := by
  intro x
  apply hF
  intro j
  by_cases hji : j = i
  · subst j; simp
  · simp [setBit, Function.update_of_ne hji]

theorem pair_sum_setBit (i : Fin n) (F : Cube n → ℝ) (x : Cube n) :
    F (setBit i false x) + F (setBit i true x) = F x + F (flip i x) := by
  have hself := setBit_self i x
  cases hx : x i
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx] using
      congrArg (fun z => F z + F (setBit i true x)) hself
  · simpa [setBit, flip, LeanBlast.GotsmanLinial.flip, hx, add_comm] using
      congrArg (fun z => F (setBit i false x) + F z) hself

theorem sum_comp_flip (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, F (flip i x)) = ∑ x, F x := by
  exact Fintype.sum_bijective (flip i) (LeanBlast.GotsmanLinial.flip_bijective i) _ _
    (fun _ => rfl)

theorem sum_setBit_pair (i : Fin n) (F : Cube n → ℝ) :
    (∑ x, (F (setBit i false x) + F (setBit i true x))) = 2 * ∑ x, F x := by
  simp_rw [pair_sum_setBit]
  rw [Finset.sum_add_distrib, sum_comp_flip]
  ring

theorem cubeAverage_sortCoordinate (i : Fin n) (F : Cube n → ℝ) :
    cubeAverage (sortCoordinate i F) = cubeAverage F := by
  have h : (∑ x, (sortCoordinate i F (setBit i false x) +
      sortCoordinate i F (setBit i true x))) =
      ∑ x, (F (setBit i false x) + F (setBit i true x)) := by
    simp only [sortCoordinate_false, sortCoordinate_true, min_add_max]
  rw [sum_setBit_pair, sum_setBit_pair] at h
  have hs : (∑ x, sortCoordinate i F x) = ∑ x, F x := by linarith
  exact congrArg (fun z : ℝ => z / (2 : ℝ) ^ n) hs

def coordinatePairMean (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i false x) + F (setBit i true x)) / 2

def coordinatePairDifference (i : Fin n) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  (F (setBit i true x) - F (setBit i false x)) / 2

def coordinateOffKernel (i : Fin n) (u : ℝ) (x y : Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    if x j = y j then (1 + u) / 2 else (1 - u) / 2

def coordinateOffNoise (i : Fin n) (u : ℝ) (F : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, coordinateOffKernel i u x y / 2 * F y

theorem coordinateOffKernel_setBit_left (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u (setBit i b x) y = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem coordinateOffKernel_setBit_right (i : Fin n) (u : ℝ) (x y : Cube n) (b : Bool) :
    coordinateOffKernel i u x (setBit i b y) = coordinateOffKernel i u x y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [setBit, Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem noiseKernel_setBit_pair (i : Fin n) (u : ℝ) (x y : Cube n) (a b : Bool) :
    noiseKernel u (setBit i a x) (setBit i b y) =
      (if a = b then (1 + u) / 2 else (1 - u) / 2) * coordinateOffKernel i u x y := by
  rw [noiseKernel_split_coord _ _ _ i]
  simp only [setBit_apply_same]
  change (if a = b then _ else _) *
    coordinateOffKernel i u (setBit i a x) (setBit i b y) = _
  rw [coordinateOffKernel_setBit_left, coordinateOffKernel_setBit_right]

theorem coordinateOffKernel_nonneg (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (x y : Cube n) : 0 ≤ coordinateOffKernel i u x y := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> linarith [hu.1, hu.2]

theorem coordinateOffNoise_add (i : Fin n) (u : ℝ) (F G : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => F y + G y) x =
      coordinateOffNoise i u F x + coordinateOffNoise i u G x := by
  simp only [coordinateOffNoise, mul_add, Finset.sum_add_distrib]

theorem coordinateOffNoise_smul (i : Fin n) (u c : ℝ) (F : Cube n → ℝ) (x : Cube n) :
    coordinateOffNoise i u (fun y => c * F y) x = c * coordinateOffNoise i u F x := by
  simp only [coordinateOffNoise, Finset.mul_sum, mul_left_comm]

theorem coordinateOffNoise_mono (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F G : Cube n → ℝ} (hFG : ∀ y, F y ≤ G y) (x : Cube n) :
    coordinateOffNoise i u F x ≤ coordinateOffNoise i u G x := by
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hFG y)
    (div_nonneg (coordinateOffKernel_nonneg i hu x y) (by norm_num))

theorem coordinateOffNoise_nonneg (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F : Cube n → ℝ} (hF : ∀ y, 0 ≤ F y) (x : Cube n) :
    0 ≤ coordinateOffNoise i u F x := by
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (div_nonneg (coordinateOffKernel_nonneg i hu x y) (by norm_num)) (hF y)

theorem coordinateOffNoise_abs_bound (i : Fin n) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (F : Cube n → ℝ) (x : Cube n) :
    -coordinateOffNoise i u (fun y => |F y|) x ≤ coordinateOffNoise i u F x ∧
      coordinateOffNoise i u F x ≤ coordinateOffNoise i u (fun y => |F y|) x := by
  constructor
  · have h := coordinateOffNoise_mono i hu (fun y => neg_abs_le (F y)) x
    have heq : coordinateOffNoise i u (fun y => -|F y|) x =
        -coordinateOffNoise i u (fun y => |F y|) x := by
      simp [coordinateOffNoise]
    rw [heq] at h
    exact h
  · exact coordinateOffNoise_mono i hu (fun y => le_abs_self (F y)) x

theorem noiseOperator_setBit (i : Fin n) (u : ℝ) (F : Cube n → ℝ)
    (x : Cube n) (b : Bool) :
    noiseOperator u F (setBit i b x) =
      coordinateOffNoise i u (coordinatePairMean i F) x +
        (if b then u else -u) * coordinateOffNoise i u (coordinatePairDifference i F) x := by
  have h := sum_setBit_pair i (fun y => noiseKernel u (setBit i b x) y * F y)
  change _ = 2 * noiseOperator u F (setBit i b x) at h
  have heq : (∑ y, (noiseKernel u (setBit i b x) (setBit i false y) * F (setBit i false y) +
      noiseKernel u (setBit i b x) (setBit i true y) * F (setBit i true y))) =
      2 * coordinateOffNoise i u (fun y => coordinatePairMean i F y +
        (if b then u else -u) * coordinatePairDifference i F y) x := by
    rw [coordinateOffNoise, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [noiseKernel_setBit_pair, noiseKernel_setBit_pair]
    cases b <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      coordinatePairMean, coordinatePairDifference] <;> ring
  rw [heq, coordinateOffNoise_add, coordinateOffNoise_smul] at h
  linarith

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

theorem isIncreasing_noiseOperator {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    {F : Cube n → ℝ} (hF : IsIncreasing F) : IsIncreasing (noiseOperator u F) := by
  apply isIncreasing_of_forall_increasingIn
  intro i x
  rw [noiseOperator_setBit, noiseOperator_setBit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hb : 0 ≤ coordinateOffNoise i u (coordinatePairDifference i F) x := by
    apply coordinateOffNoise_nonneg i hu
    intro y
    exact div_nonneg (sub_nonneg.mpr (isIncreasing_increasingIn hF i y)) (by norm_num)
  nlinarith [mul_nonneg hu.1 hb]

theorem psi_symmetric_pair_mono (a b c : ℝ) (hc : 0 ≤ c)
    (hb : -c ≤ b ∧ b ≤ c)
    (hminus : a - c ∈ Set.Icc (-1 : ℝ) 1)
    (hplus : a + c ∈ Set.Icc (-1 : ℝ) 1) :
    psi (a + b) + psi (a - b) ≤ psi (a + c) + psi (a - c) := by
  by_cases hcz : c = 0
  · have hbz : b = 0 := by rcases hb with ⟨hl, hu⟩; simp only [hcz, neg_zero] at hl hu; linarith
    simp [hcz, hbz]
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    let t : ℝ := (c + b) / (2 * c)
    let s : ℝ := (c - b) / (2 * c)
    have ht : 0 ≤ t := div_nonneg (by linarith [hb.1]) (by positivity)
    have hs : 0 ≤ s := div_nonneg (by linarith [hb.2]) (by positivity)
    have hts : t + s = 1 := by dsimp [t, s]; field_simp; ring
    have hst : s + t = 1 := by linarith
    have hr1 : t * (a + c) + s * (a - c) = a + b := by
      dsimp [t, s]; field_simp; ring
    have hr2 : s * (a + c) + t * (a - c) = a - b := by
      dsimp [t, s]; field_simp; ring
    have h1 := convexOn_psi.2 hplus hminus ht hs hts
    have h2 := convexOn_psi.2 hplus hminus hs ht hst
    simp only [smul_eq_mul, hr1] at h1
    simp only [smul_eq_mul, hr2] at h2
    calc
      psi (a + b) + psi (a - b) ≤
          (t * psi (a + c) + s * psi (a - c)) +
          (s * psi (a + c) + t * psi (a - c)) := add_le_add h1 h2
      _ = (t + s) * (psi (a + c) + psi (a - c)) := by ring
      _ = psi (a + c) + psi (a - c) := by rw [hts, one_mul]

private theorem rearrangement_sign_bounds {F : Cube n → ℝ} (hF : IsSignValued F) :
    ∀ y, -1 ≤ F y ∧ F y ≤ 1 := by
  intro y
  rcases hF y with h | h <;> rw [h] <;> norm_num

theorem psi_noise_sortCoordinate_pair (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) (x : Cube n) :
    psi (noiseOperator u F (setBit i false x)) +
        psi (noiseOperator u F (setBit i true x)) ≤
      psi (noiseOperator u (sortCoordinate i F) (setBit i false x)) +
        psi (noiseOperator u (sortCoordinate i F) (setBit i true x)) := by
  let A := coordinateOffNoise i u (coordinatePairMean i F) x
  let B := u * coordinateOffNoise i u (coordinatePairDifference i F) x
  let C := u * coordinateOffNoise i u (fun y => |coordinatePairDifference i F y|) x
  have hc : 0 ≤ C := mul_nonneg hu.1
    (coordinateOffNoise_nonneg i hu (fun y => abs_nonneg _) x)
  have hbound := coordinateOffNoise_abs_bound i hu (coordinatePairDifference i F) x
  have hb : -C ≤ B ∧ B ≤ C := by
    dsimp only [B, C]
    constructor
    · have h := mul_le_mul_of_nonneg_left hbound.1 hu.1
      nlinarith
    · exact mul_le_mul_of_nonneg_left hbound.2 hu.1
  have hfminus : noiseOperator u F (setBit i false x) = A - B := by
    rw [noiseOperator_setBit]
    dsimp [A, B]
    ring
  have hfplus : noiseOperator u F (setBit i true x) = A + B := by
    rw [noiseOperator_setBit]
    rfl
  have hsminus : noiseOperator u (sortCoordinate i F) (setBit i false x) = A - C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    dsimp [A, C]
    ring
  have hsplus : noiseOperator u (sortCoordinate i F) (setBit i true x) = A + C := by
    rw [noiseOperator_setBit, coordinatePairMean_sortCoordinate, coordinatePairDifference_sortCoordinate]
    rfl
  have hsort := rearrangement_sign_bounds (sortCoordinate_signValued i hF)
  have hminus : A - C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsminus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  have hplus : A + C ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [← hsplus]
    exact noiseOperator_bounds hu.1 hu.2 hsort _
  rw [hfminus, hfplus, hsminus, hsplus]
  simpa only [add_comm] using psi_symmetric_pair_mono A B C hc hb hminus hplus

theorem cubeAverage_psi_noise_sortCoordinate (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) :
    cubeAverage (fun x => psi (noiseOperator u F x)) ≤
      cubeAverage (fun x => psi (noiseOperator u (sortCoordinate i F) x)) := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
    psi_noise_sortCoordinate_pair i hu hF x)
  rw [sum_setBit_pair i (fun x => psi (noiseOperator u F x)),
    sum_setBit_pair i (fun x => psi (noiseOperator u (sortCoordinate i F) x))] at h
  have hs : (∑ x, psi (noiseOperator u F x)) ≤
      ∑ x, psi (noiseOperator u (sortCoordinate i F) x) := by linarith
  exact div_le_div_of_nonneg_right hs (cube_denominator_pos n).le

theorem informationDeficit_eq_psi_difference (F : Cube n → ℝ) :
    informationDeficit F = cubeAverage (fun x => psi (F x)) - psi (cubeAverage F) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem informationDeficit_noise_sortCoordinate (i : Fin n) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinate i F)) := by
  rw [informationDeficit_eq_psi_difference, informationDeficit_eq_psi_difference,
    cubeAverage_noiseOperator, cubeAverage_noiseOperator, cubeAverage_sortCoordinate]
  exact sub_le_sub_right (cubeAverage_psi_noise_sortCoordinate i hu hF) _

def sortCoordinates : List (Fin n) → (Cube n → ℝ) → Cube n → ℝ
  | [], F => F
  | i :: is, F => sortCoordinates is (sortCoordinate i F)

theorem sortCoordinates_signValued (is : List (Fin n)) {F : Cube n → ℝ}
    (hF : IsSignValued F) : IsSignValued (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hF
  | cons i is ih => exact ih (sortCoordinate_signValued i hF)

theorem cubeAverage_sortCoordinates (is : List (Fin n)) (F : Cube n → ℝ) :
    cubeAverage (sortCoordinates is F) = cubeAverage F := by
  induction is generalizing F with
  | nil => rfl
  | cons i is ih => rw [sortCoordinates, ih, cubeAverage_sortCoordinate]

theorem sortCoordinates_increasingIn (is : List (Fin n)) {F : Cube n → ℝ}
    (j : Fin n) (hj : j ∈ is ∨ IsIncreasingIn j F) :
    IsIncreasingIn j (sortCoordinates is F) := by
  induction is generalizing F with
  | nil => exact hj.resolve_left (by simp)
  | cons i is ih =>
      apply ih
      rcases hj with hmem | hinc
      · rcases List.mem_cons.mp hmem with hji | hmem
        · subst j
          exact Or.inr (sortCoordinate_increasingIn i F)
        · exact Or.inl hmem
      · exact Or.inr (sortCoordinate_preserves_increasingIn i j hinc)

theorem informationDeficit_noise_sortCoordinates (is : List (Fin n)) {u : ℝ}
    (hu : u ∈ Set.Icc 0 1) {F : Cube n → ℝ} (hF : IsSignValued F) :
    informationDeficit (noiseOperator u F) ≤
      informationDeficit (noiseOperator u (sortCoordinates is F)) := by
  induction is generalizing F with
  | nil => exact le_rfl
  | cons i is ih =>
      exact (informationDeficit_noise_sortCoordinate i hu hF).trans
        (ih (sortCoordinate_signValued i hF))

theorem exists_increasing_informationDeficit_ge (u : ℝ) (hu : u ∈ Set.Icc 0 1)
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    ∃ G : Cube n → ℝ, IsSignValued G ∧ IsIncreasing G ∧
      cubeAverage G = cubeAverage F ∧
      informationDeficit (noiseOperator u F) ≤ informationDeficit (noiseOperator u G) := by
  classical
  let is : List (Fin n) := Finset.univ.toList
  refine ⟨sortCoordinates is F, sortCoordinates_signValued is hF, ?_,
    cubeAverage_sortCoordinates is F, informationDeficit_noise_sortCoordinates is hu hF⟩
  apply isIncreasing_of_forall_increasingIn
  intro j
  apply sortCoordinates_increasingIn is j
  exact Or.inl (by simp [is])

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def bernsteinSum (d : ℕ) (B : Fin (d + 1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, B i * (d.choose i.val : ℝ) * t ^ i.val * (1 - t) ^ (d - i.val)

theorem bernsteinSum_pos (d : ℕ) (B : Fin (d + 1) → ℝ)
    (hB : ∀ i, 0 < B i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < bernsteinSum d B t := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  unfold bernsteinSum
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (hB i).le (Nat.cast_nonneg _)) (pow_nonneg ht0 _))
      (pow_nonneg h1t _)
  · by_cases hlt : t < 1
    · refine ⟨⟨0, Nat.zero_lt_succ d⟩, Finset.mem_univ _, ?_⟩
      simpa only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero,
        mul_one, Nat.sub_zero] using
        mul_pos (hB ⟨0, Nat.zero_lt_succ d⟩) (pow_pos (sub_pos.mpr hlt) d)
    · have ht : t = 1 := le_antisymm ht1 (le_of_not_gt hlt)
      refine ⟨⟨d, Nat.lt_succ_self d⟩, Finset.mem_univ _, ?_⟩
      simpa [ht] using hB ⟨d, Nat.lt_succ_self d⟩

def curvatureT (z : ℝ) : ℝ :=
  1 + z / 3 + z ^ 2 / 5 + z ^ 3 / 7 + z ^ 4 / 9 + z ^ 5 / 11

def curvatureP (z : ℝ) : ℝ :=
  347 / 500 - z / 2 - z ^ 2 / 12 - z ^ 3 / 30 - z ^ 4 / 56 - z ^ 5 / 90

def curvatureN (z : ℝ) : ℝ :=
  (1 - z) * (4 / 3 + (8 / 15) * z + (12 / 35) * z ^ 2 +
    (16 / 63) * z ^ 3 + (20 / 99) * z ^ 4) + (24 / 143) * z ^ 5

def curvaturePolynomial (z : ℝ) : ℝ :=
  2 * (1 - z) ^ 3 * curvatureT z ^ 3 - 3 * curvatureP z ^ 2 * curvatureN z

private def curvatureBernstein : Fin 19 → ℝ :=
  ![(4591 / 62500 : ℝ),
    (49876 / 703125 : ℝ),
    (616620509 / 9036562500 : ℝ),
    (425343109 / 6506325000 : ℝ),
    (1239780551 / 19880437500 : ℝ),
    (8677345901149 / 146538704812500 : ℝ),
    (243668974553 / 4355288437500 : ℝ),
    (9012669336346771 / 171450284630625000 : ℝ),
    (1633213857973883 / 33281525840062500 : ℝ),
    (270017981574109469 / 5940752362451156250 : ℝ),
    (49027630438590434159 / 1176268967765328937500 : ℝ),
    (363078011510202773129 / 9624018827170873125000 : ℝ),
    (10171907529149910232987 / 303156593055882503437500 : ℝ),
    (4117638512237582389 / 141331745014397437500 : ℝ),
    (29341211329970780039 / 1199300807693601112500 : ℝ),
    (7749647417493214337891 / 395769266538888367125000 : ℝ),
    (14423931694547701552427 / 989423166347220917812500 : ℝ),
    (140069602865401114033 / 14550340681576778203125 : ℝ),
    (2753371080520712929 / 554298692631496312500 : ℝ)]

private theorem curvatureBernstein_pos (i : Fin 19) : 0 < curvatureBernstein i := by
  fin_cases i <;> norm_num [curvatureBernstein]

theorem curvaturePolynomial_bernstein (t : ℝ) :
    curvaturePolynomial ((2 / 3) * t) = bernsteinSum 18 curvatureBernstein t := by
  simp only [bernsteinSum, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, curvatureBernstein,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num [curvatureBernstein, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  unfold curvaturePolynomial curvatureT curvatureP curvatureN
  ring

theorem curvatureCertificate_pos {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2 / 3) :
    0 < curvaturePolynomial z := by
  have ht0 : 0 ≤ (3 / 2 : ℝ) * z := by positivity
  have ht1 : (3 / 2 : ℝ) * z ≤ 1 := by linarith
  have h := bernsteinSum_pos 18 curvatureBernstein curvatureBernstein_pos ht0 ht1
  rw [← curvaturePolynomial_bernstein] at h
  have he : (2 / 3 : ℝ) * ((3 / 2) * z) = z := by ring
  simpa only [he] using h

def lambdaPolynomial (b : ℝ) : ℝ :=
  4 - (5 / 2) * b - 5 * b ^ 2 - (7 / 4) * b ^ 3 + (56 / 15) * b ^ 4 +
    b ^ 5 + (15 / 14) * b ^ 6 + (3 / 8) * b ^ 7 + (8 / 15) * b ^ 8

private def lambdaBernsteinLow : Fin 9 → ℝ :=
  ![4,
    (241 / 64 : ℝ),
    (1537 / 448 : ℝ),
    (42755 / 14336 : ℝ),
    (217187 / 89600 : ℝ),
    (510487 / 286720 : ℝ),
    (8901163 / 8028160 : ℝ),
    (19161827 / 36700160 : ℝ),
    (1316227 / 4587520 : ℝ)]

private def lambdaBernsteinHigh : Fin 9 → ℝ :=
  ![(1316227 / 4587520 : ℝ),
    (7652479 / 36700160 : ℝ),
    (5432143 / 32112640 : ℝ),
    (2869523 / 16056320 : ℝ),
    (3747241 / 15052800 : ℝ),
    (1185781 / 3010560 : ℝ),
    (79071 / 125440 : ℝ),
    (5261 / 5376 : ℝ),
    (1229 / 840 : ℝ)]

private theorem lambdaBernsteinLow_pos (i : Fin 9) : 0 < lambdaBernsteinLow i := by
  fin_cases i <;> norm_num [lambdaBernsteinLow]

private theorem lambdaBernsteinHigh_pos (i : Fin 9) : 0 < lambdaBernsteinHigh i := by
  fin_cases i <;> norm_num [lambdaBernsteinHigh]

theorem lambdaPolynomial_bernstein_low (t : ℝ) :
    lambdaPolynomial ((3 / 4) * t) = bernsteinSum 8 lambdaBernsteinLow t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinLow, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaPolynomial_bernstein_high (t : ℝ) :
    lambdaPolynomial (3 / 4 + (1 / 4) * t) = bernsteinSum 8 lambdaBernsteinHigh t := by
  unfold bernsteinSum
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  norm_num [lambdaPolynomial, lambdaBernsteinHigh, Fin.sum_univ_succ,
    Nat.descFactorial, Nat.factorial]
  ring

theorem lambdaCertificate_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 < lambdaPolynomial b := by
  by_cases hb : b ≤ 3 / 4
  · have ht0 : 0 ≤ (4 / 3 : ℝ) * b := by positivity
    have ht1 : (4 / 3 : ℝ) * b ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinLow lambdaBernsteinLow_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_low] at h
    have he : (3 / 4 : ℝ) * ((4 / 3) * b) = b := by ring
    simpa only [he] using h
  · have ht0 : 0 ≤ 4 * b - 3 := by linarith
    have ht1 : 4 * b - 3 ≤ 1 := by linarith
    have h := bernsteinSum_pos 8 lambdaBernsteinHigh lambdaBernsteinHigh_pos ht0 ht1
    rw [← lambdaPolynomial_bernstein_high] at h
    have he : (3 / 4 : ℝ) + (1 / 4) * (4 * b - 3) = b := by ring
    simpa only [he] using h

theorem two_lt_exp_347_div_500 : (2 : ℝ) < Real.exp (347 / 500) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 347 / 500) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem ell_lt_347_div_500 : ell < 347 / 500 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr two_lt_exp_347_div_500

theorem nineteen_lt_exp_three : (19 : ℝ) < Real.exp 3 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 7)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_nineteen_lt_three : Real.log 19 < 3 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 19)).mpr nineteen_lt_exp_three

theorem nine_halves_lt_exp_151_div_100 : (9 / 2 : ℝ) < Real.exp (151 / 100) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 151 / 100) 6)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_nine_halves_lt_151_div_100 : Real.log (9 / 2) < 151 / 100 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9 / 2)).mpr nine_halves_lt_exp_151_div_100

theorem ten_sevenths_lt_inv_ell : (10 / 7 : ℝ) < 1 / ell := by
  have hpos : 0 < ell := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hpos).mpr
  have h := ell_lt_347_div_500
  linarith

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def comparisonC (u : ℝ) : ℝ :=
  100 / 81 + Real.log (9 / 10) - Real.log u

def comparisonBracket (u : ℝ) : ℝ :=
  (1 + u ^ 2 / 3) * comparisonC u - 1 / 3

theorem comparisonC_eq_log_div {u : ℝ} (hu : 0 < u) :
    comparisonC u = 100 / 81 + Real.log ((9 / 10) / u) := by
  rw [Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0) hu.ne']
  unfold comparisonC
  ring

theorem comparisonC_lt_eleven_fourths {u : ℝ} (hu : (1 / 5 : ℝ) ≤ u) :
    comparisonC u < 11 / 4 := by
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 5) hu
  have hbase : Real.log (9 / 10 : ℝ) - Real.log (1 / 5 : ℝ) =
      Real.log (9 / 2 : ℝ) := by
    rw [← Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0)
      (by norm_num : (1 / 5 : ℝ) ≠ 0)]
    norm_num
  have hnum := log_nine_halves_lt_151_div_100
  unfold comparisonC
  linarith

theorem hasDerivAt_comparisonC {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt comparisonC (-u⁻¹) u := by
  exact (Real.hasDerivAt_log hu).const_sub (100 / 81 + Real.log (9 / 10 : ℝ))

theorem hasDerivAt_comparisonBracket {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt comparisonBracket
      (u * (2 * comparisonC u - 1) / 3 - 1 / u) u := by
  have hp : HasDerivAt (fun v : ℝ => 1 + v ^ 2 / 3) (2 * u / 3) u := by
    convert! (((hasDerivAt_id u).pow 2).div_const 3).const_add 1 using 1
    simp
  convert! (hp.mul (hasDerivAt_comparisonC hu)).sub_const (1 / 3) using 1
  field_simp
  ring

theorem comparisonBracket_derivative_neg {u : ℝ}
    (hu0 : (1 / 5 : ℝ) ≤ u) (hu1 : u ≤ (5 / 8 : ℝ)) :
    u * (2 * comparisonC u - 1) / 3 - 1 / u < 0 := by
  have hu : 0 < u := by linarith
  have hC := comparisonC_lt_eleven_fourths hu0
  have hu2 : u ^ 2 ≤ (5 / 8 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (5 / 8 : ℝ) - u by linarith)
      (show 0 ≤ (5 / 8 : ℝ) + u by linarith)]
  have hmul : u ^ 2 * (2 * comparisonC u - 1) ≤ (9 / 2 : ℝ) * u ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show 2 * comparisonC u - 1 ≤ (9 / 2 : ℝ) by
      linarith) (sq_nonneg u)
    nlinarith
  apply (mul_lt_mul_iff_left₀ hu).mp
  have heq : (u * (2 * comparisonC u - 1) / 3 - 1 / u) * u =
      u ^ 2 * (2 * comparisonC u - 1) / 3 - 1 := by
    field_simp
  rw [heq, zero_mul]
  nlinarith

theorem comparisonBracket_antitone :
    AntitoneOn comparisonBracket (Icc (1 / 5 : ℝ) (5 / 8)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · intro u hu
    exact (hasDerivAt_comparisonBracket (by linarith [hu.1])).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Icc (1 / 5 : ℝ) (5 / 8) := interior_subset hu
    exact (hasDerivAt_comparisonBracket (by linarith [hu'.1])).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : u ∈ Icc (1 / 5 : ℝ) (5 / 8) := interior_subset hu
    rw [(hasDerivAt_comparisonBracket (by linarith [hu'.1])).deriv]
    exact (comparisonBracket_derivative_neg hu'.1 hu'.2).le

theorem comparisonC_middle_bound {u : ℝ}
    (hu0 : (1 / 5 : ℝ) ≤ u) (hu1 : u ≤ (5 / 8 : ℝ)) :
    (1 + u ^ 2 / 3) * comparisonC u - 1 / 3 ≤ (5 / 2 : ℝ) := by
  have hanti := comparisonBracket_antitone
    (show (1 / 5 : ℝ) ∈ Icc (1 / 5 : ℝ) (5 / 8) by constructor <;> norm_num)
    (show u ∈ Icc (1 / 5 : ℝ) (5 / 8) from ⟨hu0, hu1⟩) hu0
  have hbase : comparisonBracket (1 / 5 : ℝ) < (5 / 2 : ℝ) := by
    have hC := comparisonC_lt_eleven_fourths (show (1 / 5 : ℝ) ≤ 1 / 5 by norm_num)
    unfold comparisonBracket
    norm_num
    linarith
  exact hanti.trans hbase.le

theorem comparisonC_integral_bracket_nonneg {u : ℝ}
    (hu : 0 < u) (hu9 : u ≤ (9 / 10 : ℝ)) :
    0 ≤ 1 - u ^ 2 * comparisonC u := by
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 9 / 10) hu)
  have hC : comparisonC u ≤ 100 / 81 + (9 / 10) / u - 1 := by
    rw [comparisonC_eq_log_div hu]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hC (sq_nonneg u)
  have heq : u ^ 2 * (100 / 81 + (9 / 10) / u - 1) =
      (19 / 81 : ℝ) * u ^ 2 + (9 / 10 : ℝ) * u := by
    field_simp
    ring
  rw [heq] at hmul
  have hu2 : u ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (9 / 10 : ℝ) - u by linarith)
      (show 0 ≤ (9 / 10 : ℝ) + u by linarith)]
  nlinarith

theorem comparison_large_regime (m u B P S v : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ m ^ 2 * (ell - 1 / 2))
    (hP : u ^ 2 / 2 ≤ P)
    (hS : S ≤ (1 - m ^ 2) * P + B * (1 - v))
    (hu : (5 / 8 : ℝ) ≤ u) (hv : 0 ≤ v) : S ≤ P := by
  have hlevel : ell - 1 / 2 ≤ P := by
    have hell := ell_lt_347_div_500
    nlinarith [sq_nonneg (u - 5 / 8)]
  have hcorrection : B * (1 - v) ≤ m ^ 2 * P := by
    calc
      B * (1 - v) ≤ B := by nlinarith [mul_nonneg hB0 hv]
      _ ≤ m ^ 2 * (ell - 1 / 2) := hB
      _ ≤ m ^ 2 * P := mul_le_mul_of_nonneg_left hlevel (sq_nonneg m)
  nlinarith

theorem comparison_middle_regime (m u B P S v : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ m ^ 2 * (ell - 1 / 2))
    (hP : u ^ 2 / 2 ≤ P)
    (hS : S ≤ (1 - m ^ 2) * P + B * (1 - v))
    (hv : 1 - v ≤ (5 / 2 : ℝ) * u ^ 2) : S ≤ P := by
  have hell : (ell - 1 / 2) * (5 / 2 : ℝ) ≤ 1 / 2 := by
    have h := ell_lt_347_div_500
    linarith
  have hcorrection : B * (1 - v) ≤ m ^ 2 * P := by
    calc
      B * (1 - v) ≤ B * ((5 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hv hB0
      _ ≤ (m ^ 2 * (ell - 1 / 2)) * ((5 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ m ^ 2 * (u ^ 2 / 2) := by
        have h := mul_le_mul_of_nonneg_left hell
          (mul_nonneg (sq_nonneg m) (sq_nonneg u))
        nlinarith
      _ ≤ m ^ 2 * P := mul_le_mul_of_nonneg_left hP (sq_nonneg m)
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI
end

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

def L (x : ℝ) : ℝ :=
  if 0 < x ∧ x < ell then rGap (ell - x) else 0

def LDeriv (x : ℝ) : ℝ :=
  if 0 < x ∧ x < ell then 2 - rDeriv (ell - x) else 0

def s0 : ℝ := psi (1 / 5)

def K (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rGap s else rGap s0 + (rDeriv s0 - 2) * (s - s0)

def KDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else
    if s ≤ s0 then rDeriv s - 2 else rDeriv s0 - 2

theorem psiInv_mem_of_mem_image {s : ℝ} (hs : s ∈ psi '' Set.Icc 0 1) :
    psiInv s ∈ Set.Icc 0 1 :=
  Function.invFunOn_mem hs

theorem psi_psiInv_of_mem_image {s : ℝ} (hs : s ∈ psi '' Set.Icc 0 1) :
    psi (psiInv s) = s :=
  Function.invFunOn_eq hs

@[simp] theorem rDeriv_zero : rDeriv 0 = 2 := by simp [rDeriv]
@[simp] theorem rSecondDeriv_zero : rSecondDeriv 0 = 4 / 3 := by simp [rSecondDeriv]
@[simp] theorem K_zero : K 0 = 0 := by simp [K]
@[simp] theorem KDeriv_zero : KDeriv 0 = 0 := by simp [KDeriv]

theorem L_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : L x = 0 := by
  simp [L, not_lt.mpr hx]

theorem L_eq_rGap {x : ℝ} (hx : x ∈ Set.Ioo 0 ell) :
    L x = rGap (ell - x) := by simp [L, hx.1, hx.2]

theorem K_eq_rGap {s : ℝ} (hs : 0 < s) (hs0 : s ≤ s0) : K s = rGap s := by
  simp [K, not_le.mpr hs, hs0]

theorem K_eq_tangent {s : ℝ} (hs : 0 < s) (hs0 : s0 ≤ s) :
    K s = rGap s0 + (rDeriv s0 - 2) * (s - s0) := by
  rcases hs0.eq_or_lt with rfl | hs0
  · simp [K, not_le.mpr hs]
  · simp [K, not_le.mpr hs, not_le.mpr hs0]

theorem image_psi_Icc : psi '' Icc 0 1 = Icc 0 ell := by
  simpa only [psi_zero, psi_one] using
    continuous_psi.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) strictMonoOn_psi.monotoneOn

theorem psiInv_mem_Icc {s : ℝ} (hs : s ∈ Icc 0 ell) : psiInv s ∈ Icc 0 1 := by
  exact psiInv_mem_of_mem_image (image_psi_Icc.symm ▸ hs)

theorem psi_psiInv_Icc {s : ℝ} (hs : s ∈ Icc 0 ell) : psi (psiInv s) = s := by
  exact psi_psiInv_of_mem_image (image_psi_Icc.symm ▸ hs)

theorem psiInv_psi {u : ℝ} (hu : u ∈ Icc 0 1) : psiInv (psi u) = u :=
  strictMonoOn_psi.injOn.leftInvOn_invFunOn hu

@[simp] theorem psiInv_zero : psiInv 0 = 0 := by
  simpa only [psi_zero] using psiInv_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem psiInv_ell : psiInv ell = 1 := by
  simpa only [psi_one] using psiInv_psi (show (1 : ℝ) ∈ Icc 0 1 by norm_num)

@[simp] theorem r_zero : r 0 = 0 := by simp [r]
@[simp] theorem rGap_zero : rGap 0 = 0 := by simp [rGap]

theorem psi_psiInv {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : psi (psiInv s) = s :=
  psi_psiInv_Icc ⟨hs, hsell.le⟩

theorem psiInv_mem_Ico {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    psiInv s ∈ Ico 0 1 := by
  have hu := psiInv_mem_Icc ⟨hs, hsell.le⟩
  refine ⟨hu.1, ?_⟩
  by_contra h
  have he : psiInv s = 1 := le_antisymm hu.2 (le_of_not_gt h)
  have hv := psi_psiInv hs hsell
  rw [he, psi_one] at hv
  linarith

theorem psiInv_mem_Ioo {s : ℝ} (hs : s ∈ Ioo 0 ell) : psiInv s ∈ Ioo 0 1 := by
  have hu := psiInv_mem_Ico hs.1.le hs.2
  refine ⟨?_, hu.2⟩
  by_contra h
  have he : psiInv s = 0 := le_antisymm (le_of_not_gt h) hu.1
  have hv := psi_psiInv hs.1.le hs.2
  rw [he, psi_zero] at hv
  linarith [hs.1]

def psiOrderIso : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) ell where
  toFun u := ⟨psi u, image_psi_Icc ▸ mem_image_of_mem psi u.property⟩
  invFun s := ⟨psiInv s, psiInv_mem_Icc s.property⟩
  left_inv u := Subtype.ext (psiInv_psi u.property)
  right_inv s := Subtype.ext (psi_psiInv_Icc s.property)
  map_rel_iff' := by
    intro u v
    exact strictMonoOn_psi.le_iff_le u.property v.property

theorem continuousOn_psiInv : ContinuousOn psiInv (Icc 0 ell) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp psiOrderIso.symm.continuous

theorem continuousAt_psiInv {s : ℝ} (hs : s ∈ Ioo 0 ell) : ContinuousAt psiInv s :=
  (continuousOn_psiInv s ⟨hs.1.le, hs.2.le⟩).continuousAt (Icc_mem_nhds hs.1 hs.2)

theorem r_psi_nonneg {u : ℝ} (hu : u ∈ Icc 0 1) :
    r (psi u) = u * Real.artanh u := by rw [r, psiInv_psi hu]

theorem r_psi {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    r (psi u) = u * Real.artanh u := by
  by_cases h0 : 0 ≤ u
  · exact r_psi_nonneg ⟨h0, hu.2.le⟩
  · have hn : -u ∈ Ioo (-1) 1 := by constructor <;> linarith [hu.1, hu.2]
    have hodd : Real.artanh (-u) = -Real.artanh u := by
      rw [artanh_eq_log_sub hn, artanh_eq_log_sub hu]
      simp only [sub_eq_add_neg, neg_neg]
      ring
    calc
      r (psi u) = r (psi (-u)) := by rw [psi_neg]
      _ = (-u) * Real.artanh (-u) := r_psi_nonneg ⟨by linarith, hn.2.le⟩
      _ = u * Real.artanh u := by rw [hodd]; ring

theorem s0_pos : 0 < s0 := by
  change 0 < psi (1 / 5)
  rw [← psi_zero]
  exact strictMonoOn_psi (by norm_num) (by norm_num) (by norm_num)

theorem s0_lt_ell : s0 < ell := psi_lt_ell (by norm_num)

theorem hasDerivAt_psiInv {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt psiInv (Real.artanh (psiInv s))⁻¹ s := by
  have hu := psiInv_mem_Ioo hs
  apply HasDerivAt.of_local_left_inverse (continuousAt_psiInv hs)
    (hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩) (Real.artanh_pos hu).ne'
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  exact psi_psiInv ht.1.le ht.2

theorem continuousOn_r : ContinuousOn r (Ico 0 ell) := by
  have hi : ContinuousOn psiInv (Ico 0 ell) :=
    continuousOn_psiInv.mono (fun _ h => ⟨h.1, h.2.le⟩)
  intro s hs
  have hu := psiInv_mem_Ico hs.1 hs.2
  exact (hi s hs).mul
    ((hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).continuousAt.comp_continuousWithinAt
      (hi s hs))

theorem hasDerivAt_r {s : ℝ} (hs : s ∈ Ioo 0 ell) : HasDerivAt r (rDeriv s) s := by
  have hu := psiInv_mem_Ioo hs
  have hi := hasDerivAt_psiInv hs
  have ht := (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).comp s hi
  have hn : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - (psiInv s) ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  convert! hi.mul ht using 1
  unfold rDeriv
  rw [if_neg (not_le.mpr hs.1)]
  simp only [Function.comp_apply]
  field_simp

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Filter Set
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem tendsto_artanh_div_id_zero_right :
    Tendsto (fun u : ℝ => Real.artanh u / u) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

theorem tendsto_id_div_artanh_zero_right :
    Tendsto (fun u : ℝ => u / Real.artanh u) (𝓝[>] 0) (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    tendsto_artanh_div_id_zero_right.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)

theorem tendsto_entropy_inverse_derivative_zero_right :
    Tendsto (fun u : ℝ => 1 + u / ((1 - u ^ 2) * Real.artanh u))
      (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hden : Tendsto (fun u : ℝ => 1 - u ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hu.pow 2)
  have hquot := tendsto_id_div_artanh_zero_right.div hden (show (1 : ℝ) ≠ 0 by norm_num)
  have hadd :
    Tendsto (fun u : ℝ => 1 + (u / Real.artanh u) / (1 - u ^ 2))
      (𝓝[>] 0) (𝓝 ((1 : ℝ) + 1 / 1)) := tendsto_const_nhds.add hquot
  norm_num [div_div, mul_comm] at hadd ⊢
  exact hadd

theorem tendsto_artanh_mul_id_div_psi_zero_right :
    Tendsto (fun u : ℝ => (u * Real.artanh u) / psi u) (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hda : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  have ha : Tendsto Real.artanh (𝓝[>] 0) (𝓝 0) := by
    simpa using hda.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto psi (𝓝[>] 0) (𝓝 0) := by
    simpa [psi] using
      (hasDerivAt_psi (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hquot : Tendsto
      (fun u : ℝ => (Real.artanh u + u / (1 - u ^ 2)) / Real.artanh u)
      (𝓝[>] 0) (𝓝 2) := by
    apply tendsto_entropy_inverse_derivative_zero_right.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have hne : Real.artanh u ≠ 0 := ne_of_gt (Real.artanh_pos hu)
    rw [add_div, div_self hne, div_div]
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (f' := fun u => Real.artanh u + u / (1 - u ^ 2))
    (g' := Real.artanh) (show (0 : ℝ) < 1 by norm_num)
  · intro u hu
    convert! (hasDerivAt_id u).mul
      (hasDerivAt_artanh (show u ∈ Ioo (-1) 1 from ⟨by linarith [hu.1], hu.2⟩)) using 1
    simp [id_eq, div_eq_mul_inv]
  · intro u hu
    exact hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩
  · intro u hu
    exact ne_of_gt (Real.artanh_pos hu)
  · simpa using hu.mul ha
  · exact hp
  · exact hquot

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiCoeff (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1))

theorem psiCoeff_pos (k : ℕ) : 0 < psiCoeff k := by unfold psiCoeff; positivity

theorem psiCoeff_nonneg (k : ℕ) : 0 ≤ psiCoeff k := (psiCoeff_pos k).le

@[simp] theorem psiCoeff_zero : psiCoeff 0 = 1 / 2 := by norm_num [psiCoeff]

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert h using 1 <;> try with_reducible_and_instances rfl
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem hasSum_mul_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => (2 * ((k : ℝ) + 1)) * psiCoeff k * v ^ (2 * (k + 1)))
      (v * Real.artanh v) := by
  have h := (hasSum_artanh hv).mul_left v
  convert h using 1 <;> try with_reducible_and_instances rfl
  ext k
  have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
  unfold psiCoeff
  field_simp

theorem psi_eq_mul_artanh_add_log {v : ℝ} (hv : |v| < 1) :
    psi v = v * Real.artanh v + 1 / 2 * Real.log (1 - v ^ 2) := by
  have hp : 1 + v ≠ 0 := by linarith [(abs_lt.mp hv).1]
  have hm : 1 - v ≠ 0 := by linarith [(abs_lt.mp hv).2]
  have hl : Real.log (1 - v ^ 2) = Real.log (1 + v) + Real.log (1 - v) := by
    rw [← Real.log_mul hp hm]
    congr 1
    ring
  rw [artanh_eq_log_sub (abs_lt.mp hv), hl]
  unfold psi
  ring

theorem hasSum_psi {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  have hv2 : |v ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg v)]
    have h1 : 0 < 1 + v := by linarith [(abs_lt.mp hv).1]
    have h2 : 0 < 1 - v := by linarith [(abs_lt.mp hv).2]
    nlinarith [mul_pos h1 h2]
  have h := ((hasSum_artanh hv).mul_left v).add
    ((Real.hasSum_pow_div_log_of_abs_lt_one hv2).mul_left (-(1 / 2)))
  convert h using 1 <;> try with_reducible_and_instances rfl
  · ext k
    have h1 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h3 : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
    rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ]
    unfold psiCoeff
    field_simp
    ring
  · rw [psi_eq_mul_artanh_add_log hv]
    ring

theorem sum_range_artanh_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤ Real.artanh v := by
  have h := hasSum_artanh (show |v| < 1 by rwa [abs_of_nonneg hv0])
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk => by positivity)

theorem sum_range_psi_le {v : ℝ} (hv : |v| < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, psiCoeff k * v ^ (2 * (k + 1))) ≤ psi v := by
  have h := hasSum_psi hv
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))

theorem summable_psiCoeff : Summable psiCoeff := by
  have h : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply Summable.of_nonneg_of_le psiCoeff_nonneg ?_ h
  intro k
  unfold psiCoeff
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

namespace LeanBlast.CourtadeKumar

theorem self_le_artanh {u : ℝ} (hu : u ∈ Set.Ico 0 1) : u ≤ Real.artanh u := by
  simpa using sum_range_artanh_le hu.1 hu.2 1

theorem artanh_le_div_one_sub_sq {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    Real.artanh u ≤ u / (1 - u ^ 2) := by
  have huabs : |u| < 1 := by simpa only [abs_of_nonneg hu.1] using hu.2
  have hu2 : u ^ 2 < 1 := by
    have hmul := mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + u by linarith [hu.1])
    nlinarith
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left u
  have hseries := hasSum_artanh huabs
  have hle : Real.artanh u ≤ u * (1 - u ^ 2)⁻¹ := by
    apply hasSum_le _ hseries hgeom
    intro k
    have hpow : u ^ (2 * k + 1) = u * (u ^ 2) ^ k := by
      rw [pow_add, pow_one, pow_mul]
      ring
    rw [hpow]
    exact div_le_self (mul_nonneg hu.1 (pow_nonneg (sq_nonneg u) k))
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
  simpa only [div_eq_mul_inv] using hle

theorem one_sub_sq_mul_artanh_le_self {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    (1 - u ^ 2) * Real.artanh u ≤ u := by
  have hden : 0 < 1 - u ^ 2 := by
    have hmul := mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + u by linarith [hu.1])
    nlinarith
  have hle := (le_div_iff₀ hden).mp (artanh_le_div_one_sub_sq hu)
  simpa only [mul_comm] using hle

end LeanBlast.CourtadeKumar

end OAI
end

section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem psi_pos_of_pos {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) : 0 < psi u := by
  simpa only [psi_zero] using
    strictMonoOn_psi (show (0 : ℝ) ∈ Icc 0 1 by norm_num) ⟨hu.le, hu1⟩ hu

theorem rDeriv_psi {u : ℝ} (hu : u ∈ Ioo 0 1) :
    rDeriv (psi u) = 1 + u / ((1 - u ^ 2) * Real.artanh u) := by
  simp only [rDeriv, if_neg (not_le.mpr (psi_pos_of_pos hu.1 hu.2.le)),
    psiInv_psi ⟨hu.1.le, hu.2.le⟩]

theorem hasDerivAt_rDerivativeFormula {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun v => 1 + v / ((1 - v ^ 2) * Real.artanh v))
      (((1 + u ^ 2) * Real.artanh u - u) /
        ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 2)) u := by
  have ht : Real.artanh u ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - u ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  have hd := (((hasDerivAt_id u).pow 2).const_sub 1).mul
    (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩)
  have h := ((hasDerivAt_id u).div hd (mul_ne_zero hq ht)).const_add 1
  convert! h using 1
  dsimp
  field_simp [hq, ht]
  ring

theorem hasDerivAt_rDeriv {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rDeriv (rSecondDeriv s) s := by
  have hu := psiInv_mem_Ioo hs
  have h := (hasDerivAt_rDerivativeFormula hu).comp s (hasDerivAt_psiInv hs)
  have he : rDeriv =ᶠ[𝓝 s]
      (fun z => 1 + psiInv z / ((1 - (psiInv z) ^ 2) * Real.artanh (psiInv z))) := by
    filter_upwards [Ioi_mem_nhds hs.1] with z hz
    simp only [rDeriv, if_neg (not_le.mpr (show 0 < z from hz))]
  apply (h.congr_of_eventuallyEq he).congr_deriv
  have ht : Real.artanh (psiInv s) ≠ 0 := (Real.artanh_pos hu).ne'
  have hq : 1 - (psiInv s) ^ 2 ≠ 0 := by nlinarith [hu.1, hu.2]
  simp only [rSecondDeriv, if_neg (not_le.mpr hs.1)]
  field_simp [hq, ht]

theorem continuousOn_rGap : ContinuousOn rGap (Ico 0 ell) :=
  continuousOn_r.sub (continuous_const.mul continuous_id).continuousOn

theorem hasDerivAt_rGap {s : ℝ} (hs : s ∈ Ioo 0 ell) :
    HasDerivAt rGap (rDeriv s - 2) s := by
  convert! (hasDerivAt_r hs).sub ((hasDerivAt_id s).const_mul 2) using 1
  simp

theorem L_ell_sub {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) :
    L (ell - s) = r s - 2 * s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [L]
  · have hx : 0 < ell - s ∧ ell - s < ell := by constructor <;> linarith
    simp only [L, if_pos hx, rGap, sub_sub_cancel]

theorem L_entropy {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    L (entropy u) = r (psi u) - 2 * psi u :=
  L_ell_sub (psi_nonneg u) (psi_lt_ell hu)

theorem LDeriv_entropy {u : ℝ} (hu : u ∈ Ioo 0 1) :
    LDeriv (entropy u) = 2 - rDeriv (psi u) := by
  have hp := psi_pos_of_pos hu.1 hu.2.le
  have hpl := psi_lt_ell (show u ∈ Ioo (-1) 1 by constructor <;> linarith [hu.1, hu.2])
  have hx : 0 < entropy u ∧ entropy u < ell := by unfold entropy; constructor <;> linarith
  rw [LDeriv, if_pos hx]
  simp only [entropy, sub_sub_cancel]

theorem hasDerivAt_L_of_lt {x : ℝ} (hx : x ∈ Ioo 0 ell) :
    HasDerivAt L (LDeriv x) x := by
  have hs : ell - x ∈ Ioo 0 ell := by constructor <;> linarith [hx.1, hx.2]
  have h := (hasDerivAt_rGap hs).comp x ((hasDerivAt_id x).const_sub ell)
  have he : L =ᶠ[𝓝 x] (fun z => rGap (ell - z)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact L_eq_rGap hz
  apply (h.congr_of_eventuallyEq he).congr_deriv
  rw [LDeriv, if_pos (show 0 < x ∧ x < ell from hx)]
  ring

theorem hasDerivAt_LDeriv_of_lt {x : ℝ} (hx : x ∈ Ioo 0 ell) :
    HasDerivAt LDeriv (rSecondDeriv (ell - x)) x := by
  have hs : ell - x ∈ Ioo 0 ell := by constructor <;> linarith [hx.1, hx.2]
  have h := ((hasDerivAt_rDeriv hs).comp x ((hasDerivAt_id x).const_sub ell)).const_sub 2
  have he : LDeriv =ᶠ[𝓝 x] (fun z => 2 - rDeriv (ell - z)) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact if_pos hz
  apply (h.congr_of_eventuallyEq he).congr_deriv
  ring

theorem rDeriv_ge_two {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 2 ≤ rDeriv s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · have hu := psiInv_mem_Ioo ⟨hs, hsell⟩
    have hq : 0 < 1 - (psiInv s) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
    have ht := Real.artanh_pos hu
    have hb := one_sub_sq_mul_artanh_le_self ⟨hu.1.le, hu.2⟩
    have hd : 1 ≤ psiInv s / ((1 - (psiInv s) ^ 2) * Real.artanh (psiInv s)) :=
      (le_div_iff₀ (mul_pos hq ht)).mpr (by simpa using hb)
    simp only [rDeriv, if_neg (not_le.mpr hs)]
    linarith

theorem rSecondDeriv_pos {s : ℝ} (hs : s ∈ Ioo 0 ell) : 0 < rSecondDeriv s := by
  have hu := psiInv_mem_Ioo hs
  have hq : 0 < 1 - (psiInv s) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1 + psiInv s by linarith [hu.1])]
  have ht := Real.artanh_pos hu
  have hb := self_le_artanh ⟨hu.1.le, hu.2⟩
  have hn : 0 < (1 + (psiInv s) ^ 2) * Real.artanh (psiInv s) - psiInv s := by
    nlinarith [mul_pos (sq_pos_of_pos hu.1) ht]
  simp only [rSecondDeriv, if_neg (not_le.mpr hs.1)]
  exact div_pos hn (mul_pos (sq_pos_of_pos hq) (pow_pos ht 3))

theorem convexOn_r : ConvexOn ℝ (Ico 0 ell) r := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := rDeriv) (f'' := rSecondDeriv) (convex_Ico 0 ell) continuousOn_r ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_r (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    exact (hasDerivAt_rDeriv (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    exact (rSecondDeriv_pos (by simpa using hs)).le

theorem convexOn_rGap : ConvexOn ℝ (Ico 0 ell) rGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun s => rDeriv s - 2) (f'' := rSecondDeriv)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    simpa only [sub_zero] using
      ((hasDerivAt_rDeriv (by simpa using hs)).sub_const 2).hasDerivWithinAt
  · intro s hs
    exact (rSecondDeriv_pos (by simpa using hs)).le

theorem monotoneOn_rGap : MonotoneOn rGap (Ico 0 ell) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun s => rDeriv s - 2)
    (convex_Ico 0 ell) continuousOn_rGap ?_ ?_
  · intro s hs
    exact (hasDerivAt_rGap (by simpa using hs)).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Ioo 0 ell := by simpa using hs
    exact sub_nonneg.mpr (rDeriv_ge_two hs'.1.le hs'.2)

theorem rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : 0 ≤ rGap s := by
  simpa only [rGap_zero] using monotoneOn_rGap ⟨le_rfl, ell_pos⟩ ⟨hs, hsell⟩ hs

theorem monotoneOn_rDeriv : MonotoneOn rDeriv (Ico 0 ell) := by
  have hm : MonotoneOn rDeriv (Ioo 0 ell) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := rSecondDeriv)
      (convex_Ioo 0 ell) ?_ ?_ ?_
    · exact fun s hs => (hasDerivAt_rDeriv hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hasDerivAt_rDeriv (by simpa using hs)).hasDerivWithinAt
    · intro s hs
      exact (rSecondDeriv_pos (by simpa using hs)).le
  intro s hs t ht hst
  rcases hs.1.eq_or_lt with rfl | hs0
  · simpa only [rDeriv_zero] using rDeriv_ge_two ht.1 ht.2
  · exact hm ⟨hs0, hs.2⟩ ⟨lt_of_lt_of_le hs0 hst, ht.2⟩ hst

theorem tendsto_psiInv_zero_right : Tendsto psiInv (𝓝[>] 0) (𝓝[>] 0) := by
  have hc : Tendsto psiInv (𝓝[≥] 0) (𝓝 0) := by
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE ell_pos, psiInv_zero] using
      continuousOn_psiInv 0 ⟨le_rfl, ell_pos.le⟩
  refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  exact (psiInv_mem_Ioo hs).1

theorem tendsto_rDeriv_zero_right : Tendsto rDeriv (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_entropy_inverse_derivative_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, rDeriv, if_neg (not_le.mpr (show 0 < s from hs))]

theorem continuousOn_rDeriv : ContinuousOn rDeriv (Ico 0 ell) := by
  intro s hs
  rcases hs.1.eq_or_lt with rfl | hs0
  · have hright : ContinuousWithinAt rDeriv (Ioi 0) 0 := by
      simpa only [ContinuousWithinAt, rDeriv_zero] using tendsto_rDeriv_zero_right
    apply hright.insert.mono
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · exact (hasDerivAt_rDeriv ⟨hs0, hs.2⟩).continuousAt.continuousWithinAt

theorem tendsto_r_div_zero_right :
    Tendsto (fun s : ℝ => r s / s) (𝓝[>] 0) (𝓝 2) := by
  apply (tendsto_artanh_mul_id_div_psi_zero_right.comp tendsto_psiInv_zero_right).congr'
  filter_upwards [Ioo_mem_nhdsGT ell_pos] with s hs
  simp only [Function.comp_apply, r, psi_psiInv hs.1.le hs.2]

theorem hasDerivWithinAt_r_zero : HasDerivWithinAt r 2 (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left]
  have he : slope r 0 = fun s : ℝ => r s / s := by
    ext s
    simp only [slope_def_field, r_zero, sub_zero]
  rw [he]
  exact tendsto_r_div_zero_right

theorem hasDerivWithinAt_rGap_zero : HasDerivWithinAt rGap 0 (Ici 0) 0 := by
  convert! hasDerivWithinAt_r_zero.sub
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).hasDerivWithinAt) using 1
  simp

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

namespace LeanBlast.CourtadeKumar

theorem artanh_le_cubic_tail {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    Real.artanh u ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : u < 1 := hu.2
  have huabs : |u| < 1 := by rwa [abs_of_nonneg hu0]
  have hu2 : u ^ 2 < 1 := by nlinarith [sq_nonneg (u - 1)]
  have hseries := hasSum_artanh huabs
  have htail : HasSum
      (fun k : ℕ => u ^ (2 * (k + 1) + 1) / (2 * ((k + 1 : ℕ) : ℝ) + 1))
      (Real.artanh u - u) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hseries
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left (u ^ 3 / 3)
  have hle : Real.artanh u - u ≤ (u ^ 3 / 3) * (1 - u ^ 2)⁻¹ := by
    apply hasSum_le _ htail hgeom
    intro k
    have hpow : u ^ (2 * (k + 1) + 1) = u ^ 3 * (u ^ 2) ^ k := by
      rw [show 2 * (k + 1) + 1 = 3 + 2 * k by omega, pow_add, pow_mul]
    rw [hpow]
    calc
      _ ≤ (u ^ 3 * (u ^ 2) ^ k) / 3 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) k]
      _ = _ := by ring
  calc
    Real.artanh u = u + (Real.artanh u - u) := by ring
    _ ≤ u + (u ^ 3 / 3) * (1 - u ^ 2)⁻¹ := by linarith
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem cubic_le_artanh {u : ℝ} (hu : u ∈ Set.Ico 0 1) :
    u + u ^ 3 / 3 ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu.1 hu.2 2
  norm_num [Finset.sum_range_succ] at h
  exact h

end LeanBlast.CourtadeKumar

end OAI
end

section
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiSeries (v : ℝ) : ℝ := ∑' k : ℕ, psiCoeff k * v ^ (2 * (k + 1))

theorem norm_psiSeries_term_le {v : ℝ} (hv : |v| ≤ 1) (k : ℕ) :
    ‖psiCoeff k * v ^ (2 * (k + 1))‖ ≤ psiCoeff k := by
  rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (psiCoeff_nonneg k)]
  exact mul_le_of_le_one_right (psiCoeff_nonneg k)
    (pow_le_one₀ (abs_nonneg v) hv)

theorem summable_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    Summable (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) :=
  Summable.of_norm_bounded summable_psiCoeff (norm_psiSeries_term_le hv)

theorem continuousOn_psiSeries : ContinuousOn psiSeries (Icc (-1) 1) := by
  apply continuousOn_tsum
  · intro k
    fun_prop
  · exact summable_psiCoeff
  · intro k v hv
    exact norm_psiSeries_term_le (abs_le.mpr hv) k

theorem psiSeries_eq_psi {v : ℝ} (hv : |v| ≤ 1) : psiSeries v = psi v := by
  have h : EqOn psiSeries psi (Ioo (-1) 1) := by
    intro x hx
    exact (hasSum_psi (abs_lt.mpr hx)).tsum_eq
  have h' := h.of_subset_closure continuousOn_psiSeries continuous_psi.continuousOn
    Ioo_subset_Icc_self (show Icc (-1 : ℝ) 1 ⊆ closure (Ioo (-1) 1) by
      rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)])
  exact h' (abs_le.mp hv)

theorem hasSum_psi_closed {v : ℝ} (hv : |v| ≤ 1) :
    HasSum (fun k : ℕ => psiCoeff k * v ^ (2 * (k + 1))) (psi v) := by
  rw [← psiSeries_eq_psi hv]
  exact (summable_psi_closed hv).hasSum

theorem hasSum_psiCoeff : HasSum psiCoeff ell := by
  simpa using hasSum_psi_closed (v := 1) (by norm_num)

theorem half_sq_le_psi {v : ℝ} (hv : |v| ≤ 1) : v ^ 2 / 2 ≤ psi v := by
  have h := (summable_psi_closed hv).sum_le_tsum {0} (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))
  rw [(hasSum_psi_closed hv).tsum_eq] at h
  simpa [psiCoeff_zero, div_eq_mul_inv, mul_comm] using h

theorem psi_le_ell_mul_sq {v : ℝ} (hv : |v| ≤ 1) : psi v ≤ ell * v ^ 2 := by
  have hsq : v ^ 2 ≤ 1 := by
    have h := abs_le.mp hv
    nlinarith [mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ 1 + v by linarith [h.1])]
  apply hasSum_le _ (hasSum_psi_closed hv) (hasSum_psiCoeff.mul_right (v ^ 2))
  intro k
  apply mul_le_mul_of_nonneg_left _ (psiCoeff_nonneg k)
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, pow_mul]
  exact mul_le_of_le_one_left (sq_nonneg v) (pow_le_one₀ (sq_nonneg v) hsq)

theorem ell_mul_one_sub_sq_le_entropy {v : ℝ} (hv : |v| ≤ 1) :
    ell * (1 - v ^ 2) ≤ entropy v := by
  have h := psi_le_ell_mul_sq hv
  unfold entropy
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

def curvatureNumeratorCoeff (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ) + 1) + 1 / (2 * (k : ℝ) + 3)

theorem curvatureNumeratorCoeff_antitone : Antitone curvatureNumeratorCoeff := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold curvatureNumeratorCoeff
  exact add_le_add (one_div_le_one_div_of_le (by positivity) (by linarith))
    (one_div_le_one_div_of_le (by positivity) (by linarith))

theorem hasSum_artanh_div {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 1)) * (u ^ 2) ^ k)
      (Real.artanh u / u) := by
  have h := (hasSum_artanh (show |u| < 1 by rwa [abs_of_pos hu0])).div_const u
  convert h using 1 <;> try with_reducible_and_instances rfl
  ext k
  rw [pow_add, pow_one, ← pow_mul]
  field_simp

theorem hasSum_curvatureNumerator {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => curvatureNumeratorCoeff k * (u ^ 2) ^ k)
      (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) := by
  have hA := hasSum_artanh_div hu0 hu1
  have htail := (hasSum_nat_add_iff' 1).mpr hA
  have hB : HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 3)) * (u ^ 2) ^ k)
      ((Real.artanh u / u - 1) / u ^ 2) := by
    have hdiv := htail.div_const (u ^ 2)
    convert hdiv using 1 <;> try with_reducible_and_instances rfl
    · ext k
      simp only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
      ring
    · simp
  convert hA.add hB using 1 <;> try with_reducible_and_instances rfl
  · ext k
    unfold curvatureNumeratorCoeff
    ring
  · field_simp
    ring

theorem curvatureT_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u * curvatureT (u ^ 2) ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu0.le hu1 6
  convert h using 1
  norm_num [curvatureT, Finset.sum_range_succ]
  ring

theorem curvatureP_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ≤ curvatureP (u ^ 2) := by
  have h := sum_range_psi_le (show |u| < 1 by rwa [abs_of_pos hu0]) 5
  have hs : (∑ k ∈ Finset.range 5, psiCoeff k * u ^ (2 * (k + 1))) =
      u ^ 2 / 2 + (u ^ 2) ^ 2 / 12 + (u ^ 2) ^ 3 / 30 +
        (u ^ 2) ^ 4 / 56 + (u ^ 2) ^ 5 / 90 := by
    norm_num [psiCoeff, Finset.sum_range_succ]
    ring
  rw [hs] at h
  unfold entropy curvatureP
  linarith [ell_lt_347_div_500]

theorem curvatureNumerator_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) ≤
      curvatureN (u ^ 2) / (1 - u ^ 2) := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : u ^ 2 < 1 := by nlinarith [mul_pos hu0 (sub_pos.mpr hu1)]
  have hz : 1 - u ^ 2 ≠ 0 := by linarith
  have hA := hasSum_curvatureNumerator hu0 hu1
  have htail := (hasSum_nat_add_iff' 5).mpr hA
  have hgeo := (hasSum_geometric_of_lt_one hz0 hz1).mul_left
    (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5)
  have hbound := hasSum_le
    (fun k : ℕ => calc
      curvatureNumeratorCoeff (k + 5) * (u ^ 2) ^ (k + 5) ≤
          curvatureNumeratorCoeff 5 * (u ^ 2) ^ (k + 5) :=
        mul_le_mul_of_nonneg_right
          (curvatureNumeratorCoeff_antitone (by omega)) (pow_nonneg hz0 _)
      _ = (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5) * (u ^ 2) ^ k := by
        rw [pow_add]
        ring) htail hgeo
  have hpartial :
      (∑ k ∈ Finset.range 5, curvatureNumeratorCoeff k * (u ^ 2) ^ k) +
          (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5) * (1 - u ^ 2)⁻¹ =
        curvatureN (u ^ 2) / (1 - u ^ 2) := by
    norm_num [curvatureNumeratorCoeff, Finset.sum_range_succ, curvatureN]
    field_simp
  rw [← hpartial]
  linarith

theorem medium_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hz : u ^ 2 ≤ (2 / 3 : ℝ)) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : 0 < 1 - u ^ 2 := by linarith
  have ht : 0 < Real.artanh u := Real.artanh_pos ⟨hu0, hu1⟩
  have hH : 0 < entropy u := entropy_pos ⟨by linarith, hu1⟩
  have hHP := curvatureP_upper hu0 hu1
  have hP : 0 < curvatureP (u ^ 2) := hH.trans_le hHP
  have hT : 0 < curvatureT (u ^ 2) := by unfold curvatureT; positivity
  have hTl := curvatureT_lower hu0 hu1
  have hN := curvatureNumerator_upper hu0 hu1
  have hnum : (1 + u ^ 2) * Real.artanh u - u ≤
      (curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3 :=
    (div_le_iff₀ (pow_pos hu0 3)).mp hN
  have hu_atanh : u ≤ Real.artanh u := by
    simpa using sum_range_artanh_le hu0.le hu1 1
  have hnum0 : 0 ≤ (1 + u ^ 2) * Real.artanh u - u := by
    nlinarith [mul_nonneg hz0 ht.le]
  have hsq : entropy u ^ 2 ≤ curvatureP (u ^ 2) ^ 2 :=
    pow_le_pow_left₀ hH.le hHP 2
  have hprod := mul_le_mul hsq hnum hnum0 (sq_nonneg (curvatureP (u ^ 2)))
  have hc := curvatureCertificate_pos hz0 hz
  unfold curvaturePolynomial at hc
  have hc' : 3 * curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) <
      2 * (1 - u ^ 2) ^ 3 * curvatureT (u ^ 2) ^ 3 := by linarith
  have hcert : curvatureP (u ^ 2) ^ 2 *
      ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) <
      (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := by
    rw [show curvatureP (u ^ 2) ^ 2 *
        ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) =
        (curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) * u ^ 3) / (1 - u ^ 2) by ring]
    apply (div_lt_iff₀ hz1).mpr
    have hc'' := mul_lt_mul_of_pos_right hc' (pow_pos hu0 3)
    nlinarith
  have hpow : (u * curvatureT (u ^ 2)) ^ 3 ≤ (Real.artanh u) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hu0.le hT.le) hTl 3
  have hden := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 by positivity)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (pow_pos hz1 2) (pow_pos ht 3))).mpr
  calc
    entropy u ^ 2 * ((1 + u ^ 2) * Real.artanh u - u) ≤
        curvatureP (u ^ 2) ^ 2 *
          ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) := hprod
    _ ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := hcert.le
    _ ≤ (2 / 3 : ℝ) * ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
      simpa only [mul_assoc] using hden

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem large_parameter_gt_81 {u : ℝ} (hu0 : 0 ≤ u) (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    (81 / 100 : ℝ) < u := by
  by_contra h
  have hsq := pow_le_pow_left₀ hu0 (le_of_not_gt h) 2
  norm_num at hsq
  linarith

theorem large_artanh_gt_eleven_tenths {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) : (11 / 10 : ℝ) < Real.artanh u := by
  have hu81 := (large_parameter_gt_81 hu0 hu2).le
  have hpoly : (∑ k ∈ Finset.range 5,
      (81 / 100 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤
      ∑ k ∈ Finset.range 5, u ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro k _
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 81 / 100) hu81 _) (by positivity)
  have hnum : (11 / 10 : ℝ) < ∑ k ∈ Finset.range 5,
      (81 / 100 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  exact hnum.trans_le (hpoly.trans (sum_range_artanh_le hu0 hu1 5))

theorem entropy_eq_large_parameter_form {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    entropy u = (1 - u) * Real.artanh u + Real.log (1 + (1 - u) / (1 + u)) := by
  have hp : 0 < 1 + u := by linarith
  have heq : 1 + (1 - u) / (1 + u) = 2 / (1 + u) := by
    field_simp
    ring
  rw [heq, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
    artanh_eq_log_sub ⟨by linarith, hu1⟩]
  unfold entropy psi ell
  ring

theorem large_parameter_polynomial_bound {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ (5 / 11 : ℝ)) :
    (1 / 2 : ℝ) * (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 ≤ 2 / 3 := by
  have hfirst : (1 - y) * (1 + 10 * y / 9) ^ 2 ≤ (13718 / 10935 : ℝ) := by
    have hc : (13718 / 10935 : ℝ) - (1 - y) * (1 + 10 * y / 9) ^ 2 =
        (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) := by ring
    have hp : 0 ≤ (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hsecond : (1 + y) * (1 + 10 * y / 9) ^ 2 / 81 ≤
      (355216 / 8732691 : ℝ) := by
    calc
      _ ≤ (1 + (5 / 11 : ℝ)) * (1 + 10 * (5 / 11 : ℝ) / 9) ^ 2 / 81 := by
        gcongr
      _ = _ := by norm_num
  nlinarith

theorem large_curvature_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  let t : ℝ := Real.artanh u
  let e : ℝ := (1 - u) / (1 + u)
  let y : ℝ := 1 / (2 * t)
  let R : ℝ := 1 + (1 + e) * y
  let A : ℝ := 1 - y + (1 + y) * e ^ 2
  let Q : ℝ := ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)
  have ht11 : (11 / 10 : ℝ) < t := large_artanh_gt_eleven_tenths hu0 hu1 hu2
  have ht : 0 < t := by linarith
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  have hsq : 0 < 1 - u ^ 2 := by nlinarith [mul_pos hm hp]
  have he0 : 0 ≤ e := div_nonneg hm.le hp.le
  have he1 : e ≤ (1 / 9 : ℝ) := by
    dsimp only [e]
    apply (div_le_iff₀ hp).mpr
    linarith [large_parameter_gt_81 hu0 hu2]
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hy1 : y ≤ (5 / 11 : ℝ) := by
    dsimp only [y]
    apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
    linarith
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hA0 : 0 ≤ A := by
    have hy : 0 ≤ 1 - y := by linarith
    dsimp only [A]
    positivity
  have hQ : 0 ≤ Q := by
    apply div_nonneg
    · nlinarith [mul_nonneg (sq_nonneg u) ht.le]
    · positivity
  have hH0 : 0 ≤ entropy u := entropy_nonneg ⟨by linarith, hu1.le⟩
  have hH : entropy u ≤ (1 - u) * t * R := by
    have hlog : Real.log (1 + e) ≤ e := by
      have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + e)
      linarith
    have hid : entropy u = (1 - u) * t + Real.log (1 + e) :=
      entropy_eq_large_parameter_form hu0 hu1
    have hr : (1 - u) * t * R = (1 - u) * t + e := by
      dsimp only [R, e, y]
      field_simp [ht.ne', hp.ne']
      ring
    rw [hr, hid]
    linarith
  have hcoef : ((1 - u) * t) ^ 2 * Q = (1 / 2 : ℝ) * A := by
    dsimp only [Q, A, e, y]
    field_simp [ht.ne', hp.ne', hsq.ne']
    ring
  have hRsq : R ^ 2 ≤ (1 + 10 * y / 9) ^ 2 := by
    apply pow_le_pow_left₀ hR0
    dsimp only [R]
    nlinarith [mul_le_mul_of_nonneg_right he1 hy0]
  have hA : A ≤ 1 - y + (1 + y) / 81 := by
    have he2 := pow_le_pow_left₀ he0 he1 2
    have hmul := mul_le_mul_of_nonneg_left he2 (by linarith : 0 ≤ 1 + y)
    dsimp only [A]
    nlinarith
  have hprod : A * R ^ 2 ≤ (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 :=
    mul_le_mul hA hRsq (sq_nonneg R) (hA0.trans hA)
  change entropy u ^ 2 * Q ≤ 2 / 3
  calc
    entropy u ^ 2 * Q ≤ ((1 - u) * t * R) ^ 2 * Q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH0 hH 2) hQ
    _ = (((1 - u) * t) ^ 2 * Q) * R ^ 2 := by ring
    _ = (1 / 2 : ℝ) * (A * R ^ 2) := by rw [hcoef]; ring
    _ ≤ (1 / 2 : ℝ) * ((1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 2 / 3 := by simpa only [mul_assoc] using large_parameter_polynomial_bound hy0 hy1

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def curvatureModel (u t : ℝ) : ℝ :=
  ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)

private def smallCoarseBound (z : ℝ) : ℝ :=
  ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * (1 + z / 3) ^ 3)

private theorem smallCoarseBound_lt_ten_sevenths {z : ℝ}
    (hz0 : 0 ≤ z) (hz25 : z ≤ 1 / 25) : smallCoarseBound z < 10 / 7 := by
  have hz1 : 0 < 1 - z := by linarith
  have hratio : z / (1 - z) ≤ 1 / 24 := (div_le_iff₀ hz1).mpr (by linarith)
  have hnum : (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := by linarith
  have hzsq : z ^ 2 ≤ 1 / 625 := by
    nlinarith [mul_nonneg hz0 (show 0 ≤ 1 / 25 - z by linarith)]
  have hcube : 1 + z ≤ (1 + z / 3) ^ 3 := by
    nlinarith [sq_nonneg z, pow_nonneg hz0 3]
  have hbase : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z) := by
    nlinarith [pow_nonneg hz0 3]
  have hden : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z / 3) ^ 3 :=
    hbase.trans (mul_le_mul_of_nonneg_left hcube (sq_nonneg _))
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by linarith
  apply (div_lt_iff₀ hden0).mpr
  calc
    (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := hnum
    _ < (10 / 7) * (599 / 625) := by norm_num
    _ ≤ (10 / 7) * ((1 - z) ^ 2 * (1 + z / 3) ^ 3) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

private theorem normalized_small_curvature_le {z a : ℝ}
    (hz0 : 0 < z) (hz25 : z ≤ 1 / 25)
    (hal : 1 + z / 3 ≤ a) (hau : a ≤ 1 + z / (3 * (1 - z))) :
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤ smallCoarseBound z := by
  have hz1 : 0 < 1 - z := by linarith
  have ha0 : 0 < a := by linarith
  have hnum : ((1 + z) * a - 1) / z ≤ (4 / 3) + (2 / 3) * (z / (1 - z)) := by
    calc
      ((1 + z) * a - 1) / z ≤
          ((1 + z) * (1 + z / (3 * (1 - z))) - 1) / z :=
        div_le_div_of_nonneg_right
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hau (by linarith)) 1) hz0.le
      _ = (4 / 3) + (2 / 3) * (z / (1 - z)) := by
        field_simp [hz0.ne', hz1.ne']
        ring
  have hupper0 : 0 ≤ (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) := by positivity
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by positivity
  have hdena0 : 0 < (1 - z) ^ 2 * a ^ 3 := by positivity
  have hdencmp : (1 - z) ^ 2 * (1 + z / 3) ^ 3 ≤ (1 - z) ^ 2 * a ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hal 3) (sq_nonneg _)
  calc
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤
        ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * a ^ 3) :=
      div_le_div_of_nonneg_right hnum hdena0.le
    _ ≤ smallCoarseBound z := div_le_div_of_nonneg_left hupper0 hden0 hdencmp

theorem curvatureModel_small_of_cubic_bounds {u t : ℝ}
    (hu0 : 0 < u) (hu5 : u ≤ 1 / 5)
    (hl : u + u ^ 3 / 3 ≤ t) (hu : t ≤ u + u ^ 3 / (3 * (1 - u ^ 2))) :
    curvatureModel u t < 1 / ell := by
  have hz0 : 0 < u ^ 2 := sq_pos_of_pos hu0
  have hz25 : u ^ 2 ≤ 1 / 25 := by
    nlinarith [mul_nonneg hu0.le (show 0 ≤ 1 / 5 - u by linarith)]
  have hq : 0 < 1 - u ^ 2 := by linarith
  have ht0 : 0 < t := by nlinarith [pow_pos hu0 3]
  have hal : 1 + u ^ 2 / 3 ≤ t / u := by
    apply (le_div_iff₀ hu0).mpr
    nlinarith
  have hau : t / u ≤ 1 + u ^ 2 / (3 * (1 - u ^ 2)) := by
    apply (div_le_iff₀ hu0).mpr
    calc
      t ≤ u + u ^ 3 / (3 * (1 - u ^ 2)) := hu
      _ = (1 + u ^ 2 / (3 * (1 - u ^ 2))) * u := by ring
  have he : curvatureModel u t =
      (((1 + u ^ 2) * (t / u) - 1) / u ^ 2) / ((1 - u ^ 2) ^ 2 * (t / u) ^ 3) := by
    unfold curvatureModel
    field_simp [hu0.ne', ht0.ne', hq.ne']
  rw [he]
  exact (normalized_small_curvature_le hz0 hz25 hal hau).trans_lt
    ((smallCoarseBound_lt_ten_sevenths hz0.le hz25).trans ten_sevenths_lt_inv_ell)

theorem curvatureModel_artanh_small {u : ℝ} (hu0 : 0 < u) (hu5 : u ≤ 1 / 5) :
    curvatureModel u (Real.artanh u) < 1 / ell := by
  have hu : u ∈ Set.Ico (0 : ℝ) 1 := ⟨hu0.le, by linarith⟩
  exact curvatureModel_small_of_cubic_bounds hu0 hu5
    (cubic_le_artanh hu) (artanh_le_cubic_tail hu)

theorem rSecondDeriv_le_inv_ell {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s0) :
    rSecondDeriv s ≤ 1 / ell := by
  by_cases hs_zero : s = 0
  · subst s
    rw [rSecondDeriv_zero]
    exact (show (4 / 3 : ℝ) < 10 / 7 by norm_num).trans ten_sevenths_lt_inv_ell |>.le
  · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs_zero)
    have hsell : s < ell := hs.trans_lt s0_lt_ell
    have hu := psiInv_mem_Ioo ⟨hsp, hsell⟩
    have hu5 : psiInv s ≤ 1 / 5 := by
      apply (strictMonoOn_psi.le_iff_le ⟨hu.1.le, hu.2.le⟩ (by norm_num)).mp
      rw [psi_psiInv hs0 hsell]
      exact hs
    change (if s ≤ 0 then 4 / 3 else curvatureModel (psiInv s) (Real.artanh (psiInv s))) ≤ _
    rw [if_neg (not_le.mpr hsp)]
    exact (curvatureModel_artanh_small hu.1 hu5).le

theorem entropy_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ^ 2 * curvatureModel u (Real.artanh u) ≤ 2 / 3 := by
  by_cases hz : u ^ 2 ≤ 2 / 3
  · exact medium_curvature_bound hu0 hu1 hz
  · exact large_curvature_bound hu0.le hu1 (le_of_not_ge hz)

theorem inverseEntropy_curvature_bound {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) ell) :
    (ell - s) ^ 2 * rSecondDeriv s ≤ 2 / 3 := by
  have hu := psiInv_mem_Ioo hs
  have h := entropy_curvature_bound hu.1 hu.2
  rw [rSecondDeriv, if_neg (not_le.mpr hs.1)]
  simpa only [entropy, psi_psiInv hs.1.le hs.2, curvatureModel] using h

theorem L_curvature_bound {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) ell) :
    x ^ 2 * rSecondDeriv (ell - x) ≤ 2 / 3 := by
  have hs : ell - x ∈ Ioo (0 : ℝ) ell := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa only [sub_sub_cancel] using inverseEntropy_curvature_bound hs

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def LSecondDeriv (x : ℝ) : ℝ :=
  if x < ell then rSecondDeriv (ell - x) else 0

theorem LDeriv_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : LDeriv x = 0 := by
  simp [LDeriv, not_lt.mpr hx]

theorem LSecondDeriv_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : LSecondDeriv x = 0 := by
  simp [LSecondDeriv, not_lt.mpr hx]

private theorem L_eq_rGap_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    L x = rGap (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact L_eq_rGap ⟨hx.1, hlt⟩
  · simp [L]

private theorem LDeriv_eq_formula_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    LDeriv x = 2 - rDeriv (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact if_pos ⟨hx.1, hlt⟩
  · simp [LDeriv]

private theorem L_join_neighborhood : Ioc (0 : ℝ) ell ∪ Ici ell ∈ 𝓝 ell := by
  apply mem_of_superset (Ioi_mem_nhds ell_pos)
  intro x hx
  rcases le_total x ell with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

theorem hasDerivAt_L_of_gt {x : ℝ} (hx : ell < x) :
    HasDerivAt L (LDeriv x) x := by
  have he : L =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact L_eq_zero_of_ell_le (le_of_lt hy)
  rw [LDeriv_eq_zero_of_ell_le hx.le]
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

theorem hasDerivAt_LDeriv_of_gt {x : ℝ} (hx : ell < x) :
    HasDerivAt LDeriv 0 x := by
  have he : LDeriv =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact LDeriv_eq_zero_of_ell_le (le_of_lt hy)
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

theorem hasDerivAt_LDeriv {x : ℝ} (hx : 0 < x) (hne : x ≠ ell) :
    HasDerivAt LDeriv (LSecondDeriv x) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simpa only [LSecondDeriv, if_pos hlt] using hasDerivAt_LDeriv_of_lt ⟨hx, hlt⟩
  · rw [LSecondDeriv_eq_zero_of_ell_le hgt.le]
    exact hasDerivAt_LDeriv_of_gt hgt

theorem hasDerivAt_L_at_ell : HasDerivAt L (LDeriv ell) ell := by
  have hleft0 : HasDerivWithinAt (fun x : ℝ => rGap (ell - x)) 0 (Ioc 0 ell) ell := by
    convert! hasDerivWithinAt_rGap_zero.comp_of_eq ell
      ((hasDerivAt_id ell).const_sub ell).hasDerivWithinAt
      (show MapsTo (fun x : ℝ => ell - x) (Ioc 0 ell) (Ici 0) from
        fun x hx => sub_nonneg.mpr hx.2) (by simp) using 1
    simp
  have hleft : HasDerivWithinAt L 0 (Ioc 0 ell) ell :=
    hleft0.congr (fun _ hx => L_eq_rGap_on_left hx) (by simp [L])
  have hright : HasDerivWithinAt L 0 (Ici ell) ell :=
    (hasDerivAt_const ell (0 : ℝ)).hasDerivWithinAt.congr
      (fun _ hx => L_eq_zero_of_ell_le hx) (L_eq_zero_of_ell_le le_rfl)
  simpa only [LDeriv_eq_zero_of_ell_le (le_refl ell)] using
    (hleft.union hright).hasDerivAt L_join_neighborhood

theorem hasDerivAt_L {x : ℝ} (hx : 0 < x) : HasDerivAt L (LDeriv x) x := by
  rcases lt_trichotomy x ell with hlt | rfl | hgt
  · exact hasDerivAt_L_of_lt ⟨hx, hlt⟩
  · exact hasDerivAt_L_at_ell
  · exact hasDerivAt_L_of_gt hgt

theorem continuousAt_LDeriv_at_ell : ContinuousAt LDeriv ell := by
  have hr : ContinuousWithinAt rDeriv (Ico 0 ell) 0 :=
    continuousOn_rDeriv 0 ⟨le_rfl, ell_pos⟩
  have hcomp : ContinuousWithinAt (fun x : ℝ => rDeriv (ell - x)) (Ioc 0 ell) ell := by
    exact hr.comp_of_eq
      ((continuous_const.sub continuous_id).continuousWithinAt :
        ContinuousWithinAt (fun x : ℝ => ell - x) (Ioc 0 ell) ell)
      (show MapsTo (fun x : ℝ => ell - x) (Ioc 0 ell) (Ico 0 ell) from
        fun x hx => ⟨sub_nonneg.mpr hx.2, by linarith [hx.1]⟩) (by simp)
  have hleft : ContinuousWithinAt LDeriv (Ioc 0 ell) ell :=
    (continuousWithinAt_const.sub hcomp).congr
      (fun _ hx => LDeriv_eq_formula_on_left hx) (by simp [LDeriv])
  have hright : ContinuousWithinAt LDeriv (Ici ell) ell :=
    continuousWithinAt_const.congr (fun _ hx => LDeriv_eq_zero_of_ell_le hx)
      (LDeriv_eq_zero_of_ell_le le_rfl)
  exact (hleft.union hright).continuousAt L_join_neighborhood

theorem continuousOn_LDeriv : ContinuousOn LDeriv (Ioi 0) := by
  intro x hx
  by_cases hxe : x = ell
  · subst x
    exact continuousAt_LDeriv_at_ell.continuousWithinAt
  · exact (hasDerivAt_LDeriv hx hxe).continuousAt.continuousWithinAt

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem L_eq_rGap_max {x : ℝ} (hx : 0 < x) :
    L x = rGap (max (ell - x) 0) := by
  by_cases hxl : x < ell
  · rw [L_eq_rGap ⟨hx, hxl⟩, max_eq_left (sub_nonneg.mpr hxl.le)]
  · rw [L_eq_zero_of_ell_le (le_of_not_gt hxl),
      max_eq_right (sub_nonpos.mpr (le_of_not_gt hxl)), rGap_zero]

theorem positivePart_ell_sub_mem {x : ℝ} (hx : 0 < x) :
    max (ell - x) 0 ∈ Ico 0 ell := by
  exact ⟨le_max_right _ _, max_lt (by linarith) ell_pos⟩

theorem L_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ L x := by
  rw [L_eq_rGap_max hx]
  exact rGap_nonneg (positivePart_ell_sub_mem hx).1 (positivePart_ell_sub_mem hx).2

theorem antitoneOn_L : AntitoneOn L (Ioi 0) := by
  intro x hx y hy hxy
  rw [L_eq_rGap_max hx, L_eq_rGap_max hy]
  exact monotoneOn_rGap (positivePart_ell_sub_mem hy) (positivePart_ell_sub_mem hx)
    (max_le_max (sub_le_sub_left hxy ell) le_rfl)

theorem convexOn_L : ConvexOn ℝ (Ioi 0) L := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 0 < a * x + b * y := by
    simpa only [smul_eq_mul, mem_Ioi] using (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have hsum : a * max (ell - x) 0 + b * max (ell - y) 0 ∈ Ico 0 ell := by
    simpa only [smul_eq_mul] using
      (convex_Ico (0 : ℝ) ell) (positivePart_ell_sub_mem hx)
        (positivePart_ell_sub_mem hy) ha hb hab
  have hmax : max (ell - (a * x + b * y)) 0 ≤
      a * max (ell - x) 0 + b * max (ell - y) 0 := by
    apply max_le
    · calc
        ell - (a * x + b * y) = a * (ell - x) + b * (ell - y) := by
          nlinarith [congrArg (fun t : ℝ => t * ell) hab]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _))
        (mul_nonneg hb (le_max_right _ _))
  simp only [smul_eq_mul]
  rw [L_eq_rGap_max hz, L_eq_rGap_max hx, L_eq_rGap_max hy]
  exact (monotoneOn_rGap (positivePart_ell_sub_mem hz) hsum hmax).trans
    (convexOn_rGap.2 (positivePart_ell_sub_mem hx) (positivePart_ell_sub_mem hy)
      ha hb hab)

theorem L_tangent_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    L x + LDeriv x * (y - x) ≤ L y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := convexOn_L.le_slope_of_hasDerivAt hx hy hxy (hasDerivAt_L hx)
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    linarith
  · simp
  · have hs := convexOn_L.slope_le_of_hasDerivAt hy hx hyx (hasDerivAt_L hx)
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp hs
    nlinarith

theorem L_support : ∀ x, 0 < x → ∀ y, 0 < y →
    L x + LDeriv x * (y - x) ≤ L y :=
  fun _ hx _ hy => L_tangent_le hx hy

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def noiseFlow (F : Cube n → ℝ) (t : ℝ) : Cube n → ℝ :=
  noiseOperator (Real.exp (-t)) F

private theorem noiseKernel_flip_derivative_term (u : ℝ)
    (x y : Cube n) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i,
      if x j = y j then (1 + u) / 2 else (1 - u) / 2) *
      (if x i = y i then -u / 2 else u / 2) =
        -((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) := by
  have hrest : (∏ j ∈ Finset.univ.erase i,
      if (flip i x) j = y j then (1 + u) / 2 else (1 - u) / 2) =
      ∏ j ∈ Finset.univ.erase i,
        if x j = y j then (1 + u) / 2 else (1 - u) / 2 := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [flip, LeanBlast.GotsmanLinial.flip, Function.update_of_ne hji]
  rw [noiseKernel_split_coord u x y i, noiseKernel_split_coord u (flip i x) y i, hrest]
  cases hx : x i <;> cases hy : y i <;>
    simp [flip, LeanBlast.GotsmanLinial.flip, hx] <;> ring

private theorem hasDerivAt_noise_factor (x y : Cube n) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ =>
      if x i = y i then (1 + Real.exp (-s)) / 2 else (1 - Real.exp (-s)) / 2)
      (if x i = y i then -Real.exp (-t) / 2 else Real.exp (-t) / 2) t := by
  have hu : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  by_cases hxy : x i = y i
  · simp only [if_pos hxy]
    exact (hu.const_add 1).div_const 2
  · simp only [if_neg hxy]
    simpa using (hu.const_sub 1).div_const 2

theorem hasDerivAt_noiseKernel_flow (x y : Cube n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => noiseKernel (Real.exp (-s)) x y)
      (-(∑ i : Fin n,
        (noiseKernel (Real.exp (-t)) x y -
          noiseKernel (Real.exp (-t)) (flip i x) y) / 2)) t := by
  have h := HasDerivAt.fun_finsetProd
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hasDerivAt_noise_factor x y i t)
  convert! h using 1
  simp only [smul_eq_mul, noiseKernel_flip_derivative_term, Finset.sum_neg_distrib]

theorem cubeDerivative_noiseOperator (u : ℝ) (F : Cube n → ℝ)
    (i : Fin n) (x : Cube n) :
    cubeDerivative i (noiseOperator u F) x =
      ∑ y, ((noiseKernel u x y - noiseKernel u (flip i x) y) / 2) * F y := by
  simp [cubeDerivative, noiseOperator, sub_div, sub_mul,
    div_mul_eq_mul_div, Finset.sum_sub_distrib, Finset.sum_div]

theorem hasDerivAt_noiseFlow (F : Cube n → ℝ) (t : ℝ) (x : Cube n) :
    HasDerivAt (fun s : ℝ => noiseFlow F s x)
      (-(∑ i : Fin n, cubeDerivative i (noiseFlow F t) x)) t := by
  have h := HasDerivAt.fun_sum
    (fun y (_ : y ∈ (Finset.univ : Finset (Cube n))) =>
      (hasDerivAt_noiseKernel_flow x y t).mul_const (F y))
  convert! h using 1
  simp only [noiseFlow, cubeDerivative_noiseOperator, neg_mul,
    Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

theorem continuous_noiseFlow (F : Cube n → ℝ) (x : Cube n) :
    Continuous (fun t : ℝ => noiseFlow F t x) := by
  exact continuous_iff_continuousAt.mpr fun t => (hasDerivAt_noiseFlow F t x).continuousAt

@[simp]
theorem noiseFlow_zero (F : Cube n → ℝ) : noiseFlow F 0 = F := by
  funext x
  simp [noiseFlow]

theorem cubeAverage_noiseFlow (F : Cube n → ℝ) (t : ℝ) :
    cubeAverage (noiseFlow F t) = cubeAverage F :=
  cubeAverage_noiseOperator _ _

theorem isInterior_noiseFlow (F : Cube n → ℝ) (hF : IsSignValued F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t) :
    IsInterior (noiseFlow F t) := by
  apply noiseOperator_isInterior (Real.exp_pos _).le _ hF hnc
  rw [Real.exp_lt_one_iff]
  linarith

theorem isIncreasing_noiseFlow (F : Cube n → ℝ) (hF : IsIncreasing F)
    {t : ℝ} (ht : 0 ≤ t) : IsIncreasing (noiseFlow F t) := by
  apply isIncreasing_noiseOperator ⟨(Real.exp_pos _).le, ?_⟩ hF
  rw [Real.exp_le_one_iff]
  linarith

theorem hasDerivAt_entropyAverage_noiseFlow_of_isInterior
    (F : Cube n → ℝ) (t : ℝ) (hinterior : IsInterior (noiseFlow F t)) :
    HasDerivAt (fun s : ℝ => entropyAverage (noiseFlow F s))
      (dissipation (noiseFlow F t)) t := by
  have h := (HasDerivAt.fun_sum
    (fun x (_ : x ∈ (Finset.univ : Finset (Cube n))) =>
      (hasDerivAt_entropy (hinterior x)).comp t (hasDerivAt_noiseFlow F t x))).div_const
      ((2 : ℝ) ^ n)
  convert! h using 1
  simp only [dissipation, cubeAverage, neg_mul_neg, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_comm

theorem hasDerivAt_entropyAverage_noiseFlow
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => entropyAverage (noiseFlow F s))
      (dissipation (noiseFlow F t)) t :=
  hasDerivAt_entropyAverage_noiseFlow_of_isInterior F t (isInterior_noiseFlow F hF hnc ht)

theorem hasDerivAt_informationDeficit_noiseFlow_of_isInterior
    (F : Cube n → ℝ) (t : ℝ) (hinterior : IsInterior (noiseFlow F t)) :
    HasDerivAt (fun s : ℝ => informationDeficit (noiseFlow F s))
      (-dissipation (noiseFlow F t)) t := by
  simpa only [informationDeficit, cubeAverage_noiseFlow] using
    (hasDerivAt_entropyAverage_noiseFlow_of_isInterior F t hinterior).const_sub
      (entropy (cubeAverage F))

theorem hasDerivAt_informationDeficit_noiseFlow
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => informationDeficit (noiseFlow F s))
      (-dissipation (noiseFlow F t)) t :=
  hasDerivAt_informationDeficit_noiseFlow_of_isInterior F t (isInterior_noiseFlow F hF hnc ht)

theorem continuous_entropyAverage_noiseFlow (F : Cube n → ℝ) :
    Continuous (fun t : ℝ => entropyAverage (noiseFlow F t)) := by
  apply Continuous.div_const
  exact continuous_finsetSum _ fun x _ => continuous_entropy.comp (continuous_noiseFlow F x)

theorem continuous_informationDeficit_noiseFlow (F : Cube n → ℝ) :
    Continuous (fun t : ℝ => informationDeficit (noiseFlow F t)) := by
  simp only [informationDeficit, cubeAverage_noiseFlow]
  exact continuous_const.sub (continuous_entropyAverage_noiseFlow F)

theorem entropyAverage_eq_zero_of_signValued (F : Cube n → ℝ) (hF : IsSignValued F) :
    entropyAverage F = 0 := by
  have hzero : ∀ x, entropy (F x) = 0 := by
    intro x
    rcases hF x with h | h <;> rw [h] <;> simp
  simp only [entropyAverage, cubeAverage, hzero, Finset.sum_const_zero, zero_div]

theorem tendsto_entropyAverage_noiseFlow_zero
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    Tendsto (fun t : ℝ => entropyAverage (noiseFlow F t)) (𝓝 0) (𝓝 0) := by
  simpa only [noiseFlow_zero, entropyAverage_eq_zero_of_signValued F hF] using
    (continuous_entropyAverage_noiseFlow F).continuousAt.tendsto (x := 0)

theorem tendsto_entropyAverage_noiseFlow_zero_right
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    Tendsto (fun t : ℝ => entropyAverage (noiseFlow F t)) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_entropyAverage_noiseFlow_zero F hF).mono_left nhdsWithin_le_nhds

theorem entropyAverage_noiseFlow_pos
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y)
    {t : ℝ} (ht : 0 < t) : 0 < entropyAverage (noiseFlow F t) := by
  apply div_pos _ (cube_denominator_pos n)
  exact Finset.sum_pos
    (fun x _ => entropy_pos (isInterior_noiseFlow F hF hnc ht x)) Finset.univ_nonempty

end LeanBlast.CourtadeKumar

end

end OAI
end

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

theorem cubeAverage_pairHalfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairHalfDifference g) =
      (cubeAverage (restrict g true) - cubeAverage (restrict g false)) / 2 := by
  unfold pairHalfDifference
  rw [cubeAverage_div, cubeAverage_sub]

theorem cubeAverage_pairMean_add_halfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) + cubeAverage (pairHalfDifference g) =
      cubeAverage (restrict g true) := by
  rw [cubeAverage_pairMean, cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem cubeAverage_pairMean_sub_halfDifference (g : Cube (n + 1) → ℝ) :
    cubeAverage (pairMean g) - cubeAverage (pairHalfDifference g) =
      cubeAverage (restrict g false) := by
  rw [cubeAverage_pairMean, cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem entropyAverage_split (g : Cube (n + 1) → ℝ) :
    entropyAverage g = (entropyAverage (restrict g true) + entropyAverage (restrict g false)) / 2 := by
  exact cubeAverage_split (fun x => entropy (g x))

theorem cubeAverage_pairEntropyGap (g : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) =
      entropyAverage (pairMean g) - entropyAverage g := by
  simp only [pairEntropyGap, pairMean_add_halfDifference, pairMean_sub_halfDifference]
  rw [cubeAverage_sub, cubeAverage_div, cubeAverage_add]
  change entropyAverage (pairMean g) -
    (entropyAverage (restrict g true) + entropyAverage (restrict g false)) / 2 = _
  rw [← entropyAverage_split]

theorem informationDeficit_split (g : Cube (n + 1) → ℝ) :
    (informationDeficit (restrict g true) + informationDeficit (restrict g false)) / 2 =
      informationDeficit g - pairEntropyGap (cubeAverage (pairMean g))
        (cubeAverage (pairHalfDifference g)) := by
  rw [pairEntropyGap, cubeAverage_pairMean_add_halfDifference,
    cubeAverage_pairMean_sub_halfDifference, cubeAverage_pairMean]
  simp only [informationDeficit]
  rw [entropyAverage_split]
  ring

theorem informationDeficit_eq_pairMean_add (g : Cube (n + 1) → ℝ) :
    informationDeficit g = informationDeficit (pairMean g) +
      cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) := by
  rw [cubeAverage_pairEntropyGap]
  simp only [informationDeficit, cubeAverage_pairMean]
  ring

theorem meanVariance_split (g : Cube (n + 1) → ℝ) :
    (meanVariance (restrict g true) + meanVariance (restrict g false)) / 2 =
      meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2 := by
  simp only [meanVariance]
  rw [cubeAverage_split, cubeAverage_pairHalfDifference]
  ring

theorem flip_zero_cases (b : Bool) (x : Cube n) :
    flip (0 : Fin (n + 1)) (Fin.cases b x) = Fin.cases (!b) x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [flip, LeanBlast.GotsmanLinial.flip]
  · simp [flip, LeanBlast.GotsmanLinial.flip]

theorem flip_succ_cases (i : Fin n) (b : Bool) (x : Cube n) :
    flip i.succ (Fin.cases b x) = Fin.cases b (flip i x) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · have h0 : (0 : Fin (n + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
    simp [flip, LeanBlast.GotsmanLinial.flip, h0]
  · by_cases hki : k = i
    · subst k
      simp [flip, LeanBlast.GotsmanLinial.flip]
    · simp [flip, LeanBlast.GotsmanLinial.flip, hki]

theorem cubeAverage_first_coordinate_energy (g : Cube (n + 1) → ℝ) :
    cubeAverage (fun x => Real.artanh (g x) * cubeDerivative 0 g x) =
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) := by
  rw [cubeAverage_split_pair]
  congr 1
  funext x
  simp only [restrict, cubeDerivative, flip_zero_cases, Bool.not_true, Bool.not_false]
  rw [pairDissipation, pairMean_add_halfDifference, pairMean_sub_halfDifference]
  dsimp only [pairHalfDifference, restrict]
  ring

theorem cubeAverage_succ_coordinate_energy (g : Cube (n + 1) → ℝ) (i : Fin n) :
    cubeAverage (fun x => Real.artanh (g x) * cubeDerivative i.succ g x) =
      (cubeAverage (fun x => Real.artanh (restrict g true x) * cubeDerivative i (restrict g true) x) +
        cubeAverage (fun x => Real.artanh (restrict g false x) * cubeDerivative i (restrict g false) x)) / 2 := by
  have hr (b : Bool) :
      restrict (fun x => Real.artanh (g x) * cubeDerivative i.succ g x) b =
        (fun x => Real.artanh (restrict g b x) * cubeDerivative i (restrict g b) x) := by
    funext x
    simp only [restrict, cubeDerivative, flip_succ_cases]
  rw [cubeAverage_split, hr true, hr false]

theorem dissipation_split (g : Cube (n + 1) → ℝ) :
    dissipation g = (dissipation (restrict g true) + dissipation (restrict g false)) / 2 +
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) := by
  simp only [dissipation]
  rw [Fin.sum_univ_succ, cubeAverage_first_coordinate_energy]
  simp_rw [cubeAverage_succ_coordinate_energy]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  ring

theorem IsInterior.restrict {g : Cube (n + 1) → ℝ} (hg : IsInterior g) (b : Bool) :
    IsInterior (LeanBlast.CourtadeKumar.restrict g b) := by
  intro x
  exact hg (Fin.cases b x)

theorem IsInterior.pairMean {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    IsInterior (LeanBlast.CourtadeKumar.pairMean g) := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  dsimp only [LeanBlast.CourtadeKumar.pairMean]
  constructor <;> linarith

theorem IsInterior.pairDomain {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    ∀ x, |LeanBlast.CourtadeKumar.pairMean g x| + |pairHalfDifference g x| < 1 := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  have hsum := pairMean_add_halfDifference g x
  have hsub := pairMean_sub_halfDifference g x
  rcases le_total 0 (LeanBlast.CourtadeKumar.pairMean g x) with ha | ha <;>
    rcases le_total 0 (pairHalfDifference g x) with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hb]
    linarith

def cubeVariance (g : Cube n → ℝ) : ℝ :=
  cubeAverage (fun x => (g x - cubeAverage g) ^ 2)

theorem cubeVariance_nonneg (g : Cube n → ℝ) : 0 ≤ cubeVariance g :=
  cubeAverage_nonneg fun _ => sq_nonneg _

theorem cubeVariance_eq (g : Cube n → ℝ) :
    cubeVariance g = cubeAverage (fun x => (g x) ^ 2) - (cubeAverage g) ^ 2 := by
  unfold cubeVariance
  have heq : (fun x => (g x - cubeAverage g) ^ 2) =
      (fun x => (g x) ^ 2 - (2 * cubeAverage g) * g x + (cubeAverage g) ^ 2) := by
    funext x
    ring
  rw [heq, cubeAverage_add, cubeAverage_sub, cubeAverage_smul, cubeAverage_const]
  ring

theorem average_one_sub_sq_eq_meanVariance_sub_variance (g : Cube n → ℝ) :
    cubeAverage (fun x => 1 - (g x) ^ 2) = meanVariance g - cubeVariance g := by
  rw [cubeAverage_sub, cubeAverage_const, cubeVariance_eq]
  unfold meanVariance
  ring

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

section
namespace OAI

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem hasDerivAt_tangent_extension (F : ℝ → ℝ) {c d : ℝ}
    (hF : HasDerivAt F d c) :
    HasDerivAt (fun s => if s ≤ c then F s else F c + d * (s - c)) d c := by
  let T : ℝ → ℝ := fun s => if s ≤ c then F s else F c + d * (s - c)
  have hleft : HasDerivWithinAt T d (Iic c) c := by
    apply hF.hasDerivWithinAt.congr
    · intro s hs
      change s ≤ c at hs
      simp only [T, if_pos hs]
    · simp [T]
  have hline : HasDerivAt (fun s : ℝ => F c + d * (s - c)) d c := by
    convert! (((hasDerivAt_id c).sub_const c).const_mul d).const_add (F c) using 1
    ring
  have hright : HasDerivWithinAt T d (Ici c) c := by
    apply hline.hasDerivWithinAt.congr
    · intro s hs
      change c ≤ s at hs
      rcases hs.eq_or_lt with rfl | hs
      · simp [T]
      · simp [T, not_le.mpr hs]
    · simp [T]
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

theorem clamp_nonexpansive (c x y : ℝ) :
    |min (max x 0) c - min (max y 0) c| ≤ |x - y| := by
  have h : LipschitzWith 1 (fun s : ℝ => min (max s 0) c) :=
    (LipschitzWith.id.max_const 0).min_const c
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

theorem K_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : K s = 0 := by simp [K, hs]

theorem KDeriv_eq_clamp (s : ℝ) :
    KDeriv s = rDeriv (min (max s 0) s0) - 2 := by
  by_cases hs : s ≤ 0
  · simp [KDeriv, hs, min_eq_left s0_pos.le]
  · have hs0 : 0 ≤ s := (lt_of_not_ge hs).le
    by_cases hsc : s ≤ s0
    · simp [KDeriv, hs, hsc, max_eq_left hs0]
    · simp [KDeriv, hs, hsc, max_eq_left hs0, min_eq_right (le_of_not_ge hsc)]

theorem K_eq_rGap_nonneg {s : ℝ} (hs : 0 ≤ s) (hsc : s ≤ s0) : K s = rGap s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp
  · exact K_eq_rGap hs hsc

theorem clamp_mem_inverse_domain (s : ℝ) : min (max s 0) s0 ∈ Ico 0 ell :=
  ⟨le_min (le_max_right s 0) s0_pos.le, (min_le_right _ _).trans_lt s0_lt_ell⟩

theorem hasDerivAt_K_pos {s : ℝ} (hs : 0 < s) : HasDerivAt K (KDeriv s) s := by
  by_cases hsc : s < s0
  · have he : K =ᶠ[𝓝 s] rGap := by
      filter_upwards [Ioo_mem_nhds hs hsc] with t ht
      exact K_eq_rGap ht.1 ht.2.le
    have hKd : KDeriv s = rDeriv s - 2 := by simp [KDeriv, not_le.mpr hs, hsc.le]
    rw [hKd]
    exact (hasDerivAt_rGap ⟨hs, hsc.trans s0_lt_ell⟩).congr_of_eventuallyEq he
  · have hsc' : s0 ≤ s := le_of_not_gt hsc
    rcases hsc'.eq_or_lt with rfl | hsc'
    · have hjoin := hasDerivAt_tangent_extension rGap (hasDerivAt_rGap ⟨s0_pos, s0_lt_ell⟩)
      have he : K =ᶠ[𝓝 s0]
          (fun t => if t ≤ s0 then rGap t else rGap s0 + (rDeriv s0 - 2) * (t - s0)) := by
        filter_upwards [Ioi_mem_nhds s0_pos] with t ht
        change 0 < t at ht
        simp only [K, if_neg (not_le.mpr ht)]
      have hKd : KDeriv s0 = rDeriv s0 - 2 := by simp [KDeriv, not_le.mpr s0_pos]
      rw [hKd]
      exact hjoin.congr_of_eventuallyEq he
    · have hline : HasDerivAt
          (fun t : ℝ => rGap s0 + (rDeriv s0 - 2) * (t - s0)) (rDeriv s0 - 2) s := by
        convert! (((hasDerivAt_id s).sub_const s0).const_mul (rDeriv s0 - 2)).const_add
          (rGap s0) using 1
        ring
      have he : K =ᶠ[𝓝 s]
          (fun t => rGap s0 + (rDeriv s0 - 2) * (t - s0)) := by
        filter_upwards [Ioi_mem_nhds hsc'] with t ht
        exact K_eq_tangent (s0_pos.trans ht) ht.le
      have hKd : KDeriv s = rDeriv s0 - 2 := by
        simp [KDeriv, not_le.mpr hs, not_le.mpr hsc']
      rw [hKd]
      exact hline.congr_of_eventuallyEq he

theorem hasDerivAt_K_zero_of_right_derivative
    (hzero : HasDerivWithinAt rGap 0 (Ici 0) 0) : HasDerivAt K 0 0 := by
  have hleft : HasDerivWithinAt K 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
    · intro s hs
      exact K_eq_zero_of_nonpos hs
    · simp
  have hright : HasDerivWithinAt K 0 (Ici 0) 0 := by
    apply hzero.congr_of_eventuallyEq
    · have hnear : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, s < s0 :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds s0_pos)
      filter_upwards [self_mem_nhdsWithin, hnear] with s hs hs0
      exact K_eq_rGap_nonneg hs hs0.le
    · simp
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hleft.union hright

theorem KDeriv_monotone_of_rDeriv
    (hmono : MonotoneOn rDeriv (Ico 0 ell)) : Monotone KDeriv := by
  intro x y hxy
  rw [KDeriv_eq_clamp, KDeriv_eq_clamp]
  exact sub_le_sub_right
    (hmono (clamp_mem_inverse_domain x) (clamp_mem_inverse_domain y)
      (min_le_min_right s0 (max_le_max_right 0 hxy))) 2

theorem KDeriv_lipschitz_of_rDeriv {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc (0 : ℝ) s0, ∀ y ∈ Icc (0 : ℝ) s0,
      |rDeriv x - rDeriv y| ≤ C * |x - y|) (x y : ℝ) :
    |KDeriv x - KDeriv y| ≤ C * |x - y| := by
  rw [KDeriv_eq_clamp, KDeriv_eq_clamp]
  have hx : min (max x 0) s0 ∈ Icc (0 : ℝ) s0 :=
    ⟨le_min (le_max_right x 0) s0_pos.le, min_le_right _ _⟩
  have hy : min (max y 0) s0 ∈ Icc (0 : ℝ) s0 :=
    ⟨le_min (le_max_right y 0) s0_pos.le, min_le_right _ _⟩
  rw [show rDeriv (min (max x 0) s0) - 2 - (rDeriv (min (max y 0) s0) - 2) =
    rDeriv (min (max x 0) s0) - rDeriv (min (max y 0) s0) by ring]
  exact (hbound _ hx _ hy).trans
    (mul_le_mul_of_nonneg_left (clamp_nonexpansive s0 x y) hC)

theorem rDeriv_increment_le_of_continuous
    (hcont : ContinuousOn rDeriv (Icc 0 s0))
    {x y : ℝ} (hx : x ∈ Icc 0 s0) (hy : y ∈ Icc 0 s0) (hxy : x ≤ y) :
    rDeriv y - rDeriv x ≤ (1 / ell) * (y - x) := by
  have hdiff : DifferentiableOn ℝ rDeriv (interior (Icc 0 s0)) := by
    intro s hs
    have hsi : s ∈ Ioo 0 s0 := by simpa only [interior_Icc] using hs
    exact (hasDerivAt_rDeriv ⟨hsi.1, hsi.2.trans s0_lt_ell⟩).differentiableAt.differentiableWithinAt
  have hbound : ∀ s ∈ interior (Icc 0 s0), deriv rDeriv s ≤ 1 / ell := by
    intro s hs
    have hsi : s ∈ Ioo 0 s0 := by simpa only [interior_Icc] using hs
    rw [(hasDerivAt_rDeriv ⟨hsi.1, hsi.2.trans s0_lt_ell⟩).deriv]
    exact rSecondDeriv_le_inv_ell hsi.1.le hsi.2.le
  exact (convex_Icc (0 : ℝ) s0).image_sub_le_mul_sub_of_deriv_le
    hcont hdiff hbound x hx y hy hxy

theorem rDeriv_lipschitz_of_continuous_monotone
    (hcont : ContinuousOn rDeriv (Icc 0 s0))
    (hmono : MonotoneOn rDeriv (Icc 0 s0))
    {x y : ℝ} (hx : x ∈ Icc 0 s0) (hy : y ∈ Icc 0 s0) :
    |rDeriv x - rDeriv y| ≤ (1 / ell) * |x - y| := by
  rcases le_total x y with hxy | hyx
  · calc
      |rDeriv x - rDeriv y| = rDeriv y - rDeriv x := by
        rw [abs_of_nonpos (sub_nonpos.mpr (hmono hx hy hxy))]
        ring
      _ ≤ (1 / ell) * (y - x) := rDeriv_increment_le_of_continuous hcont hx hy hxy
      _ = (1 / ell) * |x - y| := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono hy hx hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact rDeriv_increment_le_of_continuous hcont hy hx hyx

theorem K_le_rGap_of_convex (hconvex : ConvexOn ℝ (Ico 0 ell) rGap)
    {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : K s ≤ rGap s := by
  by_cases hsc : s ≤ s0
  · rw [K_eq_rGap_nonneg hs hsc]
  · have hsc' : s0 < s := lt_of_not_ge hsc
    rw [K_eq_tangent (s0_pos.trans hsc') hsc'.le]
    have hslope := hconvex.le_slope_of_hasDerivAt ⟨s0_pos.le, s0_lt_ell⟩
      ⟨hs, hsell⟩ hsc' (hasDerivAt_rGap ⟨s0_pos, s0_lt_ell⟩)
    rw [slope_def_field] at hslope
    have hmul := (le_div_iff₀ (sub_pos.mpr hsc')).mp hslope
    linarith

theorem K_nonneg_of_rGap_nonneg
    (hgap : ∀ s : ℝ, 0 ≤ s → s < ell → 0 ≤ rGap s)
    (hslope : 0 ≤ rDeriv s0 - 2) (s : ℝ) : 0 ≤ K s := by
  by_cases hs : s ≤ 0
  · rw [K_eq_zero_of_nonpos hs]
  · have hs' : 0 < s := lt_of_not_ge hs
    by_cases hsc : s ≤ s0
    · rw [K_eq_rGap hs' hsc]
      exact hgap s hs'.le (hsc.trans_lt s0_lt_ell)
    · have hsc' : s0 < s := lt_of_not_ge hsc
      rw [K_eq_tangent hs' hsc'.le]
      exact add_nonneg (hgap s0 s0_pos.le s0_lt_ell)
        (mul_nonneg hslope (sub_nonneg.mpr hsc'.le))

theorem convexOn_K_of_shape
    (hzero : HasDerivWithinAt rGap 0 (Ici 0) 0)
    (hmono : MonotoneOn rDeriv (Ico 0 ell)) : ConvexOn ℝ (Ici 0) K := by
  have hd : ∀ s ∈ Ici (0 : ℝ), HasDerivAt K (KDeriv s) s := by
    intro s hs
    rcases (show 0 ≤ s from hs).eq_or_lt with rfl | hs
    · simpa only [KDeriv_zero] using hasDerivAt_K_zero_of_right_derivative hzero
    · exact hasDerivAt_K_pos hs
  have hc : ContinuousOn K (Ici 0) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ K (interior (Ici 0)) := by
    intro s hs
    exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hm : MonotoneOn (deriv K) (interior (Ici 0)) := by
    intro x hx y hy hxy
    rw [(hd x (interior_subset hx)).deriv, (hd y (interior_subset hy)).deriv]
    exact KDeriv_monotone_of_rDeriv hmono hxy
  exact hm.convexOn_of_deriv (convex_Ici 0) hc hdiff

theorem hasDerivAt_K {s : ℝ} (hs : 0 ≤ s) : HasDerivAt K (KDeriv s) s := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa only [KDeriv_zero] using
      hasDerivAt_K_zero_of_right_derivative hasDerivWithinAt_rGap_zero
  · exact hasDerivAt_K_pos hs

theorem continuousOn_K : ContinuousOn K (Ici 0) :=
  fun _s hs => (hasDerivAt_K hs).continuousAt.continuousWithinAt

theorem convexOn_K : ConvexOn ℝ (Ici 0) K :=
  convexOn_K_of_shape hasDerivWithinAt_rGap_zero monotoneOn_rDeriv

theorem K_nonneg (s : ℝ) : 0 ≤ K s :=
  K_nonneg_of_rGap_nonneg (fun _ hs hsell => rGap_nonneg hs hsell)
    (sub_nonneg.mpr (rDeriv_ge_two s0_pos.le s0_lt_ell)) s

theorem K_le_rGap {s : ℝ} (hs : 0 ≤ s) (hsell : s < ell) : K s ≤ rGap s :=
  K_le_rGap_of_convex convexOn_rGap hs hsell

theorem KDeriv_lipschitz (x y : ℝ) :
    |KDeriv x - KDeriv y| ≤ (1 / ell) * |x - y| := by
  apply KDeriv_lipschitz_of_rDeriv (le_of_lt (one_div_pos.mpr ell_pos))
  intro a ha b hb
  have hsub : Icc (0 : ℝ) s0 ⊆ Ico 0 ell :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt s0_lt_ell⟩
  exact rDeriv_lipschitz_of_continuous_monotone
    (continuousOn_rDeriv.mono hsub) (monotoneOn_rDeriv.mono hsub) ha hb

end LeanBlast.CourtadeKumar

end OAI
end

section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem pair_mean_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a ∈ Set.Ioo (-1) 1 := by
  have ha : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  exact abs_lt.mp ha

theorem pair_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a + b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_add_le a b) h)

theorem pair_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) : a - b ∈ Set.Ioo (-1) 1 := by
  exact abs_lt.mp (lt_of_le_of_lt (abs_sub a b) h)

theorem pair_denom_add_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 + a := by
  have ha := (pair_mean_mem_Ioo a b h).1
  linarith

theorem pair_denom_sub_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a := by
  have ha := (pair_mean_mem_Ioo a b h).2
  linarith

theorem pair_abs_lt_denom_add (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 + a := by
  linarith [neg_le_abs a]

theorem pair_abs_lt_denom_sub (a b : ℝ) (h : |a| + |b| < 1) : |b| < 1 - a := by
  linarith [le_abs_self a]

private theorem div_mem_Ioo (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    b / s ∈ Set.Ioo (-1) 1 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  constructor
  · apply (lt_div_iff₀ hs).2
    linarith
  · apply (div_lt_iff₀ hs).2
    linarith

theorem pair_ratio_add_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 + a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h)

theorem pair_ratio_sub_mem_Ioo (a b : ℝ) (h : |a| + |b| < 1) :
    b / (1 - a) ∈ Set.Ioo (-1) 1 :=
  div_mem_Ioo (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)

theorem pair_variance_pos (a b : ℝ) (h : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have hp := mul_pos (pair_denom_add_pos a b h) (pair_denom_sub_pos a b h)
  nlinarith

theorem pair_abs_lt_variance (a b : ℝ) (h : |a| + |b| < 1) :
    |b| < 1 - a ^ 2 := by
  have ha1 : |a| < 1 := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) h
  have hprod := mul_nonneg (abs_nonneg a) (show 0 ≤ 1 - |a| by linarith)
  nlinarith [sq_abs a]

theorem pair_weighted_sq (a b : ℝ) (h : |a| + |b| < 1) :
    (1 + a) / 2 * (b / (1 + a)) ^ 2 + (1 - a) / 2 * (b / (1 - a)) ^ 2 =
      b ^ 2 / (1 - a ^ 2) := by
  have hp := ne_of_gt (pair_denom_add_pos a b h)
  have hm := ne_of_gt (pair_denom_sub_pos a b h)
  have hv := ne_of_gt (pair_variance_pos a b h)
  field_simp
  ring

@[simp] theorem pairEntropyGap_zero (a : ℝ) : pairEntropyGap a 0 = 0 := by
  simp [pairEntropyGap]

@[simp] theorem pairDissipation_zero (a : ℝ) : pairDissipation a 0 = 0 := by
  simp [pairDissipation]

private theorem weighted_psi_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    s / 2 * psi (b / s) =
      (s + b) / 4 * Real.log (s + b) + (s - b) / 4 * Real.log (s - b) -
        s / 2 * Real.log s := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [psi, hplus, hminus, Real.log_div hp hs0, Real.log_div hm hs0]
  field_simp
  ring

theorem pairEntropyGap_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b =
      (1 + a) / 2 * psi (b / (1 + a)) + (1 - a) / 2 * psi (b / (1 - a)) := by
  rw [weighted_psi_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    weighted_psi_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  unfold pairEntropyGap entropy psi
  ring_nf

private theorem pair_artanh_eq_log_sub (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    Real.artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨le_of_lt hx.1, le_of_lt hx.2⟩,
    Real.log_div (ne_of_gt (by linarith [hx.1])) (ne_of_gt (by linarith [hx.2]))]
  ring

private theorem artanh_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    Real.artanh (b / s) = (Real.log (s + b) - Real.log (s - b)) / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [pair_artanh_eq_log_sub _ (div_mem_Ioo s b hs hb), hplus, hminus,
    Real.log_div hp hs0, Real.log_div hm hs0]
  ring

theorem pairDissipation_weighted (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b =
      (1 + a) / 2 * (b / (1 + a) * Real.artanh (b / (1 + a))) +
        (1 - a) / 2 * (b / (1 - a) * Real.artanh (b / (1 - a))) := by
  have hp : 1 + a ≠ 0 := ne_of_gt (pair_denom_add_pos a b h)
  have hm : 1 - a ≠ 0 := ne_of_gt (pair_denom_sub_pos a b h)
  rw [pairDissipation, pair_artanh_eq_log_sub _ (pair_add_mem_Ioo a b h),
    pair_artanh_eq_log_sub _ (pair_sub_mem_Ioo a b h),
    artanh_div (1 + a) b (pair_denom_add_pos a b h) (pair_abs_lt_denom_add a b h),
    artanh_div (1 - a) b (pair_denom_sub_pos a b h) (pair_abs_lt_denom_sub a b h)]
  field_simp
  ring_nf

theorem pairDissipation_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairDissipation a b := by
  unfold pairDissipation
  by_cases hb : 0 ≤ b
  · apply mul_nonneg (by positivity)
    apply sub_nonneg.mpr
    exact Real.artanh_le_artanh (pair_sub_mem_Ioo a b h).1
      (pair_add_mem_Ioo a b h).2 (by linarith)
  · apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
    apply sub_nonpos.mpr
    exact Real.artanh_le_artanh (pair_add_mem_Ioo a b h).1
      (pair_sub_mem_Ioo a b h).2 (by linarith)

theorem pairEntropyGap_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b := by
  rw [pairEntropyGap_weighted a b h]
  exact add_nonneg
    (mul_nonneg (by linarith [pair_denom_add_pos a b h]) (psi_nonneg _))
    (mul_nonneg (by linarith [pair_denom_sub_pos a b h]) (psi_nonneg _))

theorem pairEntropyGap_div_variance_nonneg (a b : ℝ) (h : |a| + |b| < 1) :
    0 ≤ pairEntropyGap a b / (1 - a ^ 2) :=
  div_nonneg (pairEntropyGap_nonneg a b h) (le_of_lt (pair_variance_pos a b h))

theorem pairEntropyGap_lt_ell (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b < ell := by
  rw [pairEntropyGap_weighted a b h]
  calc
    _ < (1 + a) / 2 * ell + (1 - a) / 2 * ell :=
      add_lt_add
        (mul_lt_mul_of_pos_left (psi_lt_ell (pair_ratio_add_mem_Ioo a b h))
          (by linarith [pair_denom_add_pos a b h]))
        (mul_lt_mul_of_pos_left (psi_lt_ell (pair_ratio_sub_mem_Ioo a b h))
          (by linarith [pair_denom_sub_pos a b h]))
    _ = ell := by ring

theorem pairEntropyGap_le_quadratic (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b ≤ ell * (b ^ 2 / (1 - a ^ 2)) := by
  calc
    _ = (1 + a) / 2 * psi (b / (1 + a)) +
        (1 - a) / 2 * psi (b / (1 - a)) := pairEntropyGap_weighted a b h
    _ ≤ (1 + a) / 2 * (ell * (b / (1 + a)) ^ 2) +
        (1 - a) / 2 * (ell * (b / (1 - a)) ^ 2) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_add_mem_Ioo a b h))))
          (by linarith [pair_denom_add_pos a b h]))
        (mul_le_mul_of_nonneg_left
          (psi_le_ell_mul_sq (le_of_lt (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b h))))
          (by linarith [pair_denom_sub_pos a b h]))
    _ = ell * ((1 + a) / 2 * (b / (1 + a)) ^ 2 +
        (1 - a) / 2 * (b / (1 - a)) ^ 2) := by ring
    _ = _ := by rw [pair_weighted_sq a b h]

theorem pairEntropyGap_div_variance_lt_ell (a b : ℝ) (h : |a| + |b| < 1) :
    pairEntropyGap a b / (1 - a ^ 2) < ell := by
  have hA := pair_variance_pos a b h
  have hb := pair_abs_lt_variance a b h
  have hprod := mul_pos (show 0 < 1 - a ^ 2 - |b| by linarith)
    (show 0 < 1 - a ^ 2 + |b| by linarith [abs_nonneg b])
  have hsq : b ^ 2 < (1 - a ^ 2) * (1 - a ^ 2) := by nlinarith [sq_abs b]
  have hratio : b ^ 2 / (1 - a ^ 2) < 1 - a ^ 2 := (div_lt_iff₀ hA).2 hsq
  apply (div_lt_iff₀ hA).2
  exact (pairEntropyGap_le_quadratic a b h).trans_lt
    (mul_lt_mul_of_pos_left hratio ell_pos)

theorem pairDissipation_weighted_r (a b : ℝ) (h : |a| + |b| < 1) :
    pairDissipation a b =
      (1 + a) / 2 * r (psi (b / (1 + a))) +
        (1 - a) / 2 * r (psi (b / (1 - a))) := by
  rw [r_psi (pair_ratio_add_mem_Ioo a b h), r_psi (pair_ratio_sub_mem_Ioo a b h)]
  exact pairDissipation_weighted a b h

theorem r_pairEntropyGap_le_pairDissipation (a b : ℝ) (h : |a| + |b| < 1) :
    r (pairEntropyGap a b) ≤ pairDissipation a b := by
  have hp := pair_ratio_add_mem_Ioo a b h
  have hm := pair_ratio_sub_mem_Ioo a b h
  have hJ := convexOn_r.2
    (show psi (b / (1 + a)) ∈ Set.Ico 0 ell from ⟨psi_nonneg _, psi_lt_ell hp⟩)
    (show psi (b / (1 - a)) ∈ Set.Ico 0 ell from ⟨psi_nonneg _, psi_lt_ell hm⟩)
    (show 0 ≤ (1 + a) / 2 by linarith [pair_denom_add_pos a b h])
    (show 0 ≤ (1 - a) / 2 by linarith [pair_denom_sub_pos a b h])
    (show (1 + a) / 2 + (1 - a) / 2 = 1 by ring)
  simp only [smul_eq_mul] at hJ
  rw [← pairEntropyGap_weighted a b h] at hJ
  exact hJ.trans_eq (pairDissipation_weighted_r a b h).symm

theorem rGap_pairEntropyGap_le (a b : ℝ) (h : |a| + |b| < 1) :
    rGap (pairEntropyGap a b) ≤ pairDissipation a b - 2 * pairEntropyGap a b := by
  exact sub_le_sub_right (r_pairEntropyGap_le_pairDissipation a b h) _

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def lambda (z : ℝ) : ℝ := if z = 0 then 1 else -Real.log (1 - z) / z

@[simp] theorem lambda_zero : lambda 0 = 1 := by simp [lambda]

theorem lambda_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    lambda z = -Real.log (1 - z) / z := by simp [lambda, hz]

theorem mul_lambda (z : ℝ) : z * lambda z = -Real.log (1 - z) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [lambda_of_ne_zero hz]
    field_simp

theorem hasSum_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) (lambda z) := by
  by_cases hz : z = 0
  · subst z
    rw [lambda_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) using 1
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  · have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |z| < 1 by rwa [abs_of_nonneg hz0])).div_const z
    rw [lambda_of_ne_zero hz]
    convert hlog using 1 <;> try with_reducible_and_instances rfl
    ext j
    rw [pow_succ]
    field_simp

theorem monotoneOn_lambda : MonotoneOn lambda (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  apply hasSum_le _ (hasSum_lambda hx.1 hx.2) (hasSum_lambda hy.1 hy.2)
  intro j
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hx.1 hxy j) (by positivity)

theorem one_le_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 1 ≤ lambda z := by
  simpa using monotoneOn_lambda (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hz0, hz1⟩ hz0

theorem lambda_nonneg {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) : 0 ≤ lambda z :=
  zero_le_one.trans (one_le_lambda hz0 hz1)

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators


namespace LeanBlast.CourtadeKumar

theorem pow_tangent_remainder_nonneg (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x ^ (n + 1) - y ^ (n + 1) - (n + 1 : ℝ) * y ^ n * (x - y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := add_nonneg (mul_nonneg hx ih)
      (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) (pow_nonneg hy n))
        (sq_nonneg (x - y)))
    convert hp using 1 <;> try with_reducible_and_instances rfl
    push_cast
    simp only [pow_succ]
    ring

theorem pow_tangent_remainder_lower (n : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 ≤
      x ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x - y) := by
  have hp := mul_nonneg hx (pow_tangent_remainder_nonneg n x y hx hy)
  have hid : x ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x - y) =
      x * (x ^ (n + 1) - y ^ (n + 1) - (n + 1 : ℝ) * y ^ n * (x - y)) +
        (n + 1 : ℝ) * y ^ n * (x - y) ^ 2 := by
    simp only [pow_succ]
    ring
  rw [hid]
  linarith

section Weighted

variable {ι : Type u} [Fintype ι]

private abbrev entropySeriesCoeff (j : ℕ) : ℝ := psiCoeff j

theorem weighted_even_pow_jensen (w x : ι → ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) :
    (∑ i, w i * x i) ^ (2 * n) ≤ ∑ i, w i * (x i) ^ (2 * n) := by
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ (2 * n)) :=
    (even_two_mul n).convexOn_pow
  simpa only [smul_eq_mul] using hc.map_sum_le (fun i _ => hw i) hprob
    (fun i _ => Set.mem_univ (x i))

theorem weighted_centered_second_moment (w x : ι → ℝ) (y : ℝ)
    (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y) :
    (∑ i, w i * (x i - y) ^ 2) = (∑ i, w i * (x i) ^ 2) - y ^ 2 := by
  calc
    (∑ i, w i * (x i - y) ^ 2) =
        ∑ i, (w i * (x i) ^ 2 - 2 * y * (w i * x i) + y ^ 2 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, w i * (x i) ^ 2) - 2 * y * (∑ i, w i * x i) + y ^ 2 * (∑ i, w i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hprob, hmean]; ring

theorem weighted_pow_gap_lower (w x : ι → ℝ) (y : ℝ) (n : ℕ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hx : ∀ i, 0 ≤ x i) (hy : 0 ≤ y) (hmean : ∑ i, w i * x i = y) :
    (n + 1 : ℝ) * y ^ n * ((∑ i, w i * (x i) ^ 2) - y ^ 2) ≤
      (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (pow_tangent_remainder_lower n (x i) y (hx i) hy) (hw i))
  have hleft : (∑ i, w i * ((n + 1 : ℝ) * y ^ n * (x i - y) ^ 2)) =
      (n + 1 : ℝ) * y ^ n * ((∑ i, w i * (x i) ^ 2) - y ^ 2) := by
    rw [← weighted_centered_second_moment w x y hprob hmean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright : (∑ i, w i *
      ((x i) ^ (n + 2) - y ^ (n + 2) - (n + 2 : ℝ) * y ^ (n + 1) * (x i - y))) =
      (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) := by
    calc
      _ = ∑ i, (w i * (x i) ^ (n + 2) - y ^ (n + 2) * w i -
          (n + 2 : ℝ) * y ^ (n + 1) * (w i * x i - y * w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, w i * (x i) ^ (n + 2)) - y ^ (n + 2) * (∑ i, w i) -
          (n + 2 : ℝ) * y ^ (n + 1) * ((∑ i, w i * x i) - y * (∑ i, w i)) := by
        simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
      _ = _ := by rw [hprob, hmean]; ring
  rwa [hleft, hright] at h

theorem weighted_series_gap_hasSum (c : ℕ → ℝ) (p : ℕ → ℕ) (F : ℝ → ℝ)
    (w x : ι → ℝ) (y : ℝ)
    (hx : ∀ i, HasSum (fun j => c j * (x i) ^ (p j)) (F (x i)))
    (hy : HasSum (fun j => c j * y ^ (p j)) (F y)) :
    HasSum (fun j => 2 * c j * ((∑ i, w i * (x i) ^ (p j)) - y ^ (p j)))
      (2 * ((∑ i, w i * F (x i)) - F y)) := by
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => (hx i).mul_left (w i))
  have h := (hsum.sub hy).mul_left 2
  have heq : ∀ j, (∑ i, w i * (c j * (x i) ^ (p j))) =
      c j * (∑ i, w i * (x i) ^ (p j)) := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq] at h
  convert h using 1 <;> try with_reducible_and_instances rfl
  ext j
  ring

private theorem entropy_series_gap_lower (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, HasSum (fun j => entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    (∑ i, w i * (x i) ^ 2) - y ^ 2 ≤ 2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  apply hasSum_le _ (hasSum_ite_eq (0 : ℕ) ((∑ i, w i * (x i) ^ 2) - y ^ 2)) hsum
  intro j
  by_cases hj : j = 0
  · subst j
    norm_num [entropySeriesCoeff]
  · simp only [if_neg hj]
    have hp := weighted_even_pow_jensen w x (j + 1) hw hprob
    rw [hmean] at hp
    exact mul_nonneg (mul_nonneg (by norm_num) (psiCoeff_nonneg j)) (sub_nonneg.mpr hp)

private theorem entropy_series_gap_strengthened (F : ℝ → ℝ) (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hx : ∀ i, HasSum (fun j => entropySeriesCoeff j * (x i) ^ (2 * (j + 1))) (F (x i)))
    (hy : HasSum (fun j => entropySeriesCoeff j * y ^ (2 * (j + 1))) (F y)) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * F (x i)) - F y) := by
  have hsum := weighted_series_gap_hasSum entropySeriesCoeff (fun j => 2 * (j + 1)) F w x y hx hy
  have hlambda := (hasSum_lambda (sq_nonneg y) (by nlinarith : y ^ 2 < 1)).mul_left
    ((∑ i, w i * (x i) ^ 2) - y ^ 2)
  apply hasSum_le _ hlambda hsum
  intro j
  have hp := weighted_pow_gap_lower w x y (2 * j) hw hprob hx0 hy0 hmean
  have hc : 0 ≤ 2 * entropySeriesCoeff j := mul_nonneg (by norm_num) (psiCoeff_nonneg j)
  have h := mul_le_mul_of_nonneg_left hp hc
  have heq : 2 * entropySeriesCoeff j *
      ((2 * j + 1 : ℝ) * y ^ (2 * j) * ((∑ i, w i * (x i) ^ 2) - y ^ 2)) =
      ((∑ i, w i * (x i) ^ 2) - y ^ 2) * ((y ^ 2) ^ j / ((j : ℝ) + 1)) := by
    simp only [entropySeriesCoeff, psiCoeff, pow_mul]
    field_simp
  rw [show 2 * j + 2 = 2 * (j + 1) by omega] at h
  push_cast at h
  rwa [heq] at h

theorem weighted_psi_gap (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, |x i| < 1) :
    (∑ i, w i * (x i) ^ 2) - y ^ 2 ≤ 2 * ((∑ i, w i * psi (x i)) - psi y) := by
  have hy : |y| < 1 := by
    apply abs_lt.mpr
    rw [← hmean]
    simpa only [smul_eq_mul, Set.mem_Ioo] using (convex_Ioo (-1 : ℝ) 1).sum_mem
      (fun i _ => hw i) hprob (fun i _ => abs_lt.mp (hx i))
  exact entropy_series_gap_lower psi w x y hw hprob hmean
    (fun i => hasSum_psi (hx i)) (hasSum_psi hy)

theorem weighted_psi_gap_strengthened (w x : ι → ℝ) (y : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (hmean : ∑ i, w i * x i = y)
    (hx : ∀ i, |x i| < 1) (hx0 : ∀ i, 0 ≤ x i) :
    ((∑ i, w i * (x i) ^ 2) - y ^ 2) * lambda (y ^ 2) ≤
      2 * ((∑ i, w i * psi (x i)) - psi y) := by
  have hy : |y| < 1 := by
    apply abs_lt.mpr
    rw [← hmean]
    simpa only [smul_eq_mul, Set.mem_Ioo] using (convex_Ioo (-1 : ℝ) 1).sum_mem
      (fun i _ => hw i) hprob (fun i _ => abs_lt.mp (hx i))
  have hy0 : 0 ≤ y := by
    rw [← hmean]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx0 i))
  exact entropy_series_gap_strengthened psi w x y hw hprob hmean hx0 hy0
    (abs_lt.mp hy).2 (fun i => hasSum_psi (hx i)) (hasSum_psi hy)

private theorem normalized_ratio_weights_data (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∀ i, 0 ≤ w i * t i / T) ∧ (∑ i, w i * t i / T) = 1 ∧
      (∑ i, (w i * t i / T) * (b i / t i)) = k / T := by
  refine ⟨fun i => div_nonneg (mul_nonneg (hw i) (ht i).le) hT.le, ?_, ?_⟩
  · rw [← Finset.sum_div, hmass, div_self hT.ne']
  · calc
      _ = ∑ i, (w i * b i) / T := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(ht i).ne']
      _ = k / T := by rw [← Finset.sum_div, hmean]

private theorem rescale_perspective_gap (w t b : ι → ℝ) (T k C : ℝ)
    (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hgap : ((∑ i, (w i * t i / T) * (b i / t i) ^ 2) - (k / T) ^ 2) * C ≤
      2 * ((∑ i, (w i * t i / T) * psi (b i / t i)) - psi (k / T))) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * C ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  have hsecond : (∑ i, (w i * t i / T) * (b i / t i) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(ht i).ne']
  have hentropy : (∑ i, (w i * t i / T) * psi (b i / t i)) =
      (∑ i, w i * t i * psi (b i / t i)) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsecond, hentropy] at hgap
  have h := mul_le_mul_of_nonneg_left hgap hT.le
  convert h using 1 <;> first | with_reducible_and_instances rfl | field_simp

theorem weighted_perspective_gap (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k)
    (hdom : ∀ i, |b i| < t i) :
    (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  obtain ⟨hq0, hq1, hqm⟩ := normalized_ratio_weights_data w t b T k hw ht hT hmass hmean
  have hx : ∀ i, |b i / t i| < 1 := by
    intro i
    rw [abs_div, abs_of_pos (ht i)]
    exact (div_lt_one (ht i)).mpr (hdom i)
  have hg := weighted_psi_gap (fun i => w i * t i / T) (fun i => b i / t i)
    (k / T) hq0 hq1 hqm hx
  simpa only [mul_one] using rescale_perspective_gap w t b T k 1 ht hT
    (by simpa only [mul_one] using hg)

theorem weighted_perspective_gap_strengthened (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k)
    (hdom : ∀ i, |b i| < t i) (hb : ∀ i, 0 ≤ b i) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * lambda ((k / T) ^ 2) ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  obtain ⟨hq0, hq1, hqm⟩ := normalized_ratio_weights_data w t b T k hw ht hT hmass hmean
  have hx : ∀ i, |b i / t i| < 1 := by
    intro i
    rw [abs_div, abs_of_pos (ht i)]
    exact (div_lt_one (ht i)).mpr (hdom i)
  have hg := weighted_psi_gap_strengthened (fun i => w i * t i / T) (fun i => b i / t i)
    (k / T) hq0 hq1 hqm hx (fun i => div_nonneg (hb i) (ht i).le)
  exact rescale_perspective_gap w t b T k (lambda ((k / T) ^ 2)) ht hT hg

theorem weighted_abs_mean_le (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |∑ i, w i * x i| ≤ ∑ i, w i * |x i| := by
  calc
    |∑ i, w i * x i| ≤ ∑ i, |w i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (hw _)]

theorem weighted_pair_mean_interior (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    |∑ i, w i * a i| + |∑ i, w i * b i| < 1 := by
  have havg : (∑ i, w i * (|a i| + |b i|)) < 1 := by
    simpa only [smul_eq_mul, Set.mem_Iio] using (convex_Iio (1 : ℝ)).sum_mem
      (fun i _ => hw i) hprob (fun i _ => hdom i)
  have h := add_le_add (weighted_abs_mean_le w a hw) (weighted_abs_mean_le w b hw)
  rw [← Finset.sum_add_distrib] at h
  simp only [← mul_add] at h
  exact h.trans_lt havg

theorem weighted_positive_mean (w t : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1) (ht : ∀ i, 0 < t i) :
    0 < ∑ i, w i * t i := by
  simpa only [smul_eq_mul, Set.mem_Ioi] using (convex_Ioi (0 : ℝ)).sum_mem
    (fun i _ => hw i) hprob (fun i _ => ht i)

theorem weighted_ratio_centered_identity (w t b : ι → ℝ) (y : ℝ)
    (ht : ∀ i, t i ≠ 0) :
    (∑ i, w i * t i * (b i / t i - y) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) - 2 * y * (∑ i, w i * b i) +
        y ^ 2 * (∑ i, w i * t i) := by
  calc
    _ = ∑ i, (w i * (b i) ^ 2 / t i - 2 * y * (w i * b i) +
        y ^ 2 * (w i * t i)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [ht i]
      ring
    _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

theorem weighted_ratio_variance_identity (w t b : ι → ℝ) (T k : ℝ)
    (ht : ∀ i, t i ≠ 0) (hT : T ≠ 0)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    (∑ i, w i * t i * (b i / t i - k / T) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T := by
  rw [weighted_ratio_centered_identity w t b _ ht, hmass, hmean]
  field_simp
  ring

theorem weighted_ratio_variance_nonneg (w t b : ι → ℝ) (T k : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hmass : ∑ i, w i * t i = T) (hmean : ∑ i, w i * b i = k) :
    0 ≤ (∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T := by
  rw [← weighted_ratio_variance_identity w t b T k (fun i => (ht i).ne') hT.ne'
    hmass hmean]
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (hw i) (ht i).le) (sq_nonneg _))

theorem weighted_variance_gap_lower_bound (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    (∑ i, w i * b i) ^ 2 / (∑ i, w i * (1 - (a i) ^ 2)) -
        (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) ≤
      (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
        (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) := by
  have ht : ∀ i, 0 < 1 - (a i) ^ 2 := by
    intro i
    have hi := hdom i
    have hsq := sq_abs (a i)
    nlinarith [abs_nonneg (a i), abs_nonneg (b i)]
  have hT := weighted_positive_mean w (fun i => 1 - (a i) ^ 2) hw hprob ht
  have h := weighted_ratio_variance_nonneg w (fun i => 1 - (a i) ^ 2) b _ _
    hw ht hT rfl rfl
  linarith

theorem weighted_variance_gap_nonneg (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    0 ≤ (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) := by
  have ht : ∀ i, 0 < 1 - (a i) ^ 2 := by
    intro i
    have hi := hdom i
    nlinarith [sq_abs (a i), abs_nonneg (a i), abs_nonneg (b i)]
  have hT := weighted_positive_mean w (fun i => 1 - (a i) ^ 2) hw hprob ht
  have hj := weighted_even_pow_jensen w a 1 hw hprob
  norm_num only [Nat.mul_one] at hj
  have hW : (∑ i, w i * (1 - (a i) ^ 2)) ≤ 1 - (∑ i, w i * a i) ^ 2 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob]
    linarith
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (∑ i, w i * b i)) hT hW
  have h := weighted_variance_gap_lower_bound w a b hw hprob hdom
  linarith

private theorem pair_reciprocal_square_identity (a b : ℝ) (h : |a| + |b| < 1) :
    b ^ 2 / (1 + a) + b ^ 2 / (1 - a) = 2 * (b ^ 2 / (1 - a ^ 2)) := by
  have hp := (pair_denom_add_pos a b h).ne'
  have hm := (pair_denom_sub_pos a b h).ne'
  have hv := (pair_variance_pos a b h).ne'
  field_simp
  ring

private theorem weighted_pair_gap_combine (w a b : ι → ℝ) (m k C : ℝ)
    (hdom : ∀ i, |a i| + |b i| < 1) (hcenter : |m| + |k| < 1)
    (hp : ((∑ i, w i * (b i) ^ 2 / (1 + a i)) - k ^ 2 / (1 + m)) * C ≤
      2 * ((∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) -
        (1 + m) * psi (k / (1 + m))))
    (hm : ((∑ i, w i * (b i) ^ 2 / (1 - a i)) - k ^ 2 / (1 - m)) * C ≤
      2 * ((∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) -
        (1 - m) * psi (k / (1 - m)))) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) - k ^ 2 / (1 - m ^ 2)) * C ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) - pairEntropyGap m k) := by
  have hv : (∑ i, w i * (b i) ^ 2 / (1 + a i)) +
      (∑ i, w i * (b i) ^ 2 / (1 - a i)) =
      2 * (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = w i * ((b i) ^ 2 / (1 + a i) + (b i) ^ 2 / (1 - a i)) := by ring
      _ = _ := by rw [pair_reciprocal_square_identity (a i) (b i) (hdom i)]; ring
  have hvc := pair_reciprocal_square_identity m k hcenter
  have he : (∑ i, w i * (1 + a i) * psi (b i / (1 + a i))) +
      (∑ i, w i * (1 - a i) * psi (b i / (1 - a i))) =
      2 * (∑ i, w i * pairEntropyGap (a i) (b i)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pairEntropyGap_weighted (a i) (b i) (hdom i)]
    ring
  have hec : (1 + m) * psi (k / (1 + m)) + (1 - m) * psi (k / (1 - m)) =
      2 * pairEntropyGap m k := by
    rw [pairEntropyGap_weighted m k hcenter]
    ring
  have hvC := congrArg (fun z : ℝ => z * C) hv
  have hvcC := congrArg (fun z : ℝ => z * C) hvc
  nlinarith only [hp, hm, hvC, hvcC, he, hec]

theorem weighted_pair_jensen_gap (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) :
    (∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2) ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) -
        pairEntropyGap (∑ i, w i * a i) (∑ i, w i * b i)) := by
  let m := ∑ i, w i * a i
  let k := ∑ i, w i * b i
  have hc : |m| + |k| < 1 := weighted_pair_mean_interior w a b hw hprob hdom
  have hmp : (∑ i, w i * (1 + a i)) = 1 + m := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hprob, m]
  have hmm : (∑ i, w i * (1 - a i)) = 1 - m := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob, m]
  have hp := weighted_perspective_gap w (fun i => 1 + a i) b (1 + m) k hw
    (fun i => pair_denom_add_pos (a i) (b i) (hdom i))
    (pair_denom_add_pos m k hc) hmp rfl
    (fun i => pair_abs_lt_denom_add (a i) (b i) (hdom i))
  have hm := weighted_perspective_gap w (fun i => 1 - a i) b (1 - m) k hw
    (fun i => pair_denom_sub_pos (a i) (b i) (hdom i))
    (pair_denom_sub_pos m k hc) hmm rfl
    (fun i => pair_abs_lt_denom_sub (a i) (b i) (hdom i))
  simpa only [mul_one] using weighted_pair_gap_combine w a b m k 1 hdom hc
    (by simpa only [mul_one] using hp) (by simpa only [mul_one] using hm)

private theorem lambda_ratio_min_le (m k t : ℝ) (hk : 0 ≤ k)
    (ht : 0 < t) (htmax : t ≤ 1 + |m|) (hkt : k < t) :
    lambda ((k / (1 + |m|)) ^ 2) ≤ lambda ((k / t) ^ 2) := by
  have hmax : 0 < 1 + |m| := by positivity
  have hx : 0 ≤ k / (1 + |m|) := div_nonneg hk hmax.le
  have hy : 0 ≤ k / t := div_nonneg hk ht.le
  have hxy := div_le_div_of_nonneg_left hk ht htmax
  have hy1 : k / t < 1 := (div_lt_one ht).mpr hkt
  apply monotoneOn_lambda
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact ⟨sq_nonneg _, by nlinarith⟩
  · exact pow_le_pow_left₀ hx hxy 2

theorem weighted_pair_jensen_gap_strengthened (w a b : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hprob : ∑ i, w i = 1)
    (hdom : ∀ i, |a i| + |b i| < 1) (hb : ∀ i, 0 ≤ b i) :
    ((∑ i, w i * (b i) ^ 2 / (1 - (a i) ^ 2)) -
      (∑ i, w i * b i) ^ 2 / (1 - (∑ i, w i * a i) ^ 2)) *
        lambda (((∑ i, w i * b i) / (1 + |∑ i, w i * a i|)) ^ 2) ≤
      2 * ((∑ i, w i * pairEntropyGap (a i) (b i)) -
        pairEntropyGap (∑ i, w i * a i) (∑ i, w i * b i)) := by
  let m := ∑ i, w i * a i
  let k := ∑ i, w i * b i
  have hc : |m| + |k| < 1 := weighted_pair_mean_interior w a b hw hprob hdom
  have hk : 0 ≤ k := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hb i))
  have htp := pair_denom_add_pos m k hc
  have htm := pair_denom_sub_pos m k hc
  have hp0 : ∀ i, 0 < 1 + a i := fun i => pair_denom_add_pos (a i) (b i) (hdom i)
  have hm0 : ∀ i, 0 < 1 - a i := fun i => pair_denom_sub_pos (a i) (b i) (hdom i)
  have hmp : (∑ i, w i * (1 + a i)) = 1 + m := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hprob, m]
  have hmm : (∑ i, w i * (1 - a i)) = 1 - m := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hprob, m]
  have hp := weighted_perspective_gap_strengthened w (fun i => 1 + a i) b (1 + m) k
    hw hp0 htp hmp rfl (fun i => pair_abs_lt_denom_add (a i) (b i) (hdom i)) hb
  have hm := weighted_perspective_gap_strengthened w (fun i => 1 - a i) b (1 - m) k
    hw hm0 htm hmm rfl (fun i => pair_abs_lt_denom_sub (a i) (b i) (hdom i)) hb
  have hvp := weighted_ratio_variance_nonneg w (fun i => 1 + a i) b (1 + m) k
    hw hp0 htp hmp rfl
  have hvm := weighted_ratio_variance_nonneg w (fun i => 1 - a i) b (1 - m) k
    hw hm0 htm hmm rfl
  have hcp := lambda_ratio_min_le m k (1 + m) hk htp (by linarith [le_abs_self m])
    (by simpa only [abs_of_nonneg hk] using pair_abs_lt_denom_add m k hc)
  have hcm := lambda_ratio_min_le m k (1 - m) hk htm (by linarith [neg_le_abs m])
    (by simpa only [abs_of_nonneg hk] using pair_abs_lt_denom_sub m k hc)
  exact weighted_pair_gap_combine w a b m k _ hdom hc
    ((mul_le_mul_of_nonneg_left hcp hvp).trans hp)
    ((mul_le_mul_of_nonneg_left hcm hvm).trans hm)

end Weighted

private theorem cube_uniform_weights_sum_one (n : ℕ) :
    ∑ _ : Cube n, ((2 : ℝ) ^ n)⁻¹ = 1 := by
  simp [Cube, LeanBlast.GotsmanLinial.Cube]

private theorem cubeAverage_as_weighted_sum {n : ℕ} (f : Cube n → ℝ) :
    cubeAverage f = ∑ x, ((2 : ℝ) ^ n)⁻¹ * f x := by
  rw [cubeAverage, ← Finset.mul_sum]
  ring

theorem convexOn_cubeAverage_le {n : ℕ} (F : ℝ → ℝ) {s : Set ℝ}
    (hF : ConvexOn ℝ s F) (v : Cube n → ℝ) (hv : ∀ x, v x ∈ s) :
    F (cubeAverage v) ≤ cubeAverage (fun x => F (v x)) := by
  simp only [cubeAverage_as_weighted_sum]
  simpa only [smul_eq_mul] using hF.map_sum_le
    (fun (_ : Cube n) _ => inv_nonneg.mpr (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n))
    (cube_uniform_weights_sum_one n) (fun x _ => hv x)

theorem pair_variance_gap_lower_bound {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    (cubeAverage b) ^ 2 / cubeAverage (fun x => 1 - (a x) ^ 2) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_variance_gap_lower_bound (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_variance_gap_nonneg {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    0 ≤ cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_variance_gap_nonneg (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_jensen_gap {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) ≤
      2 * (cubeAverage (fun x => pairEntropyGap (a x) (b x)) -
        pairEntropyGap (cubeAverage a) (cubeAverage b)) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_pair_jensen_gap (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom

theorem pair_jensen_gap_strengthened {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) (hb : ∀ x, 0 ≤ b x) :
    (cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) *
        lambda (((cubeAverage b) / (1 + |cubeAverage a|)) ^ 2) ≤
      2 * (cubeAverage (fun x => pairEntropyGap (a x) (b x)) -
        pairEntropyGap (cubeAverage a) (cubeAverage b)) := by
  simpa only [cubeAverage_as_weighted_sum, ← mul_div_assoc] using
    weighted_pair_jensen_gap_strengthened (fun _ => ((2 : ℝ) ^ n)⁻¹) a b
      (fun _ => by positivity) (cube_uniform_weights_sum_one n) hdom hb

theorem pair_jensen_gap_nonneg {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    pairEntropyGap (cubeAverage a) (cubeAverage b) ≤
      cubeAverage (fun x => pairEntropyGap (a x) (b x)) := by
  have hv := pair_variance_gap_nonneg a b hdom
  have hj := pair_jensen_gap a b hdom
  linarith

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

def binaryRelativeEntropy (a m : ℝ) : ℝ :=
  (1 + a) / 2 * Real.log ((1 + a) / (1 + m)) +
    (1 - a) / 2 * Real.log ((1 - a) / (1 - m))

theorem one_sub_sq_pos_of_interior {a : ℝ} (ha : -1 < a ∧ a < 1) :
    0 < 1 - a ^ 2 := by
  nlinarith [mul_pos (by linarith : 0 < 1 - a) (by linarith : 0 < 1 + a)]

theorem binaryRelativeEntropy_eq {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    binaryRelativeEntropy a m = psi a - psi m -
      (a - m) / 2 * (Real.log (1 + m) - Real.log (1 - m)) := by
  have hap : 1 + a ≠ 0 := ne_of_gt (by linarith)
  have ham : 1 - a ≠ 0 := ne_of_gt (by linarith)
  have hmp : 1 + m ≠ 0 := ne_of_gt (by linarith)
  have hmm : 1 - m ≠ 0 := ne_of_gt (by linarith)
  unfold binaryRelativeEntropy psi
  rw [Real.log_div hap hmp, Real.log_div ham hmm]
  ring

theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * Real.log (a / b) := by
  have h := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos ha hb)) ha.le
  have heq : a * (1 - (a / b)⁻¹) = a - b := by
    field_simp
  rwa [heq] at h

theorem binaryRelativeEntropy_nonneg {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    0 ≤ binaryRelativeEntropy a m := by
  have hp := sub_le_mul_log_div (a := 1 + a) (b := 1 + m)
    (by linarith) (by linarith)
  have hm' := sub_le_mul_log_div (a := 1 - a) (b := 1 - m)
    (by linarith) (by linarith)
  unfold binaryRelativeEntropy
  nlinarith

theorem binaryRelativeEntropy_le_sq_div {a m : ℝ}
    (ha : -1 < a ∧ a < 1) (hm : -1 < m ∧ m < 1) :
    binaryRelativeEntropy a m ≤ (a - m) ^ 2 / (1 - m ^ 2) := by
  have hmp : 1 + m ≠ 0 := ne_of_gt (by linarith)
  have hmm : 1 - m ≠ 0 := ne_of_gt (by linarith)
  have hA : 1 - m ^ 2 ≠ 0 := ne_of_gt (one_sub_sq_pos_of_interior hm)
  have hp := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos
      (div_pos (by linarith : 0 < 1 + a) (by linarith : 0 < 1 + m)))
    (show 0 ≤ (1 + a) / 2 by linarith)
  have hn := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos
      (div_pos (by linarith : 0 < 1 - a) (by linarith : 0 < 1 - m)))
    (show 0 ≤ (1 - a) / 2 by linarith)
  calc
    binaryRelativeEntropy a m ≤
        (1 + a) / 2 * ((1 + a) / (1 + m) - 1) +
          (1 - a) / 2 * ((1 - a) / (1 - m) - 1) := add_le_add hp hn
    _ = (a - m) ^ 2 / (1 - m ^ 2) := by
      field_simp
      ring

theorem informationDeficit_eq_average_psi (g : Cube n → ℝ) :
    informationDeficit g = cubeAverage (fun x => psi (g x)) - psi (cubeAverage g) := by
  unfold informationDeficit entropyAverage entropy
  rw [cubeAverage_sub, cubeAverage_const]
  ring

theorem informationDeficit_eq_average_binaryRelativeEntropy
    {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g =
      cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) := by
  let m := cubeAverage g
  let c := Real.log (1 + m) - Real.log (1 - m)
  have hlin : cubeAverage (fun x => (g x - m) / 2 * c) = 0 := by
    have heq : (fun x => (g x - m) / 2 * c) = (fun x => (c / 2) * (g x - m)) := by
      funext x
      ring
    rw [heq, cubeAverage_smul, cubeAverage_sub, cubeAverage_const]
    dsimp [m]
    ring
  have heq : (fun x => binaryRelativeEntropy (g x) m) =
      (fun x => psi (g x) - psi m - (g x - m) / 2 * c) := by
    funext x
    exact binaryRelativeEntropy_eq (hg x) hg.cubeAverage
  rw [show (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) =
      (fun x => binaryRelativeEntropy (g x) m) from rfl, heq]
  rw [cubeAverage_sub, cubeAverage_sub, cubeAverage_const, hlin, sub_zero]
  exact informationDeficit_eq_average_psi g

theorem informationDeficit_nonneg {g : Cube n → ℝ} (hg : IsInterior g) :
    0 ≤ informationDeficit g := by
  rw [informationDeficit_eq_average_binaryRelativeEntropy hg]
  exact cubeAverage_nonneg fun x => binaryRelativeEntropy_nonneg (hg x) hg.cubeAverage

theorem informationDeficit_le_variance_div {g : Cube n → ℝ} (hg : IsInterior g) :
    informationDeficit g ≤ cubeVariance g / meanVariance g := by
  rw [informationDeficit_eq_average_binaryRelativeEntropy hg]
  calc
    cubeAverage (fun x => binaryRelativeEntropy (g x) (cubeAverage g)) ≤
        cubeAverage (fun x => (g x - cubeAverage g) ^ 2 / (1 - (cubeAverage g) ^ 2)) :=
      cubeAverage_mono fun x => binaryRelativeEntropy_le_sq_div (hg x) hg.cubeAverage
    _ = cubeVariance g / meanVariance g := cubeAverage_div _ _

theorem abs_cubeAverage_le (g : Cube n → ℝ) :
    |cubeAverage g| ≤ cubeAverage (fun x => |g x|) := by
  unfold cubeAverage
  rw [abs_div, abs_of_pos (cube_denominator_pos n)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (cube_denominator_pos n).le

theorem cubeAverage_pairDomain {a b : Cube n → ℝ}
    (hdom : ∀ x, |a x| + |b x| < 1) :
    |cubeAverage a| + |cubeAverage b| < 1 := by
  calc
    |cubeAverage a| + |cubeAverage b| ≤
        cubeAverage (fun x => |a x|) + cubeAverage (fun x => |b x|) :=
      add_le_add (abs_cubeAverage_le a) (abs_cubeAverage_le b)
    _ = cubeAverage (fun x => |a x| + |b x|) := (cubeAverage_add _ _).symm
    _ < 1 := by simpa using cubeAverage_lt hdom

theorem IsInterior.of_pairDomain_left {a b : Cube n → ℝ}
    (hdom : ∀ x, |a x| + |b x| < 1) : IsInterior a := by
  intro x
  apply abs_lt.mp
  exact lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg _)) (hdom x)

theorem average_one_sub_sq_pos {g : Cube n → ℝ} (hg : IsInterior g) :
    0 < cubeAverage (fun x => 1 - (g x) ^ 2) := by
  have h := cubeAverage_lt (fun x => one_sub_sq_pos_of_interior (hg x))
  simpa using h

theorem scaled_informationDeficit_le_variance_gap (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    ((cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) * informationDeficit a ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
  have ha : IsInterior a := IsInterior.of_pairDomain_left hdom
  let A := 1 - (cubeAverage a) ^ 2
  let W := cubeAverage (fun x => 1 - (a x) ^ 2)
  let q := (cubeAverage b) ^ 2 / A
  have hA : 0 < A := one_sub_sq_pos_of_interior ha.cubeAverage
  have hW : 0 < W := average_one_sub_sq_pos ha
  have hvar : 0 ≤ cubeVariance a := cubeVariance_nonneg a
  have hWA : W = A - cubeVariance a := average_one_sub_sq_eq_meanVariance_sub_variance a
  have hWle : W ≤ A := by linarith
  have hq : 0 ≤ q := div_nonneg (sq_nonneg _) hA.le
  have hSa : informationDeficit a ≤ cubeVariance a / W :=
    (informationDeficit_le_variance_div ha).trans
      (div_le_div_of_nonneg_left hvar hW hWle)
  have halg : q * (cubeVariance a / W) = (cubeAverage b) ^ 2 / W -
      (cubeAverage b) ^ 2 / A := by
    have hv : cubeVariance a = A - W := by linarith
    rw [hv]
    dsimp [q]
    field_simp
  calc
    q * informationDeficit a ≤ q * (cubeVariance a / W) :=
      mul_le_mul_of_nonneg_left hSa hq
    _ = (cubeAverage b) ^ 2 / W - (cubeAverage b) ^ 2 / A := halg
    _ ≤ _ := pair_variance_gap_lower_bound a b hdom

theorem entropy_product_le_scaled_informationDeficit (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    pairEntropyGap (cubeAverage a) (cubeAverage b) * informationDeficit a / ell ≤
      ((cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)) * informationDeficit a := by
  have hSa : 0 ≤ informationDeficit a :=
    informationDeficit_nonneg (IsInterior.of_pairDomain_left hdom)
  have hJ := pairEntropyGap_le_quadratic (cubeAverage a) (cubeAverage b)
    (cubeAverage_pairDomain hdom)
  have hJdiv : pairEntropyGap (cubeAverage a) (cubeAverage b) / ell ≤
      (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) := by
    apply (div_le_iff₀ ell_pos).2
    exact hJ.trans_eq (mul_comm _ _)
  calc
    pairEntropyGap (cubeAverage a) (cubeAverage b) * informationDeficit a / ell =
        (pairEntropyGap (cubeAverage a) (cubeAverage b) / ell) * informationDeficit a := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hJdiv hSa

theorem entropy_product_le_variance_gap (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) :
    pairEntropyGap (cubeAverage a) (cubeAverage b) * informationDeficit a / ell ≤
      cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2) :=
  (entropy_product_le_scaled_informationDeficit a b hdom).trans
    (scaled_informationDeficit_le_variance_gap a b hdom)

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter


namespace LeanBlast.CourtadeKumar

theorem weighted_perspective_jensen {ι : Type u} [Fintype ι]
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (p A H : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hA : ∀ i, 0 < A i)
    (hH : ∀ i, 0 < H i) (hS : 0 < ∑ i, p i * A i) :
    (∑ i, p i * A i) * f ((∑ i, p i * H i) / (∑ i, p i * A i)) ≤
      ∑ i, p i * A i * f (H i / A i) := by
  have hj := hf.map_centerMass_le
    (t := Finset.univ) (w := fun i => p i * A i) (p := fun i => H i / A i)
    (fun i _ => mul_nonneg (hp i) (hA i).le) hS (fun i _ => div_pos (hH i) (hA i))
  have heq : (∑ i, p i * A i * (H i / A i)) = ∑ i, p i * H i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hA i).ne']
  simp only [Finset.centerMass, smul_eq_mul, Function.comp_apply] at hj
  rw [heq] at hj
  have hm := mul_le_mul_of_nonneg_left hj hS.le
  simp only [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul] at hm
  simpa [← div_eq_inv_mul, mul_assoc] using hm

theorem cubeAverage_perspective_jensen {n : ℕ}
    (f : ℝ → ℝ) (hf : ConvexOn ℝ (Ioi 0) f)
    (A H : Cube n → ℝ) (hA : ∀ i, 0 < A i) (hH : ∀ i, 0 < H i) :
    cubeAverage A * f (cubeAverage H / cubeAverage A) ≤
      cubeAverage (fun i => A i * f (H i / A i)) := by
  have hc : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hs : 0 < ∑ i, ((2 : ℝ) ^ n)⁻¹ * A i :=
    Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr hc) (hA i)) Finset.univ_nonempty
  have h := weighted_perspective_jensen f hf (fun _ => ((2 : ℝ) ^ n)⁻¹)
    A H (fun _ => (inv_pos.mpr hc).le) hA hH hs
  have havg (g : Cube n → ℝ) :
      (∑ i, ((2 : ℝ) ^ n)⁻¹ * g i) = cubeAverage g := by
    rw [← Finset.mul_sum, cubeAverage, div_eq_mul_inv]
    ring
  simpa only [mul_assoc, havg] using h

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem hasSum_weighted_nonneg_of_single_crossing
    {x weight : ℕ → ℝ} {total : ℝ}
    (hs : HasSum x 0) (hws : HasSum (fun j => weight j * x j) total)
    (hw : Monotone weight)
    (hcross : ∀ i j, i ≤ j → 0 < x i → 0 ≤ x j) : 0 ≤ total := by
  classical
  by_cases hpos : ∃ j, 0 < x j
  · let k := Nat.find hpos
    have hk : 0 < x k := Nat.find_spec hpos
    have hbefore : ∀ j, j < k → x j ≤ 0 := by
      intro j hj
      exact le_of_not_gt (Nat.find_min hpos hj)
    have hafter : ∀ j, k ≤ j → 0 ≤ x j := fun j hj => hcross k j hj hk
    have hshift : HasSum (fun j => (weight j - weight k) * x j) total := by
      convert hws.sub (hs.mul_left (weight k)) using 1 <;> try with_reducible_and_instances rfl
      · ext j
        ring
      · ring
    apply hshift.nonneg
    intro j
    by_cases hj : j < k
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hw hj.le)) (hbefore j hj)
    · exact mul_nonneg (sub_nonneg.mpr (hw (le_of_not_gt hj)))
        (hafter j (le_of_not_gt hj))
  · have hx : ∀ j, x j ≤ 0 := fun j => le_of_not_gt (fun hj => hpos ⟨j, hj⟩)
    have hzero : ∀ j, x j = 0 := by
      intro j
      have hle : -x j ≤ (0 : ℝ) := by
        simpa using le_hasSum hs.neg j (fun i _ => neg_nonneg.mpr (hx i))
      linarith [hx j]
    exact hws.nonneg (fun j => by rw [hzero j]; simp)

theorem logconvex_single_crossing {z : ℕ → ℝ}
    (hz : ∀ j, 0 ≤ z j) (hz0 : z 0 ≤ 1)
    (hlog : ∀ j, z (j + 1) ^ 2 ≤ z j * z (j + 2))
    (i j : ℕ) (hij : i ≤ j) (hi : 1 < z i) : 1 < z j := by
  have hprevious : ∀ n, 1 < z (n + 1) → z n ≤ z (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro h
      exact hz0.trans h.le
    | succ n ih =>
      intro h
      change 1 < z (n + 2) at h
      change z (n + 1) ≤ z (n + 2)
      by_contra hnot
      have hdesc : z (n + 2) < z (n + 1) := lt_of_not_ge hnot
      have hprev := ih (h.trans hdesc)
      have hmul := mul_le_mul_of_nonneg_right hprev (hz (n + 2))
      have hsq := hlog n
      nlinarith
  have hnext : ∀ n, 1 < z n → 1 < z (n + 1) := by
    intro n hn
    cases n with
    | zero => exact (not_lt_of_ge hz0 hn).elim
    | succ n =>
      have hprev := hprevious n hn
      have hmul := mul_le_mul_of_nonneg_right hprev (hz (n + 2))
      have hsq := hlog n
      change 1 < z (n + 2)
      nlinarith
  exact Nat.le_induction hi (fun n _ hn => hnext n hn) j hij

theorem logconvex_mul_pow {m : ℕ → ℝ}
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2)) (c : ℝ) (j : ℕ) :
    (m (j + 1) * c ^ (j + 1)) ^ 2 ≤
      (m j * c ^ j) * (m (j + 2) * c ^ (j + 2)) := by
  calc
    (m (j + 1) * c ^ (j + 1)) ^ 2 =
        m (j + 1) ^ 2 * (c ^ (j + 1)) ^ 2 := mul_pow _ _ _
    _ ≤ (m j * m (j + 2)) * (c ^ (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right (hlog j) (sq_nonneg _)
    _ = (m j * c ^ j) * (m (j + 2) * c ^ (j + 2)) := by
      simp only [pow_add, pow_one, pow_two]
      ring

theorem logconvex_geometric_single_crossing {m : ℕ → ℝ}
    (hm : ∀ j, 0 ≤ m j) (hm0 : m 0 ≤ 1)
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2))
    {t : ℝ} (ht : 0 ≤ t) (i j : ℕ) (hij : i ≤ j)
    (hi : t ^ i < m i) : t ^ j < m j := by
  by_cases ht0 : t = 0
  · subst t
    by_cases hi0 : i = 0
    · subst i
      simp only [pow_zero] at hi
      exact (not_lt_of_ge hm0 hi).elim
    · have hmi : 0 < m i := by simpa [zero_pow hi0] using hi
      have hpositive : ∀ n, 0 < m (n + 1) → 0 < m (n + 2) := by
        intro n hn
        have hsq := hlog n
        have hm0 := hm n
        have hm2 := hm (n + 2)
        nlinarith
      have htail : ∀ k, i ≤ k → 0 < m k := by
        intro k hk
        induction k, hk using Nat.le_induction with
        | base => exact hmi
        | succ k hk ih =>
          obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          exact hpositive l ih
      have hj0 : j ≠ 0 := by omega
      simpa [zero_pow hj0] using htail j hij
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hzi : 1 < m i * (t⁻¹) ^ i := by
      rw [inv_pow, ← div_eq_mul_inv]
      exact (lt_div_iff₀ (pow_pos htpos i)).mpr (by simpa using hi)
    have hzj := logconvex_single_crossing
      (z := fun k => m k * (t⁻¹) ^ k)
      (fun k => mul_nonneg (hm k) (pow_nonneg (inv_nonneg.mpr ht) k))
      (by simpa using hm0) (logconvex_mul_pow hlog (t⁻¹)) i j hij hzi
    change 1 < m j * (t⁻¹) ^ j at hzj
    rw [inv_pow, ← div_eq_mul_inv] at hzj
    simpa only [one_mul] using (lt_div_iff₀ (pow_pos htpos j)).mp hzj

theorem weighted_hasSum_le_of_logconvex
    {m c weight : ℕ → ℝ} {t mass moment geometricMoment : ℝ}
    (hm : ∀ j, 0 ≤ m j) (hm0 : m 0 ≤ 1)
    (hlog : ∀ j, m (j + 1) ^ 2 ≤ m j * m (j + 2))
    (hc : ∀ j, 0 ≤ c j) (hw : Monotone weight) (ht : 0 ≤ t)
    (hs : HasSum (fun k => c k * m (k + 1)) mass)
    (hts : HasSum (fun k => c k * t ^ (k + 1)) mass)
    (hws : HasSum (fun k => weight k * (c k * m (k + 1))) moment)
    (hwts : HasSum (fun k => weight k * (c k * t ^ (k + 1))) geometricMoment) :
    geometricMoment ≤ moment := by
  have hdiff : HasSum (fun k => c k * (m (k + 1) - t ^ (k + 1))) 0 := by
    convert hs.sub hts using 1 <;> try with_reducible_and_instances rfl
    · ext k
      ring
    · ring
  have hwdiff : HasSum
      (fun k => weight k * (c k * (m (k + 1) - t ^ (k + 1))))
      (moment - geometricMoment) := by
    convert hws.sub hwts using 1 <;> try with_reducible_and_instances rfl
    ext k
    ring
  have hnonneg := hasSum_weighted_nonneg_of_single_crossing hdiff hwdiff hw ?_
  · linarith
  · intro i j hij hi
    have hmi : t ^ (i + 1) < m (i + 1) := by
      have hci := hc i
      nlinarith
    have hmj := logconvex_geometric_single_crossing hm hm0 hlog ht
      (i + 1) (j + 1) (Nat.add_le_add_right hij 1) hmi
    exact mul_nonneg (hc j) (sub_nonneg.mpr hmj.le)

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

theorem normalized_pair_scale_pos {a b : ℝ} (hab : |a| + |b| < 1) : 0 < 1 - a ^ 2 := by
  have h := mul_pos (pair_denom_add_pos a b hab) (pair_denom_sub_pos a b hab)
  nlinarith

theorem two_atom_moment_logconvex (w u p q : ℝ)
    (hw : 0 ≤ w) (hu : 0 ≤ u) (hp : 0 ≤ p) (hq : 0 ≤ q) (j : ℕ) :
    (w * p ^ (j + 1) + u * q ^ (j + 1)) ^ 2 ≤
      (w * p ^ j + u * q ^ j) * (w * p ^ (j + 2) + u * q ^ (j + 2)) := by
  have hnonneg : 0 ≤ w * u * p ^ j * q ^ j * (p - q) ^ 2 := by positivity
  have heq :
      (w * p ^ j + u * q ^ j) * (w * p ^ (j + 2) + u * q ^ (j + 2)) -
          (w * p ^ (j + 1) + u * q ^ (j + 1)) ^ 2 =
        w * u * p ^ j * q ^ j * (p - q) ^ 2 := by
    simp only [pow_add, pow_one, pow_two]
    ring
  linarith

theorem rawPairMoment_logconvex {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    rawPairMoment a b (j + 1) ^ 2 ≤
      rawPairMoment a b j * rawPairMoment a b (j + 2) := by
  simpa only [rawPairMoment, ← pow_mul] using
    two_atom_moment_logconvex ((1 + a) / 2) ((1 - a) / 2)
      ((b / (1 + a)) ^ 2) ((b / (1 - a)) ^ 2)
      (le_of_lt (div_pos (pair_denom_add_pos a b hab) (by norm_num)))
      (le_of_lt (div_pos (pair_denom_sub_pos a b hab) (by norm_num)))
      (sq_nonneg _) (sq_nonneg _) j

theorem normalizedPairMoment_nonneg {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    0 ≤ normalizedPairMoment a b j := by
  unfold normalizedPairMoment
  split_ifs with hj
  · norm_num
  · apply div_nonneg _ (normalized_pair_scale_pos hab).le
    unfold rawPairMoment
    apply add_nonneg
    · apply mul_nonneg (by linarith [pair_denom_add_pos a b hab])
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j
    · apply mul_nonneg (by linarith [pair_denom_sub_pos a b hab])
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) j

theorem normalizedPairMoment_one {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 1 = b ^ 2 / (1 - a ^ 2) ^ 2 := by
  have hp := ne_of_gt (pair_denom_add_pos a b hab)
  have hm := ne_of_gt (pair_denom_sub_pos a b hab)
  have hA := ne_of_gt (normalized_pair_scale_pos hab)
  norm_num [normalizedPairMoment, rawPairMoment]
  field_simp
  ring

theorem normalizedPairMoment_two {a b : ℝ} (hab : |a| + |b| < 1) :
    normalizedPairMoment a b 2 = b ^ 4 * (1 + 3 * a ^ 2) / (1 - a ^ 2) ^ 4 := by
  have hp := ne_of_gt (pair_denom_add_pos a b hab)
  have hm := ne_of_gt (pair_denom_sub_pos a b hab)
  have hA := ne_of_gt (normalized_pair_scale_pos hab)
  norm_num [normalizedPairMoment, rawPairMoment]
  field_simp
  ring

theorem normalizedPairMoment_logconvex {a b : ℝ} (hab : |a| + |b| < 1) (j : ℕ) :
    normalizedPairMoment a b (j + 1) ^ 2 ≤
      normalizedPairMoment a b j * normalizedPairMoment a b (j + 2) := by
  cases j with
  | zero =>
    rw [normalizedPairMoment_zero, one_mul, normalizedPairMoment_one hab,
      normalizedPairMoment_two hab]
    calc
      (b ^ 2 / (1 - a ^ 2) ^ 2) ^ 2 = b ^ 4 / (1 - a ^ 2) ^ 4 := by
        rw [div_pow, ← pow_mul, ← pow_mul]
      _ ≤ b ^ 4 * (1 + 3 * a ^ 2) / (1 - a ^ 2) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [show 0 ≤ 3 * a ^ 2 * b ^ 4 by positivity]
  | succ j =>
    change (rawPairMoment a b (j + 2) / (1 - a ^ 2)) ^ 2 ≤
      (rawPairMoment a b (j + 1) / (1 - a ^ 2)) *
        (rawPairMoment a b (j + 3) / (1 - a ^ 2))
    rw [div_pow, div_mul_div_comm, ← pow_two (1 - a ^ 2)]
    exact div_le_div_of_nonneg_right (rawPairMoment_logconvex hab (j + 1))
      (sq_nonneg (1 - a ^ 2))

theorem hasSum_normalizedPairEntropy {a b : ℝ} (hab : |a| + |b| < 1) :
    HasSum (fun k => psiCoeff k * normalizedPairMoment a b (k + 1))
      (pairEntropyGap a b / (1 - a ^ 2)) := by
  have hp := hasSum_psi (abs_lt.mpr (pair_ratio_add_mem_Ioo a b hab))
  have hm := hasSum_psi (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b hab))
  have hs := ((hp.mul_left ((1 + a) / 2)).add
    (hm.mul_left ((1 - a) / 2))).div_const (1 - a ^ 2)
  convert hs using 1 <;> try with_reducible_and_instances rfl
  · ext k
    rw [normalizedPairMoment_succ]
    unfold rawPairMoment
    ring
  · rw [pairEntropyGap_weighted a b hab]

theorem hasSum_normalizedPairDissipation {a b : ℝ} (hab : |a| + |b| < 1) :
    HasSum (fun k : ℕ => (2 * ((k : ℝ) + 1)) *
      (psiCoeff k * normalizedPairMoment a b (k + 1)))
      (pairDissipation a b / (1 - a ^ 2)) := by
  have hp := hasSum_mul_artanh (abs_lt.mpr (pair_ratio_add_mem_Ioo a b hab))
  have hm := hasSum_mul_artanh (abs_lt.mpr (pair_ratio_sub_mem_Ioo a b hab))
  have hs := ((hp.mul_left ((1 + a) / 2)).add
    (hm.mul_left ((1 - a) / 2))).div_const (1 - a ^ 2)
  convert hs using 1 <;> try with_reducible_and_instances rfl
  · ext k
    rw [normalizedPairMoment_succ]
    unfold rawPairMoment
    ring
  · rw [pairDissipation_weighted a b hab]

theorem normalized_pair_dissipation_ge_of_psi {a b v : ℝ}
    (hab : |a| + |b| < 1) (hv : |v| < 1)
    (hvpsi : psi v = pairEntropyGap a b / (1 - a ^ 2)) :
    v * Real.artanh v ≤ pairDissipation a b / (1 - a ^ 2) := by
  apply weighted_hasSum_le_of_logconvex
    (m := normalizedPairMoment a b) (c := psiCoeff)
    (weight := fun k => 2 * ((k : ℝ) + 1)) (t := v ^ 2)
    (normalizedPairMoment_nonneg hab)
    (by simp) (normalizedPairMoment_logconvex hab) psiCoeff_nonneg
  · intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    dsimp
    linarith
  · exact sq_nonneg v
  · exact hasSum_normalizedPairEntropy hab
  · simpa only [← pow_mul, hvpsi] using hasSum_psi hv
  · exact hasSum_normalizedPairDissipation hab
  · simpa only [← pow_mul, mul_assoc] using hasSum_mul_artanh hv

theorem normalized_pair_dissipation_ge_r {a b : ℝ} (hab : |a| + |b| < 1) :
    r (pairEntropyGap a b / (1 - a ^ 2)) ≤ pairDissipation a b / (1 - a ^ 2) := by
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hv := psiInv_mem_Ico hs0 hs1
  exact normalized_pair_dissipation_ge_of_psi hab
    (by simpa only [abs_of_nonneg hv.1] using hv.2) (psi_psiInv hs0 hs1)

private theorem normalized_pair_bound_of_antitone
    (hanti : AntitoneOn L (Set.Ioi 0)) {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b := by
  have hA := normalized_pair_scale_pos hab
  have hs0 := pairEntropyGap_div_variance_nonneg a b hab
  have hs1 := pairEntropyGap_div_variance_lt_ell a b hab
  have hlow : 0 < ell - pairEntropyGap a b / (1 - a ^ 2) := sub_pos.mpr hs1
  have ha : |a| ≤ 1 :=
    (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg b)) hab).le
  have hH := ell_mul_one_sub_sq_le_entropy ha
  have hratio : ell - pairEntropyGap a b / (1 - a ^ 2) ≤
      ((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2) := by
    apply (le_div_iff₀ hA).mpr
    calc
      (ell - pairEntropyGap a b / (1 - a ^ 2)) * (1 - a ^ 2) =
          ell * (1 - a ^ 2) - pairEntropyGap a b := by
        field_simp
      _ ≤ entropy a - pairEntropyGap a b := sub_le_sub_right hH _
      _ = (entropy (a + b) + entropy (a - b)) / 2 := by
        unfold pairEntropyGap
        ring
  have hL := hanti hlow (hlow.trans_le hratio) hratio
  rw [L_ell_sub hs0 hs1] at hL
  have hr := normalized_pair_dissipation_ge_r hab
  have hbound :
      L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        (pairDissipation a b - 2 * pairEntropyGap a b) / (1 - a ^ 2) := by
    calc
      _ ≤ r (pairEntropyGap a b / (1 - a ^ 2)) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := hL
      _ ≤ pairDissipation a b / (1 - a ^ 2) -
          2 * (pairEntropyGap a b / (1 - a ^ 2)) := sub_le_sub_right hr _
      _ = _ := by ring
  simpa only [mul_comm] using (le_div_iff₀ hA).mp hbound

theorem normalized_pair_bound {a b : ℝ} (hab : |a| + |b| < 1) :
    (1 - a ^ 2) *
        L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
      pairDissipation a b - 2 * pairEntropyGap a b :=
  normalized_pair_bound_of_antitone antitoneOn_L hab

end LeanBlast.CourtadeKumar

end OAI
end

section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

private def trapezoidGap (q w : ℝ) : ℝ :=
  (1 + w - 2 * q) * (Real.log (1 - q) - Real.log (w - q)) +
    (1 + w) * Real.log w

private def trapezoidGapDeriv (q w : ℝ) : ℝ :=
  Real.log (1 - q) - Real.log (w - q) - (1 + w - 2 * q) / (w - q) +
    Real.log w + (1 + w) / w

private theorem hasDerivAt_trapezoidGap (q w : ℝ) (hw0 : 0 < w) (hqw : q < w) :
    HasDerivAt (trapezoidGap q) (trapezoidGapDeriv q w) w := by
  have ha := ((hasDerivAt_id w).const_add (1 : ℝ)).sub_const (2 * q)
  have hb := HasDerivAt.const_sub (Real.log (1 - q))
    (((hasDerivAt_id w).sub_const q).log (ne_of_gt (sub_pos.mpr hqw)))
  have hc := ((hasDerivAt_id w).const_add (1 : ℝ)).mul
    (Real.hasDerivAt_log (ne_of_gt hw0))
  convert! (ha.mul hb).add hc using 1
  dsimp [trapezoidGap, trapezoidGapDeriv]
  ring

private theorem trapezoidGapDeriv_nonpos (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) : trapezoidGapDeriv q w ≤ 0 := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd : 0 < w - q := sub_pos.mpr hqw
  have hq1 : q < 1 := lt_of_lt_of_le hqw hw1
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  let r : ℝ := (1 - q) * w / (w - q)
  have hr : 0 < r := div_pos (mul_pos h1q hw0) hd
  have hlog := Real.log_le_sub_one_of_pos hr
  have hlogeq : Real.log r = Real.log (1 - q) + Real.log w - Real.log (w - q) := by
    dsimp [r]
    rw [Real.log_div (ne_of_gt (mul_pos h1q hw0)) (ne_of_gt hd),
      Real.log_mul (ne_of_gt h1q) (ne_of_gt hw0)]
  rw [hlogeq] at hlog
  have hrem : r - 1 + (1 + w) / w - (1 + w - 2 * q) / (w - q) =
      -q * (1 - w) ^ 2 / (w * (w - q)) := by
    dsimp [r]
    field_simp [ne_of_gt hw0, ne_of_gt hd]
    ring
  have hrest : r - 1 + (1 + w) / w - (1 + w - 2 * q) / (w - q) ≤ 0 := by
    rw [hrem]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq0) (sq_nonneg _))
      (mul_nonneg hw0.le hd.le)
  unfold trapezoidGapDeriv
  linarith

private theorem trapezoidGap_nonneg (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) : 0 ≤ trapezoidGap q w := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd (v : ℝ) (hv : v ∈ Set.Icc w 1) :
      HasDerivAt (trapezoidGap q) (trapezoidGapDeriv q v) v :=
    hasDerivAt_trapezoidGap q v (lt_of_lt_of_le hw0 hv.1) (lt_of_lt_of_le hqw hv.1)
  have hanti : AntitoneOn (trapezoidGap q) (Set.Icc w 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc w 1)
    · intro v hv
      exact (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      exact (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      have hvm : v ∈ Set.Icc w 1 := interior_subset hv
      rw [(hd v hvm).deriv]
      exact trapezoidGapDeriv_nonpos q v hq0 (lt_of_lt_of_le hqw hvm.1) hvm.2
  have h := hanti ⟨le_refl w, hw1⟩ ⟨hw1, le_refl 1⟩ hw1
  simpa [trapezoidGap] using h

theorem perspective_log_trapezoid (q w : ℝ)
    (hq0 : 0 ≤ q) (hqw : q < w) (hw1 : w ≤ 1) :
    2 * ((w - q) * Real.log (w - q) - (1 - q) * Real.log (1 - q) -
      w * Real.log w) ≤
      (1 - w) * (-Real.log (1 - q / w) - Real.log (1 - q)) := by
  have hw0 : 0 < w := lt_of_le_of_lt hq0 hqw
  have hd : 0 < w - q := sub_pos.mpr hqw
  have hlog : Real.log (1 - q / w) = Real.log (w - q) - Real.log w := by
    rw [show 1 - q / w = (w - q) / w by field_simp]
    exact Real.log_div (ne_of_gt hd) (ne_of_gt hw0)
  have hgap := trapezoidGap_nonneg q w hq0 hqw hw1
  rw [hlog]
  unfold trapezoidGap at hgap
  nlinarith only [hgap]

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem antitoneOn_Ioi_of_hasDerivAt_nonpos_except
    (f f' : ℝ → ℝ) (a c : ℝ)
    (hf : ContinuousOn f (Ioi a))
    (hd : ∀ x, a < x → x ≠ c → HasDerivAt f (f' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f' x ≤ 0) :
    AntitoneOn f (Ioi a) := by
  have hsegment (l r : ℝ) (hal : a < l) (hlr : l ≤ r)
      (hc : c ∉ Ioo l r) : f r ≤ f l := by
    have hanti : AntitoneOn f (Icc l r) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := f') (convex_Icc l r)
      · exact hf.mono (fun _ hz => hal.trans_le hz.1)
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact (hd z (hal.trans hz.1) hzc).hasDerivWithinAt
      · intro z hz
        rw [interior_Icc] at hz
        have hzc : z ≠ c := by
          rintro rfl
          exact hc hz
        exact hneg z (hal.trans hz.1) hzc
    exact hanti ⟨le_rfl, hlr⟩ ⟨hlr, le_rfl⟩ hlr
  intro x hx y hy hxy
  by_cases hc : c ∈ Ioo x y
  · exact (hsegment c y (hx.trans hc.1) hc.2.le (by simp)).trans
      (hsegment x c hx hc.1.le (by simp))
  · exact hsegment x y hx hxy hc

theorem concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (f f' f'' : ℝ → ℝ) (a c : ℝ)
    (hd : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hcf' : ContinuousOn f' (Ioi a))
    (hd' : ∀ x, a < x → x ≠ c → HasDerivAt f' (f'' x) x)
    (hneg : ∀ x, a < x → x ≠ c → f'' x ≤ 0) :
    ConcaveOn ℝ (Ioi a) f := by
  have hanti := antitoneOn_Ioi_of_hasDerivAt_nonpos_except f' f'' a c hcf' hd' hneg
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi a)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Ioi] at hx hy
    rw [(hd x hx).deriv, (hd y hy).deriv]
    exact hanti hx hy hxy

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

def logCorrectedPerspective (f : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  v * f (x / v) - C * v * Real.log v

def logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  f (x / v) - (x / v) * f' (x / v) - C * (Real.log v + 1)

def logCorrectedPerspectiveSecondDeriv (f'' : ℝ → ℝ) (x C v : ℝ) : ℝ :=
  ((x / v) ^ 2 * f'' (x / v) - C) / v

private theorem hasDerivAt_const_quotient (x v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => x / w) (-x / v ^ 2) v := by
  convert! (hasDerivAt_const v x).div (hasDerivAt_id v) (ne_of_gt hv) using 1
  simp

theorem hasDerivAt_logCorrectedPerspective (f f' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspective f x C)
      (logCorrectedPerspectiveDeriv f f' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hp := (hasDerivAt_id v).mul (hf.comp v hi)
  have hl := ((hasDerivAt_id v).mul (Real.hasDerivAt_log (ne_of_gt hv))).const_mul C
  convert hp.sub hl using 1 <;> try with_reducible_and_instances rfl
  · ext w
    change w * f (x / w) - C * w * Real.log w =
      w * f (x / w) - C * (w * Real.log w)
    ring
  · dsimp only [logCorrectedPerspectiveDeriv, id_eq, Function.comp_def]
    field_simp [ne_of_gt hv]
    ring

theorem hasDerivAt_logCorrectedPerspectiveDeriv (f f' f'' : ℝ → ℝ) (x C : ℝ)
    {v : ℝ} (hv : 0 < v) (hf : HasDerivAt f (f' (x / v)) (x / v))
    (hf' : HasDerivAt f' (f'' (x / v)) (x / v)) :
    HasDerivAt (logCorrectedPerspectiveDeriv f f' x C)
      (logCorrectedPerspectiveSecondDeriv f'' x C v) v := by
  have hi := hasDerivAt_const_quotient x v hv
  have hfirst := hf.comp v hi
  have hsecond := hi.mul (hf'.comp v hi)
  have hlog := ((Real.hasDerivAt_log (ne_of_gt hv)).add_const 1).const_mul C
  convert! (hfirst.sub hsecond).sub hlog using 1
  dsimp only [logCorrectedPerspectiveSecondDeriv, Function.comp_apply]
  field_simp [ne_of_gt hv]
  ring

theorem continuousOn_logCorrectedPerspectiveDeriv (f f' : ℝ → ℝ) (x C : ℝ)
    (hx : 0 < x) (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hf' : ContinuousOn f' (Ioi 0)) :
    ContinuousOn (logCorrectedPerspectiveDeriv f f' x C) (Ioi 0) := by
  have hi : ContinuousOn (fun v : ℝ => x / v) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ hv => ne_of_gt hv)
  have hmap : MapsTo (fun v : ℝ => x / v) (Ioi 0) (Ioi 0) :=
    fun _ hv => div_pos hx hv
  have hcf : ContinuousOn f (Ioi 0) :=
    fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hl : ContinuousOn Real.log (Ioi 0) :=
    continuousOn_id.log (fun _ hv => ne_of_gt hv)
  exact ((hcf.comp hi hmap).sub (hi.mul (hf'.comp hi hmap))).sub
    (continuousOn_const.mul (hl.add continuousOn_const))

theorem concaveOn_logCorrectedPerspective (f f' f'' : ℝ → ℝ)
    (x C join : ℝ) (hx : 0 < x) (hjoin : 0 < join)
    (hf : ∀ y, 0 < y → HasDerivAt f (f' y) y)
    (hcf' : ContinuousOn f' (Ioi 0))
    (hf' : ∀ y, 0 < y → y ≠ join → HasDerivAt f' (f'' y) y)
    (hcurv : ∀ y, 0 < y → y ≠ join → y ^ 2 * f'' y ≤ C) :
    ConcaveOn ℝ (Ioi 0) (logCorrectedPerspective f x C) := by
  have hneq {v : ℝ} (hv : 0 < v) (hvc : v ≠ x / join) : x / v ≠ join := by
    intro heq
    apply hvc
    apply (eq_div_iff (ne_of_gt hjoin)).mpr
    have h := (div_eq_iff (ne_of_gt hv)).mp heq
    linarith
  apply concaveOn_Ioi_of_hasDerivAt2_nonpos_except
    (logCorrectedPerspective f x C) (logCorrectedPerspectiveDeriv f f' x C)
    (logCorrectedPerspectiveSecondDeriv f'' x C) 0 (x / join)
  · intro v hv
    exact hasDerivAt_logCorrectedPerspective f f' x C hv (hf _ (div_pos hx hv))
  · exact continuousOn_logCorrectedPerspectiveDeriv f f' x C hx hf hcf'
  · intro v hv hvc
    exact hasDerivAt_logCorrectedPerspectiveDeriv f f' f'' x C hv
      (hf _ (div_pos hx hv)) (hf' _ (div_pos hx hv) (hneq hv hvc))
  · intro v hv hvc
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hcurv _ (div_pos hx hv) (hneq hv hvc))) hv.le

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

def logBarrier (b : ℝ) : ℝ := -Real.log (1 - b)

@[simp] theorem logBarrier_zero : logBarrier 0 = 0 := by simp [logBarrier]

theorem hasDerivAt_logBarrier {b : ℝ} (hb : b < 1) :
    HasDerivAt logBarrier (1 / (1 - b)) b := by
  have h := (((hasDerivAt_const b (1 : ℝ)).sub (hasDerivAt_id b)).log
    (show 1 - b ≠ 0 by linarith)).neg
  convert! h using 1
  simp [neg_div]

theorem lambda_truncated_upper {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k m : ℕ) :
    (1 - z ^ k) * lambda z ≤
      (∑ j ∈ Finset.range k, z ^ j / ((j : ℝ) + 1)) -
      ∑ j ∈ Finset.range m,
        (z ^ k * (z ^ j / ((j : ℝ) + 1)) -
          z ^ (j + k) / ((j : ℝ) + k + 1)) := by
  have hs := hasSum_lambda hz0 hz1
  have ht := (hasSum_nat_add_iff' k).mpr hs
  have hd := (hs.mul_left (z ^ k)).sub ht
  simp only [Nat.cast_add] at hd
  have hnonneg : ∀ j : ℕ,
      0 ≤ z ^ k * (z ^ j / ((j : ℝ) + 1)) -
        z ^ (j + k) / ((j : ℝ) + k + 1) := by
    intro j
    rw [sub_nonneg, ← mul_div_assoc, ← pow_add, Nat.add_comm k j]
    apply div_le_div_of_nonneg_left (pow_nonneg hz0 _) (by positivity)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hp := sum_le_hasSum (Finset.range m) (fun j _ => hnonneg j) hd
  linarith

theorem lambda_cutoff_four {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (1 - b ^ 4) * lambda b ≤
      1 + b / 2 + b ^ 2 / 3 + b ^ 3 / 4 - (4 / 5 : ℝ) * b ^ 4 -
        b ^ 5 / 3 - (4 / 21 : ℝ) * b ^ 6 - b ^ 7 / 8 - (4 / 45 : ℝ) * b ^ 8 := by
  have h := lambda_truncated_upper hb0 hb1 4 5
  norm_num [Finset.sum_range_succ] at h
  nlinarith

private theorem sq_lt_one_of_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) : b ^ 2 < 1 := by
  have h := mul_pos (sub_pos.mpr hb1) (show 0 < 1 + b by linarith)
  nlinarith

theorem lambda_cutoff_two_sq {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    (1 - b ^ 4) * lambda (b ^ 2) ≤
      1 + b ^ 2 / 2 - (2 / 3 : ℝ) * b ^ 4 - b ^ 6 / 4 - (2 / 15 : ℝ) * b ^ 8 := by
  have h := lambda_truncated_upper (sq_nonneg b) (sq_lt_one_of_nonneg hb0 hb1) 2 3
  norm_num [Finset.sum_range_succ] at h
  nlinarith

def lambdaDerivativeFactor (b : ℝ) : ℝ :=
  9 - b - 3 * b ^ 2 - b ^ 3 - 3 * (1 - b ^ 4) * lambda b -
    2 * (1 - b ^ 4) * lambda (b ^ 2)

theorem lambda_polynomial_le_factor {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    4 - (5 / 2 : ℝ) * b - 5 * b ^ 2 - (7 / 4 : ℝ) * b ^ 3 +
      (56 / 15 : ℝ) * b ^ 4 + b ^ 5 + (15 / 14 : ℝ) * b ^ 6 +
      (3 / 8 : ℝ) * b ^ 7 + (8 / 15 : ℝ) * b ^ 8 ≤ lambdaDerivativeFactor b := by
  unfold lambdaDerivativeFactor
  have h1 := lambda_cutoff_four hb0 hb1
  have h2 := lambda_cutoff_two_sq hb0 hb1
  nlinarith

def lambdaAuxiliary (b : ℝ) : ℝ :=
  3 * logBarrier (b ^ 4) - b ^ 3 * logBarrier b - b ^ 2 * logBarrier (b ^ 2)

def lambdaAuxiliaryDerivative (b : ℝ) : ℝ :=
  12 * b ^ 3 / (1 - b ^ 4) - 3 * b ^ 2 * logBarrier b - b ^ 3 / (1 - b) -
    2 * b * logBarrier (b ^ 2) - 2 * b ^ 3 / (1 - b ^ 2)

@[simp] theorem lambdaAuxiliary_zero : lambdaAuxiliary 0 = 0 := by
  simp [lambdaAuxiliary]

theorem hasDerivAt_lambdaAuxiliary {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasDerivAt lambdaAuxiliary (lambdaAuxiliaryDerivative b) b := by
  have hb2 := sq_lt_one_of_nonneg hb0 hb1
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) hb2
    nlinarith
  have h1 := hasDerivAt_logBarrier hb1
  have h2 := (hasDerivAt_logBarrier hb2).comp b (h := fun t : ℝ => t ^ 2) (hasDerivAt_pow 2 b)
  have h4 := (hasDerivAt_logBarrier hb4).comp b (h := fun t : ℝ => t ^ 4) (hasDerivAt_pow 4 b)
  have hd := ((h4.const_mul 3).sub ((hasDerivAt_pow 3 b).mul h1)).sub
    ((hasDerivAt_pow 2 b).mul h2)
  convert! hd using 1
  simp only [lambdaAuxiliaryDerivative, Function.comp_apply]
  ring

theorem lambdaAuxiliaryDerivative_factor {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    lambdaAuxiliaryDerivative b = b ^ 3 / (1 - b ^ 4) * lambdaDerivativeFactor b := by
  have hb2 := sq_lt_one_of_nonneg hb0.le hb1
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) hb2
    nlinarith
  have hne : b ≠ 0 := hb0.ne'
  have hne2 : b ^ 2 ≠ 0 := pow_ne_zero _ hne
  have h1 : 1 - b ≠ 0 := by linarith
  have h2 : 1 - b ^ 2 ≠ 0 := by linarith
  have h4 : 1 - b ^ 4 ≠ 0 := by linarith
  simp only [lambdaAuxiliaryDerivative, lambdaDerivativeFactor, logBarrier,
    lambda_of_ne_zero hne, lambda_of_ne_zero hne2]
  field_simp
  ring

theorem lambdaDerivativeFactor_pos {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 < lambdaDerivativeFactor b := by
  have hp := lambdaCertificate_pos hb0 hb1.le
  have hf := lambda_polynomial_le_factor hb0 hb1
  unfold lambdaPolynomial at hp
  linarith

theorem lambdaAuxiliaryDerivative_nonneg {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ lambdaAuxiliaryDerivative b := by
  rw [lambdaAuxiliaryDerivative_factor hb0 hb1]
  have hb4 : b ^ 4 < 1 := by
    have h := sq_lt_one_of_nonneg (sq_nonneg b) (sq_lt_one_of_nonneg hb0.le hb1)
    nlinarith
  exact mul_nonneg (div_nonneg (pow_nonneg hb0.le _) (sub_nonneg.mpr hb4.le))
    (lambdaDerivativeFactor_pos hb0.le hb1).le

theorem monotoneOn_lambdaAuxiliary : MonotoneOn lambdaAuxiliary (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    (fun b hb => (hasDerivAt_lambdaAuxiliary hb.1 hb.2).continuousAt.continuousWithinAt)
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact (hasDerivAt_lambdaAuxiliary hb.1.le hb.2).hasDerivWithinAt
  · intro b hb
    simp only [interior_Ico, mem_Ioo] at hb
    exact lambdaAuxiliaryDerivative_nonneg hb.1 hb.2

theorem lambdaAuxiliary_nonneg {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    0 ≤ lambdaAuxiliary b := by
  simpa using monotoneOn_lambdaAuxiliary
    (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hb0, hb1⟩ hb0

theorem lambdaAuxiliary_eq (b : ℝ) :
    lambdaAuxiliary b = b ^ 4 * (3 * lambda (b ^ 4) - lambda b - lambda (b ^ 2)) := by
  have hM (z : ℝ) : logBarrier z = z * lambda z := (mul_lambda z).symm
  rw [lambdaAuxiliary, hM, hM, hM]
  ring

theorem lambda_add_sq_le (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    lambda b + lambda (b ^ 2) ≤ 3 * lambda (b ^ 4) := by
  by_cases hb : b = 0
  · subst b
    norm_num
  have h := lambdaAuxiliary_nonneg hb0 hb1
  rw [lambdaAuxiliary_eq] at h
  have hp : 0 < b ^ 4 := pow_pos (lt_of_le_of_ne hb0 (Ne.symm hb)) _
  have ht := nonneg_of_mul_nonneg_right h hp
  linarith

theorem lambda_sqrt_add_le (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    lambda (Real.sqrt q) + lambda q ≤ 3 * lambda (q ^ 2) := by
  have hsq := Real.sq_sqrt hq0
  have hq : Real.sqrt q < 1 := by nlinarith [Real.sqrt_nonneg q]
  have h := lambda_add_sq_le (Real.sqrt q) (Real.sqrt_nonneg q) hq
  have hfour : (Real.sqrt q) ^ 4 = q ^ 2 := by nlinarith [sq_nonneg (Real.sqrt q)]
  simpa only [hsq, hfour] using h

theorem concave_perspective_exchange (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Ioi 0) f)
    (w q : ℝ) (hq0 : 0 < q) (hqw : q < w) (hw1 : w ≤ 1) :
    f 1 + f (w - q) ≤ f w + f (1 - q) := by
  let a := q / (1 - w + q)
  let b := (1 - w) / (1 - w + q)
  have hr : 0 < 1 - w + q := by linarith
  have ha : 0 ≤ a := div_nonneg hq0.le hr.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hw1) hr.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hab' : b + a = 1 := by linarith
  have hp1 : a * 1 + b * (w - q) = w := by dsimp [a, b]; field_simp; ring
  have hp2 : b * 1 + a * (w - q) = 1 - q := by dsimp [a, b]; field_simp; ring
  have h1 := hf.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show w - q ∈ Ioi 0 from sub_pos.mpr hqw) ha hb hab
  have h2 := hf.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show w - q ∈ Ioi 0 from sub_pos.mpr hqw) hb ha hab'
  simp only [smul_eq_mul, hp1, hp2] at h1 h2
  calc
    f 1 + f (w - q) = (a * f 1 + b * f (w - q)) +
        (b * f 1 + a * f (w - q)) := by
      calc
        _ = (a + b) * f 1 + (a + b) * f (w - q) := by rw [hab]; ring
        _ = _ := by ring
    _ ≤ f w + f (1 - q) := add_le_add h1 h2

theorem perspective_kernel_upper (f : ℝ → ℝ) (x w q : ℝ)
    (hx : 0 < x) (hq0 : 0 < q) (hqw : q < w) (hw1 : w ≤ 1)
    (hf0 : ∀ t, 0 < t → 0 ≤ f t)
    (hconc : ConcaveOn ℝ (Ioi 0)
      (fun v => v * f (x / v) - (2 / 3 : ℝ) * v * Real.log v)) :
    f x - (1 - q) * f (x / (1 - q)) - w * f (x / w) ≤
      (2 / 3 : ℝ) * ((w - q) * Real.log (w - q) -
        (1 - q) * Real.log (1 - q) - w * Real.log w) := by
  have he := concave_perspective_exchange _ hconc w q hq0 hqw hw1
  have hn : 0 ≤ (w - q) * f (x / (w - q)) :=
    mul_nonneg (sub_nonneg.mpr hqw.le) (hf0 _ (div_pos hx (sub_pos.mpr hqw)))
  simp only [one_mul, div_one, Real.log_one, mul_zero, sub_zero] at he
  nlinarith

theorem lt_weight_of_le_weight_sq {w q : ℝ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hq1 : q < 1) (hqw : q ≤ w ^ 2) : q < w := by
  rcases eq_or_lt_of_le hw1 with rfl | hwlt
  · simpa using hq1
  · have hsq : w ^ 2 < w := by nlinarith [mul_pos hw0 (sub_pos.mpr hwlt)]
    exact hqw.trans_lt hsq

theorem lambda_trapezoid_bound (w q : ℝ)
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) :
    (1 - w) / 3 * (logBarrier (q / w) + logBarrier q) ≤
      q * (1 / w - 1) * lambda (q ^ 2) := by
  have hlt := lt_weight_of_le_weight_sq hw0 hw1 hq1 hqw
  have hqdiv0 : 0 ≤ q / w := div_nonneg hq0 hw0.le
  have hqdiv1 : q / w < 1 := (div_lt_one hw0).mpr hlt
  have hs0 := Real.sqrt_nonneg q
  have hs2 := Real.sq_sqrt hq0
  have hs1 : Real.sqrt q < 1 := by nlinarith
  have hsw : Real.sqrt q ≤ w := by nlinarith
  have hdivsqrt : q / w ≤ Real.sqrt q := by
    apply (div_le_iff₀ hw0).mpr
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hsw)]
  have hl1 := monotoneOn_lambda ⟨hqdiv0, hqdiv1⟩ ⟨hs0, hs1⟩ hdivsqrt
  have hl2 : w * lambda q ≤ lambda q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (lambda_nonneg hq0 hq1)]
  have hls := lambda_sqrt_add_le q hq0 hq1
  have hsum : lambda (q / w) + w * lambda q ≤ 3 * lambda (q ^ 2) := by linarith
  have hcoef : 0 ≤ q * (1 - w) / (3 * w) :=
    div_nonneg (mul_nonneg hq0 (sub_nonneg.mpr hw1)) (mul_nonneg (by norm_num) hw0.le)
  have hm := mul_le_mul_of_nonneg_left hsum hcoef
  have hM (z : ℝ) : logBarrier z = z * lambda z := (mul_lambda z).symm
  rw [hM, hM]
  convert hm using 1 <;> first | with_reducible_and_instances rfl | field_simp

theorem perspective_inequality_of_adjusted_concave (f : ℝ → ℝ) (x w q : ℝ)
    (hx : 0 < x) (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) (hf0 : ∀ t, 0 < t → 0 ≤ f t)
    (hconc : ConcaveOn ℝ (Ioi 0)
      (fun v => v * f (x / v) - (2 / 3 : ℝ) * v * Real.log v)) :
    f x - (1 - q) * f (x / (1 - q)) - w * f (x / w) ≤
      q * (1 / w - 1) * lambda (q ^ 2) := by
  rcases eq_or_lt_of_le hq0 with hq | hq
  · subst q
    have hn := mul_nonneg hw0.le (hf0 _ (div_pos hx hw0))
    simpa using neg_nonpos.mpr hn
  have hlt := lt_weight_of_le_weight_sq hw0 hw1 hq1 hqw
  have hk := perspective_kernel_upper f x w q hx hq hlt hw1 hf0 hconc
  have ht := perspective_log_trapezoid q w hq0 hlt hw1
  have hl := lambda_trapezoid_bound w q hw0 hw1 hq0 hq1 hqw
  have hc : (2 / 3 : ℝ) * ((w - q) * Real.log (w - q) -
        (1 - q) * Real.log (1 - q) - w * Real.log w) ≤
      (1 - w) / 3 * (logBarrier (q / w) + logBarrier q) := by
    unfold logBarrier
    nlinarith
  exact hk.trans (hc.trans hl)

theorem LSecondDeriv_curvature_bound {x : ℝ} (hx : 0 < x) :
    x ^ 2 * LSecondDeriv x ≤ 2 / 3 := by
  by_cases hxl : x < ell
  · simpa only [LSecondDeriv, if_pos hxl] using L_curvature_bound ⟨hx, hxl⟩
  · simp only [LSecondDeriv, if_neg hxl, mul_zero]
    norm_num

theorem concaveOn_L_logCorrectedPerspective (x : ℝ) (hx : 0 < x) :
    ConcaveOn ℝ (Ioi 0)
      (fun v => v * L (x / v) - (2 / 3 : ℝ) * v * Real.log v) := by
  exact concaveOn_logCorrectedPerspective L LDeriv LSecondDeriv x (2 / 3) ell
    hx ell_pos (fun y hy => hasDerivAt_L hy) continuousOn_LDeriv
    (fun y hy hne => hasDerivAt_LDeriv hy hne)
    (fun y hy _ => LSecondDeriv_curvature_bound hy)

theorem perspective_inequality (x w q : ℝ)
    (hx : 0 < x) (hw0 : 0 < w) (hw1 : w ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hqw : q ≤ w ^ 2) :
    L x - (1 - q) * L (x / (1 - q)) - w * L (x / w) ≤
      q * (1 / w - 1) * lambda (q ^ 2) :=
  perspective_inequality_of_adjusted_concave L x w q hx hw0 hw1 hq0 hq1 hqw
    (fun _ ht => L_nonneg ht) (concaveOn_L_logCorrectedPerspective x hx)

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace LeanBlast.CourtadeKumar

theorem IsIncreasing.restrict {n : ℕ} {g : Cube (n + 1) → ℝ}
    (hg : IsIncreasing g) (b : Bool) : IsIncreasing (restrict g b) := by
  intro x y hxy
  apply hg
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · exact hxy j

theorem IsIncreasing.pairHalfDifference_nonneg {n : ℕ} {g : Cube (n + 1) → ℝ}
    (hg : IsIncreasing g) (x : Cube n) : 0 ≤ pairHalfDifference g x := by
  have horder : CourtadeKumar.restrict g false x ≤ CourtadeKumar.restrict g true x := by
    apply hg
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact le_rfl
  exact div_nonneg (sub_nonneg.mpr horder) (by norm_num)

theorem scalar_meanVariance_pos {m : ℝ} (hm : |m| < 1) : 0 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ (abs_nonneg m) (by norm_num : (0 : ℝ) ≤ 1)).mpr hm
  rw [sq_abs] at hsq
  nlinarith

theorem scalar_meanVariance_le_one (m : ℝ) : 1 - m ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg m]

theorem IsInterior.meanVariance_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < meanVariance g :=
  scalar_meanVariance_pos (abs_lt.mpr hg.cubeAverage)

theorem IsInterior.entropyAverage_pos {n : ℕ} {g : Cube n → ℝ}
    (hg : IsInterior g) : 0 < entropyAverage g := by
  have h := cubeAverage_lt (fun x => entropy_pos (hg x))
  simpa only [cubeAverage_const, entropyAverage] using h

theorem average_one_sub_sq_le_meanVariance {n : ℕ} (a : Cube n → ℝ) :
    cubeAverage (fun x => 1 - (a x) ^ 2) ≤ meanVariance a := by
  rw [average_one_sub_sq_eq_meanVariance_sub_variance]
  linarith [cubeVariance_nonneg a]

theorem monotone_pair_average_geometry {n : ℕ} (a b : Cube n → ℝ)
    (hdom : ∀ x, |a x| + |b x| < 1) (hb : ∀ x, 0 ≤ b x) :
    |cubeAverage a| < 1 ∧ 0 ≤ cubeAverage b ∧
      cubeAverage b < 1 - |cubeAverage a| ∧
      0 < cubeAverage (fun x => 1 - (a x) ^ 2) ∧
      cubeAverage (fun x => 1 - (a x) ^ 2) ≤ 1 - (cubeAverage a) ^ 2 ∧
      cubeAverage b ≤ cubeAverage (fun x => 1 - (a x) ^ 2) := by
  have ha : IsInterior a := by
    intro x
    apply abs_lt.mp
    linarith [hdom x, abs_nonneg (b x)]
  have hm : |cubeAverage a| < 1 := abs_lt.mpr ha.cubeAverage
  have hk : 0 ≤ cubeAverage b := cubeAverage_nonneg hb
  have hplus : cubeAverage a + cubeAverage b < 1 := by
    have h := cubeAverage_lt (g := fun x => a x + b x) (h := fun _ => 1) (by
      intro x
      have hd := hdom x
      rw [abs_of_nonneg (hb x)] at hd
      linarith [le_abs_self (a x)])
    simpa only [cubeAverage_add, cubeAverage_const] using h
  have hminus : -cubeAverage a + cubeAverage b < 1 := by
    have h := cubeAverage_lt (g := fun x => -a x + b x) (h := fun _ => 1) (by
      intro x
      have hd := hdom x
      rw [abs_of_nonneg (hb x)] at hd
      linarith [neg_le_abs (a x)])
    simpa only [cubeAverage_add, cubeAverage_neg, cubeAverage_const] using h
  have hkm : cubeAverage b < 1 - |cubeAverage a| := by
    by_cases hm0 : 0 ≤ cubeAverage a
    · rw [abs_of_nonneg hm0]
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hm0)]
      linarith
  have hW : 0 < cubeAverage (fun x => 1 - (a x) ^ 2) := by
    have h := cubeAverage_lt (fun x => scalar_meanVariance_pos (abs_lt.mpr (ha x)))
    simpa only [cubeAverage_const] using h
  have hkW : cubeAverage b ≤ cubeAverage (fun x => 1 - (a x) ^ 2) := by
    apply cubeAverage_mono
    intro x
    have hd := hdom x
    rw [abs_of_nonneg (hb x)] at hd
    have ha1 : |a x| ≤ 1 := (abs_lt.mpr (ha x)).le
    have hasq : |a x| ^ 2 ≤ |a x| := by
      nlinarith [mul_nonneg (abs_nonneg (a x)) (sub_nonneg.mpr ha1)]
    nlinarith [sq_abs (a x)]
  exact ⟨hm, hk, hkm, hW, average_one_sub_sq_le_meanVariance a, hkW⟩

theorem halfDifference_sq_lt_meanVariance {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ hk (sub_nonneg.mpr hm.le)).mpr hkm
  have ha : |m| ^ 2 ≤ |m| := by
    nlinarith [mul_nonneg (abs_nonneg m) (sub_nonneg.mpr hm.le)]
  nlinarith [sq_abs m]

theorem monotone_split_parameter_bounds {m k W : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W) :
    0 ≤ k ^ 2 / (1 - m ^ 2) ∧ k ^ 2 / (1 - m ^ 2) < 1 ∧
      0 < W / (1 - m ^ 2) ∧ W / (1 - m ^ 2) ≤ 1 ∧
      k ^ 2 / (1 - m ^ 2) ≤ (W / (1 - m ^ 2)) ^ 2 := by
  have hA := scalar_meanVariance_pos hm
  have hA1 := scalar_meanVariance_le_one m
  refine ⟨div_nonneg (sq_nonneg _) hA.le,
    (div_lt_one hA).mpr (halfDifference_sq_lt_meanVariance hm hk hkm),
    div_pos hW hA, (div_le_one hA).mpr hWA, ?_⟩
  have hk2W2 : k ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hk hW.le).mpr hkW
  have hk2A : k ^ 2 * (1 - m ^ 2) ≤ W ^ 2 := by
    calc
      k ^ 2 * (1 - m ^ 2) ≤ k ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hA1 (sq_nonneg _)
      _ = k ^ 2 := mul_one _
      _ ≤ W ^ 2 := hk2W2
  rw [div_pow]
  apply (div_le_div_iff₀ hA (sq_pos_of_pos hA)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hk2A hA.le]

theorem meanSquare_ratio_le_jensen_ratio {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 / (1 - m ^ 2) ≤ k / (1 + |m|) := by
  have hA := scalar_meanVariance_pos hm
  have hden : 0 < 1 + |m| := by positivity
  apply (div_le_div_iff₀ hA hden).mpr
  have hprod := mul_le_mul_of_nonneg_left hkm.le
    (mul_nonneg hk hden.le)
  rw [← sq_abs m]
  nlinarith [hprod]

theorem jensen_ratio_mem_unit_interval {m k : ℝ}
    (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    0 ≤ k / (1 + |m|) ∧ k / (1 + |m|) < 1 := by
  have hden : 0 < 1 + |m| := by positivity
  refine ⟨div_nonneg hk hden.le, (div_lt_one hden).mpr ?_⟩
  linarith [abs_nonneg m]

theorem normalized_variance_gap_nonneg {q w : ℝ}
    (hq : 0 ≤ q) (hw : 0 < w) (hw1 : w ≤ 1) :
    0 ≤ q * (1 / w - 1) := by
  have hinv : 1 ≤ 1 / w := (le_div_iff₀ hw).mpr (by simpa using hw1)
  exact mul_nonneg hq (sub_nonneg.mpr hinv)

theorem normalized_variance_gap_identity {A W k : ℝ} (hA : A ≠ 0) (hW : W ≠ 0) :
    k ^ 2 / W - k ^ 2 / A = (k ^ 2 / A) * (1 / (W / A) - 1) := by
  field_simp

theorem normalized_jensen_correction_le {m k W V : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V) :
    (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
        lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2) ≤
      V * lambda ((k / (1 + |m|)) ^ 2) := by
  obtain ⟨hq, hq1, hw, hw1, _⟩ :=
    monotone_split_parameter_bounds hm hk hkm hW hWA hkW
  obtain ⟨hs, hs1⟩ := jensen_ratio_mem_unit_interval hk hkm
  have hq2 : (k ^ 2 / (1 - m ^ 2)) ^ 2 < 1 := by nlinarith
  have hs2 : (k / (1 + |m|)) ^ 2 < 1 := by nlinarith
  have hqs : (k ^ 2 / (1 - m ^ 2)) ^ 2 ≤ (k / (1 + |m|)) ^ 2 :=
    (sq_le_sq₀ hq hs).mpr (meanSquare_ratio_le_jensen_ratio hm hk hkm)
  have hB := normalized_variance_gap_nonneg hq hw hw1
  have hBV : (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) ≤ V := by
    rwa [← normalized_variance_gap_identity (scalar_meanVariance_pos hm).ne' hW.ne']
  have hlambda := monotoneOn_lambda ⟨sq_nonneg _, hq2⟩ ⟨sq_nonneg _, hs2⟩ hqs
  exact mul_le_mul hBV hlambda (lambda_nonneg (sq_nonneg _) hq2) (hB.trans hBV)

theorem scaled_perspective_bound (F : ℝ → ℝ) {A W k h B : ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (hW : 0 < W) (hAk : 0 < A - k ^ 2)
    (hB : 0 ≤ B)
    (hperspective : F (h / A) - (1 - k ^ 2 / A) * F ((h / A) / (1 - k ^ 2 / A)) -
      (W / A) * F ((h / A) / (W / A)) ≤ B) :
    A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) - W * F (h / W) ≤ B := by
  have harg1 : (h / A) / (1 - k ^ 2 / A) = h / (A - k ^ 2) := by
    have hden : 1 - k ^ 2 / A = (A - k ^ 2) / A := by field_simp
    rw [hden]
    field_simp
  have harg2 : (h / A) / (W / A) = h / W := by field_simp
  rw [harg1, harg2] at hperspective
  have hscaled := mul_le_mul_of_nonneg_left hperspective hA.le
  have hcoef1 : A * (1 - k ^ 2 / A) = A - k ^ 2 := by field_simp
  have hcoef2 : A * (W / A) = W := by field_simp
  have hleft : A * (F (h / A) - (1 - k ^ 2 / A) * F (h / (A - k ^ 2)) -
      (W / A) * F (h / W)) =
      A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) - W * F (h / W) := by
    rw [mul_sub, mul_sub, ← mul_assoc, hcoef1, ← mul_assoc, hcoef2]
  rw [hleft] at hscaled
  exact hscaled.trans (by nlinarith)

theorem monotone_dissipation_step_algebra (F : ℝ → ℝ)
    {S Jm A k h W B Drestr Dpair : ℝ}
    (hrestr : 2 * (S - Jm) + (A - k ^ 2) * F (h / (A - k ^ 2)) ≤ Drestr)
    (hpair : W * F (h / W) + B ≤ Dpair - 2 * Jm)
    (hperspective : A * F (h / A) - (A - k ^ 2) * F (h / (A - k ^ 2)) -
      W * F (h / W) ≤ B) :
    2 * S + A * F (h / A) ≤ Drestr + Dpair := by
  linarith

theorem monotone_pair_correction {m k W h Je Jm V Dpair : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V)
    (hnormalized : W * L (h / W) ≤ Dpair - 2 * Je)
    (hgap : V * lambda ((k / (1 + |m|)) ^ 2) ≤ 2 * (Je - Jm)) :
    W * L (h / W) +
        (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
          lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2) ≤ Dpair - 2 * Jm := by
  have hcorrection := normalized_jensen_correction_le hm hk hkm hW hWA hkW hV
  linarith

theorem monotone_dissipation_step_of_perspective
    {m k W h S Je Jm V Drestr Dpair : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W)
    (hV : k ^ 2 / W - k ^ 2 / (1 - m ^ 2) ≤ V)
    (hrestr : 2 * (S - Jm) + (1 - m ^ 2 - k ^ 2) *
      L (h / (1 - m ^ 2 - k ^ 2)) ≤ Drestr)
    (hnormalized : W * L (h / W) ≤ Dpair - 2 * Je)
    (hgap : V * lambda ((k / (1 + |m|)) ^ 2) ≤ 2 * (Je - Jm))
    (hperspective : L (h / (1 - m ^ 2)) -
      (1 - k ^ 2 / (1 - m ^ 2)) *
        L ((h / (1 - m ^ 2)) / (1 - k ^ 2 / (1 - m ^ 2))) -
      (W / (1 - m ^ 2)) * L ((h / (1 - m ^ 2)) / (W / (1 - m ^ 2))) ≤
      (k ^ 2 / (1 - m ^ 2)) * (1 / (W / (1 - m ^ 2)) - 1) *
        lambda ((k ^ 2 / (1 - m ^ 2)) ^ 2)) :
    2 * S + (1 - m ^ 2) * L (h / (1 - m ^ 2)) ≤ Drestr + Dpair := by
  have hA := scalar_meanVariance_pos hm
  have hAk : 0 < 1 - m ^ 2 - k ^ 2 := by
    linarith [halfDifference_sq_lt_meanVariance hm hk hkm]
  obtain ⟨hq, hq1, hw, hw1, _⟩ :=
    monotone_split_parameter_bounds hm hk hkm hW hWA hkW
  have hq2 : (k ^ 2 / (1 - m ^ 2)) ^ 2 < 1 := by nlinarith
  have hB := mul_nonneg (normalized_variance_gap_nonneg hq hw hw1)
    (lambda_nonneg (sq_nonneg _) hq2)
  have hp := scaled_perspective_bound L hA (scalar_meanVariance_le_one m) hW hAk hB
    hperspective
  have hc := monotone_pair_correction hm hk hkm hW hWA hkW hV hnormalized hgap
  exact monotone_dissipation_step_algebra L hrestr hc hp

theorem two_point_perspective_jensen (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ioi 0) F) {A₀ A₁ H₀ H₁ : ℝ}
    (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) (hH₀ : 0 < H₀) (hH₁ : 0 < H₁) :
    ((A₁ + A₀) / 2) * F (((H₁ + H₀) / 2) / ((A₁ + A₀) / 2)) ≤
      (A₁ * F (H₁ / A₁) + A₀ * F (H₀ / A₀)) / 2 := by
  have hsum : 0 < A₁ + A₀ := add_pos hA₁ hA₀
  have hweights : A₁ / (A₁ + A₀) + A₀ / (A₁ + A₀) = 1 := by field_simp
  have hJ := hF.2 (show H₁ / A₁ ∈ Ioi 0 from div_pos hH₁ hA₁)
    (show H₀ / A₀ ∈ Ioi 0 from div_pos hH₀ hA₀)
    (div_nonneg hA₁.le hsum.le) (div_nonneg hA₀.le hsum.le) hweights
  simp only [smul_eq_mul] at hJ
  have harg : A₁ / (A₁ + A₀) * (H₁ / A₁) +
      A₀ / (A₁ + A₀) * (H₀ / A₀) = (H₁ + H₀) / (A₁ + A₀) := by
    field_simp
  rw [harg] at hJ
  have hhalf : ((H₁ + H₀) / 2) / ((A₁ + A₀) / 2) =
      (H₁ + H₀) / (A₁ + A₀) := by field_simp
  rw [hhalf]
  have hscaled := mul_le_mul_of_nonneg_left hJ (show 0 ≤ (A₁ + A₀) / 2 by positivity)
  have hright : (A₁ + A₀) / 2 *
      (A₁ / (A₁ + A₀) * F (H₁ / A₁) + A₀ / (A₁ + A₀) * F (H₀ / A₀)) =
      (A₁ * F (H₁ / A₁) + A₀ * F (H₀ / A₀)) / 2 := by
    field_simp
  rwa [hright] at hscaled

theorem monotone_dissipation_zero (g : Cube 0 → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g +
      meanVariance g * L (entropyAverage g / meanVariance g) ≤ dissipation g := by
  have hA : 0 < meanVariance g := hg.meanVariance_pos
  have hscalar := ell_mul_one_sub_sq_le_entropy
    (abs_lt.mpr (hg (fun _ => false))).le
  have hratio : ell ≤ entropyAverage g / meanVariance g := by
    apply (le_div_iff₀ hA).mpr
    simpa only [entropyAverage, meanVariance, cubeAverage_zeroDim] using hscalar
  rw [informationDeficit_dim_zero, dissipation_dim_zero, L_eq_zero_of_ell_le hratio]
  simp

theorem averaged_normalized_pair_of_pointwise
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    (hpair : ∀ a b : ℝ, |a| + |b| < 1 →
      (1 - a ^ 2) * L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        pairDissipation a b - 2 * pairEntropyGap a b)
    {n : ℕ} (g : Cube (n + 1) → ℝ) (hg : IsInterior g) :
    cubeAverage (fun x => 1 - (pairMean g x) ^ 2) *
        L (entropyAverage g / cubeAverage (fun x => 1 - (pairMean g x) ^ 2)) ≤
      cubeAverage (fun x => pairDissipation (pairMean g x) (pairHalfDifference g x)) -
        2 * cubeAverage (fun x => pairEntropyGap (pairMean g x) (pairHalfDifference g x)) := by
  let A : Cube n → ℝ := fun x => 1 - (pairMean g x) ^ 2
  let H : Cube n → ℝ := fun x =>
    (entropy (pairMean g x + pairHalfDifference g x) +
      entropy (pairMean g x - pairHalfDifference g x)) / 2
  have hA : ∀ x, 0 < A x := fun x =>
    scalar_meanVariance_pos (abs_lt.mpr (hg.pairMean x))
  have hH : ∀ x, 0 < H x := by
    intro x
    dsimp [H]
    rw [pairMean_add_halfDifference, pairMean_sub_halfDifference]
    exact div_pos (add_pos (entropy_pos (hg.restrict true x))
      (entropy_pos (hg.restrict false x))) (by norm_num)
  have hHavg : cubeAverage H = entropyAverage g := by
    dsimp [H]
    simp only [pairMean_add_halfDifference, pairMean_sub_halfDifference]
    rw [cubeAverage_half_sum]
    exact (entropyAverage_split g).symm
  have hJ := cubeAverage_perspective_jensen L hconvex A H hA hH
  rw [hHavg] at hJ
  have hpoint := cubeAverage_mono (fun x => hpair _ _ (hg.pairDomain x))
  have hcombined := hJ.trans hpoint
  simpa only [A, cubeAverage_sub, cubeAverage_smul] using hcombined

theorem restricted_monotone_dissipation_lower
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    {n : ℕ} (g : Cube (n + 1) → ℝ) (hg : IsInterior g)
    (htrue : 2 * informationDeficit (restrict g true) +
      meanVariance (restrict g true) *
        L (entropyAverage (restrict g true) / meanVariance (restrict g true)) ≤
      dissipation (restrict g true))
    (hfalse : 2 * informationDeficit (restrict g false) +
      meanVariance (restrict g false) *
        L (entropyAverage (restrict g false) / meanVariance (restrict g false)) ≤
      dissipation (restrict g false)) :
    2 * (informationDeficit g - pairEntropyGap (cubeAverage (pairMean g))
        (cubeAverage (pairHalfDifference g))) +
      (meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2) *
        L (entropyAverage g / (meanVariance g - (cubeAverage (pairHalfDifference g)) ^ 2)) ≤
      (dissipation (restrict g true) + dissipation (restrict g false)) / 2 := by
  have hJ := two_point_perspective_jensen L hconvex
    (hg.restrict false).meanVariance_pos (hg.restrict true).meanVariance_pos
    (hg.restrict false).entropyAverage_pos (hg.restrict true).entropyAverage_pos
  rw [meanVariance_split, ← entropyAverage_split g] at hJ
  have hS := informationDeficit_split g
  linarith

theorem monotone_dissipation_from_scalar_lemmas
    (hconvex : ConvexOn ℝ (Ioi 0) L)
    (hpair : ∀ a b : ℝ, |a| + |b| < 1 →
      (1 - a ^ 2) * L (((entropy (a + b) + entropy (a - b)) / 2) / (1 - a ^ 2)) ≤
        pairDissipation a b - 2 * pairEntropyGap a b)
    (hperspective : ∀ x w q : ℝ, 0 < x → 0 < w → w ≤ 1 → 0 ≤ q → q < 1 → q ≤ w ^ 2 →
      L x - (1 - q) * L (x / (1 - q)) - w * L (x / w) ≤
        q * (1 / w - 1) * lambda (q ^ 2)) :
    ∀ {n : ℕ} (g : Cube n → ℝ), IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g := by
  intro n
  induction n with
  | zero =>
      intro g hg _
      exact monotone_dissipation_zero g hg
  | succ n ih =>
      intro g hg hmono
      let a := pairMean g
      let b := pairHalfDifference g
      have hdom : ∀ x, |a x| + |b x| < 1 := hg.pairDomain
      have hb : ∀ x, 0 ≤ b x := hmono.pairHalfDifference_nonneg
      obtain ⟨hm, hk, hkm, hW, hWA, hkW⟩ := monotone_pair_average_geometry a b hdom hb
      have htrue := ih (restrict g true) (hg.restrict true) (hmono.restrict true)
      have hfalse := ih (restrict g false) (hg.restrict false) (hmono.restrict false)
      have hrestr := restricted_monotone_dissipation_lower hconvex g hg htrue hfalse
      have hrestr' :
          2 * (informationDeficit g - pairEntropyGap (cubeAverage a) (cubeAverage b)) +
          (1 - (cubeAverage a) ^ 2 - (cubeAverage b) ^ 2) *
            L (entropyAverage g / (1 - (cubeAverage a) ^ 2 - (cubeAverage b) ^ 2)) ≤
          (dissipation (restrict g true) + dissipation (restrict g false)) / 2 := by
        simpa only [a, b, meanVariance, cubeAverage_pairMean] using hrestr
      have hnorm := averaged_normalized_pair_of_pointwise hconvex hpair g hg
      have hgap := pair_jensen_gap_strengthened a b hdom hb
      have hV := pair_variance_gap_lower_bound a b hdom
      obtain ⟨hq, hq1, hw, hw1, hqw⟩ :=
        monotone_split_parameter_bounds hm hk hkm hW hWA hkW
      have hx : 0 < entropyAverage g / (1 - (cubeAverage a) ^ 2) :=
        div_pos hg.entropyAverage_pos (scalar_meanVariance_pos hm)
      have hp := hperspective _ _ _ hx hw hw1 hq hq1 hqw
      have hfinal := monotone_dissipation_step_of_perspective hm hk hkm hW hWA hkW
        hV hrestr' hnorm hgap hp
      rw [dissipation_split g]
      simpa only [a, b, meanVariance, cubeAverage_pairMean] using hfinal

theorem monotone_dissipation {n : ℕ} (g : Cube n → ℝ)
    (hg : IsInterior g) (hmono : IsIncreasing g) :
    2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
      dissipation g := by
  exact monotone_dissipation_from_scalar_lemmas convexOn_L
    (fun _ _ hab => normalized_pair_bound hab) perspective_inequality g hg hmono

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

open Set

namespace LeanBlast.CourtadeKumar

theorem function_increment_le_of_lipschitz_deriv
    (F : ℝ → ℝ) (C : ℝ)
    (hcont : ContinuousOn F (Ici 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ F x)
    (hlip : ∀ x y : ℝ, 0 < x → 0 < y →
      |deriv F x - deriv F y| ≤ C * |x - y|)
    (hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ F x)
    {Je Jm Sa : ℝ} (hJm : 0 ≤ Jm) (hJe : Jm ≤ Je) (hSa : 0 ≤ Sa) :
    F (Je + Sa) - F (Je + Sa - Jm) ≤ F Je + C * Jm * Sa := by
  let G : ℝ → ℝ := fun t => F (Je + t) - F (Je - Jm + t)
  have hJe0 : 0 ≤ Je := hJm.trans hJe
  have hbase : 0 ≤ Je - Jm := sub_nonneg.mpr hJe
  have hGcont : ContinuousOn G (Ici 0) := by
    apply ContinuousOn.sub
    · exact hcont.comp (continuous_const.add continuous_id).continuousOn
        (fun t ht => add_nonneg hJe0 ht)
    · exact hcont.comp (continuous_const.add continuous_id).continuousOn
        (fun t ht => add_nonneg hbase ht)
  have hGderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt G (deriv F (Je + t) - deriv F (Je - Jm + t)) t := by
    intro t ht
    exact ((hdiff (Je + t) (add_pos_of_nonneg_of_pos hJe0 ht)).hasDerivAt.comp_const_add Je t).sub
      ((hdiff (Je - Jm + t) (add_pos_of_nonneg_of_pos hbase ht)).hasDerivAt.comp_const_add
        (Je - Jm) t)
  have hGdiff : DifferentiableOn ℝ G (interior (Ici 0)) := by
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (hGderiv t ht0).differentiableAt.differentiableWithinAt
  have hGbound : ∀ t ∈ interior (Ici 0), deriv G t ≤ C * Jm := by
    intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(hGderiv t ht0).deriv]
    calc
      _ ≤ |deriv F (Je + t) - deriv F (Je - Jm + t)| := le_abs_self _
      _ ≤ C * |(Je + t) - (Je - Jm + t)| :=
        hlip _ _ (add_pos_of_nonneg_of_pos hJe0 ht0) (add_pos_of_nonneg_of_pos hbase ht0)
      _ = C * Jm := by rw [show (Je + t) - (Je - Jm + t) = Jm by ring, abs_of_nonneg hJm]
  have hstep := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    hGcont hGdiff hGbound 0 (by simp) Sa hSa hSa
  simp only [G, add_zero, sub_zero] at hstep
  rw [show Je - Jm + Sa = Je + Sa - Jm by ring] at hstep
  linarith [hnonneg (Je - Jm) hbase]

theorem general_dissipation_step_algebra (F : ℝ → ℝ)
    {S Je Jm Sa V Drestr Dpair : ℝ}
    (hrestr : 2 * (S - Jm) + F (S - Jm) ≤ Drestr)
    (hpair : F Je + V ≤ Dpair - 2 * Jm)
    (hvariance : Jm * Sa / ell ≤ V)
    (hincrement : F S - F (S - Jm) ≤ F Je + Jm * Sa / ell) :
    2 * S + F S ≤ Drestr + Dpair := by
  linarith

theorem restriction_bound_of_convex (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ici 0) F) {S₁ S₀ D₁ D₀ : ℝ}
    (hS₁ : 0 ≤ S₁) (hS₀ : 0 ≤ S₀)
    (hD₁ : 2 * S₁ + F S₁ ≤ D₁) (hD₀ : 2 * S₀ + F S₀ ≤ D₀) :
    2 * ((S₁ + S₀) / 2) + F ((S₁ + S₀) / 2) ≤ (D₁ + D₀) / 2 := by
  have hmid := hF.2 hS₁ hS₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hmid
  rw [show (1 / 2 : ℝ) * S₁ + (1 / 2 : ℝ) * S₀ = (S₁ + S₀) / 2 by ring] at hmid
  linarith

theorem averaged_remainder_bound {n : ℕ} (F : ℝ → ℝ)
    (hF : ConvexOn ℝ (Ici 0) F) (J d : Cube n → ℝ)
    (hJ : ∀ x, 0 ≤ J x) (hpoint : ∀ x, F (J x) ≤ d x - 2 * J x)
    {Jm V : ℝ} (hgap : V ≤ 2 * (cubeAverage J - Jm)) :
    F (cubeAverage J) + V ≤ cubeAverage d - 2 * Jm := by
  have havg : cubeAverage (fun x => F (J x)) ≤ cubeAverage (fun x => d x - 2 * J x) := by
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hpoint x)) (by positivity)
  have hidentity : cubeAverage (fun x => d x - 2 * J x) =
      cubeAverage d - 2 * cubeAverage J := by
    simp [cubeAverage, Finset.sum_sub_distrib, ← Finset.mul_sum, sub_div, mul_div_assoc]
  rw [hidentity] at havg
  have hjensen := convexOn_cubeAverage_le F hF J hJ
  linarith

theorem general_dissipation_of_K_estimates
    (hconvex : ConvexOn ℝ (Ici 0) K)
    (hincrement : ∀ {Je Jm Sa : ℝ}, 0 ≤ Jm → Jm ≤ Je → 0 ≤ Sa →
      K (Je + Sa) - K (Je + Sa - Jm) ≤ K Je + Jm * Sa / ell)
    (hpoint : ∀ (a b : ℝ), |a| + |b| < 1 →
      K (pairEntropyGap a b) ≤ pairDissipation a b - 2 * pairEntropyGap a b) :
    ∀ {n : ℕ} (g : Cube n → ℝ), IsInterior g →
      2 * informationDeficit g + K (informationDeficit g) ≤ dissipation g := by
  intro n
  induction n with
  | zero =>
      intro g _
      simp
  | succ n ih =>
      intro g hg
      let a := pairMean g
      let b := pairHalfDifference g
      let J := fun x => pairEntropyGap (a x) (b x)
      let Je := cubeAverage J
      let Jm := pairEntropyGap (cubeAverage a) (cubeAverage b)
      let Sa := informationDeficit a
      let V := cubeAverage (fun x => (b x) ^ 2 / (1 - (a x) ^ 2)) -
        (cubeAverage b) ^ 2 / (1 - (cubeAverage a) ^ 2)
      have hdom : ∀ x, |a x| + |b x| < 1 := hg.pairDomain
      have hSa : 0 ≤ Sa := informationDeficit_nonneg hg.pairMean
      have hJm : 0 ≤ Jm := pairEntropyGap_nonneg _ _ (cubeAverage_pairDomain hdom)
      have hJmJe : Jm ≤ Je := pair_jensen_gap_nonneg a b hdom
      have hrestr := restriction_bound_of_convex K hconvex
        (informationDeficit_nonneg (hg.restrict true))
        (informationDeficit_nonneg (hg.restrict false))
        (ih (restrict g true) (hg.restrict true))
        (ih (restrict g false) (hg.restrict false))
      rw [informationDeficit_split] at hrestr
      have hpairavg : K Je + V ≤
          cubeAverage (fun x => pairDissipation (a x) (b x)) - 2 * Jm :=
        averaged_remainder_bound K hconvex J (fun x => pairDissipation (a x) (b x))
          (fun x => pairEntropyGap_nonneg _ _ (hdom x))
          (fun x => hpoint _ _ (hdom x)) (pair_jensen_gap a b hdom)
      have hvariance : Jm * Sa / ell ≤ V := entropy_product_le_variance_gap a b hdom
      have hinc := hincrement hJm hJmJe hSa
      have hS : informationDeficit g = Je + Sa := by
        dsimp only [Je, J, Sa, a, b]
        rw [informationDeficit_eq_pairMean_add]
        ring
      rw [← hS] at hinc
      have htotal := general_dissipation_step_algebra K hrestr hpairavg hvariance hinc
      rw [dissipation_split]
      exact htotal

theorem K_increment {Je Jm Sa : ℝ}
    (hJm : 0 ≤ Jm) (hJe : Jm ≤ Je) (hSa : 0 ≤ Sa) :
    K (Je + Sa) - K (Je + Sa - Jm) ≤ K Je + Jm * Sa / ell := by
  have h := function_increment_le_of_lipschitz_deriv K (1 / ell) continuousOn_K
    (fun x hx => (hasDerivAt_K hx.le).differentiableAt)
    (fun x y hx hy => by
      rw [(hasDerivAt_K hx.le).deriv, (hasDerivAt_K hy.le).deriv]
      exact KDeriv_lipschitz x y)
    (fun x _ => K_nonneg x) hJm hJe hSa
  calc
    _ ≤ K Je + (1 / ell) * Jm * Sa := h
    _ = K Je + Jm * Sa / ell := by ring

theorem general_dissipation {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    2 * informationDeficit g + K (informationDeficit g) ≤ dissipation g := by
  apply general_dissipation_of_K_estimates convexOn_K K_increment ?_ g hg
  intro a b hdom
  exact (K_le_rGap (pairEntropyGap_nonneg a b hdom) (pairEntropyGap_lt_ell a b hdom)).trans
    (rGap_pairEntropyGap_le a b hdom)

theorem small_information_dissipation {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g)
    (hS : informationDeficit g ≤ s0) : r (informationDeficit g) ≤ dissipation g := by
  have h := general_dissipation g hg
  rw [K_eq_rGap_nonneg (informationDeficit_nonneg hg) hS, rGap] at h
  linarith

end LeanBlast.CourtadeKumar

end OAI
end

section
namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem le_add_initial_gap_of_deriv_le_on_above
    {f g f' g' : ℝ → ℝ} {a b δ : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Ico a b, g t ≤ f t → f' t ≤ g' t)
    (hδ : 0 ≤ δ) (ha : f a ≤ g a + δ) :
    ∀ t ∈ Icc a b, f t ≤ g t + δ := by
  have hfcont : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (Icc a b) :=
    fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hpert : ∀ t ∈ Icc a b, ∀ ε > 0,
      f t ≤ g t + δ + ε * (t - a) := by
    intro t ht ε hε
    apply image_le_of_deriv_right_lt_deriv_boundary' hfcont
      (fun x hx => (hf x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt)
      (B := fun x => g x + δ + ε * (x - a))
      (B' := fun x => g' x + ε)
    · simpa using ha
    · exact (hgcont.add continuousOn_const).add
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    · intro x hx
      convert! (((hg x ⟨hx.1, hx.2.le⟩).add_const δ).add
        (((hasDerivAt_id x).sub_const a).const_mul ε)).hasDerivWithinAt using 1
      simp
    · intro x hx heq
      have hnonneg : 0 ≤ ε * (x - a) := mul_nonneg hε.le (sub_nonneg.mpr hx.1)
      have hgf : g x ≤ f x := by rw [heq]; linarith
      have hd := hderiv x hx hgf
      linarith
    · exact ht
  intro t ht
  have hc : ContinuousWithinAt (fun ε : ℝ => g t + δ + ε * (t - a)) (Ioi 0) 0 := by
    fun_prop
  convert continuousWithinAt_const.closure_le _ hc (hpert t ht) using 1 <;>
    first | with_reducible_and_instances rfl | simp

theorem le_of_deriv_le_on_above
    {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Ico a b, g t ≤ f t → f' t ≤ g' t)
    (ha : f a ≤ g a) : ∀ t ∈ Icc a b, f t ≤ g t := by
  simpa only [add_zero] using
    le_add_initial_gap_of_deriv_le_on_above hf hg hderiv (δ := 0) le_rfl (by simpa using ha)

theorem le_of_deriv_le_on_above_of_tendsto
    {f g f' g' : ℝ → ℝ} {l : ℝ}
    (hf : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hg : ∀ t, 0 < t → HasDerivAt g (g' t) t)
    (hderiv : ∀ t, 0 < t → g t ≤ f t → f' t ≤ g' t)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 l))
    (hg0 : Tendsto g (𝓝[>] 0) (𝓝 l)) :
    ∀ t, 0 < t → f t ≤ g t := by
  intro t ht
  have hlim : Tendsto (fun a => g t + max (f a - g a) 0) (𝓝[>] 0) (𝓝 (g t)) := by
    convert tendsto_const_nhds.add ((hf0.sub hg0).max tendsto_const_nhds) using 1
    simp
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  apply le_add_initial_gap_of_deriv_le_on_above
    (fun x hx => hf x (ha.1.trans_le hx.1))
    (fun x hx => hg x (ha.1.trans_le hx.1))
    (fun x hx => hderiv x (ha.1.trans_le hx.1))
    (le_max_right (f a - g a) 0)
  · have hgmax := le_max_left (f a - g a) 0
    linarith
  · exact ⟨ha.2.le, le_rfl⟩

def comparisonKernel (s : ℝ) : ℝ := 1 / (s ^ 2 * Real.artanh s)

def comparisonV (u : ℝ) : ℝ :=
  2 * u * Real.artanh u * ∫ s in u..1, comparisonKernel s

def comparisonVTime (t : ℝ) : ℝ := comparisonV (Real.exp (-t))

theorem measurable_comparisonKernel : Measurable comparisonKernel := by
  unfold comparisonKernel Real.artanh
  fun_prop

theorem comparisonKernel_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ comparisonKernel s := by
  exact one_div_nonneg.mpr (mul_nonneg (sq_nonneg s) (Real.artanh_nonneg hs))

@[simp] theorem comparisonKernel_one : comparisonKernel 1 = 0 := by
  norm_num [comparisonKernel, Real.artanh]

theorem comparisonKernel_le {u s : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hus : u ≤ s) (hs1 : s ≤ 1) : comparisonKernel s ≤ comparisonKernel u := by
  by_cases hs : s = 1
  · subst s
    simpa using comparisonKernel_nonneg hu.le
  · have hslt : s < 1 := lt_of_le_of_ne hs1 hs
    apply one_div_le_one_div_of_le
      (mul_pos (sq_pos_of_pos hu) (Real.artanh_pos ⟨hu, hu1⟩))
    exact mul_le_mul (sq_le_sq₀ hu.le (hu.le.trans hus) |>.mpr hus)
      (Real.artanh_le_artanh (by linarith) hslt hus)
      (Real.artanh_nonneg hu.le) (sq_nonneg s)

theorem intervalIntegrable_comparisonKernel {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    IntervalIntegrable comparisonKernel volume u 1 := by
  apply (intervalIntegrable_const (c := comparisonKernel u)).mono_fun'
    measurable_comparisonKernel.aestronglyMeasurable
  rw [uIoc_of_le hu1.le]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (comparisonKernel_nonneg (hu.le.trans hs.1.le))]
  exact comparisonKernel_le hu hu1 hs.1.le hs.2

theorem continuousAt_comparisonKernel {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ContinuousAt comparisonKernel u := by
  exact continuousAt_const.div
    ((continuousAt_id.pow 2).mul (hasDerivAt_artanh ⟨by linarith, hu1⟩).continuousAt)
    (mul_ne_zero (pow_ne_zero 2 hu.ne') (ne_of_gt (Real.artanh_pos ⟨hu, hu1⟩)))

theorem comparisonV_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ comparisonV u := by
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) hu) (Real.artanh_nonneg hu)
  · exact intervalIntegral.integral_nonneg hu1 fun s hs =>
      comparisonKernel_nonneg (hu.trans hs.1)

theorem comparisonV_le_endpoint_bound {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    comparisonV u ≤ 2 * (1 - u) / u := by
  have hI : (∫ s in u..1, comparisonKernel s) ≤ (1 - u) * comparisonKernel u := by
    calc
      _ ≤ ∫ _s in u..1, comparisonKernel u :=
        intervalIntegral.integral_mono_on hu1.le (intervalIntegrable_comparisonKernel hu hu1)
          intervalIntegrable_const (fun s hs => comparisonKernel_le hu hu1 hs.1 hs.2)
      _ = _ := by simp
  unfold comparisonV
  calc
    _ ≤ 2 * u * Real.artanh u * ((1 - u) * comparisonKernel u) :=
      mul_le_mul_of_nonneg_left hI
        (mul_nonneg (mul_nonneg (by norm_num) hu.le) (Real.artanh_nonneg hu.le))
    _ = 2 * (1 - u) / u := by
      unfold comparisonKernel
      field_simp [hu.ne', (Real.artanh_pos ⟨hu, hu1⟩).ne']

theorem tendsto_comparisonVTime_zero :
    Tendsto comparisonVTime (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hbound : Tendsto (fun t : ℝ => 2 * (1 - Real.exp (-t)) / Real.exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    convert ((tendsto_const_nhds (x := (2 : ℝ))).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hu)).div hu (by norm_num) using 1 <;>
      first | rfl | norm_num
  apply squeeze_zero' _ _ hbound
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact comparisonV_nonneg (Real.exp_pos _).le (le_of_lt (Real.exp_lt_one_iff.mpr (by linarith)))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact comparisonV_le_endpoint_bound (Real.exp_pos _) (Real.exp_lt_one_iff.mpr (by linarith))

theorem hasDerivAt_comparisonV {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    HasDerivAt comparisonV
      (2 * (Real.artanh u + u / (1 - u ^ 2)) *
        (∫ s in u..1, comparisonKernel s) - 2 / u) u := by
  have hI := intervalIntegral.integral_hasDerivAt_left
    (intervalIntegrable_comparisonKernel hu hu1)
    measurable_comparisonKernel.stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_comparisonKernel hu hu1)
  have hprod := (((hasDerivAt_id u).const_mul 2).mul
    (hasDerivAt_artanh ⟨by linarith, hu1⟩)).mul hI
  convert! hprod using 1
  simp only [id_eq, Pi.mul_apply]
  unfold comparisonKernel
  field_simp [hu.ne', (Real.artanh_pos ⟨hu, hu1⟩).ne']
  ring

theorem hasDerivAt_comparisonVTime {t : ℝ} (ht : 0 < t) :
    let u := Real.exp (-t)
    HasDerivAt comparisonVTime
      (2 - (1 + u / ((1 - u ^ 2) * Real.artanh u)) * comparisonVTime t) t := by
  dsimp only
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hderiv := (hasDerivAt_comparisonV hu hu1).comp t (hasDerivAt_id t).neg.exp
  convert! hderiv using 1
  simp only [id_eq, Pi.neg_apply]
  unfold comparisonVTime comparisonV
  have hden : 1 - Real.exp (-t) ^ 2 ≠ 0 := by nlinarith
  field_simp [hu.ne', (Real.artanh_pos ⟨hu, hu1⟩).ne', hden]
  ring

private theorem sq_lt_one_of_mem {u : ℝ} (hu : u ∈ Ioo (-1) 1) : u ^ 2 < 1 := by
  have hp : 0 < (1 - u) * (u + 1) := mul_pos (by linarith [hu.2]) (by linarith [hu.1])
  nlinarith

private theorem hasDerivAt_artanh_cubic_gap {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt (fun x : ℝ => Real.artanh x - x - x ^ 3 / 3)
      (u ^ 4 / (1 - u ^ 2)) u := by
  have hden : 1 - u ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr (sq_lt_one_of_mem hu))
  convert! ((hasDerivAt_artanh hu).sub (hasDerivAt_id u)).sub
    (((hasDerivAt_id u).pow 3).div_const 3) using 1
  simp only [id_eq]
  field_simp [hden]
  ring

theorem artanh_cubic_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    u + u ^ 3 / 3 ≤ Real.artanh u := by
  have hm : MonotoneOn (fun x : ℝ => Real.artanh x - x - x ^ 3 / 3) (Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
    · intro x hx
      exact (hasDerivAt_artanh_cubic_gap ⟨by linarith [hx.1], hx.2⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
      exact (hasDerivAt_artanh_cubic_gap ⟨by linarith [hx'.1], hx'.2⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ico (0 : ℝ) 1 := interior_subset hx
      exact div_nonneg (by positivity)
        (sub_nonneg.mpr (le_of_lt (sq_lt_one_of_mem ⟨by linarith [hx'.1], hx'.2⟩)))
  have h := hm (show (0 : ℝ) ∈ Ico 0 1 by norm_num) ⟨hu, hu1⟩ hu
  simp only [Real.artanh_zero, sub_zero] at h
  linarith

def rationalArtanhGap (u : ℝ) : ℝ := u / (1 - u ^ 2 / 2) - Real.artanh u

theorem hasDerivAt_rationalArtanhGap {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt rationalArtanhGap
      (u ^ 2 * (2 - 3 * u ^ 2) / ((2 - u ^ 2) ^ 2 * (1 - u ^ 2))) u := by
  have hsq := sq_lt_one_of_mem hu
  have hden : 1 - u ^ 2 / 2 ≠ 0 := by nlinarith
  have hden' : 1 - u ^ 2 ≠ 0 := by nlinarith
  have hden'' : 2 - u ^ 2 ≠ 0 := by nlinarith
  have hd := ((hasDerivAt_id u).div
    ((hasDerivAt_const u 1).sub (((hasDerivAt_id u).pow 2).div_const 2)) hden).sub
      (hasDerivAt_artanh hu)
  convert! hd using 1
  simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
  field_simp [hden, hden', hden'']
  ring

theorem artanh_le_rational {u : ℝ} (hu : 0 ≤ u) (hu9 : u ≤ 9 / 10) :
    Real.artanh u ≤ u / (1 - u ^ 2 / 2) := by
  let c : ℝ := Real.sqrt (2 / 3)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hc9 : c < 9 / 10 := by nlinarith
  have hdenpos : ∀ x ∈ Icc (0 : ℝ) (9 / 10),
      0 < (2 - x ^ 2) ^ 2 * (1 - x ^ 2) := by
    intro x hx
    have hsq : x ^ 2 < 1 := sq_lt_one_of_mem ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hleft : MonotoneOn rationalArtanhGap (Icc 0 c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 c)
    · intro x hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) c := interior_subset hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) c := interior_subset hx
      have hsq : x ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hx'.1 hc0).mpr hx'.2
      exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith))
        (hdenpos x ⟨hx'.1, hx'.2.trans hc9.le⟩).le
  have hright : AntitoneOn rationalArtanhGap (Icc c (9 / 10)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c (9 / 10))
    · intro x hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc c (9 / 10 : ℝ) := interior_subset hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc c (9 / 10 : ℝ) := interior_subset hx
      have hx0 : 0 ≤ x := hc0.trans hx'.1
      have hsq : c ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hc0 hx0).mpr hx'.1
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith))
        (hdenpos x ⟨hx0, hx'.2⟩).le
  have hend : 0 ≤ rationalArtanhGap (9 / 10) := by
    have ha : Real.artanh (9 / 10) = Real.log 19 / 2 := by
      rw [Real.artanh_eq_half_log (by norm_num)]
      norm_num
      ring
    unfold rationalArtanhGap
    rw [ha]
    norm_num
    linarith [log_nineteen_lt_three]
  have hgap : 0 ≤ rationalArtanhGap u := by
    by_cases huc : u ≤ c
    · have h := hleft ⟨le_rfl, hc0⟩ ⟨hu, huc⟩ hu
      simpa [rationalArtanhGap] using h
    · exact hend.trans (hright ⟨le_of_not_ge huc, hu9⟩ ⟨hc9.le, le_rfl⟩ hu9)
  exact sub_nonneg.mp hgap

def comparisonModelKernel (s : ℝ) : ℝ := (1 - s ^ 2 / 2) / s ^ 3

def comparisonPrimitive (s : ℝ) : ℝ := -(1 / (2 * s ^ 2)) - Real.log s / 2

theorem comparisonModelKernel_le {s : ℝ} (hs : 0 < s) (hs9 : s ≤ 9 / 10) :
    comparisonModelKernel s ≤ comparisonKernel s := by
  have hs1 : s < 1 := by linarith
  have hsq := sq_lt_one_of_mem (show s ∈ Ioo (-1) 1 from ⟨by linarith, hs1⟩)
  have hnum : 0 < 1 - s ^ 2 / 2 := by linarith
  have ha := (le_div_iff₀ hnum).mp (artanh_le_rational hs.le hs9)
  have hmul := mul_le_mul_of_nonneg_left ha (sq_nonneg s)
  unfold comparisonModelKernel comparisonKernel
  apply (div_le_div_iff₀ (pow_pos hs 3)
    (mul_pos (sq_pos_of_pos hs) (Real.artanh_pos ⟨hs, hs1⟩))).mpr
  nlinarith

theorem hasDerivAt_comparisonPrimitive {s : ℝ} (hs : 0 < s) :
    HasDerivAt comparisonPrimitive (comparisonModelKernel s) s := by
  have hden : 2 * s ^ 2 ≠ 0 := by positivity
  have hd := (((hasDerivAt_const s 1).div
    (((hasDerivAt_id s).pow 2).const_mul 2) hden).neg).sub
      ((Real.hasDerivAt_log hs.ne').div_const 2)
  convert! hd using 1
  simp only [id_eq, Pi.pow_apply]
  unfold comparisonModelKernel
  field_simp [hs.ne']
  ring

theorem continuousAt_comparisonModelKernel {s : ℝ} (hs : 0 < s) :
    ContinuousAt comparisonModelKernel s := by
  unfold comparisonModelKernel
  fun_prop (disch := positivity)

theorem integral_comparisonModelKernel {u : ℝ} (hu : 0 < u) (hu9 : u ≤ 9 / 10) :
    (∫ s in u..(9 / 10), comparisonModelKernel s) =
      (1 - u ^ 2 * comparisonC u) / (2 * u ^ 2) := by
  have hpos : ∀ s ∈ uIcc u (9 / 10), 0 < s := by
    intro s hs
    rw [uIcc_of_le hu9] at hs
    exact hu.trans_le hs.1
  have hint : IntervalIntegrable comparisonModelKernel volume u (9 / 10) :=
    ContinuousOn.intervalIntegrable
      (fun s hs => (continuousAt_comparisonModelKernel (hpos s hs)).continuousWithinAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hasDerivAt_comparisonPrimitive (hpos s hs)) hint]
  unfold comparisonPrimitive comparisonC
  norm_num
  field_simp [hu.ne']
  ring

theorem comparisonV_lower {u : ℝ} (hu : 0 < u) (hu9 : u ≤ 9 / 10) :
    Real.artanh u / u * (1 - u ^ 2 * comparisonC u) ≤ comparisonV u := by
  have hu1 : u < 1 := by linarith
  have hkernel := intervalIntegrable_comparisonKernel hu hu1
  have hkernel9 : IntervalIntegrable comparisonKernel volume u (9 / 10) := by
    apply hkernel.mono_set
    rw [uIcc_of_le hu9, uIcc_of_le hu1.le]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hmodel : IntervalIntegrable comparisonModelKernel volume u (9 / 10) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [uIcc_of_le hu9] at hs
    exact (continuousAt_comparisonModelKernel (hu.trans_le hs.1)).continuousWithinAt
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc u 1)] comparisonKernel := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact comparisonKernel_nonneg (hu.le.trans hs.1.le)
  have hI : (1 - u ^ 2 * comparisonC u) / (2 * u ^ 2) ≤
      ∫ s in u..1, comparisonKernel s := by
    rw [← integral_comparisonModelKernel hu hu9]
    calc
      _ ≤ ∫ s in u..(9 / 10), comparisonKernel s :=
        intervalIntegral.integral_mono_on hu9 hmodel hkernel9
          (fun s hs => comparisonModelKernel_le (hu.trans_le hs.1) hs.2)
      _ ≤ ∫ s in u..1, comparisonKernel s :=
        intervalIntegral.integral_mono_interval le_rfl hu9 (by norm_num) hpos hkernel
  have hm := mul_le_mul_of_nonneg_left hI
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hu.le)
      (Real.artanh_nonneg hu.le))
  convert! hm using 1
  field_simp [hu.ne']

theorem one_sub_comparisonV_le {u : ℝ} (hu0 : 1 / 5 ≤ u) (hu1 : u ≤ 5 / 8) :
    1 - comparisonV u ≤ 5 / 2 * u ^ 2 := by
  have hu : 0 < u := by linarith
  have hu9 : u ≤ 9 / 10 := by linarith
  have hcubic := artanh_cubic_lower hu.le (show u < 1 by linarith)
  have hratio : 1 + u ^ 2 / 3 ≤ Real.artanh u / u := by
    apply (le_div_iff₀ hu).mpr
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hratio
    (comparisonC_integral_bracket_nonneg hu hu9)
  have hlow := comparisonV_lower hu hu9
  have hQ := mul_le_mul_of_nonneg_left (comparisonC_middle_bound hu0 hu1) (sq_nonneg u)
  nlinarith

def comparisonBias (m : ℝ) : ℝ := m ^ 2 * ell - psi m

theorem comparisonBias_eq (m : ℝ) :
    entropy m = (1 - m ^ 2) * ell + comparisonBias m := by
  unfold comparisonBias entropy
  ring

theorem comparisonBias_bounds {m : ℝ} (hm : |m| ≤ 1) :
    0 ≤ comparisonBias m ∧ comparisonBias m ≤ m ^ 2 * (ell - 1 / 2) := by
  have hlow := half_sq_le_psi hm
  have hupp := psi_le_ell_mul_sq hm
  unfold comparisonBias
  constructor <;> nlinarith

def comparisonLower (A B t : ℝ) : ℝ :=
  A * entropy (Real.exp (-t)) + B * comparisonVTime t

theorem hasDerivAt_entropy_exp_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ => entropy (Real.exp (-z)))
      (Real.exp (-t) * Real.artanh (Real.exp (-t))) t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  convert! (hasDerivAt_entropy ⟨by linarith, hu1⟩).comp t (hasDerivAt_id t).neg.exp using 1
  simp only [id_eq, Pi.neg_apply]
  ring

theorem hasDerivAt_comparisonLower (A B : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (comparisonLower A B)
      (A * r (psi (Real.exp (-t))) +
        B * (2 - rDeriv (psi (Real.exp (-t))) * comparisonVTime t)) t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [r_psi ⟨by linarith, hu1⟩, rDeriv_psi ⟨hu, hu1⟩]
  exact
    ((hasDerivAt_entropy_exp_neg ht).const_mul A).add ((hasDerivAt_comparisonVTime ht).const_mul B)

theorem comparisonLower_pos {A B t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (ht : 0 < t) :
    0 < comparisonLower A B t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact add_pos_of_pos_of_nonneg
    (mul_pos hA (entropy_pos ⟨by linarith, hu1⟩))
    (mul_nonneg hB (comparisonV_nonneg hu.le hu1.le))

theorem tendsto_comparisonLower_zero (A B : ℝ) :
    Tendsto (comparisonLower A B) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
    simpa using (h.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun t : ℝ => entropy (Real.exp (-t))) (𝓝[>] 0) (𝓝 0) := by
    convert! (continuous_entropy.tendsto 1).comp hu using 1
    simp
  convert! (tendsto_const_nhds.mul hh).add
    (tendsto_const_nhds.mul tendsto_comparisonVTime_zero) using 1
  simp

theorem comparisonLower_subsolution
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {A B H t : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hH : H = A * ell + B) (ht : 0 < t) :
    A * r (psi (Real.exp (-t))) +
        B * (2 - rDeriv (psi (Real.exp (-t))) * comparisonVTime t) ≤
      2 * (H - comparisonLower A B t) + A * L (comparisonLower A B t / A) := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hHu : 0 < entropy (Real.exp (-t)) := entropy_pos ⟨by linarith, hu1⟩
  have hlowpos := comparisonLower_pos hA hB ht
  have htangent := hLsupport _ hHu _ (div_pos hlowpos hA)
  have hscaled : A * L (entropy (Real.exp (-t))) +
      LDeriv (entropy (Real.exp (-t))) * (B * comparisonVTime t) ≤
        A * L (comparisonLower A B t / A) := by
    calc
      _ = A * (L (entropy (Real.exp (-t))) +
          LDeriv (entropy (Real.exp (-t))) *
            (comparisonLower A B t / A - entropy (Real.exp (-t)))) := by
              unfold comparisonLower
              field_simp [hA.ne']
              ring
      _ ≤ _ := mul_le_mul_of_nonneg_left htangent hA.le
  rw [L_entropy ⟨by linarith, hu1⟩, LDeriv_entropy ⟨hu, hu1⟩] at hscaled
  rw [hH]
  unfold comparisonLower entropy at hscaled ⊢
  nlinarith [hscaled]

theorem comparison_rhs_antitone (hLmono : AntitoneOn L (Ioi 0))
    {A : ℝ} (hA : 0 < A) (H : ℝ) :
    AntitoneOn (fun x => 2 * (H - x) + A * L (x / A)) (Ioi 0) := by
  intro x hx y hy hxy
  have hL := hLmono (div_pos hx hA) (div_pos hy hA) ((div_le_div_iff_of_pos_right hA).mpr hxy)
  exact add_le_add (by linarith) (mul_le_mul_of_nonneg_left hL hA.le)

theorem comparisonLower_le_of_differential_inequality
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {A B H : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hH : H = A * ell + B)
    (h h' : ℝ → ℝ) (hpos : ∀ t, 0 < t → 0 < h t)
    (hderiv : ∀ t, 0 < t → HasDerivAt h (h' t) t)
    (hdiff : ∀ t, 0 < t → 2 * (H - h t) + A * L (h t / A) ≤ h' t)
    (hinit : Tendsto h (𝓝[>] 0) (𝓝 0)) :
    ∀ t, 0 < t → comparisonLower A B t ≤ h t := by
  apply le_of_deriv_le_on_above_of_tendsto
    (fun t ht => hasDerivAt_comparisonLower A B ht) hderiv
    _ (tendsto_comparisonLower_zero A B) hinit
  intro t ht horder
  exact (comparisonLower_subsolution hLsupport hA hB hH ht).trans
    (((comparison_rhs_antitone hLmono hA H) (hpos t ht)
      (comparisonLower_pos hA hB ht) horder).trans (hdiff t ht))

theorem hasDerivAt_psi_exp_neg {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ => psi (Real.exp (-z)))
      (-r (psi (Real.exp (-t)))) t := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  rw [r_psi ⟨by linarith, hu1⟩]
  convert! (hasDerivAt_psi ⟨by linarith, hu1⟩).comp t (hasDerivAt_id t).neg.exp using 1
  simp only [id_eq, Pi.neg_apply]
  ring

theorem small_information_comparison
    (hrmono : MonotoneOn r (Ico 0 ell))
    (S S' : ℝ → ℝ) {t0 : ℝ} (ht0 : 0 < t0)
    (hderiv : ∀ t, t0 ≤ t → HasDerivAt S (S' t) t)
    (hrange : ∀ t, t0 ≤ t → S t ∈ Ico 0 ell)
    (hdecay : ∀ t, t0 ≤ t → S' t ≤ -r (S t))
    (hstart : S t0 ≤ psi (Real.exp (-t0))) :
    ∀ t, t0 ≤ t → S t ≤ psi (Real.exp (-t)) := by
  intro t htt0
  refine le_of_deriv_le_on_above (a := t0) (b := t)
    (fun z hz => hderiv z hz.1)
    (fun z hz => hasDerivAt_psi_exp_neg (ht0.trans_le hz.1))
    ?_ hstart t ⟨htt0, le_rfl⟩
  intro z hz hcross
  have hz0 : 0 < z := ht0.trans_le hz.1
  have hu := Real.exp_pos (-z)
  have hu1 : Real.exp (-z) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpsi : psi (Real.exp (-z)) ∈ Ico 0 ell :=
    ⟨psi_nonneg _, psi_lt_ell ⟨by linarith, hu1⟩⟩
  exact (hdecay z hz.1).trans (neg_le_neg (hrmono hpsi (hrange z hz.1) hcross))

theorem noiseFlow_comparison_lower_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) :
    ∀ t, 0 < t →
      comparisonLower (1 - (cubeAverage F) ^ 2) (comparisonBias (cubeAverage F)) t ≤
        entropyAverage (noiseFlow F t) := by
  have hm : |cubeAverage F| ≤ 1 :=
    (abs_lt.mpr (cubeAverage_mem_Ioo_of_signValued_nonconstant hF hnc)).le
  have hA : 0 < 1 - (cubeAverage F) ^ 2 :=
    meanVariance_pos_of_signValued_nonconstant hF hnc
  apply comparisonLower_le_of_differential_inequality hLmono hLsupport hA
    (comparisonBias_bounds hm).1 (comparisonBias_eq (cubeAverage F))
    (fun t => entropyAverage (noiseFlow F t)) (fun t => dissipation (noiseFlow F t))
    (fun t ht => entropyAverage_noiseFlow_pos F hF hnc ht)
    (fun t ht => hasDerivAt_entropyAverage_noiseFlow F hF hnc ht)
    _ (tendsto_entropyAverage_noiseFlow_zero_right F hF)
  intro t ht
  simpa only [informationDeficit, meanVariance, cubeAverage_noiseFlow] using
    hmonoD (noiseFlow F t) (isInterior_noiseFlow F hF hnc ht) (isIncreasing_noiseFlow F hinc ht.le)

theorem informationDeficit_noiseFlow_le_comparison_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t) :
    informationDeficit (noiseFlow F t) ≤
      (1 - (cubeAverage F) ^ 2) * psi (Real.exp (-t)) +
        comparisonBias (cubeAverage F) * (1 - comparisonVTime t) := by
  have hlow := noiseFlow_comparison_lower_from_dissipation
    hLmono hLsupport hmonoD F hF hinc hnc t ht
  calc
    informationDeficit (noiseFlow F t) =
        entropy (cubeAverage F) - entropyAverage (noiseFlow F t) := by
      simp only [informationDeficit, cubeAverage_noiseFlow]
    _ ≤ entropy (cubeAverage F) -
        comparisonLower (1 - (cubeAverage F) ^ 2) (comparisonBias (cubeAverage F)) t :=
      sub_le_sub_left hlow _
    _ = _ := by
      rw [comparisonBias_eq (cubeAverage F)]
      unfold comparisonLower entropy
      ring

theorem informationDeficit_noiseFlow_le_psi_large_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t)
    (hu0 : 1 / 5 ≤ Real.exp (-t)) :
    informationDeficit (noiseFlow F t) ≤ psi (Real.exp (-t)) := by
  have hu := Real.exp_pos (-t)
  have hu1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hm : |cubeAverage F| ≤ 1 :=
    (abs_lt.mpr (cubeAverage_mem_Ioo_of_signValued_nonconstant hF hnc)).le
  have hB := comparisonBias_bounds hm
  have hP := half_sq_le_psi (show |Real.exp (-t)| ≤ 1 by rw [abs_of_pos hu]; exact hu1.le)
  have hS := informationDeficit_noiseFlow_le_comparison_from_dissipation
    hLmono hLsupport hmonoD F hF hinc hnc ht
  by_cases hlarge : 5 / 8 ≤ Real.exp (-t)
  · exact comparison_large_regime (cubeAverage F) (Real.exp (-t))
      (comparisonBias (cubeAverage F)) (psi (Real.exp (-t)))
      (informationDeficit (noiseFlow F t)) (comparisonVTime t)
      hB.1 hB.2 hP hS hlarge (comparisonV_nonneg hu.le hu1.le)
  · apply comparison_middle_regime (cubeAverage F) (Real.exp (-t))
      (comparisonBias (cubeAverage F)) (psi (Real.exp (-t)))
      (informationDeficit (noiseFlow F t)) (comparisonVTime t)
      hB.1 hB.2 hP hS
    exact one_sub_comparisonV_le hu0 (le_of_not_ge hlarge)

theorem dissipation_nonneg {n : ℕ} (g : Cube n → ℝ) (hg : IsInterior g) :
    0 ≤ dissipation g := by
  induction n with
  | zero => simp [dissipation]
  | succ n ih =>
      rw [dissipation_split]
      exact add_nonneg
        (div_nonneg (add_nonneg (ih _ (hg.restrict true)) (ih _ (hg.restrict false)))
          (by norm_num))
        (cubeAverage_nonneg fun x => pairDissipation_nonneg _ _ (hg.pairDomain x))

theorem antitone_informationDeficit_noiseFlow {n : ℕ}
    (F : Cube n → ℝ) (hF : IsSignValued F) (hnc : ∃ x y, F x ≠ F y) :
    AntitoneOn (fun t => informationDeficit (noiseFlow F t)) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (continuous_informationDeficit_noiseFlow F).continuousOn
  · intro t ht
    have ht' : 0 < t := interior_subset ht
    exact (hasDerivAt_informationDeficit_noiseFlow F hF hnc ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := interior_subset ht
    exact neg_nonpos.mpr (dissipation_nonneg _ (isInterior_noiseFlow F hF hnc ht'))

private theorem exp_neg_log_five : Real.exp (-Real.log 5) = (1 / 5 : ℝ) := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem informationDeficit_noiseFlow_le_psi_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    (hrmono : MonotoneOn r (Ico 0 ell))
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (hsmallD : ∀ g : Cube n → ℝ, IsInterior g → informationDeficit g ≤ s0 →
      r (informationDeficit g) ≤ dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) {t : ℝ} (ht : 0 < t) :
    informationDeficit (noiseFlow F t) ≤ psi (Real.exp (-t)) := by
  have hlarge (z : ℝ) (hz : 0 < z) (huz : 1 / 5 ≤ Real.exp (-z)) :
      informationDeficit (noiseFlow F z) ≤ psi (Real.exp (-z)) :=
    informationDeficit_noiseFlow_le_psi_large_from_dissipation
      hLmono hLsupport hmonoD F hF hinc hnc hz huz
  by_cases hu0 : 1 / 5 ≤ Real.exp (-t)
  · exact hlarge t ht hu0
  · have ht0 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have hstart : informationDeficit (noiseFlow F (Real.log 5)) ≤ psi (Real.exp (-Real.log 5)) :=
      hlarge (Real.log 5) ht0 (by rw [exp_neg_log_five])
    have hstart0 : informationDeficit (noiseFlow F (Real.log 5)) ≤ s0 := by
      simpa only [exp_neg_log_five, s0] using hstart
    have hSsmall : ∀ z, Real.log 5 ≤ z → informationDeficit (noiseFlow F z) ≤ s0 := by
      intro z hz
      exact ((antitone_informationDeficit_noiseFlow F hF hnc) ht0 (ht0.trans_le hz) hz).trans hstart0
    have hSrange : ∀ z, Real.log 5 ≤ z → informationDeficit (noiseFlow F z) ∈ Ico 0 ell := by
      intro z hz
      refine ⟨informationDeficit_nonneg (isInterior_noiseFlow F hF hnc (ht0.trans_le hz)), ?_⟩
      exact (hSsmall z hz).trans_lt (psi_lt_ell (by norm_num : (1 / 5 : ℝ) ∈ Ioo (-1) 1))
    have hbound := small_information_comparison hrmono
      (fun z => informationDeficit (noiseFlow F z)) (fun z => -dissipation (noiseFlow F z)) ht0
      (fun z hz => hasDerivAt_informationDeficit_noiseFlow F hF hnc (ht0.trans_le hz))
      hSrange
      (fun z hz => neg_le_neg (hsmallD _ (isInterior_noiseFlow F hF hnc (ht0.trans_le hz))
        (hSsmall z hz))) hstart
    apply hbound t
    have hcomp : Real.exp (-t) ≤ Real.exp (-Real.log 5) := by
      rw [exp_neg_log_five]
      exact le_of_not_ge hu0
    have hcomp' := Real.exp_le_exp.mp hcomp
    linarith

theorem informationDeficit_noise_le_psi_from_dissipation
    (hLmono : AntitoneOn L (Ioi 0))
    (hLsupport : ∀ x, 0 < x → ∀ y, 0 < y → L x + LDeriv x * (y - x) ≤ L y)
    (hrmono : MonotoneOn r (Ico 0 ell))
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (hsmallD : ∀ g : Cube n → ℝ, IsInterior g → informationDeficit g ≤ s0 →
      r (informationDeficit g) ≤ dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  have ht : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu0 hu1)
  simpa only [noiseFlow, neg_neg, Real.exp_log hu0] using
    informationDeficit_noiseFlow_le_psi_from_dissipation hLmono hLsupport hrmono hmonoD hsmallD
      F hF hinc hnc ht

theorem informationDeficit_noise_le_psi_from_sharp_dissipation
    {n : ℕ}
    (hmonoD : ∀ g : Cube n → ℝ, IsInterior g → IsIncreasing g →
      2 * informationDeficit g + meanVariance g * L (entropyAverage g / meanVariance g) ≤
        dissipation g)
    (hsmallD : ∀ g : Cube n → ℝ, IsInterior g → informationDeficit g ≤ s0 →
      r (informationDeficit g) ≤ dissipation g)
    (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  have hrmono : MonotoneOn r (Ico 0 ell) := by
    intro x hx y hy hxy
    have hgap := monotoneOn_rGap hx hy hxy
    unfold rGap at hgap
    linarith
  exact informationDeficit_noise_le_psi_from_dissipation
    antitoneOn_L L_support hrmono hmonoD hsmallD F hF hinc hnc u hu0 hu1

theorem informationDeficit_noise_le_psi_of_increasing
    {n : ℕ} (F : Cube n → ℝ) (hF : IsSignValued F) (hinc : IsIncreasing F)
    (hnc : ∃ x y, F x ≠ F y) (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    informationDeficit (noiseOperator u F) ≤ psi u :=
  informationDeficit_noise_le_psi_from_sharp_dissipation
    (fun g hg hmono => monotone_dissipation g hg hmono)
    (fun g hg hS => small_information_dissipation g hg hS)
    F hF hinc hnc u hu0 hu1

end LeanBlast.CourtadeKumar

end

end OAI
end

section
namespace OAI

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem informationDeficit_noise_le_psi_of_increasing_case {n : ℕ}
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hcase : 0 < u → u < 1 →
      ∀ G : Cube n → ℝ, IsSignValued G → IsIncreasing G →
        (∃ x y, G x ≠ G y) →
          informationDeficit (noiseOperator u G) ≤ psi u)
    (F : Cube n → ℝ) (hF : IsSignValued F) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  classical
  by_cases hu0 : u = 0
  · subst u
    simp
  by_cases hu1 : u = 1
  · subst u
    exact informationDeficit_noise_one_le F hF
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hult : u < 1 := lt_of_le_of_ne hu.2 hu1
  obtain ⟨G, hG, hinc, _, hdom⟩ := exists_increasing_informationDeficit_ge u hu F hF
  apply hdom.trans
  by_cases hnc : ∃ x y, G x ≠ G y
  · exact hcase hupos hult G hG hinc hnc
  · have hconstant : G = fun _ => G (fun _ => false) := by
      funext x
      by_contra hx
      exact hnc ⟨x, (fun _ => false), hx⟩
    rw [hconstant, informationDeficit_noise_const]
    exact psi_nonneg u

theorem informationDeficit_noise_le_psi {n : ℕ}
    (F : Cube n → ℝ) (hF : IsSignValued F)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    informationDeficit (noiseOperator u F) ≤ psi u := by
  apply informationDeficit_noise_le_psi_of_increasing_case u hu _ F hF
  intro hu0 hu1 G hG hinc hnc
  exact informationDeficit_noise_le_psi_of_increasing G hG hinc hnc u hu0 hu1

theorem courtadeKumar_bound {n : ℕ} (ε : ℝ)
    (hε0 : 0 ≤ ε) (hεhalf : ε ≤ (1 : ℝ) / 2) (f : Cube n → Bool) :
    mutualInformation ε f ≤ 1 - binaryEntropy ε := by
  rw [mutualInformation_eq_informationDeficit ε f hε0 hεhalf,
    one_sub_binaryEntropy_eq_psi]
  apply div_le_div_of_nonneg_right _ ell_pos.le
  apply informationDeficit_noise_le_psi (signEncoding f) (isSignValued_signEncoding f)
  constructor <;> linarith

end LeanBlast.CourtadeKumar

end

end OAI
end

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

/-- Relabelling the observation along a bijection preserves the mutual information. -/
theorem mutualInformation_congr {n : ℕ} (f : Cube n → Bool) (p q : ℝ) (e : Cube n ≃ Cube n)
    (h : ∀ b y, jointMass f p b y = jointMass f q b (e y)) :
    mutualInformation f p = mutualInformation f q := by
  unfold mutualInformation entropy
  simp only [h]
  have h1 : ∀ b, (∑ y, jointMass f q b (e y)) = ∑ y, jointMass f q b y :=
    fun b => Equiv.sum_comp e (fun y => jointMass f q b y)
  have h2 : (∑ y, Real.negMulLog (∑ b, jointMass f q b (e y))) =
      ∑ y, Real.negMulLog (∑ b, jointMass f q b y) :=
    Equiv.sum_comp e (fun y => Real.negMulLog (∑ b, jointMass f q b y))
  have h3 : (∑ z : Bool × Cube n, Real.negMulLog (jointMass f q z.1 (e z.2))) =
      ∑ z : Bool × Cube n, Real.negMulLog (jointMass f q z.1 z.2) :=
    Equiv.sum_comp ((Equiv.refl Bool).prodCongr e)
      (fun z : Bool × Cube n => Real.negMulLog (jointMass f q z.1 z.2))
  simp only [h1]
  rw [h2, h3]

/-- Complementing every coordinate of the observation. -/
def flipAll (n : ℕ) : Cube n ≃ Cube n where
  toFun y i := !y i
  invFun y i := !y i
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp

theorem jointMass_one_sub {n : ℕ} (f : Cube n → Bool) (p : ℝ) (b : Bool) (y : Cube n) :
    jointMass f p b y = jointMass f (1 - p) b (flipAll n y) := by
  unfold jointMass
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · unfold noiseKernel
    refine Finset.prod_congr rfl fun i _ => ?_
    show (if x i = y i then 1 - p else p) = if x i = !y i then 1 - (1 - p) else 1 - p
    cases x i <;> cases y i <;> simp
  · rfl

/-- The mutual information is symmetric under `p ↦ 1 - p`. -/
theorem mutualInformation_one_sub {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f p = mutualInformation f (1 - p) :=
  mutualInformation_congr f p (1 - p) (flipAll n) (jointMass_one_sub f p)

theorem H_one_sub (p : ℝ) : H (1 - p) = H p := by
  unfold H
  rw [Real.binEntropy_one_sub]

/-- OpenAI's binary entropy is the published one. -/
theorem H_eq_oai (p : ℝ) : H p = OAI.LeanBlast.CourtadeKumar.binaryEntropy p := by
  rw [OAI.LeanBlast.CourtadeKumar.binaryEntropy_eq_binEntropy]
  rfl

theorem bound_of_le_half {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    mutualInformation f p ≤ 1 - H p := by
  rw [mutualInformation_eq_oai f hp0 hp, H_eq_oai]
  exact OAI.LeanBlast.CourtadeKumar.courtadeKumar_bound p hp0 hp f

theorem generalCourtadeKumar : GeneralCourtadeKumar := by
  intro n f p hp0 hp1
  rcases le_or_gt p (1 / 2) with hp | hp
  · exact bound_of_le_half f hp0 hp
  · rw [mutualInformation_one_sub f p, ← H_one_sub p]
    exact bound_of_le_half f (by linarith) (by linarith)

end GeneralCK.OAIBridge
end

theorem solution : GeneralCK.GeneralCourtadeKumar := by
  exact GeneralCK.OAIBridge.generalCourtadeKumar
