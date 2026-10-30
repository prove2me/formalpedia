-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:41:51.392176+00:00
-- url     : https://prove2.me/submissions/1f6fd5ef-0874-473b-babc-ebc92882ef6c

import Mathlib
import Definitions.Def_OAIQ081S042

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyCharacters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.instDecidableGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Real Walsh characters of the Boolean cube, with unnormalized Fourier sums. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

theorem bitSign_add (a b : ZMod 2) : bitSign (a + b) = bitSign a * bitSign b := by
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, bitSign, eq_self, ite_true, if_true, one_mul]
  by_cases hb : b = 0
  · subst b
    simp only [add_zero, bitSign, eq_self, ite_true, if_true, mul_one]
  have ha1 : a = 1 := by
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hval : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
    have hlt := a.val_lt
    omega
  have hb1 : b = 1 := by
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
    have hlt := b.val_lt
    omega
  have hab : a + b = 0 := by
    rw [ha1, hb1]
    exact CharTwo.add_self_eq_zero 1
  unfold bitSign
  rw [ite_eq_left hab, ite_eq_right ha, ite_eq_right hb]
  norm_num

theorem character_comm {r : ℕ} (a x : Cube r) : character a x = character x a := by
  simp only [character, mul_comm]

theorem character_add_right {r : ℕ} (a x y : Cube r) :
    character a (x + y) = character a x * character a y := by
  simp only [character, Pi.add_apply, mul_add, bitSign_add, Finset.prod_mul_distrib]

theorem character_sum {r : ℕ} (a : Cube r) :
    (∑ x : Cube r, character a x) = if a = 0 then (Fintype.card (Cube r) : ℝ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  · rw [ite_eq_right ha]
    unfold character
    rw [← Fintype.prod_sum (fun j (z : ZMod 2) => bitSign (a j * z))]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hlocal : ∀ b : ZMod 2, b ≠ 0 → (∑ z : ZMod 2, bitSign (b * z)) = 0 := by
      intro b hb
      have hb1 : b = 1 := by
        apply ZMod.val_injective
        rw [ZMod.val_one]
        have hval : b.val ≠ 0 := fun h => hb ((ZMod.val_eq_zero b).mp h)
        have hlt := b.val_lt
        omega
      subst b
      have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
        decide
      rw [hu]
      rw [Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
      rw [one_mul, one_mul, bitSign_zero, bitSign_one]
      norm_num
    exact hlocal (a j) hj

theorem character_orthogonal {r : ℕ} (x y : Cube r) :
    (∑ a : Cube r, character a x * character a y) =
      if x = y then (Fintype.card (Cube r) : ℝ) else 0 := by
  simp_rw [← character_add_right, character_comm _ (x + y)]
  rw [character_sum]
  have heq : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      have := congrArg (fun z : Cube r => z + y) h
      simpa only [add_assoc, cube_add_self, add_zero, zero_add] using this
    · rintro rfl
      exact cube_add_self _
  simp only [heq]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyFourier
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.instDecidableGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

variable {r : ℕ}

theorem fourier_inversion_sum (f : Cube r → ℝ) (x : Cube r) :
    (∑ a, fourier f a * character a x) = (Fintype.card (Cube r) : ℝ) * f x := by
  classical
  simp only [fourier, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, character_orthogonal]
  simp [mul_comm]

theorem fourier_pairing (f g : Cube r → ℝ) :
    (∑ a, fourier f a * fourier g a) =
      (Fintype.card (Cube r) : ℝ) * ∑ x, f x * g x := by
  classical
  conv_lhs => arg 2; ext a; arg 2; unfold fourier
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x, g x * ∑ a, fourier f a * character a x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by simp_rw [fourier_inversion_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem fourier_energy (f : Cube r → ℝ) :
    (∑ a, fourier f a ^ 2) = (Fintype.card (Cube r) : ℝ) * ∑ x, f x ^ 2 := by
  simpa only [pow_two] using fourier_pairing f f

theorem sum_translate (f : Cube r → ℝ) (s : Cube r) :
    (∑ x, f (x + s)) = ∑ x, f x := by
  exact Fintype.sum_equiv (Equiv.addRight s) _ _ (fun _ => rfl)

theorem fourier_translate (f : Cube r → ℝ) (s a : Cube r) :
    fourier (fun x => f (x + s)) a = character a s * fourier f a := by
  classical
  have h := sum_translate (fun x => f (x + s) * character a x) s
  simp only [add_assoc, cube_add_self, add_zero, character_add_right] at h
  rw [fourier, ← h]
  unfold fourier
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem fourier_adjacency {P : Type*} [Fintype P] (shifts : P → Cube r)
    (f : Cube r → ℝ) (a : Cube r) :
    fourier (adjacency shifts f) a = walsh shifts a * fourier f a := by
  classical
  simp only [fourier, adjacency, Finset.sum_mul]
  rw [Finset.sum_comm]
  change (∑ i, fourier (fun x => f (x + shifts i)) a) = _
  simp_rw [fourier_translate]
  rw [← Finset.sum_mul]
  rfl

theorem adjacency_pairing {P : Type*} [Fintype P] (shifts : P → Cube r)
    (f g : Cube r → ℝ) :
    (Fintype.card (Cube r) : ℝ) * ∑ x, f x * adjacency shifts g x =
      ∑ a, walsh shifts a * (fourier f a * fourier g a) := by
  rw [← fourier_pairing]
  simp_rw [fourier_adjacency]
  apply Finset.sum_congr rfl
  intro a _
  ring


/-- Cauchy--Schwarz in the unnormalized Fourier coordinates. -/
theorem fourier_abs_pairing_le (f g : Cube r → ℝ) :
    (∑ a, |fourier f a| * |fourier g a|) ≤
      Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, f x ^ 2) *
      Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, g x ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun a => |fourier f a|) (fun a => |fourier g a|)
  simpa only [sq_abs, fourier_energy] using h

/-- A spectral bound with an explicit constant-character term. -/
theorem adjacency_pairing_le {P : Type*} [Fintype P]
    (shifts : P → Cube r) (ε : ℝ) (hε : 0 ≤ ε) (hW : SmallWalsh shifts ε)
    (f g : Cube r → ℝ) :
    (Fintype.card (Cube r) : ℝ) * ∑ x, f x * adjacency shifts g x ≤
      (Fintype.card P : ℝ) * (∑ x, f x) * (∑ x, g x) +
      ε * Fintype.card P *
        (Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, f x ^ 2) *
         Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, g x ^ 2)) := by
  classical
  rw [adjacency_pairing]
  have hnonneg : 0 ≤ ε * (Fintype.card P : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ a : Cube r,
        ((if a = 0 then (Fintype.card P : ℝ) * fourier f 0 * fourier g 0 else 0) +
         ε * Fintype.card P * (|fourier f a| * |fourier g a|)) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a = 0
      · subst a
        simp only [walsh_zero, ite_true, if_true]
        have hp := mul_nonneg hnonneg (mul_nonneg (abs_nonneg (fourier f 0))
          (abs_nonneg (fourier g 0)))
        nlinarith
      · rw [ite_eq_right ha, zero_add]
        calc
          _ ≤ |walsh shifts a * (fourier f a * fourier g a)| := le_abs_self _
          _ = |walsh shifts a| * (|fourier f a| * |fourier g a|) := by rw [abs_mul, abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hW a ha)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (Fintype.card P : ℝ) * (∑ x, f x) * (∑ x, g x) +
        ε * Fintype.card P * (∑ a, |fourier f a| * |fourier g a|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left (fourier_abs_pairing_le f g) hnonneg) _

theorem sqrt_scaled_product (N u v : ℝ) (hN : 0 ≤ N) (hu : 0 ≤ u) :
    Real.sqrt (N * u) * Real.sqrt (N * v) = N * Real.sqrt (u * v) := by
  rw [← Real.sqrt_mul (mul_nonneg hN hu),
    show N * u * (N * v) = N ^ 2 * (u * v) by ring,
    Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CayleyGraph
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.instDecidableGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A bipartite regular Cayley multigraph with explicit ordered ports.
Every pair `(x,i)` is a separate edge, including repeated shifts. -/
namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators
open SubexponentialSAT.SqrtLog.SparseCode

variable {r : ℕ} {P : Type*}

variable [Fintype P]

theorem edgeCount_eq_pairing (shifts : P → Cube r) (U W : Finset (Cube r)) :
    ((graph shifts).edgeCount U W : ℝ) =
      ∑ x, indicator U x * adjacency shifts (indicator W) x := by
  classical
  simp only [PortGraph.edgeCount, PortGraph.edgesBetween, Finset.card_eq_sum_ones,
    Nat.cast_sum, Finset.sum_filter, Fintype.sum_prod_type,
    graph_rotation, indicator, adjacency, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ U <;> by_cases hw : x + shifts i ∈ W <;>
    simp [ hx, hw]

/-- Small nonconstant Walsh sums imply the edge mixing inequality used by
Tanner-code distance. This includes the zero-dimensional cube and empty ports. -/
theorem hasMixing_of_smallWalsh_oai (shifts : P → Cube r) (ε : ℝ)
    (hε : 0 ≤ ε) (hW : SmallWalsh shifts ε) : (graph shifts).HasMixing ε := by
  classical
  intro U W
  have h := adjacency_pairing_le shifts ε hε hW (indicator U) (indicator W)
  rw [← edgeCount_eq_pairing] at h
  simp only [sum_indicator, sum_indicator_sq] at h
  rw [sqrt_scaled_product _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at h
  have hN : (0 : ℝ) < Fintype.card (Cube r) := by
    exact_mod_cast Fintype.card_pos
  apply le_of_mul_le_mul_left ?_ hN
  convert h using 1 <;> first | rfl | (field_simp) | (field_simp; ring)

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end

theorem solution.{u_1} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh_oai.{u_1} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh_oai.{u_1}
