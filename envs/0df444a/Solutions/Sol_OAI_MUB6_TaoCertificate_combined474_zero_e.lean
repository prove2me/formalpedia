-- Prove2me | solution 1 for OAI.MUB6.TaoCertificate.combined474_zero_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:26:37.379363+00:00
-- url     : https://prove2.me/submissions/55c68d4c-55e4-44a6-9b39-c445eec86a5f

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E158
import Definitions.Def_OAIQ106E165
import Definitions.Def_OAIQ106E167
import Theorems.Thm_OAI_MUB6_TaoCertificate_combined455_zero_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_IntegerMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation-preserving sparse integer merge. Its soundness needs no sorting
hypothesis: ordering is only used to make generated witnesses short. Each merge
can be checked independently by a finite integer-list equality. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*}

theorem eval_mergeFuel [LinearOrder ι] (fuel : ℕ) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeFuel fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeFuel]
      | cons b bs =>
        simp only [mergeFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_merge [LinearOrder ι] (a b : Sparse ι) (x : ι → ℝ) :
    eval (merge a b) x = eval a x + eval b x := eval_mergeFuel _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_Tao
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit five-cycle representative of Tao's cubic matrix. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem omega_isPrimitiveRoot : IsPrimitiveRoot omega 3 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 3 (by decide)

theorem omega_cube : omega ^ 3 = 1 := omega_isPrimitiveRoot.pow_eq_one

theorem omega_norm : ‖omega‖ = 1 :=
  omega_isPrimitiveRoot.norm'_eq_one (by decide)

theorem omega_normSq : Complex.normSq omega = 1 := by
  rw [Complex.normSq_eq_norm_sq, omega_norm]
  norm_num

theorem omega_sum : 1 + omega + omega ^ 2 = 0 := by
  simpa [Finset.sum_range_succ] using
    omega_isPrimitiveRoot.geom_sum_eq_zero (by decide : 1 < 3)

theorem omega_conj : conj omega = omega ^ 2 := by
  have homega : omega ≠ 0 := by
    intro hzero
    simpa [hzero] using omega_normSq
  apply mul_left_cancel₀ homega
  calc
    omega * conj omega = 1 := by simp [Complex.mul_conj, omega_normSq]
    _ = omega * omega ^ 2 := by rw [← pow_succ', omega_cube]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoArithmetic
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.character_zero _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.g_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact arithmetic in `ℤ[ω]`, interpreted in the same complex root as Tao's
matrix.  These definitions are for certificate checking, not assumptions. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

theorem value_mul (z w : Coeff) : value (mul z w) = value z * value w := by
  simp only [value, mul, Int.cast_add, Int.cast_sub, Int.cast_mul]
  linear_combination -(z.2 : ℂ) * (w.2 : ℂ) * omega_sum

theorem value_conjugate (z : Coeff) : value (conjugate z) = conj (value z) := by
  simp only [value, conjugate, Int.cast_sub, Int.cast_neg, map_add, map_mul,
    map_intCast, omega_conj]
  linear_combination -(z.2 : ℂ) * omega_sum

theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → Coeff) :
    value (∑ i ∈ s, f i) = ∑ i ∈ s, value (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem omega_zpow_mod (n : ℤ) : omega ^ n = omega ^ (n % 3) := by
  have hn : n = n % 3 + 3 * (n / 3) := (Int.emod_add_mul_ediv n 3).symm
  have h3 : omega ^ (3 : ℤ) = 1 := by simpa only [zpow_ofNat] using omega_cube
  calc
    omega ^ n = omega ^ (n % 3 + 3 * (n / 3)) := by rw [← hn]
    _ = omega ^ (n % 3) := by
      rw [zpow_add₀ (omega_isPrimitiveRoot.ne_zero (by decide)), zpow_mul, h3,
        one_zpow, mul_one]

theorem value_root (n : ℤ) : value (root n) = omega ^ n := by
  rw [omega_zpow_mod]
  have h0 := Int.emod_nonneg n (by decide : (3 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos n (by decide : (0 : ℤ) < 3)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · simp [root, h, value]
  · simp [root, h, value]
  · simp only [root, h]
    norm_num [value]
    linear_combination -omega_sum

theorem omega_zpow_sum (a : Charge) : (∏ i, omega ^ a i) = omega ^ (∑ i, a i) := by
  have h (s : Finset Coord) : (∏ i ∈ s, omega ^ a i) = omega ^ (∑ i ∈ s, a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
        zpow_add₀ (omega_isPrimitiveRoot.ne_zero (by decide))]
  exact h Finset.univ

theorem counts_interpretation (a : Charge) : value (counts a) = 6 * g tao a := by
  unfold counts
  rw [value_sum]
  have hc (k : Coord) : character (fun i => tao i k) a =
      omega ^ (∑ i, (taoExponent i k : ℤ) * a i) := by
    unfold character tao
    simp_rw [← zpow_natCast, ← zpow_mul]
    exact omega_zpow_sum _
  simp_rw [value_root]
  simp only [g, hc]
  ring

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Tao_TaoSparse
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6.TaoArithmetic

theorem eval_monomial (f : Charge → ℂ) (a : Charge) (z : Coeff) :
    Certificate.Integer.Sparse.eval (monomial a z) (momentValues f) =
      (value z * f a).re := by
  simp [Certificate.Integer.Sparse.eval, monomial, momentValues, value,
    add_mul, Complex.add_re, Complex.mul_re]
  ring

theorem offDiagonalPairs_sum (f : Coord → Coord → ℂ) :
    (offDiagonalPairs.map (fun p => f p.1 p.2)).sum = offDiagSum f := by
  simp [offDiagonalPairs, offDiagSum, Finset.sum_erase_eq_sub, Fin.sum_univ_succ]
  ring

theorem eval_flatMap {ι : Type*} (l : List ι) (r : ι → Sparse) (x : List ℤ → ℝ) :
    Certificate.Integer.Sparse.eval (l.flatMap r) x =
      (l.map (fun i => Certificate.Integer.Sparse.eval (r i) x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [List.flatMap_cons, ih]

theorem re_list_sum (l : List ℂ) : l.sum.re = (l.map Complex.re).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Complex.add_re, ih]

theorem eval_row (f : Charge → ℂ) (a c : Charge) (w : Coeff) :
    Certificate.Integer.Sparse.eval (row a c w) (momentValues f) =
      6 * (value w * offDiagSum
        (fun i j => f (a + difference i j) * conj (g tao (c + difference i j)))).re := by
  rw [row, eval_flatMap]
  simp_rw [eval_monomial, value_mul, value_conjugate, counts_interpretation,
    map_mul, map_ofNat]
  have hs : (offDiagonalPairs.map (fun p =>
      ((value w * (6 * conj (g tao (c + difference p.1 p.2)))) *
        f (a + difference p.1 p.2)).re)).sum =
      (6 * value w * (offDiagonalPairs.map (fun p =>
        f (a + difference p.1 p.2) * conj (g tao (c + difference p.1 p.2)))).sum).re := by
    rw [← List.sum_map_mul_left, re_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    ring
  rw [hs, offDiagonalPairs_sum (fun i j =>
    f (a + difference i j) * conj (g tao (c + difference i j)))]
  simp only [mul_assoc, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]

theorem eval_row_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        conj (g tao (c + difference i j))) = 0)
    (a c : Charge) (ha : Balanced a) (hc : Balanced c) (w : Coeff) :
    Certificate.Integer.Sparse.eval (row a c w) (momentValues f) = 0 := by
  rw [eval_row, hcross a c ha hc]
  simp

theorem eval_normalize (r : Sparse) (x : List ℤ → ℝ) :
    Certificate.Integer.Sparse.eval (normalize r) x =
      Certificate.Integer.Sparse.eval r x := by
  induction r with
  | nil => rfl
  | cons p ps ih =>
    simp only [normalize]
    split_ifs with h
    · simp [ih, h]
    · simp [ih]

end MUB6.TaoArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source9_checked : normalize (row ![0, 0, -2, 0, 0, 2] ![0, 0, -2, 0, 0, 2] (6, 0)) = source9 := by
  decide +kernel

theorem source9_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source9 (momentValues f) = 0 := by
  rw [← source9_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source10_checked : normalize (row ![0, 0, -2, 0, 2, 0] ![0, 0, -2, 0, 2, 0] (6, 0)) = source10 := by
  decide +kernel

theorem source10_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source10 (momentValues f) = 0 := by
  rw [← source10_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source11_checked : normalize (row ![0, 0, -2, 2, 0, 0] ![0, 0, -2, 2, 0, 0] (6, 0)) = source11 := by
  decide +kernel

theorem source11_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source11 (momentValues f) = 0 := by
  rw [← source11_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source81_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 1, -1, 0, 1, -1] (-12, 0)) = source81 := by
  decide +kernel

theorem source81_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source81 (momentValues f) = 0 := by
  rw [← source81_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source90_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![1, -1, -1, 0, 0, 1] (-12, 0)) = source90 := by
  decide +kernel

theorem source90_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source90 (momentValues f) = 0 := by
  rw [← source90_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source91_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![1, -1, -1, 0, 1, 0] (-12, 0)) = source91 := by
  decide +kernel

theorem source91_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source91 (momentValues f) = 0 := by
  rw [← source91_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source92_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![1, -1, -1, 1, 0, 0] (-12, 0)) = source92 := by
  decide +kernel

theorem source92_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source92 (momentValues f) = 0 := by
  rw [← source92_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source102_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![1, 0, -1, -1, 0, 1] (-12, 0)) = source102 := by
  decide +kernel

theorem source102_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source102 (momentValues f) = 0 := by
  rw [← source102_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source103_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![1, 0, -1, -1, 1, 0] (-12, 0)) = source103 := by
  decide +kernel

theorem source103_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source103 (momentValues f) = 0 := by
  rw [← source103_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source104_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![1, 0, -1, 0, -1, 1] (-12, 0)) = source104 := by
  decide +kernel

theorem source104_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source104 (momentValues f) = 0 := by
  rw [← source104_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source106_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![1, 0, -1, 1, -1, 0] (-12, 0)) = source106 := by
  decide +kernel

theorem source106_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source106 (momentValues f) = 0 := by
  rw [← source106_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source114_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![1, 1, -1, -1, 0, 0] (-12, 0)) = source114 := by
  decide +kernel

theorem source114_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source114 (momentValues f) = 0 := by
  rw [← source114_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source115_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![1, 1, -1, 0, -1, 0] (-12, 0)) = source115 := by
  decide +kernel

theorem source115_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source115 (momentValues f) = 0 := by
  rw [← source115_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source120_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source120 := by
  decide +kernel

theorem source120_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source120 (momentValues f) = 0 := by
  rw [← source120_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source122_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source122 := by
  decide +kernel

theorem source122_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source122 (momentValues f) = 0 := by
  rw [← source122_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source144_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source144 := by
  decide +kernel

theorem source144_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source144 (momentValues f) = 0 := by
  rw [← source144_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source150_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source150 := by
  decide +kernel

theorem source150_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source150 (momentValues f) = 0 := by
  rw [← source150_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source156_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source156 := by
  decide +kernel

theorem source156_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source156 (momentValues f) = 0 := by
  rw [← source156_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source21_checked : normalize (row ![0, 2, -2, 0, 0, 0] ![0, 2, -2, 0, 0, 0] (6, 0)) = source21 := by
  decide +kernel

theorem source21_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source21 (momentValues f) = 0 := by
  rw [← source21_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source162_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source162 := by
  decide +kernel

theorem source162_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source162 (momentValues f) = 0 := by
  rw [← source162_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source168_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source168 := by
  decide +kernel

theorem source168_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source168 (momentValues f) = 0 := by
  rw [← source168_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source174_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source174 := by
  decide +kernel

theorem source174_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source174 (momentValues f) = 0 := by
  rw [← source174_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source176_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source176 := by
  decide +kernel

theorem source176_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source176 (momentValues f) = 0 := by
  rw [← source176_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source180_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![1, -1, 0, 0, 0, 0] (0, -3)) = source180 := by
  decide +kernel

theorem source180_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source180 (momentValues f) = 0 := by
  rw [← source180_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source182_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![1, -1, 0, 0, 0, 0] (3, 3)) = source182 := by
  decide +kernel

theorem source182_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source182 (momentValues f) = 0 := by
  rw [← source182_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source193_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![0, 1, -1, 0, 0, 0] (3, 3)) = source193 := by
  decide +kernel

theorem source193_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source193 (momentValues f) = 0 := by
  rw [← source193_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source195_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![0, 1, -1, 0, 0, 0] (3, 3)) = source195 := by
  decide +kernel

theorem source195_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source195 (momentValues f) = 0 := by
  rw [← source195_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source197_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![0, 1, -1, 0, 0, 0] (0, -3)) = source197 := by
  decide +kernel

theorem source197_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source197 (momentValues f) = 0 := by
  rw [← source197_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source222_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, -1, 0, 0, 1, 0] (0, -3)) = source222 := by
  decide +kernel

theorem source222_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source222 (momentValues f) = 0 := by
  rw [← source222_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source224_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, -1, 0, 0, 1, 0] (0, -3)) = source224 := by
  decide +kernel

theorem source224_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source224 (momentValues f) = 0 := by
  rw [← source224_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source234_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source234 := by
  decide +kernel

theorem source234_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source234 (momentValues f) = 0 := by
  rw [← source234_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source26_checked : normalize (row ![2, 0, -2, 0, 0, 0] ![2, 0, -2, 0, 0, 0] (6, 0)) = source26 := by
  decide +kernel

theorem source26_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source26 (momentValues f) = 0 := by
  rw [← source26_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source253_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![0, -1, 1, 0, 0, 0] (0, -3)) = source253 := by
  decide +kernel

theorem source253_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source253 (momentValues f) = 0 := by
  rw [← source253_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source255_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![0, -1, 1, 0, 0, 0] (3, 3)) = source255 := by
  decide +kernel

theorem source255_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source255 (momentValues f) = 0 := by
  rw [← source255_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source257_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![0, -1, 1, 0, 0, 0] (3, 3)) = source257 := by
  decide +kernel

theorem source257_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source257 (momentValues f) = 0 := by
  rw [← source257_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source265_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![0, 0, 1, -1, 0, 0] (0, -3)) = source265 := by
  decide +kernel

theorem source265_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source265 (momentValues f) = 0 := by
  rw [← source265_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source267_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![0, 0, 1, -1, 0, 0] (3, 3)) = source267 := by
  decide +kernel

theorem source267_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source267 (momentValues f) = 0 := by
  rw [← source267_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source269_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![0, 0, 1, -1, 0, 0] (3, 3)) = source269 := by
  decide +kernel

theorem source269_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source269 (momentValues f) = 0 := by
  rw [← source269_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source271_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 0, 1, -1, 0, 0] (0, -3)) = source271 := by
  decide +kernel

theorem source271_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source271 (momentValues f) = 0 := by
  rw [← source271_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source273_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 0, 1, -1, 0, 0] (3, 3)) = source273 := by
  decide +kernel

theorem source273_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source273 (momentValues f) = 0 := by
  rw [← source273_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source275_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, 1, -1, 0, 0] (0, -3)) = source275 := by
  decide +kernel

theorem source275_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source275 (momentValues f) = 0 := by
  rw [← source275_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source277_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![0, 0, 1, 0, -1, 0] (0, -3)) = source277 := by
  decide +kernel

theorem source277_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source277 (momentValues f) = 0 := by
  rw [← source277_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source279_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![0, 0, 1, 0, -1, 0] (0, -3)) = source279 := by
  decide +kernel

theorem source279_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source279 (momentValues f) = 0 := by
  rw [← source279_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source281_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![0, 0, 1, 0, -1, 0] (3, 3)) = source281 := by
  decide +kernel

theorem source281_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source281 (momentValues f) = 0 := by
  rw [← source281_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source297_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source297 := by
  decide +kernel

theorem source297_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source297 (momentValues f) = 0 := by
  rw [← source297_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source299_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source299 := by
  decide +kernel

theorem source299_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source299 (momentValues f) = 0 := by
  rw [← source299_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source300_checked : normalize (row ![1, -1, -1, 1, 0, 0] ![1, 0, 0, -1, 0, 0] (0, -3)) = source300 := by
  decide +kernel

theorem source300_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source300 (momentValues f) = 0 := by
  rw [← source300_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source306_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![1, 0, 0, -1, 0, 0] (0, -3)) = source306 := by
  decide +kernel

theorem source306_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source306 (momentValues f) = 0 := by
  rw [← source306_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source325_checked : normalize (row ![1, 1, -1, -1, 0, 0] ![0, 0, -1, 1, 0, 0] (3, 3)) = source325 := by
  decide +kernel

theorem source325_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source325 (momentValues f) = 0 := by
  rw [← source325_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source327_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![0, 0, -1, 1, 0, 0] (0, -3)) = source327 := by
  decide +kernel

theorem source327_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source327 (momentValues f) = 0 := by
  rw [← source327_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source329_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![0, 0, -1, 1, 0, 0] (3, 3)) = source329 := by
  decide +kernel

theorem source329_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source329 (momentValues f) = 0 := by
  rw [← source329_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source331_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 0, -1, 1, 0, 0] (0, -3)) = source331 := by
  decide +kernel

theorem source331_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source331 (momentValues f) = 0 := by
  rw [← source331_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source333_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 0, -1, 1, 0, 0] (0, -3)) = source333 := by
  decide +kernel

theorem source333_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source333 (momentValues f) = 0 := by
  rw [← source333_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source335_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, -1, 1, 0, 0] (3, 3)) = source335 := by
  decide +kernel

theorem source335_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source335 (momentValues f) = 0 := by
  rw [← source335_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source346_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, 0, -1, 1, 0] (3, 3)) = source346 := by
  decide +kernel

theorem source346_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source346 (momentValues f) = 0 := by
  rw [← source346_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source360_checked : normalize (row ![1, -1, -1, 0, 1, 0] ![1, 0, 0, 0, -1, 0] (3, 3)) = source360 := by
  decide +kernel

theorem source360_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source360 (momentValues f) = 0 := by
  rw [← source360_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source366_checked : normalize (row ![1, 0, -1, -1, 1, 0] ![1, 0, 0, 0, -1, 0] (0, -3)) = source366 := by
  decide +kernel

theorem source366_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source366 (momentValues f) = 0 := by
  rw [← source366_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source378_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 1, 0, 0, -1, 0] (0, -3)) = source378 := by
  decide +kernel

theorem source378_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source378 (momentValues f) = 0 := by
  rw [← source378_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source380_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 1, 0, 0, -1, 0] (3, 3)) = source380 := by
  decide +kernel

theorem source380_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source380 (momentValues f) = 0 := by
  rw [← source380_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source385_checked : normalize (row ![1, 1, -1, 0, -1, 0] ![0, 0, -1, 0, 1, 0] (3, 3)) = source385 := by
  decide +kernel

theorem source385_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source385 (momentValues f) = 0 := by
  rw [← source385_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source387_checked : normalize (row ![1, 0, -1, 1, -1, 0] ![0, 0, -1, 0, 1, 0] (0, -3)) = source387 := by
  decide +kernel

theorem source387_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source387 (momentValues f) = 0 := by
  rw [← source387_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source389_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![0, 0, -1, 0, 1, 0] (0, -3)) = source389 := by
  decide +kernel

theorem source389_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source389 (momentValues f) = 0 := by
  rw [← source389_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source406_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, 0, 1, -1, 0] (3, 3)) = source406 := by
  decide +kernel

theorem source406_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source406 (momentValues f) = 0 := by
  rw [← source406_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source418_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source418 := by
  decide +kernel

theorem source418_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source418 (momentValues f) = 0 := by
  rw [← source418_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source420_checked : normalize (row ![1, -1, -1, 0, 0, 1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source420 := by
  decide +kernel

theorem source420_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source420 (momentValues f) = 0 := by
  rw [← source420_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source426_checked : normalize (row ![1, 0, -1, -1, 0, 1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source426 := by
  decide +kernel

theorem source426_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source426 (momentValues f) = 0 := by
  rw [← source426_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source428_checked : normalize (row ![1, 0, -1, 0, -1, 1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source428 := by
  decide +kernel

theorem source428_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source428 (momentValues f) = 0 := by
  rw [← source428_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source438_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source438 := by
  decide +kernel

theorem source438_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source438 (momentValues f) = 0 := by
  rw [← source438_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source453_checked : normalize (row ![0, 1, -1, 0, 1, -1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source453 := by
  decide +kernel

theorem source453_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source453 (momentValues f) = 0 := by
  rw [← source453_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source455_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source455 := by
  decide +kernel

theorem source455_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source455 (momentValues f) = 0 := by
  rw [← source455_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source478_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source478 := by
  decide +kernel

theorem source478_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source478 (momentValues f) = 0 := by
  rw [← source478_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source72_checked : normalize (row ![0, 0, -1, -1, 1, 1] ![0, 0, -1, -1, 1, 1] (-12, 0)) = source72 := by
  decide +kernel

theorem source72_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source72 (momentValues f) = 0 := by
  rw [← source72_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source74_checked : normalize (row ![0, 0, -1, 1, 1, -1] ![0, 0, -1, 1, 1, -1] (-12, 0)) = source74 := by
  decide +kernel

theorem source74_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source74 (momentValues f) = 0 := by
  rw [← source74_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source78_checked : normalize (row ![0, 1, -1, -1, 0, 1] ![0, 1, -1, -1, 0, 1] (-12, 0)) = source78 := by
  decide +kernel

theorem source78_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source78 (momentValues f) = 0 := by
  rw [← source78_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source79_checked : normalize (row ![0, 1, -1, -1, 1, 0] ![0, 1, -1, -1, 1, 0] (-12, 0)) = source79 := by
  decide +kernel

theorem source79_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source79 (momentValues f) = 0 := by
  rw [← source79_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined168_checked : Certificate.Integer.Sparse.merge source72 source275 = combined168 := by
  decide +kernel

theorem combined168_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined168 (momentValues f) = 0 := by
  rw [← combined168_checked, Certificate.Integer.Sparse.eval_merge,
    source72_zero f hcross, source275_zero f hcross, add_zero]

theorem combined169_checked : Certificate.Integer.Sparse.merge combined168 source335 = combined169 := by
  decide +kernel

theorem combined169_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined169 (momentValues f) = 0 := by
  rw [← combined169_checked, Certificate.Integer.Sparse.eval_merge,
    combined168_zero f hcross, source335_zero f hcross, add_zero]

theorem combined170_checked : Certificate.Integer.Sparse.merge combined169 source418 = combined170 := by
  decide +kernel

theorem combined170_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined170 (momentValues f) = 0 := by
  rw [← combined170_checked, Certificate.Integer.Sparse.eval_merge,
    combined169_zero f hcross, source418_zero f hcross, add_zero]

theorem combined171_checked : Certificate.Integer.Sparse.merge combined170 source478 = combined171 := by
  decide +kernel

theorem combined171_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined171 (momentValues f) = 0 := by
  rw [← combined171_checked, Certificate.Integer.Sparse.eval_merge,
    combined170_zero f hcross, source478_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined176_checked : Certificate.Integer.Sparse.merge source74 source299 = combined176 := by
  decide +kernel

theorem combined176_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined176 (momentValues f) = 0 := by
  rw [← combined176_checked, Certificate.Integer.Sparse.eval_merge,
    source74_zero f hcross, source299_zero f hcross, add_zero]

theorem combined177_checked : Certificate.Integer.Sparse.merge combined176 source346 = combined177 := by
  decide +kernel

theorem combined177_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined177 (momentValues f) = 0 := by
  rw [← combined177_checked, Certificate.Integer.Sparse.eval_merge,
    combined176_zero f hcross, source346_zero f hcross, add_zero]

theorem combined178_checked : Certificate.Integer.Sparse.merge combined177 source406 = combined178 := by
  decide +kernel

theorem combined178_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined178 (momentValues f) = 0 := by
  rw [← combined178_checked, Certificate.Integer.Sparse.eval_merge,
    combined177_zero f hcross, source406_zero f hcross, add_zero]

theorem combined179_checked : Certificate.Integer.Sparse.merge combined178 source455 = combined179 := by
  decide +kernel

theorem combined179_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined179 (momentValues f) = 0 := by
  rw [← combined179_checked, Certificate.Integer.Sparse.eval_merge,
    combined178_zero f hcross, source455_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined192_checked : Certificate.Integer.Sparse.merge source78 source234 = combined192 := by
  decide +kernel

theorem combined192_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined192 (momentValues f) = 0 := by
  rw [← combined192_checked, Certificate.Integer.Sparse.eval_merge,
    source78_zero f hcross, source234_zero f hcross, add_zero]

theorem combined193_checked : Certificate.Integer.Sparse.merge combined192 source273 = combined193 := by
  decide +kernel

theorem combined193_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined193 (momentValues f) = 0 := by
  rw [← combined193_checked, Certificate.Integer.Sparse.eval_merge,
    combined192_zero f hcross, source273_zero f hcross, add_zero]

theorem combined194_checked : Certificate.Integer.Sparse.merge combined193 source333 = combined194 := by
  decide +kernel

theorem combined194_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined194 (momentValues f) = 0 := by
  rw [← combined194_checked, Certificate.Integer.Sparse.eval_merge,
    combined193_zero f hcross, source333_zero f hcross, add_zero]

theorem combined195_checked : Certificate.Integer.Sparse.merge combined194 source438 = combined195 := by
  decide +kernel

theorem combined195_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined195 (momentValues f) = 0 := by
  rw [← combined195_checked, Certificate.Integer.Sparse.eval_merge,
    combined194_zero f hcross, source438_zero f hcross, add_zero]

theorem combined196_checked : Certificate.Integer.Sparse.merge source79 source222 = combined196 := by
  decide +kernel

theorem combined196_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined196 (momentValues f) = 0 := by
  rw [← combined196_checked, Certificate.Integer.Sparse.eval_merge,
    source79_zero f hcross, source222_zero f hcross, add_zero]

theorem combined197_checked : Certificate.Integer.Sparse.merge combined196 source271 = combined197 := by
  decide +kernel

theorem combined197_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined197 (momentValues f) = 0 := by
  rw [← combined197_checked, Certificate.Integer.Sparse.eval_merge,
    combined196_zero f hcross, source271_zero f hcross, add_zero]

theorem combined198_checked : Certificate.Integer.Sparse.merge combined197 source331 = combined198 := by
  decide +kernel

theorem combined198_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined198 (momentValues f) = 0 := by
  rw [← combined198_checked, Certificate.Integer.Sparse.eval_merge,
    combined197_zero f hcross, source331_zero f hcross, add_zero]

theorem combined199_checked : Certificate.Integer.Sparse.merge combined198 source378 = combined199 := by
  decide +kernel

theorem combined199_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined199 (momentValues f) = 0 := by
  rw [← combined199_checked, Certificate.Integer.Sparse.eval_merge,
    combined198_zero f hcross, source378_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined204_checked : Certificate.Integer.Sparse.merge source81 source224 = combined204 := by
  decide +kernel

theorem combined204_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined204 (momentValues f) = 0 := by
  rw [← combined204_checked, Certificate.Integer.Sparse.eval_merge,
    source81_zero f hcross, source224_zero f hcross, add_zero]

theorem combined205_checked : Certificate.Integer.Sparse.merge combined204 source297 = combined205 := by
  decide +kernel

theorem combined205_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined205 (momentValues f) = 0 := by
  rw [← combined205_checked, Certificate.Integer.Sparse.eval_merge,
    combined204_zero f hcross, source297_zero f hcross, add_zero]

theorem combined206_checked : Certificate.Integer.Sparse.merge combined205 source380 = combined206 := by
  decide +kernel

theorem combined206_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined206 (momentValues f) = 0 := by
  rw [← combined206_checked, Certificate.Integer.Sparse.eval_merge,
    combined205_zero f hcross, source380_zero f hcross, add_zero]

theorem combined207_checked : Certificate.Integer.Sparse.merge combined206 source453 = combined207 := by
  decide +kernel

theorem combined207_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined207 (momentValues f) = 0 := by
  rw [← combined207_checked, Certificate.Integer.Sparse.eval_merge,
    combined206_zero f hcross, source453_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined240_checked : Certificate.Integer.Sparse.merge source90 source168 = combined240 := by
  decide +kernel

theorem combined240_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined240 (momentValues f) = 0 := by
  rw [← combined240_checked, Certificate.Integer.Sparse.eval_merge,
    source90_zero f hcross, source168_zero f hcross, add_zero]

theorem combined241_checked : Certificate.Integer.Sparse.merge combined240 source197 = combined241 := by
  decide +kernel

theorem combined241_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined241 (momentValues f) = 0 := by
  rw [← combined241_checked, Certificate.Integer.Sparse.eval_merge,
    combined240_zero f hcross, source197_zero f hcross, add_zero]

theorem combined242_checked : Certificate.Integer.Sparse.merge combined241 source257 = combined242 := by
  decide +kernel

theorem combined242_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined242 (momentValues f) = 0 := by
  rw [← combined242_checked, Certificate.Integer.Sparse.eval_merge,
    combined241_zero f hcross, source257_zero f hcross, add_zero]

theorem combined243_checked : Certificate.Integer.Sparse.merge combined242 source420 = combined243 := by
  decide +kernel

theorem combined243_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined243 (momentValues f) = 0 := by
  rw [← combined243_checked, Certificate.Integer.Sparse.eval_merge,
    combined242_zero f hcross, source420_zero f hcross, add_zero]

theorem combined244_checked : Certificate.Integer.Sparse.merge source91 source156 = combined244 := by
  decide +kernel

theorem combined244_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined244 (momentValues f) = 0 := by
  rw [← combined244_checked, Certificate.Integer.Sparse.eval_merge,
    source91_zero f hcross, source156_zero f hcross, add_zero]

theorem combined245_checked : Certificate.Integer.Sparse.merge combined244 source195 = combined245 := by
  decide +kernel

theorem combined245_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined245 (momentValues f) = 0 := by
  rw [← combined245_checked, Certificate.Integer.Sparse.eval_merge,
    combined244_zero f hcross, source195_zero f hcross, add_zero]

theorem combined246_checked : Certificate.Integer.Sparse.merge combined245 source255 = combined246 := by
  decide +kernel

theorem combined246_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined246 (momentValues f) = 0 := by
  rw [← combined246_checked, Certificate.Integer.Sparse.eval_merge,
    combined245_zero f hcross, source255_zero f hcross, add_zero]

theorem combined247_checked : Certificate.Integer.Sparse.merge combined246 source360 = combined247 := by
  decide +kernel

theorem combined247_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined247 (momentValues f) = 0 := by
  rw [← combined247_checked, Certificate.Integer.Sparse.eval_merge,
    combined246_zero f hcross, source360_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined248_checked : Certificate.Integer.Sparse.merge source92 source144 = combined248 := by
  decide +kernel

theorem combined248_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined248 (momentValues f) = 0 := by
  rw [← combined248_checked, Certificate.Integer.Sparse.eval_merge,
    source92_zero f hcross, source144_zero f hcross, add_zero]

theorem combined249_checked : Certificate.Integer.Sparse.merge combined248 source193 = combined249 := by
  decide +kernel

theorem combined249_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined249 (momentValues f) = 0 := by
  rw [← combined249_checked, Certificate.Integer.Sparse.eval_merge,
    combined248_zero f hcross, source193_zero f hcross, add_zero]

theorem combined250_checked : Certificate.Integer.Sparse.merge combined249 source253 = combined250 := by
  decide +kernel

theorem combined250_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined250 (momentValues f) = 0 := by
  rw [← combined250_checked, Certificate.Integer.Sparse.eval_merge,
    combined249_zero f hcross, source253_zero f hcross, add_zero]

theorem combined251_checked : Certificate.Integer.Sparse.merge combined250 source300 = combined251 := by
  decide +kernel

theorem combined251_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined251 (momentValues f) = 0 := by
  rw [← combined251_checked, Certificate.Integer.Sparse.eval_merge,
    combined250_zero f hcross, source300_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined288_checked : Certificate.Integer.Sparse.merge source102 source174 = combined288 := by
  decide +kernel

theorem combined288_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined288 (momentValues f) = 0 := by
  rw [← combined288_checked, Certificate.Integer.Sparse.eval_merge,
    source102_zero f hcross, source174_zero f hcross, add_zero]

theorem combined289_checked : Certificate.Integer.Sparse.merge combined288 source269 = combined289 := by
  decide +kernel

theorem combined289_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined289 (momentValues f) = 0 := by
  rw [← combined289_checked, Certificate.Integer.Sparse.eval_merge,
    combined288_zero f hcross, source269_zero f hcross, add_zero]

theorem combined290_checked : Certificate.Integer.Sparse.merge combined289 source329 = combined290 := by
  decide +kernel

theorem combined290_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined290 (momentValues f) = 0 := by
  rw [← combined290_checked, Certificate.Integer.Sparse.eval_merge,
    combined289_zero f hcross, source329_zero f hcross, add_zero]

theorem combined291_checked : Certificate.Integer.Sparse.merge combined290 source426 = combined291 := by
  decide +kernel

theorem combined291_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined291 (momentValues f) = 0 := by
  rw [← combined291_checked, Certificate.Integer.Sparse.eval_merge,
    combined290_zero f hcross, source426_zero f hcross, add_zero]

theorem combined292_checked : Certificate.Integer.Sparse.merge source103 source162 = combined292 := by
  decide +kernel

theorem combined292_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined292 (momentValues f) = 0 := by
  rw [← combined292_checked, Certificate.Integer.Sparse.eval_merge,
    source103_zero f hcross, source162_zero f hcross, add_zero]

theorem combined293_checked : Certificate.Integer.Sparse.merge combined292 source267 = combined293 := by
  decide +kernel

theorem combined293_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined293 (momentValues f) = 0 := by
  rw [← combined293_checked, Certificate.Integer.Sparse.eval_merge,
    combined292_zero f hcross, source267_zero f hcross, add_zero]

theorem combined294_checked : Certificate.Integer.Sparse.merge combined293 source327 = combined294 := by
  decide +kernel

theorem combined294_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined294 (momentValues f) = 0 := by
  rw [← combined294_checked, Certificate.Integer.Sparse.eval_merge,
    combined293_zero f hcross, source327_zero f hcross, add_zero]

theorem combined295_checked : Certificate.Integer.Sparse.merge combined294 source366 = combined295 := by
  decide +kernel

theorem combined295_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined295 (momentValues f) = 0 := by
  rw [← combined295_checked, Certificate.Integer.Sparse.eval_merge,
    combined294_zero f hcross, source366_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined296_checked : Certificate.Integer.Sparse.merge source104 source176 = combined296 := by
  decide +kernel

theorem combined296_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined296 (momentValues f) = 0 := by
  rw [← combined296_checked, Certificate.Integer.Sparse.eval_merge,
    source104_zero f hcross, source176_zero f hcross, add_zero]

theorem combined297_checked : Certificate.Integer.Sparse.merge combined296 source281 = combined297 := by
  decide +kernel

theorem combined297_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined297 (momentValues f) = 0 := by
  rw [← combined297_checked, Certificate.Integer.Sparse.eval_merge,
    combined296_zero f hcross, source281_zero f hcross, add_zero]

theorem combined298_checked : Certificate.Integer.Sparse.merge combined297 source389 = combined298 := by
  decide +kernel

theorem combined298_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined298 (momentValues f) = 0 := by
  rw [← combined298_checked, Certificate.Integer.Sparse.eval_merge,
    combined297_zero f hcross, source389_zero f hcross, add_zero]

theorem combined299_checked : Certificate.Integer.Sparse.merge combined298 source428 = combined299 := by
  decide +kernel

theorem combined299_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined299 (momentValues f) = 0 := by
  rw [← combined299_checked, Certificate.Integer.Sparse.eval_merge,
    combined298_zero f hcross, source428_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined304_checked : Certificate.Integer.Sparse.merge source106 source150 = combined304 := by
  decide +kernel

theorem combined304_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined304 (momentValues f) = 0 := by
  rw [← combined304_checked, Certificate.Integer.Sparse.eval_merge,
    source106_zero f hcross, source150_zero f hcross, add_zero]

theorem combined305_checked : Certificate.Integer.Sparse.merge combined304 source279 = combined305 := by
  decide +kernel

theorem combined305_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined305 (momentValues f) = 0 := by
  rw [← combined305_checked, Certificate.Integer.Sparse.eval_merge,
    combined304_zero f hcross, source279_zero f hcross, add_zero]

theorem combined306_checked : Certificate.Integer.Sparse.merge combined305 source306 = combined306 := by
  decide +kernel

theorem combined306_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined306 (momentValues f) = 0 := by
  rw [← combined306_checked, Certificate.Integer.Sparse.eval_merge,
    combined305_zero f hcross, source306_zero f hcross, add_zero]

theorem combined307_checked : Certificate.Integer.Sparse.merge combined306 source387 = combined307 := by
  decide +kernel

theorem combined307_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined307 (momentValues f) = 0 := by
  rw [← combined307_checked, Certificate.Integer.Sparse.eval_merge,
    combined306_zero f hcross, source387_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined336_checked : Certificate.Integer.Sparse.merge source114 source120 = combined336 := by
  decide +kernel

theorem combined336_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined336 (momentValues f) = 0 := by
  rw [← combined336_checked, Certificate.Integer.Sparse.eval_merge,
    source114_zero f hcross, source120_zero f hcross, add_zero]

theorem combined337_checked : Certificate.Integer.Sparse.merge combined336 source180 = combined337 := by
  decide +kernel

theorem combined337_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined337 (momentValues f) = 0 := by
  rw [← combined337_checked, Certificate.Integer.Sparse.eval_merge,
    combined336_zero f hcross, source180_zero f hcross, add_zero]

theorem combined338_checked : Certificate.Integer.Sparse.merge combined337 source265 = combined338 := by
  decide +kernel

theorem combined338_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined338 (momentValues f) = 0 := by
  rw [← combined338_checked, Certificate.Integer.Sparse.eval_merge,
    combined337_zero f hcross, source265_zero f hcross, add_zero]

theorem combined339_checked : Certificate.Integer.Sparse.merge combined338 source325 = combined339 := by
  decide +kernel

theorem combined339_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined339 (momentValues f) = 0 := by
  rw [← combined339_checked, Certificate.Integer.Sparse.eval_merge,
    combined338_zero f hcross, source325_zero f hcross, add_zero]

theorem combined340_checked : Certificate.Integer.Sparse.merge source115 source122 = combined340 := by
  decide +kernel

theorem combined340_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined340 (momentValues f) = 0 := by
  rw [← combined340_checked, Certificate.Integer.Sparse.eval_merge,
    source115_zero f hcross, source122_zero f hcross, add_zero]

theorem combined341_checked : Certificate.Integer.Sparse.merge combined340 source182 = combined341 := by
  decide +kernel

theorem combined341_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined341 (momentValues f) = 0 := by
  rw [← combined341_checked, Certificate.Integer.Sparse.eval_merge,
    combined340_zero f hcross, source182_zero f hcross, add_zero]

theorem combined342_checked : Certificate.Integer.Sparse.merge combined341 source277 = combined342 := by
  decide +kernel

theorem combined342_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined342 (momentValues f) = 0 := by
  rw [← combined342_checked, Certificate.Integer.Sparse.eval_merge,
    combined341_zero f hcross, source277_zero f hcross, add_zero]

theorem combined343_checked : Certificate.Integer.Sparse.merge combined342 source385 = combined343 := by
  decide +kernel

theorem combined343_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined343 (momentValues f) = 0 := by
  rw [← combined343_checked, Certificate.Integer.Sparse.eval_merge,
    combined342_zero f hcross, source385_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined456_checked : Certificate.Integer.Sparse.merge combined455 combined243 = combined456 := by
  decide +kernel

theorem combined456_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined456 (momentValues f) = 0 := by
  rw [← combined456_checked, Certificate.Integer.Sparse.eval_merge,
    combined455_zero_e f hcross, combined243_zero f hcross, add_zero]

theorem combined457_checked : Certificate.Integer.Sparse.merge combined456 combined247 = combined457 := by
  decide +kernel

theorem combined457_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined457 (momentValues f) = 0 := by
  rw [← combined457_checked, Certificate.Integer.Sparse.eval_merge,
    combined456_zero f hcross, combined247_zero f hcross, add_zero]

theorem combined458_checked : Certificate.Integer.Sparse.merge combined457 combined251 = combined458 := by
  decide +kernel

theorem combined458_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined458 (momentValues f) = 0 := by
  rw [← combined458_checked, Certificate.Integer.Sparse.eval_merge,
    combined457_zero f hcross, combined251_zero f hcross, add_zero]

theorem combined459_checked : Certificate.Integer.Sparse.merge combined458 combined307 = combined459 := by
  decide +kernel

theorem combined459_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined459 (momentValues f) = 0 := by
  rw [← combined459_checked, Certificate.Integer.Sparse.eval_merge,
    combined458_zero f hcross, combined307_zero f hcross, add_zero]

theorem combined460_checked : Certificate.Integer.Sparse.merge combined459 combined299 = combined460 := by
  decide +kernel

theorem combined460_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined460 (momentValues f) = 0 := by
  rw [← combined460_checked, Certificate.Integer.Sparse.eval_merge,
    combined459_zero f hcross, combined299_zero f hcross, add_zero]

theorem combined461_checked : Certificate.Integer.Sparse.merge combined460 combined343 = combined461 := by
  decide +kernel

theorem combined461_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined461 (momentValues f) = 0 := by
  rw [← combined461_checked, Certificate.Integer.Sparse.eval_merge,
    combined460_zero f hcross, combined343_zero f hcross, add_zero]

theorem combined462_checked : Certificate.Integer.Sparse.merge combined461 source9 = combined462 := by
  decide +kernel

theorem combined462_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined462 (momentValues f) = 0 := by
  rw [← combined462_checked, Certificate.Integer.Sparse.eval_merge,
    combined461_zero f hcross, source9_zero f hcross, add_zero]

theorem combined463_checked : Certificate.Integer.Sparse.merge combined462 source11 = combined463 := by
  decide +kernel

theorem combined463_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined463 (momentValues f) = 0 := by
  rw [← combined463_checked, Certificate.Integer.Sparse.eval_merge,
    combined462_zero f hcross, source11_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined464_checked : Certificate.Integer.Sparse.merge combined463 source21 = combined464 := by
  decide +kernel

theorem combined464_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined464 (momentValues f) = 0 := by
  rw [← combined464_checked, Certificate.Integer.Sparse.eval_merge,
    combined463_zero f hcross, source21_zero f hcross, add_zero]

theorem combined465_checked : Certificate.Integer.Sparse.merge combined464 combined195 = combined465 := by
  decide +kernel

theorem combined465_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined465 (momentValues f) = 0 := by
  rw [← combined465_checked, Certificate.Integer.Sparse.eval_merge,
    combined464_zero f hcross, combined195_zero f hcross, add_zero]

theorem combined466_checked : Certificate.Integer.Sparse.merge combined465 combined171 = combined466 := by
  decide +kernel

theorem combined466_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined466 (momentValues f) = 0 := by
  rw [← combined466_checked, Certificate.Integer.Sparse.eval_merge,
    combined465_zero f hcross, combined171_zero f hcross, add_zero]

theorem combined467_checked : Certificate.Integer.Sparse.merge combined466 combined199 = combined467 := by
  decide +kernel

theorem combined467_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined467 (momentValues f) = 0 := by
  rw [← combined467_checked, Certificate.Integer.Sparse.eval_merge,
    combined466_zero f hcross, combined199_zero f hcross, add_zero]

theorem combined468_checked : Certificate.Integer.Sparse.merge combined467 combined291 = combined468 := by
  decide +kernel

theorem combined468_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined468 (momentValues f) = 0 := by
  rw [← combined468_checked, Certificate.Integer.Sparse.eval_merge,
    combined467_zero f hcross, combined291_zero f hcross, add_zero]

theorem combined469_checked : Certificate.Integer.Sparse.merge combined468 combined295 = combined469 := by
  decide +kernel

theorem combined469_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined469 (momentValues f) = 0 := by
  rw [← combined469_checked, Certificate.Integer.Sparse.eval_merge,
    combined468_zero f hcross, combined295_zero f hcross, add_zero]

theorem combined470_checked : Certificate.Integer.Sparse.merge combined469 combined339 = combined470 := by
  decide +kernel

theorem combined470_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined470 (momentValues f) = 0 := by
  rw [← combined470_checked, Certificate.Integer.Sparse.eval_merge,
    combined469_zero f hcross, combined339_zero f hcross, add_zero]

theorem combined471_checked : Certificate.Integer.Sparse.merge combined470 source26 = combined471 := by
  decide +kernel

theorem combined471_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined471 (momentValues f) = 0 := by
  rw [← combined471_checked, Certificate.Integer.Sparse.eval_merge,
    combined470_zero f hcross, source26_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined472_checked : Certificate.Integer.Sparse.merge combined471 source10 = combined472 := by
  decide +kernel

theorem combined472_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined472 (momentValues f) = 0 := by
  rw [← combined472_checked, Certificate.Integer.Sparse.eval_merge,
    combined471_zero f hcross, source10_zero f hcross, add_zero]

theorem combined473_checked : Certificate.Integer.Sparse.merge combined472 combined179 = combined473 := by
  decide +kernel

theorem combined473_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined473 (momentValues f) = 0 := by
  rw [← combined473_checked, Certificate.Integer.Sparse.eval_merge,
    combined472_zero f hcross, combined179_zero f hcross, add_zero]

theorem combined474_checked : Certificate.Integer.Sparse.merge combined473 combined207 = combined474 := by
  decide +kernel

theorem combined474_zero_e_oai (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined474 (momentValues f) = 0 := by
  rw [← combined474_checked, Certificate.Integer.Sparse.eval_merge,
    combined473_zero f hcross, combined207_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

theorem solution : type_of% @OAI.MUB6.TaoCertificate.combined474_zero_e_oai := @OAI.MUB6.TaoCertificate.combined474_zero_e_oai
