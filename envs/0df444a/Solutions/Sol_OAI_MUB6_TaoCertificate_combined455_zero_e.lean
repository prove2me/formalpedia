-- Prove2me | solution 1 for OAI.MUB6.TaoCertificate.combined455_zero_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:26:35.710206+00:00
-- url     : https://prove2.me/submissions/9ff82f96-0bd7-4705-87eb-8c14bc170dea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E158
import Definitions.Def_OAIQ106E163
import Definitions.Def_OAIQ106E166
import Definitions.Def_OAIQ106E167
import Theorems.Thm_OAI_MUB6_TaoCertificate_combined438_zero_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source80_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 1, -1, 0, -1, 1] (-12, 0)) = source80 := by
  decide +kernel

theorem source80_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source80 (momentValues f) = 0 := by
  rw [← source80_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source82_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 1, -1, 1, -1, 0] (-12, 0)) = source82 := by
  decide +kernel

theorem source82_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source82 (momentValues f) = 0 := by
  rw [← source82_checked, eval_normalize]
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

theorem source94_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![1, -1, 0, -1, 1, 0] (-12, 0)) = source94 := by
  decide +kernel

theorem source94_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source94 (momentValues f) = 0 := by
  rw [← source94_checked, eval_normalize]
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

theorem source96_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![1, -1, 0, 0, 1, -1] (-12, 0)) = source96 := by
  decide +kernel

theorem source96_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source96 (momentValues f) = 0 := by
  rw [← source96_checked, eval_normalize]
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

theorem source109_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![1, 0, 0, -1, 1, -1] (-12, 0)) = source109 := by
  decide +kernel

theorem source109_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source109 (momentValues f) = 0 := by
  rw [← source109_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source133_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![1, 0, -1, 0, 0, 0] (3, 3)) = source133 := by
  decide +kernel

theorem source133_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source133 (momentValues f) = 0 := by
  rw [← source133_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source135_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![1, 0, -1, 0, 0, 0] (3, 3)) = source135 := by
  decide +kernel

theorem source135_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source135 (momentValues f) = 0 := by
  rw [← source135_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source137_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![1, 0, -1, 0, 0, 0] (0, -3)) = source137 := by
  decide +kernel

theorem source137_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source137 (momentValues f) = 0 := by
  rw [← source137_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source139_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![1, 0, -1, 0, 0, 0] (0, -3)) = source139 := by
  decide +kernel

theorem source139_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source139 (momentValues f) = 0 := by
  rw [← source139_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source141_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![1, 0, -1, 0, 0, 0] (3, 3)) = source141 := by
  decide +kernel

theorem source141_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source141 (momentValues f) = 0 := by
  rw [← source141_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source143_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![1, 0, -1, 0, 0, 0] (0, -3)) = source143 := by
  decide +kernel

theorem source143_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source143 (momentValues f) = 0 := by
  rw [← source143_checked, eval_normalize]
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

theorem source158_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source158 := by
  decide +kernel

theorem source158_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source158 (momentValues f) = 0 := by
  rw [← source158_checked, eval_normalize]
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

theorem source160_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source160 := by
  decide +kernel

theorem source160_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source160 (momentValues f) = 0 := by
  rw [← source160_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source166_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source166 := by
  decide +kernel

theorem source166_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source166 (momentValues f) = 0 := by
  rw [← source166_checked, eval_normalize]
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

theorem source199_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, 1, -1, 0, 0, 0] (0, -3)) = source199 := by
  decide +kernel

theorem source199_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source199 (momentValues f) = 0 := by
  rw [← source199_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source201_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, 1, -1, 0, 0, 0] (0, -3)) = source201 := by
  decide +kernel

theorem source201_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source201 (momentValues f) = 0 := by
  rw [← source201_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source203_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, 1, -1, 0, 0, 0] (3, 3)) = source203 := by
  decide +kernel

theorem source203_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source203 (momentValues f) = 0 := by
  rw [← source203_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source204_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![0, -1, 0, 1, 0, 0] (3, 3)) = source204 := by
  decide +kernel

theorem source204_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source204 (momentValues f) = 0 := by
  rw [← source204_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source207_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![0, 1, 0, -1, 0, 0] (3, 3)) = source207 := by
  decide +kernel

theorem source207_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source207 (momentValues f) = 0 := by
  rw [← source207_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source210_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, -1, 0, 1, 0, 0] (3, 3)) = source210 := by
  decide +kernel

theorem source210_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source210 (momentValues f) = 0 := by
  rw [← source210_checked, eval_normalize]
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

theorem source216_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source216 := by
  decide +kernel

theorem source216_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source216 (momentValues f) = 0 := by
  rw [← source216_checked, eval_normalize]
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

theorem source228_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source228 := by
  decide +kernel

theorem source228_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source228 (momentValues f) = 0 := by
  rw [← source228_checked, eval_normalize]
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

theorem source233_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source233 := by
  decide +kernel

theorem source233_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source233 (momentValues f) = 0 := by
  rw [← source233_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source236_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source236 := by
  decide +kernel

theorem source236_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source236 (momentValues f) = 0 := by
  rw [← source236_checked, eval_normalize]
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

theorem source25_checked : normalize (row ![2, -2, 0, 0, 0, 0] ![2, -2, 0, 0, 0, 0] (6, 0)) = source25 := by
  decide +kernel

theorem source25_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source25 (momentValues f) = 0 := by
  rw [← source25_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source27_checked : normalize (row ![2, 0, 0, -2, 0, 0] ![2, 0, 0, -2, 0, 0] (6, 0)) = source27 := by
  decide +kernel

theorem source27_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source27 (momentValues f) = 0 := by
  rw [← source27_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source241_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source241 := by
  decide +kernel

theorem source241_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source241 (momentValues f) = 0 := by
  rw [← source241_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source243_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source243 := by
  decide +kernel

theorem source243_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source243 (momentValues f) = 0 := by
  rw [← source243_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source245_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source245 := by
  decide +kernel

theorem source245_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source245 (momentValues f) = 0 := by
  rw [← source245_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source247_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source247 := by
  decide +kernel

theorem source247_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source247 (momentValues f) = 0 := by
  rw [← source247_checked, eval_normalize]
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

theorem source249_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source249 := by
  decide +kernel

theorem source249_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source249 (momentValues f) = 0 := by
  rw [← source249_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source251_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source251 := by
  decide +kernel

theorem source251_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source251 (momentValues f) = 0 := by
  rw [← source251_checked, eval_normalize]
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

theorem source259_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, -1, 1, 0, 0, 0] (3, 3)) = source259 := by
  decide +kernel

theorem source259_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source259 (momentValues f) = 0 := by
  rw [← source259_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source261_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, -1, 1, 0, 0, 0] (0, -3)) = source261 := by
  decide +kernel

theorem source261_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source261 (momentValues f) = 0 := by
  rw [← source261_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source263_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, -1, 1, 0, 0, 0] (0, -3)) = source263 := by
  decide +kernel

theorem source263_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source263 (momentValues f) = 0 := by
  rw [← source263_checked, eval_normalize]
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

theorem source283_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 0, 1, 0, -1, 0] (3, 3)) = source283 := by
  decide +kernel

theorem source283_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source283 (momentValues f) = 0 := by
  rw [← source283_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source285_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 0, 1, 0, -1, 0] (3, 3)) = source285 := by
  decide +kernel

theorem source285_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source285 (momentValues f) = 0 := by
  rw [← source285_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source287_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, 1, 0, -1, 0] (0, -3)) = source287 := by
  decide +kernel

theorem source287_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source287 (momentValues f) = 0 := by
  rw [← source287_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source312_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![0, 1, 0, -1, 0, 0] (3, 3)) = source312 := by
  decide +kernel

theorem source312_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source312 (momentValues f) = 0 := by
  rw [← source312_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source315_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![0, -1, 0, 1, 0, 0] (0, -3)) = source315 := by
  decide +kernel

theorem source315_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source315 (momentValues f) = 0 := by
  rw [← source315_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source318_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 1, 0, -1, 0, 0] (0, -3)) = source318 := by
  decide +kernel

theorem source318_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source318 (momentValues f) = 0 := by
  rw [← source318_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source36_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![-1, 0, -1, 0, 1, 1] (-12, 0)) = source36 := by
  decide +kernel

theorem source36_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source36 (momentValues f) = 0 := by
  rw [← source36_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source37_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![-1, 0, -1, 1, 0, 1] (-12, 0)) = source37 := by
  decide +kernel

theorem source37_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source37 (momentValues f) = 0 := by
  rw [← source37_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source38_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![-1, 0, -1, 1, 1, 0] (-12, 0)) = source38 := by
  decide +kernel

theorem source38_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source38 (momentValues f) = 0 := by
  rw [← source38_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source338_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![0, 0, 0, -1, 1, 0] (3, 3)) = source338 := by
  decide +kernel

theorem source338_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source338 (momentValues f) = 0 := by
  rw [← source338_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source342_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, 0, 0, -1, 1, 0] (0, -3)) = source342 := by
  decide +kernel

theorem source342_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source342 (momentValues f) = 0 := by
  rw [← source342_checked, eval_normalize]
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

theorem source350_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source350 := by
  decide +kernel

theorem source350_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source350 (momentValues f) = 0 := by
  rw [← source350_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source353_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source353 := by
  decide +kernel

theorem source353_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source353 (momentValues f) = 0 := by
  rw [← source353_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source354_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source354 := by
  decide +kernel

theorem source354_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source354 (momentValues f) = 0 := by
  rw [← source354_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source358_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source358 := by
  decide +kernel

theorem source358_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source358 (momentValues f) = 0 := by
  rw [← source358_checked, eval_normalize]
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

theorem source362_checked : normalize (row ![1, -1, 0, -1, 1, 0] ![1, 0, 0, 0, -1, 0] (3, 3)) = source362 := by
  decide +kernel

theorem source362_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source362 (momentValues f) = 0 := by
  rw [← source362_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source364_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![1, 0, 0, 0, -1, 0] (0, -3)) = source364 := by
  decide +kernel

theorem source364_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source364 (momentValues f) = 0 := by
  rw [← source364_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source370_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![1, 0, 0, 0, -1, 0] (0, -3)) = source370 := by
  decide +kernel

theorem source370_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source370 (momentValues f) = 0 := by
  rw [← source370_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source372_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![0, 1, 0, 0, -1, 0] (0, -3)) = source372 := by
  decide +kernel

theorem source372_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source372 (momentValues f) = 0 := by
  rw [← source372_checked, eval_normalize]
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

theorem source391_checked : normalize (row ![0, 1, -1, 1, -1, 0] ![0, 0, -1, 0, 1, 0] (0, -3)) = source391 := by
  decide +kernel

theorem source391_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source391 (momentValues f) = 0 := by
  rw [← source391_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source393_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 0, -1, 0, 1, 0] (3, 3)) = source393 := by
  decide +kernel

theorem source393_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source393 (momentValues f) = 0 := by
  rw [← source393_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source395_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, -1, 0, 1, 0] (3, 3)) = source395 := by
  decide +kernel

theorem source395_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source395 (momentValues f) = 0 := by
  rw [← source395_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source398_checked : normalize (row ![-1, 0, -1, 1, 1, 0] ![0, 0, 0, 1, -1, 0] (0, -3)) = source398 := by
  decide +kernel

theorem source398_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source398 (momentValues f) = 0 := by
  rw [← source398_checked, eval_normalize]
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

theorem source402_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, 0, 0, 1, -1, 0] (3, 3)) = source402 := by
  decide +kernel

theorem source402_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source402 (momentValues f) = 0 := by
  rw [← source402_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source410_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source410 := by
  decide +kernel

theorem source410_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source410 (momentValues f) = 0 := by
  rw [← source410_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source414_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source414 := by
  decide +kernel

theorem source414_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source414 (momentValues f) = 0 := by
  rw [← source414_checked, eval_normalize]
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

theorem source432_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source432 := by
  decide +kernel

theorem source432_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source432 (momentValues f) = 0 := by
  rw [← source432_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source437_checked : normalize (row ![1, -1, 0, 0, 1, -1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source437 := by
  decide +kernel

theorem source437_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source437 (momentValues f) = 0 := by
  rw [← source437_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source440_checked : normalize (row ![0, 1, -1, 0, -1, 1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source440 := by
  decide +kernel

theorem source440_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source440 (momentValues f) = 0 := by
  rw [← source440_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source458_checked : normalize (row ![-1, 0, -1, 1, 0, 1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source458 := by
  decide +kernel

theorem source458_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source458 (momentValues f) = 0 := by
  rw [← source458_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source461_checked : normalize (row ![1, 0, 0, -1, 1, -1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source461 := by
  decide +kernel

theorem source461_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source461 (momentValues f) = 0 := by
  rw [← source461_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source462_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source462 := by
  decide +kernel

theorem source462_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source462 (momentValues f) = 0 := by
  rw [← source462_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source466_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source466 := by
  decide +kernel

theorem source466_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source466 (momentValues f) = 0 := by
  rw [← source466_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source470_checked : normalize (row ![-1, 0, -1, 0, 1, 1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source470 := by
  decide +kernel

theorem source470_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source470 (momentValues f) = 0 := by
  rw [← source470_checked, eval_normalize]
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

theorem source474_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source474 := by
  decide +kernel

theorem source474_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source474 (momentValues f) = 0 := by
  rw [← source474_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source48_checked : normalize (row ![-1, 1, -1, 0, 0, 1] ![-1, 1, -1, 0, 0, 1] (-12, 0)) = source48 := by
  decide +kernel

theorem source48_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source48 (momentValues f) = 0 := by
  rw [← source48_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source49_checked : normalize (row ![-1, 1, -1, 0, 1, 0] ![-1, 1, -1, 0, 1, 0] (-12, 0)) = source49 := by
  decide +kernel

theorem source49_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source49 (momentValues f) = 0 := by
  rw [← source49_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source50_checked : normalize (row ![-1, 1, -1, 1, 0, 0] ![-1, 1, -1, 1, 0, 0] (-12, 0)) = source50 := by
  decide +kernel

theorem source50_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source50 (momentValues f) = 0 := by
  rw [← source50_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source60_checked : normalize (row ![0, -1, -1, 0, 1, 1] ![0, -1, -1, 0, 1, 1] (-12, 0)) = source60 := by
  decide +kernel

theorem source60_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source60 (momentValues f) = 0 := by
  rw [← source60_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source61_checked : normalize (row ![0, -1, -1, 1, 0, 1] ![0, -1, -1, 1, 0, 1] (-12, 0)) = source61 := by
  decide +kernel

theorem source61_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source61 (momentValues f) = 0 := by
  rw [← source61_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source62_checked : normalize (row ![0, -1, -1, 1, 1, 0] ![0, -1, -1, 1, 1, 0] (-12, 0)) = source62 := by
  decide +kernel

theorem source62_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source62 (momentValues f) = 0 := by
  rw [← source62_checked, eval_normalize]
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

theorem source73_checked : normalize (row ![0, 0, -1, 1, -1, 1] ![0, 0, -1, 1, -1, 1] (-12, 0)) = source73 := by
  decide +kernel

theorem source73_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source73 (momentValues f) = 0 := by
  rw [← source73_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined24_checked : Certificate.Integer.Sparse.merge source36 source143 = combined24 := by
  decide +kernel

theorem combined24_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined24 (momentValues f) = 0 := by
  rw [← combined24_checked, Certificate.Integer.Sparse.eval_merge,
    source36_zero f hcross, source143_zero f hcross, add_zero]

theorem combined25_checked : Certificate.Integer.Sparse.merge combined24 source251 = combined25 := by
  decide +kernel

theorem combined25_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined25 (momentValues f) = 0 := by
  rw [← combined25_checked, Certificate.Integer.Sparse.eval_merge,
    combined24_zero f hcross, source251_zero f hcross, add_zero]

theorem combined26_checked : Certificate.Integer.Sparse.merge combined25 source410 = combined26 := by
  decide +kernel

theorem combined26_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined26 (momentValues f) = 0 := by
  rw [← combined26_checked, Certificate.Integer.Sparse.eval_merge,
    combined25_zero f hcross, source410_zero f hcross, add_zero]

theorem combined27_checked : Certificate.Integer.Sparse.merge combined26 source470 = combined27 := by
  decide +kernel

theorem combined27_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined27 (momentValues f) = 0 := by
  rw [← combined27_checked, Certificate.Integer.Sparse.eval_merge,
    combined26_zero f hcross, source470_zero f hcross, add_zero]

theorem combined28_checked : Certificate.Integer.Sparse.merge source37 source141 = combined28 := by
  decide +kernel

theorem combined28_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined28 (momentValues f) = 0 := by
  rw [← combined28_checked, Certificate.Integer.Sparse.eval_merge,
    source37_zero f hcross, source141_zero f hcross, add_zero]

theorem combined29_checked : Certificate.Integer.Sparse.merge combined28 source249 = combined29 := by
  decide +kernel

theorem combined29_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined29 (momentValues f) = 0 := by
  rw [← combined29_checked, Certificate.Integer.Sparse.eval_merge,
    combined28_zero f hcross, source249_zero f hcross, add_zero]

theorem combined30_checked : Certificate.Integer.Sparse.merge combined29 source350 = combined30 := by
  decide +kernel

theorem combined30_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined30 (momentValues f) = 0 := by
  rw [← combined30_checked, Certificate.Integer.Sparse.eval_merge,
    combined29_zero f hcross, source350_zero f hcross, add_zero]

theorem combined31_checked : Certificate.Integer.Sparse.merge combined30 source458 = combined31 := by
  decide +kernel

theorem combined31_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined31 (momentValues f) = 0 := by
  rw [← combined31_checked, Certificate.Integer.Sparse.eval_merge,
    combined30_zero f hcross, source458_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined32_checked : Certificate.Integer.Sparse.merge source38 source139 = combined32 := by
  decide +kernel

theorem combined32_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined32 (momentValues f) = 0 := by
  rw [← combined32_checked, Certificate.Integer.Sparse.eval_merge,
    source38_zero f hcross, source139_zero f hcross, add_zero]

theorem combined33_checked : Certificate.Integer.Sparse.merge combined32 source247 = combined33 := by
  decide +kernel

theorem combined33_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined33 (momentValues f) = 0 := by
  rw [← combined33_checked, Certificate.Integer.Sparse.eval_merge,
    combined32_zero f hcross, source247_zero f hcross, add_zero]

theorem combined34_checked : Certificate.Integer.Sparse.merge combined33 source338 = combined34 := by
  decide +kernel

theorem combined34_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined34 (momentValues f) = 0 := by
  rw [← combined34_checked, Certificate.Integer.Sparse.eval_merge,
    combined33_zero f hcross, source338_zero f hcross, add_zero]

theorem combined35_checked : Certificate.Integer.Sparse.merge combined34 source398 = combined35 := by
  decide +kernel

theorem combined35_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined35 (momentValues f) = 0 := by
  rw [← combined35_checked, Certificate.Integer.Sparse.eval_merge,
    combined34_zero f hcross, source398_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined72_checked : Certificate.Integer.Sparse.merge source48 source137 = combined72 := by
  decide +kernel

theorem combined72_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined72 (momentValues f) = 0 := by
  rw [← combined72_checked, Certificate.Integer.Sparse.eval_merge,
    source48_zero f hcross, source137_zero f hcross, add_zero]

theorem combined73_checked : Certificate.Integer.Sparse.merge combined72 source228 = combined73 := by
  decide +kernel

theorem combined73_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined73 (momentValues f) = 0 := by
  rw [← combined73_checked, Certificate.Integer.Sparse.eval_merge,
    combined72_zero f hcross, source228_zero f hcross, add_zero]

theorem combined74_checked : Certificate.Integer.Sparse.merge combined73 source245 = combined74 := by
  decide +kernel

theorem combined74_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined74 (momentValues f) = 0 := by
  rw [← combined74_checked, Certificate.Integer.Sparse.eval_merge,
    combined73_zero f hcross, source245_zero f hcross, add_zero]

theorem combined75_checked : Certificate.Integer.Sparse.merge combined74 source432 = combined75 := by
  decide +kernel

theorem combined75_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined75 (momentValues f) = 0 := by
  rw [← combined75_checked, Certificate.Integer.Sparse.eval_merge,
    combined74_zero f hcross, source432_zero f hcross, add_zero]

theorem combined76_checked : Certificate.Integer.Sparse.merge source49 source135 = combined76 := by
  decide +kernel

theorem combined76_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined76 (momentValues f) = 0 := by
  rw [← combined76_checked, Certificate.Integer.Sparse.eval_merge,
    source49_zero f hcross, source135_zero f hcross, add_zero]

theorem combined77_checked : Certificate.Integer.Sparse.merge combined76 source216 = combined77 := by
  decide +kernel

theorem combined77_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined77 (momentValues f) = 0 := by
  rw [← combined77_checked, Certificate.Integer.Sparse.eval_merge,
    combined76_zero f hcross, source216_zero f hcross, add_zero]

theorem combined78_checked : Certificate.Integer.Sparse.merge combined77 source243 = combined78 := by
  decide +kernel

theorem combined78_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined78 (momentValues f) = 0 := by
  rw [← combined78_checked, Certificate.Integer.Sparse.eval_merge,
    combined77_zero f hcross, source243_zero f hcross, add_zero]

theorem combined79_checked : Certificate.Integer.Sparse.merge combined78 source372 = combined79 := by
  decide +kernel

theorem combined79_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined79 (momentValues f) = 0 := by
  rw [← combined79_checked, Certificate.Integer.Sparse.eval_merge,
    combined78_zero f hcross, source372_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined80_checked : Certificate.Integer.Sparse.merge source50 source133 = combined80 := by
  decide +kernel

theorem combined80_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined80 (momentValues f) = 0 := by
  rw [← combined80_checked, Certificate.Integer.Sparse.eval_merge,
    source50_zero f hcross, source133_zero f hcross, add_zero]

theorem combined81_checked : Certificate.Integer.Sparse.merge combined80 source204 = combined81 := by
  decide +kernel

theorem combined81_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined81 (momentValues f) = 0 := by
  rw [← combined81_checked, Certificate.Integer.Sparse.eval_merge,
    combined80_zero f hcross, source204_zero f hcross, add_zero]

theorem combined82_checked : Certificate.Integer.Sparse.merge combined81 source241 = combined82 := by
  decide +kernel

theorem combined82_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined82 (momentValues f) = 0 := by
  rw [← combined82_checked, Certificate.Integer.Sparse.eval_merge,
    combined81_zero f hcross, source241_zero f hcross, add_zero]

theorem combined83_checked : Certificate.Integer.Sparse.merge combined82 source312 = combined83 := by
  decide +kernel

theorem combined83_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined83 (momentValues f) = 0 := by
  rw [← combined83_checked, Certificate.Integer.Sparse.eval_merge,
    combined82_zero f hcross, source312_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined120_checked : Certificate.Integer.Sparse.merge source60 source203 = combined120 := by
  decide +kernel

theorem combined120_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined120 (momentValues f) = 0 := by
  rw [← combined120_checked, Certificate.Integer.Sparse.eval_merge,
    source60_zero f hcross, source203_zero f hcross, add_zero]

theorem combined121_checked : Certificate.Integer.Sparse.merge combined120 source263 = combined121 := by
  decide +kernel

theorem combined121_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined121 (momentValues f) = 0 := by
  rw [← combined121_checked, Certificate.Integer.Sparse.eval_merge,
    combined120_zero f hcross, source263_zero f hcross, add_zero]

theorem combined122_checked : Certificate.Integer.Sparse.merge combined121 source414 = combined122 := by
  decide +kernel

theorem combined122_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined122 (momentValues f) = 0 := by
  rw [← combined122_checked, Certificate.Integer.Sparse.eval_merge,
    combined121_zero f hcross, source414_zero f hcross, add_zero]

theorem combined123_checked : Certificate.Integer.Sparse.merge combined122 source474 = combined123 := by
  decide +kernel

theorem combined123_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined123 (momentValues f) = 0 := by
  rw [← combined123_checked, Certificate.Integer.Sparse.eval_merge,
    combined122_zero f hcross, source474_zero f hcross, add_zero]

theorem combined124_checked : Certificate.Integer.Sparse.merge source61 source201 = combined124 := by
  decide +kernel

theorem combined124_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined124 (momentValues f) = 0 := by
  rw [← combined124_checked, Certificate.Integer.Sparse.eval_merge,
    source61_zero f hcross, source201_zero f hcross, add_zero]

theorem combined125_checked : Certificate.Integer.Sparse.merge combined124 source261 = combined125 := by
  decide +kernel

theorem combined125_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined125 (momentValues f) = 0 := by
  rw [← combined125_checked, Certificate.Integer.Sparse.eval_merge,
    combined124_zero f hcross, source261_zero f hcross, add_zero]

theorem combined126_checked : Certificate.Integer.Sparse.merge combined125 source354 = combined126 := by
  decide +kernel

theorem combined126_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined126 (momentValues f) = 0 := by
  rw [← combined126_checked, Certificate.Integer.Sparse.eval_merge,
    combined125_zero f hcross, source354_zero f hcross, add_zero]

theorem combined127_checked : Certificate.Integer.Sparse.merge combined126 source462 = combined127 := by
  decide +kernel

theorem combined127_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined127 (momentValues f) = 0 := by
  rw [← combined127_checked, Certificate.Integer.Sparse.eval_merge,
    combined126_zero f hcross, source462_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined128_checked : Certificate.Integer.Sparse.merge source62 source199 = combined128 := by
  decide +kernel

theorem combined128_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined128 (momentValues f) = 0 := by
  rw [← combined128_checked, Certificate.Integer.Sparse.eval_merge,
    source62_zero f hcross, source199_zero f hcross, add_zero]

theorem combined129_checked : Certificate.Integer.Sparse.merge combined128 source259 = combined129 := by
  decide +kernel

theorem combined129_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined129 (momentValues f) = 0 := by
  rw [← combined129_checked, Certificate.Integer.Sparse.eval_merge,
    combined128_zero f hcross, source259_zero f hcross, add_zero]

theorem combined130_checked : Certificate.Integer.Sparse.merge combined129 source342 = combined130 := by
  decide +kernel

theorem combined130_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined130 (momentValues f) = 0 := by
  rw [← combined130_checked, Certificate.Integer.Sparse.eval_merge,
    combined129_zero f hcross, source342_zero f hcross, add_zero]

theorem combined131_checked : Certificate.Integer.Sparse.merge combined130 source402 = combined131 := by
  decide +kernel

theorem combined131_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined131 (momentValues f) = 0 := by
  rw [← combined131_checked, Certificate.Integer.Sparse.eval_merge,
    combined130_zero f hcross, source402_zero f hcross, add_zero]

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

theorem combined172_checked : Certificate.Integer.Sparse.merge source73 source287 = combined172 := by
  decide +kernel

theorem combined172_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined172 (momentValues f) = 0 := by
  rw [← combined172_checked, Certificate.Integer.Sparse.eval_merge,
    source73_zero f hcross, source287_zero f hcross, add_zero]

theorem combined173_checked : Certificate.Integer.Sparse.merge combined172 source358 = combined173 := by
  decide +kernel

theorem combined173_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined173 (momentValues f) = 0 := by
  rw [← combined173_checked, Certificate.Integer.Sparse.eval_merge,
    combined172_zero f hcross, source358_zero f hcross, add_zero]

theorem combined174_checked : Certificate.Integer.Sparse.merge combined173 source395 = combined174 := by
  decide +kernel

theorem combined174_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined174 (momentValues f) = 0 := by
  rw [← combined174_checked, Certificate.Integer.Sparse.eval_merge,
    combined173_zero f hcross, source395_zero f hcross, add_zero]

theorem combined175_checked : Certificate.Integer.Sparse.merge combined174 source466 = combined175 := by
  decide +kernel

theorem combined175_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined175 (momentValues f) = 0 := by
  rw [← combined175_checked, Certificate.Integer.Sparse.eval_merge,
    combined174_zero f hcross, source466_zero f hcross, add_zero]

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

theorem combined200_checked : Certificate.Integer.Sparse.merge source80 source236 = combined200 := by
  decide +kernel

theorem combined200_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined200 (momentValues f) = 0 := by
  rw [← combined200_checked, Certificate.Integer.Sparse.eval_merge,
    source80_zero f hcross, source236_zero f hcross, add_zero]

theorem combined201_checked : Certificate.Integer.Sparse.merge combined200 source285 = combined201 := by
  decide +kernel

theorem combined201_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined201 (momentValues f) = 0 := by
  rw [← combined201_checked, Certificate.Integer.Sparse.eval_merge,
    combined200_zero f hcross, source285_zero f hcross, add_zero]

theorem combined202_checked : Certificate.Integer.Sparse.merge combined201 source393 = combined202 := by
  decide +kernel

theorem combined202_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined202 (momentValues f) = 0 := by
  rw [← combined202_checked, Certificate.Integer.Sparse.eval_merge,
    combined201_zero f hcross, source393_zero f hcross, add_zero]

theorem combined203_checked : Certificate.Integer.Sparse.merge combined202 source440 = combined203 := by
  decide +kernel

theorem combined203_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined203 (momentValues f) = 0 := by
  rw [← combined203_checked, Certificate.Integer.Sparse.eval_merge,
    combined202_zero f hcross, source440_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined208_checked : Certificate.Integer.Sparse.merge source82 source210 = combined208 := by
  decide +kernel

theorem combined208_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined208 (momentValues f) = 0 := by
  rw [← combined208_checked, Certificate.Integer.Sparse.eval_merge,
    source82_zero f hcross, source210_zero f hcross, add_zero]

theorem combined209_checked : Certificate.Integer.Sparse.merge combined208 source283 = combined209 := by
  decide +kernel

theorem combined209_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined209 (momentValues f) = 0 := by
  rw [← combined209_checked, Certificate.Integer.Sparse.eval_merge,
    combined208_zero f hcross, source283_zero f hcross, add_zero]

theorem combined210_checked : Certificate.Integer.Sparse.merge combined209 source318 = combined210 := by
  decide +kernel

theorem combined210_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined210 (momentValues f) = 0 := by
  rw [← combined210_checked, Certificate.Integer.Sparse.eval_merge,
    combined209_zero f hcross, source318_zero f hcross, add_zero]

theorem combined211_checked : Certificate.Integer.Sparse.merge combined210 source391 = combined211 := by
  decide +kernel

theorem combined211_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined211 (momentValues f) = 0 := by
  rw [← combined211_checked, Certificate.Integer.Sparse.eval_merge,
    combined210_zero f hcross, source391_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined256_checked : Certificate.Integer.Sparse.merge source94 source158 = combined256 := by
  decide +kernel

theorem combined256_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined256 (momentValues f) = 0 := by
  rw [← combined256_checked, Certificate.Integer.Sparse.eval_merge,
    source94_zero f hcross, source158_zero f hcross, add_zero]

theorem combined257_checked : Certificate.Integer.Sparse.merge combined256 source207 = combined257 := by
  decide +kernel

theorem combined257_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined257 (momentValues f) = 0 := by
  rw [← combined257_checked, Certificate.Integer.Sparse.eval_merge,
    combined256_zero f hcross, source207_zero f hcross, add_zero]

theorem combined258_checked : Certificate.Integer.Sparse.merge combined257 source315 = combined258 := by
  decide +kernel

theorem combined258_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined258 (momentValues f) = 0 := by
  rw [← combined258_checked, Certificate.Integer.Sparse.eval_merge,
    combined257_zero f hcross, source315_zero f hcross, add_zero]

theorem combined259_checked : Certificate.Integer.Sparse.merge combined258 source362 = combined259 := by
  decide +kernel

theorem combined259_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined259 (momentValues f) = 0 := by
  rw [← combined259_checked, Certificate.Integer.Sparse.eval_merge,
    combined258_zero f hcross, source362_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined264_checked : Certificate.Integer.Sparse.merge source96 source160 = combined264 := by
  decide +kernel

theorem combined264_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined264 (momentValues f) = 0 := by
  rw [← combined264_checked, Certificate.Integer.Sparse.eval_merge,
    source96_zero f hcross, source160_zero f hcross, add_zero]

theorem combined265_checked : Certificate.Integer.Sparse.merge combined264 source233 = combined265 := by
  decide +kernel

theorem combined265_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined265 (momentValues f) = 0 := by
  rw [← combined265_checked, Certificate.Integer.Sparse.eval_merge,
    combined264_zero f hcross, source233_zero f hcross, add_zero]

theorem combined266_checked : Certificate.Integer.Sparse.merge combined265 source364 = combined266 := by
  decide +kernel

theorem combined266_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined266 (momentValues f) = 0 := by
  rw [← combined266_checked, Certificate.Integer.Sparse.eval_merge,
    combined265_zero f hcross, source364_zero f hcross, add_zero]

theorem combined267_checked : Certificate.Integer.Sparse.merge combined266 source437 = combined267 := by
  decide +kernel

theorem combined267_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined267 (momentValues f) = 0 := by
  rw [← combined267_checked, Certificate.Integer.Sparse.eval_merge,
    combined266_zero f hcross, source437_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined316_checked : Certificate.Integer.Sparse.merge source109 source166 = combined316 := by
  decide +kernel

theorem combined316_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined316 (momentValues f) = 0 := by
  rw [← combined316_checked, Certificate.Integer.Sparse.eval_merge,
    source109_zero f hcross, source166_zero f hcross, add_zero]

theorem combined317_checked : Certificate.Integer.Sparse.merge combined316 source353 = combined317 := by
  decide +kernel

theorem combined317_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined317 (momentValues f) = 0 := by
  rw [← combined317_checked, Certificate.Integer.Sparse.eval_merge,
    combined316_zero f hcross, source353_zero f hcross, add_zero]

theorem combined318_checked : Certificate.Integer.Sparse.merge combined317 source370 = combined318 := by
  decide +kernel

theorem combined318_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined318 (momentValues f) = 0 := by
  rw [← combined318_checked, Certificate.Integer.Sparse.eval_merge,
    combined317_zero f hcross, source370_zero f hcross, add_zero]

theorem combined319_checked : Certificate.Integer.Sparse.merge combined318 source461 = combined319 := by
  decide +kernel

theorem combined319_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined319 (momentValues f) = 0 := by
  rw [← combined319_checked, Certificate.Integer.Sparse.eval_merge,
    combined318_zero f hcross, source461_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined439_checked : Certificate.Integer.Sparse.merge combined438 combined319 = combined439 := by
  decide +kernel

theorem combined439_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined439 (momentValues f) = 0 := by
  rw [← combined439_checked, Certificate.Integer.Sparse.eval_merge,
    combined438_zero_e f hcross, combined319_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined440_checked : Certificate.Integer.Sparse.merge combined439 combined259 = combined440 := by
  decide +kernel

theorem combined440_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined440 (momentValues f) = 0 := by
  rw [← combined440_checked, Certificate.Integer.Sparse.eval_merge,
    combined439_zero f hcross, combined259_zero f hcross, add_zero]

theorem combined441_checked : Certificate.Integer.Sparse.merge combined440 combined267 = combined441 := by
  decide +kernel

theorem combined441_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined441 (momentValues f) = 0 := by
  rw [← combined441_checked, Certificate.Integer.Sparse.eval_merge,
    combined440_zero f hcross, combined267_zero f hcross, add_zero]

theorem combined442_checked : Certificate.Integer.Sparse.merge combined441 source25 = combined442 := by
  decide +kernel

theorem combined442_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined442 (momentValues f) = 0 := by
  rw [← combined442_checked, Certificate.Integer.Sparse.eval_merge,
    combined441_zero f hcross, source25_zero f hcross, add_zero]

theorem combined443_checked : Certificate.Integer.Sparse.merge combined442 source27 = combined443 := by
  decide +kernel

theorem combined443_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined443 (momentValues f) = 0 := by
  rw [← combined443_checked, Certificate.Integer.Sparse.eval_merge,
    combined442_zero f hcross, source27_zero f hcross, add_zero]

theorem combined444_checked : Certificate.Integer.Sparse.merge combined443 combined35 = combined444 := by
  decide +kernel

theorem combined444_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined444 (momentValues f) = 0 := by
  rw [← combined444_checked, Certificate.Integer.Sparse.eval_merge,
    combined443_zero f hcross, combined35_zero f hcross, add_zero]

theorem combined445_checked : Certificate.Integer.Sparse.merge combined444 combined83 = combined445 := by
  decide +kernel

theorem combined445_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined445 (momentValues f) = 0 := by
  rw [← combined445_checked, Certificate.Integer.Sparse.eval_merge,
    combined444_zero f hcross, combined83_zero f hcross, add_zero]

theorem combined446_checked : Certificate.Integer.Sparse.merge combined445 combined211 = combined446 := by
  decide +kernel

theorem combined446_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined446 (momentValues f) = 0 := by
  rw [← combined446_checked, Certificate.Integer.Sparse.eval_merge,
    combined445_zero f hcross, combined211_zero f hcross, add_zero]

theorem combined447_checked : Certificate.Integer.Sparse.merge combined446 combined79 = combined447 := by
  decide +kernel

theorem combined447_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined447 (momentValues f) = 0 := by
  rw [← combined447_checked, Certificate.Integer.Sparse.eval_merge,
    combined446_zero f hcross, combined79_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined448_checked : Certificate.Integer.Sparse.merge combined447 combined27 = combined448 := by
  decide +kernel

theorem combined448_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined448 (momentValues f) = 0 := by
  rw [← combined448_checked, Certificate.Integer.Sparse.eval_merge,
    combined447_zero f hcross, combined27_zero f hcross, add_zero]

theorem combined449_checked : Certificate.Integer.Sparse.merge combined448 combined75 = combined449 := by
  decide +kernel

theorem combined449_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined449 (momentValues f) = 0 := by
  rw [← combined449_checked, Certificate.Integer.Sparse.eval_merge,
    combined448_zero f hcross, combined75_zero f hcross, add_zero]

theorem combined450_checked : Certificate.Integer.Sparse.merge combined449 combined31 = combined450 := by
  decide +kernel

theorem combined450_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined450 (momentValues f) = 0 := by
  rw [← combined450_checked, Certificate.Integer.Sparse.eval_merge,
    combined449_zero f hcross, combined31_zero f hcross, add_zero]

theorem combined451_checked : Certificate.Integer.Sparse.merge combined450 combined203 = combined451 := by
  decide +kernel

theorem combined451_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined451 (momentValues f) = 0 := by
  rw [← combined451_checked, Certificate.Integer.Sparse.eval_merge,
    combined450_zero f hcross, combined203_zero f hcross, add_zero]

theorem combined452_checked : Certificate.Integer.Sparse.merge combined451 combined175 = combined452 := by
  decide +kernel

theorem combined452_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined452 (momentValues f) = 0 := by
  rw [← combined452_checked, Certificate.Integer.Sparse.eval_merge,
    combined451_zero f hcross, combined175_zero f hcross, add_zero]

theorem combined453_checked : Certificate.Integer.Sparse.merge combined452 combined127 = combined453 := by
  decide +kernel

theorem combined453_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined453 (momentValues f) = 0 := by
  rw [← combined453_checked, Certificate.Integer.Sparse.eval_merge,
    combined452_zero f hcross, combined127_zero f hcross, add_zero]

theorem combined454_checked : Certificate.Integer.Sparse.merge combined453 combined123 = combined454 := by
  decide +kernel

theorem combined454_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined454 (momentValues f) = 0 := by
  rw [← combined454_checked, Certificate.Integer.Sparse.eval_merge,
    combined453_zero f hcross, combined123_zero f hcross, add_zero]

theorem combined455_checked : Certificate.Integer.Sparse.merge combined454 combined131 = combined455 := by
  decide +kernel

theorem combined455_zero_e_oai (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined455 (momentValues f) = 0 := by
  rw [← combined455_checked, Certificate.Integer.Sparse.eval_merge,
    combined454_zero f hcross, combined131_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

theorem solution : type_of% @OAI.MUB6.TaoCertificate.combined455_zero_e_oai := @OAI.MUB6.TaoCertificate.combined455_zero_e_oai
