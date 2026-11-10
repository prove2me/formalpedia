-- Prove2me | solution 1 for OAI.MUB6.TaoCertificate.combined414_zero_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:00:06.090392+00:00
-- url     : https://prove2.me/submissions/8920cd5b-d923-4b4a-ab66-dc0ce9d79bc1

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E161
import Definitions.Def_OAIQ106E163
import Definitions.Def_OAIQ106E164
import Definitions.Def_OAIQ106E167
import Theorems.Thm_OAI_MUB6_TaoCertificate_combined396_zero_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source2_checked : normalize (row ![-2, 0, 0, 2, 0, 0] ![-2, 0, 0, 2, 0, 0] (6, 0)) = source2 := by
  decide +kernel

theorem source2_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source2 (momentValues f) = 0 := by
  rw [← source2_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source4_checked : normalize (row ![-2, 2, 0, 0, 0, 0] ![-2, 2, 0, 0, 0, 0] (6, 0)) = source4 := by
  decide +kernel

theorem source4_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source4 (momentValues f) = 0 := by
  rw [← source4_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

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

theorem source13_checked : normalize (row ![0, 0, 0, -2, 2, 0] ![0, 0, 0, -2, 2, 0] (6, 0)) = source13 := by
  decide +kernel

theorem source13_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source13 (momentValues f) = 0 := by
  rw [← source13_checked, eval_normalize]
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

theorem source85_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 1, 0, -1, 1, -1] (-12, 0)) = source85 := by
  decide +kernel

theorem source85_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source85 (momentValues f) = 0 := by
  rw [← source85_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source87_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 1, 1, -1, -1, 0] (-12, 0)) = source87 := by
  decide +kernel

theorem source87_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source87 (momentValues f) = 0 := by
  rw [← source87_checked, eval_normalize]
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

theorem source89_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 1, 1, 0, -1, -1] (-12, 0)) = source89 := by
  decide +kernel

theorem source89_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source89 (momentValues f) = 0 := by
  rw [← source89_checked, eval_normalize]
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

theorem source99_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![1, -1, 1, -1, 0, 0] (-12, 0)) = source99 := by
  decide +kernel

theorem source99_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source99 (momentValues f) = 0 := by
  rw [← source99_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source100_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![1, -1, 1, 0, -1, 0] (-12, 0)) = source100 := by
  decide +kernel

theorem source100_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source100 (momentValues f) = 0 := by
  rw [← source100_checked, eval_normalize]
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

theorem source111_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![1, 0, 1, -1, -1, 0] (-12, 0)) = source111 := by
  decide +kernel

theorem source111_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source111 (momentValues f) = 0 := by
  rw [← source111_checked, eval_normalize]
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

theorem source112_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![1, 0, 1, -1, 0, -1] (-12, 0)) = source112 := by
  decide +kernel

theorem source112_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source112 (momentValues f) = 0 := by
  rw [← source112_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source113_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![1, 0, 1, 0, -1, -1] (-12, 0)) = source113 := by
  decide +kernel

theorem source113_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source113 (momentValues f) = 0 := by
  rw [← source113_checked, eval_normalize]
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

theorem source132_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source132 := by
  decide +kernel

theorem source132_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source132 (momentValues f) = 0 := by
  rw [← source132_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source134_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source134 := by
  decide +kernel

theorem source134_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source134 (momentValues f) = 0 := by
  rw [← source134_checked, eval_normalize]
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

theorem source138_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source138 := by
  decide +kernel

theorem source138_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source138 (momentValues f) = 0 := by
  rw [← source138_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source140_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![-1, 0, 1, 0, 0, 0] (0, -3)) = source140 := by
  decide +kernel

theorem source140_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source140 (momentValues f) = 0 := by
  rw [← source140_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source142_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source142 := by
  decide +kernel

theorem source142_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source142 (momentValues f) = 0 := by
  rw [← source142_checked, eval_normalize]
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

theorem source147_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![1, 0, 0, -1, 0, 0] (3, 3)) = source147 := by
  decide +kernel

theorem source147_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source147 (momentValues f) = 0 := by
  rw [← source147_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source149_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![1, 0, 0, -1, 0, 0] (0, -3)) = source149 := by
  decide +kernel

theorem source149_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source149 (momentValues f) = 0 := by
  rw [← source149_checked, eval_normalize]
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

theorem source159_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![1, 0, 0, 0, -1, 0] (3, 3)) = source159 := by
  decide +kernel

theorem source159_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source159 (momentValues f) = 0 := by
  rw [← source159_checked, eval_normalize]
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

theorem source161_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![1, 0, 0, 0, -1, 0] (0, -3)) = source161 := by
  decide +kernel

theorem source161_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source161 (momentValues f) = 0 := by
  rw [← source161_checked, eval_normalize]
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

theorem source171_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source171 := by
  decide +kernel

theorem source171_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source171 (momentValues f) = 0 := by
  rw [← source171_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source173_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source173 := by
  decide +kernel

theorem source173_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source173 (momentValues f) = 0 := by
  rw [← source173_checked, eval_normalize]
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

theorem source179_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source179 := by
  decide +kernel

theorem source179_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source179 (momentValues f) = 0 := by
  rw [← source179_checked, eval_normalize]
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

theorem source198_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, -1, 1, 0, 0, 0] (3, 3)) = source198 := by
  decide +kernel

theorem source198_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source198 (momentValues f) = 0 := by
  rw [← source198_checked, eval_normalize]
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

theorem source202_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, -1, 1, 0, 0, 0] (0, -3)) = source202 := by
  decide +kernel

theorem source202_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source202 (momentValues f) = 0 := by
  rw [← source202_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source205_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![0, 1, 0, -1, 0, 0] (0, -3)) = source205 := by
  decide +kernel

theorem source205_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source205 (momentValues f) = 0 := by
  rw [← source205_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source206_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![0, -1, 0, 1, 0, 0] (0, -3)) = source206 := by
  decide +kernel

theorem source206_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source206 (momentValues f) = 0 := by
  rw [← source206_checked, eval_normalize]
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

theorem source208_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![0, -1, 0, 1, 0, 0] (3, 3)) = source208 := by
  decide +kernel

theorem source208_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source208 (momentValues f) = 0 := by
  rw [← source208_checked, eval_normalize]
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

theorem source217_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![0, 1, 0, 0, -1, 0] (0, -3)) = source217 := by
  decide +kernel

theorem source217_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source217 (momentValues f) = 0 := by
  rw [← source217_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source218_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![0, -1, 0, 0, 1, 0] (0, -3)) = source218 := by
  decide +kernel

theorem source218_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source218 (momentValues f) = 0 := by
  rw [← source218_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source220_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![0, -1, 0, 0, 1, 0] (3, 3)) = source220 := by
  decide +kernel

theorem source220_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source220 (momentValues f) = 0 := by
  rw [← source220_checked, eval_normalize]
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

theorem source226_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, -1, 0, 0, 1, 0] (3, 3)) = source226 := by
  decide +kernel

theorem source226_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source226 (momentValues f) = 0 := by
  rw [← source226_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source230_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source230 := by
  decide +kernel

theorem source230_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source230 (momentValues f) = 0 := by
  rw [← source230_checked, eval_normalize]
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

theorem source232_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source232 := by
  decide +kernel

theorem source232_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source232 (momentValues f) = 0 := by
  rw [← source232_checked, eval_normalize]
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

theorem source240_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![1, 0, -1, 0, 0, 0] (0, -3)) = source240 := by
  decide +kernel

theorem source240_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source240 (momentValues f) = 0 := by
  rw [← source240_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source242_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![1, 0, -1, 0, 0, 0] (3, 3)) = source242 := by
  decide +kernel

theorem source242_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source242 (momentValues f) = 0 := by
  rw [← source242_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source246_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![1, 0, -1, 0, 0, 0] (0, -3)) = source246 := by
  decide +kernel

theorem source246_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source246 (momentValues f) = 0 := by
  rw [← source246_checked, eval_normalize]
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

theorem source248_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![1, 0, -1, 0, 0, 0] (3, 3)) = source248 := by
  decide +kernel

theorem source248_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source248 (momentValues f) = 0 := by
  rw [← source248_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source250_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![1, 0, -1, 0, 0, 0] (3, 3)) = source250 := by
  decide +kernel

theorem source250_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source250 (momentValues f) = 0 := by
  rw [← source250_checked, eval_normalize]
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

theorem source258_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 1, -1, 0, 0, 0] (0, -3)) = source258 := by
  decide +kernel

theorem source258_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source258 (momentValues f) = 0 := by
  rw [← source258_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source262_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 1, -1, 0, 0, 0] (3, 3)) = source262 := by
  decide +kernel

theorem source262_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source262 (momentValues f) = 0 := by
  rw [← source262_checked, eval_normalize]
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

theorem source303_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source303 := by
  decide +kernel

theorem source303_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source303 (momentValues f) = 0 := by
  rw [← source303_checked, eval_normalize]
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

theorem source305_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source305 := by
  decide +kernel

theorem source305_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source305 (momentValues f) = 0 := by
  rw [← source305_checked, eval_normalize]
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

theorem source313_checked : normalize (row ![1, -1, 1, -1, 0, 0] ![0, -1, 0, 1, 0, 0] (0, -3)) = source313 := by
  decide +kernel

theorem source313_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source313 (momentValues f) = 0 := by
  rw [← source313_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source314_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![0, 1, 0, -1, 0, 0] (3, 3)) = source314 := by
  decide +kernel

theorem source314_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source314 (momentValues f) = 0 := by
  rw [← source314_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source316_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![0, 1, 0, -1, 0, 0] (0, -3)) = source316 := by
  decide +kernel

theorem source316_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source316 (momentValues f) = 0 := by
  rw [← source316_checked, eval_normalize]
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

theorem source339_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![0, 0, 0, 1, -1, 0] (0, -3)) = source339 := by
  decide +kernel

theorem source339_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source339 (momentValues f) = 0 := by
  rw [← source339_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source340_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![0, 0, 0, -1, 1, 0] (0, -3)) = source340 := by
  decide +kernel

theorem source340_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source340 (momentValues f) = 0 := by
  rw [← source340_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source343_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 0, 0, 1, -1, 0] (3, 3)) = source343 := by
  decide +kernel

theorem source343_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source343 (momentValues f) = 0 := by
  rw [← source343_checked, eval_normalize]
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

theorem source351_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source351 := by
  decide +kernel

theorem source351_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source351 (momentValues f) = 0 := by
  rw [← source351_checked, eval_normalize]
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

theorem source357_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source357 := by
  decide +kernel

theorem source357_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source357 (momentValues f) = 0 := by
  rw [← source357_checked, eval_normalize]
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

theorem source363_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source363 := by
  decide +kernel

theorem source363_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source363 (momentValues f) = 0 := by
  rw [← source363_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source365_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source365 := by
  decide +kernel

theorem source365_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source365 (momentValues f) = 0 := by
  rw [← source365_checked, eval_normalize]
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

theorem source373_checked : normalize (row ![1, -1, 1, 0, -1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source373 := by
  decide +kernel

theorem source373_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source373 (momentValues f) = 0 := by
  rw [← source373_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source374_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![0, 1, 0, 0, -1, 0] (3, 3)) = source374 := by
  decide +kernel

theorem source374_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source374 (momentValues f) = 0 := by
  rw [← source374_checked, eval_normalize]
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

theorem source376_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![0, 1, 0, 0, -1, 0] (3, 3)) = source376 := by
  decide +kernel

theorem source376_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source376 (momentValues f) = 0 := by
  rw [← source376_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source382_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 1, 0, 0, -1, 0] (0, -3)) = source382 := by
  decide +kernel

theorem source382_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source382 (momentValues f) = 0 := by
  rw [← source382_checked, eval_normalize]
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

theorem source399_checked : normalize (row ![1, 0, 1, -1, -1, 0] ![0, 0, 0, -1, 1, 0] (3, 3)) = source399 := by
  decide +kernel

theorem source399_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source399 (momentValues f) = 0 := by
  rw [← source399_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source41_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![-1, 0, 0, 1, 1, -1] (-12, 0)) = source41 := by
  decide +kernel

theorem source41_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source41 (momentValues f) = 0 := by
  rw [← source41_checked, eval_normalize]
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

theorem source400_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![0, 0, 0, 1, -1, 0] (3, 3)) = source400 := by
  decide +kernel

theorem source400_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source400 (momentValues f) = 0 := by
  rw [← source400_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source403_checked : normalize (row ![0, 1, 1, -1, -1, 0] ![0, 0, 0, -1, 1, 0] (0, -3)) = source403 := by
  decide +kernel

theorem source403_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source403 (momentValues f) = 0 := by
  rw [← source403_checked, eval_normalize]
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

theorem source411_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source411 := by
  decide +kernel

theorem source411_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source411 (momentValues f) = 0 := by
  rw [← source411_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source415_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source415 := by
  decide +kernel

theorem source415_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source415 (momentValues f) = 0 := by
  rw [← source415_checked, eval_normalize]
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

theorem source423_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source423 := by
  decide +kernel

theorem source423_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source423 (momentValues f) = 0 := by
  rw [← source423_checked, eval_normalize]
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

theorem source425_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source425 := by
  decide +kernel

theorem source425_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source425 (momentValues f) = 0 := by
  rw [← source425_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source431_checked : normalize (row ![-1, 0, 0, 1, 1, -1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source431 := by
  decide +kernel

theorem source431_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source431 (momentValues f) = 0 := by
  rw [← source431_checked, eval_normalize]
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

theorem source434_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source434 := by
  decide +kernel

theorem source434_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source434 (momentValues f) = 0 := by
  rw [← source434_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source436_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source436 := by
  decide +kernel

theorem source436_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source436 (momentValues f) = 0 := by
  rw [← source436_checked, eval_normalize]
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

theorem source459_checked : normalize (row ![1, 0, 1, -1, 0, -1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source459 := by
  decide +kernel

theorem source459_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source459 (momentValues f) = 0 := by
  rw [← source459_checked, eval_normalize]
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

theorem source465_checked : normalize (row ![0, 1, 0, -1, 1, -1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source465 := by
  decide +kernel

theorem source465_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source465 (momentValues f) = 0 := by
  rw [← source465_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source471_checked : normalize (row ![1, 0, 1, 0, -1, -1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source471 := by
  decide +kernel

theorem source471_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source471 (momentValues f) = 0 := by
  rw [← source471_checked, eval_normalize]
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

theorem source475_checked : normalize (row ![0, 1, 1, 0, -1, -1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source475 := by
  decide +kernel

theorem source475_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source475 (momentValues f) = 0 := by
  rw [← source475_checked, eval_normalize]
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

theorem source51_checked : normalize (row ![-1, 1, 0, -1, 0, 1] ![-1, 1, 0, -1, 0, 1] (-12, 0)) = source51 := by
  decide +kernel

theorem source51_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source51 (momentValues f) = 0 := by
  rw [← source51_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source52_checked : normalize (row ![-1, 1, 0, -1, 1, 0] ![-1, 1, 0, -1, 1, 0] (-12, 0)) = source52 := by
  decide +kernel

theorem source52_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source52 (momentValues f) = 0 := by
  rw [← source52_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source53_checked : normalize (row ![-1, 1, 0, 0, -1, 1] ![-1, 1, 0, 0, -1, 1] (-12, 0)) = source53 := by
  decide +kernel

theorem source53_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source53 (momentValues f) = 0 := by
  rw [← source53_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source54_checked : normalize (row ![-1, 1, 0, 0, 1, -1] ![-1, 1, 0, 0, 1, -1] (-12, 0)) = source54 := by
  decide +kernel

theorem source54_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source54 (momentValues f) = 0 := by
  rw [← source54_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source55_checked : normalize (row ![-1, 1, 0, 1, -1, 0] ![-1, 1, 0, 1, -1, 0] (-12, 0)) = source55 := by
  decide +kernel

theorem source55_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source55 (momentValues f) = 0 := by
  rw [← source55_checked, eval_normalize]
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

theorem source56_checked : normalize (row ![-1, 1, 0, 1, 0, -1] ![-1, 1, 0, 1, 0, -1] (-12, 0)) = source56 := by
  decide +kernel

theorem source56_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source56 (momentValues f) = 0 := by
  rw [← source56_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined44_checked : Certificate.Integer.Sparse.merge source41 source179 = combined44 := by
  decide +kernel

theorem combined44_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined44 (momentValues f) = 0 := by
  rw [← combined44_checked, Certificate.Integer.Sparse.eval_merge,
    source41_zero f hcross, source179_zero f hcross, add_zero]

theorem combined45_checked : Certificate.Integer.Sparse.merge combined44 source340 = combined45 := by
  decide +kernel

theorem combined45_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined45 (momentValues f) = 0 := by
  rw [← combined45_checked, Certificate.Integer.Sparse.eval_merge,
    combined44_zero f hcross, source340_zero f hcross, add_zero]

theorem combined46_checked : Certificate.Integer.Sparse.merge combined45 source400 = combined46 := by
  decide +kernel

theorem combined46_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined46 (momentValues f) = 0 := by
  rw [← combined46_checked, Certificate.Integer.Sparse.eval_merge,
    combined45_zero f hcross, source400_zero f hcross, add_zero]

theorem combined47_checked : Certificate.Integer.Sparse.merge combined46 source431 = combined47 := by
  decide +kernel

theorem combined47_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined47 (momentValues f) = 0 := by
  rw [← combined47_checked, Certificate.Integer.Sparse.eval_merge,
    combined46_zero f hcross, source431_zero f hcross, add_zero]

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

theorem combined84_checked : Certificate.Integer.Sparse.merge source51 source149 = combined84 := by
  decide +kernel

theorem combined84_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined84 (momentValues f) = 0 := by
  rw [← combined84_checked, Certificate.Integer.Sparse.eval_merge,
    source51_zero f hcross, source149_zero f hcross, add_zero]

theorem combined85_checked : Certificate.Integer.Sparse.merge combined84 source230 = combined85 := by
  decide +kernel

theorem combined85_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined85 (momentValues f) = 0 := by
  rw [← combined85_checked, Certificate.Integer.Sparse.eval_merge,
    combined84_zero f hcross, source230_zero f hcross, add_zero]

theorem combined86_checked : Certificate.Integer.Sparse.merge combined85 source305 = combined86 := by
  decide +kernel

theorem combined86_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined86 (momentValues f) = 0 := by
  rw [← combined86_checked, Certificate.Integer.Sparse.eval_merge,
    combined85_zero f hcross, source305_zero f hcross, add_zero]

theorem combined87_checked : Certificate.Integer.Sparse.merge combined86 source434 = combined87 := by
  decide +kernel

theorem combined87_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined87 (momentValues f) = 0 := by
  rw [← combined87_checked, Certificate.Integer.Sparse.eval_merge,
    combined86_zero f hcross, source434_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined88_checked : Certificate.Integer.Sparse.merge source52 source147 = combined88 := by
  decide +kernel

theorem combined88_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined88 (momentValues f) = 0 := by
  rw [← combined88_checked, Certificate.Integer.Sparse.eval_merge,
    source52_zero f hcross, source147_zero f hcross, add_zero]

theorem combined89_checked : Certificate.Integer.Sparse.merge combined88 source218 = combined89 := by
  decide +kernel

theorem combined89_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined89 (momentValues f) = 0 := by
  rw [← combined89_checked, Certificate.Integer.Sparse.eval_merge,
    combined88_zero f hcross, source218_zero f hcross, add_zero]

theorem combined90_checked : Certificate.Integer.Sparse.merge combined89 source303 = combined90 := by
  decide +kernel

theorem combined90_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined90 (momentValues f) = 0 := by
  rw [← combined90_checked, Certificate.Integer.Sparse.eval_merge,
    combined89_zero f hcross, source303_zero f hcross, add_zero]

theorem combined91_checked : Certificate.Integer.Sparse.merge combined90 source374 = combined91 := by
  decide +kernel

theorem combined91_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined91 (momentValues f) = 0 := by
  rw [← combined91_checked, Certificate.Integer.Sparse.eval_merge,
    combined90_zero f hcross, source374_zero f hcross, add_zero]

theorem combined92_checked : Certificate.Integer.Sparse.merge source53 source161 = combined92 := by
  decide +kernel

theorem combined92_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined92 (momentValues f) = 0 := by
  rw [← combined92_checked, Certificate.Integer.Sparse.eval_merge,
    source53_zero f hcross, source161_zero f hcross, add_zero]

theorem combined93_checked : Certificate.Integer.Sparse.merge combined92 source232 = combined93 := by
  decide +kernel

theorem combined93_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined93 (momentValues f) = 0 := by
  rw [← combined93_checked, Certificate.Integer.Sparse.eval_merge,
    combined92_zero f hcross, source232_zero f hcross, add_zero]

theorem combined94_checked : Certificate.Integer.Sparse.merge combined93 source365 = combined94 := by
  decide +kernel

theorem combined94_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined94 (momentValues f) = 0 := by
  rw [← combined94_checked, Certificate.Integer.Sparse.eval_merge,
    combined93_zero f hcross, source365_zero f hcross, add_zero]

theorem combined95_checked : Certificate.Integer.Sparse.merge combined94 source436 = combined95 := by
  decide +kernel

theorem combined95_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined95 (momentValues f) = 0 := by
  rw [← combined95_checked, Certificate.Integer.Sparse.eval_merge,
    combined94_zero f hcross, source436_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined96_checked : Certificate.Integer.Sparse.merge source54 source173 = combined96 := by
  decide +kernel

theorem combined96_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined96 (momentValues f) = 0 := by
  rw [← combined96_checked, Certificate.Integer.Sparse.eval_merge,
    source54_zero f hcross, source173_zero f hcross, add_zero]

theorem combined97_checked : Certificate.Integer.Sparse.merge combined96 source220 = combined97 := by
  decide +kernel

theorem combined97_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined97 (momentValues f) = 0 := by
  rw [← combined97_checked, Certificate.Integer.Sparse.eval_merge,
    combined96_zero f hcross, source220_zero f hcross, add_zero]

theorem combined98_checked : Certificate.Integer.Sparse.merge combined97 source376 = combined98 := by
  decide +kernel

theorem combined98_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined98 (momentValues f) = 0 := by
  rw [← combined98_checked, Certificate.Integer.Sparse.eval_merge,
    combined97_zero f hcross, source376_zero f hcross, add_zero]

theorem combined99_checked : Certificate.Integer.Sparse.merge combined98 source425 = combined99 := by
  decide +kernel

theorem combined99_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined99 (momentValues f) = 0 := by
  rw [← combined99_checked, Certificate.Integer.Sparse.eval_merge,
    combined98_zero f hcross, source425_zero f hcross, add_zero]

theorem combined100_checked : Certificate.Integer.Sparse.merge source55 source159 = combined100 := by
  decide +kernel

theorem combined100_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined100 (momentValues f) = 0 := by
  rw [← combined100_checked, Certificate.Integer.Sparse.eval_merge,
    source55_zero f hcross, source159_zero f hcross, add_zero]

theorem combined101_checked : Certificate.Integer.Sparse.merge combined100 source206 = combined101 := by
  decide +kernel

theorem combined101_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined101 (momentValues f) = 0 := by
  rw [← combined101_checked, Certificate.Integer.Sparse.eval_merge,
    combined100_zero f hcross, source206_zero f hcross, add_zero]

theorem combined102_checked : Certificate.Integer.Sparse.merge combined101 source314 = combined102 := by
  decide +kernel

theorem combined102_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined102 (momentValues f) = 0 := by
  rw [← combined102_checked, Certificate.Integer.Sparse.eval_merge,
    combined101_zero f hcross, source314_zero f hcross, add_zero]

theorem combined103_checked : Certificate.Integer.Sparse.merge combined102 source363 = combined103 := by
  decide +kernel

theorem combined103_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined103 (momentValues f) = 0 := by
  rw [← combined103_checked, Certificate.Integer.Sparse.eval_merge,
    combined102_zero f hcross, source363_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined104_checked : Certificate.Integer.Sparse.merge source56 source171 = combined104 := by
  decide +kernel

theorem combined104_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined104 (momentValues f) = 0 := by
  rw [← combined104_checked, Certificate.Integer.Sparse.eval_merge,
    source56_zero f hcross, source171_zero f hcross, add_zero]

theorem combined105_checked : Certificate.Integer.Sparse.merge combined104 source208 = combined105 := by
  decide +kernel

theorem combined105_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined105 (momentValues f) = 0 := by
  rw [← combined105_checked, Certificate.Integer.Sparse.eval_merge,
    combined104_zero f hcross, source208_zero f hcross, add_zero]

theorem combined106_checked : Certificate.Integer.Sparse.merge combined105 source316 = combined106 := by
  decide +kernel

theorem combined106_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined106 (momentValues f) = 0 := by
  rw [← combined106_checked, Certificate.Integer.Sparse.eval_merge,
    combined105_zero f hcross, source316_zero f hcross, add_zero]

theorem combined107_checked : Certificate.Integer.Sparse.merge combined106 source423 = combined107 := by
  decide +kernel

theorem combined107_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined107 (momentValues f) = 0 := by
  rw [← combined107_checked, Certificate.Integer.Sparse.eval_merge,
    combined106_zero f hcross, source423_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined220_checked : Certificate.Integer.Sparse.merge source85 source226 = combined220 := by
  decide +kernel

theorem combined220_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined220 (momentValues f) = 0 := by
  rw [← combined220_checked, Certificate.Integer.Sparse.eval_merge,
    source85_zero f hcross, source226_zero f hcross, add_zero]

theorem combined221_checked : Certificate.Integer.Sparse.merge combined220 source357 = combined221 := by
  decide +kernel

theorem combined221_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined221 (momentValues f) = 0 := by
  rw [← combined221_checked, Certificate.Integer.Sparse.eval_merge,
    combined220_zero f hcross, source357_zero f hcross, add_zero]

theorem combined222_checked : Certificate.Integer.Sparse.merge combined221 source382 = combined222 := by
  decide +kernel

theorem combined222_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined222 (momentValues f) = 0 := by
  rw [← combined222_checked, Certificate.Integer.Sparse.eval_merge,
    combined221_zero f hcross, source382_zero f hcross, add_zero]

theorem combined223_checked : Certificate.Integer.Sparse.merge combined222 source465 = combined223 := by
  decide +kernel

theorem combined223_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined223 (momentValues f) = 0 := by
  rw [← combined223_checked, Certificate.Integer.Sparse.eval_merge,
    combined222_zero f hcross, source465_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined228_checked : Certificate.Integer.Sparse.merge source87 source198 = combined228 := by
  decide +kernel

theorem combined228_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined228 (momentValues f) = 0 := by
  rw [← combined228_checked, Certificate.Integer.Sparse.eval_merge,
    source87_zero f hcross, source198_zero f hcross, add_zero]

theorem combined229_checked : Certificate.Integer.Sparse.merge combined228 source258 = combined229 := by
  decide +kernel

theorem combined229_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined229 (momentValues f) = 0 := by
  rw [← combined229_checked, Certificate.Integer.Sparse.eval_merge,
    combined228_zero f hcross, source258_zero f hcross, add_zero]

theorem combined230_checked : Certificate.Integer.Sparse.merge combined229 source343 = combined230 := by
  decide +kernel

theorem combined230_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined230 (momentValues f) = 0 := by
  rw [← combined230_checked, Certificate.Integer.Sparse.eval_merge,
    combined229_zero f hcross, source343_zero f hcross, add_zero]

theorem combined231_checked : Certificate.Integer.Sparse.merge combined230 source403 = combined231 := by
  decide +kernel

theorem combined231_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined231 (momentValues f) = 0 := by
  rw [← combined231_checked, Certificate.Integer.Sparse.eval_merge,
    combined230_zero f hcross, source403_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined236_checked : Certificate.Integer.Sparse.merge source89 source202 = combined236 := by
  decide +kernel

theorem combined236_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined236 (momentValues f) = 0 := by
  rw [← combined236_checked, Certificate.Integer.Sparse.eval_merge,
    source89_zero f hcross, source202_zero f hcross, add_zero]

theorem combined237_checked : Certificate.Integer.Sparse.merge combined236 source262 = combined237 := by
  decide +kernel

theorem combined237_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined237 (momentValues f) = 0 := by
  rw [← combined237_checked, Certificate.Integer.Sparse.eval_merge,
    combined236_zero f hcross, source262_zero f hcross, add_zero]

theorem combined238_checked : Certificate.Integer.Sparse.merge combined237 source415 = combined238 := by
  decide +kernel

theorem combined238_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined238 (momentValues f) = 0 := by
  rw [← combined238_checked, Certificate.Integer.Sparse.eval_merge,
    combined237_zero f hcross, source415_zero f hcross, add_zero]

theorem combined239_checked : Certificate.Integer.Sparse.merge combined238 source475 = combined239 := by
  decide +kernel

theorem combined239_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined239 (momentValues f) = 0 := by
  rw [← combined239_checked, Certificate.Integer.Sparse.eval_merge,
    combined238_zero f hcross, source475_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined276_checked : Certificate.Integer.Sparse.merge source99 source132 = combined276 := by
  decide +kernel

theorem combined276_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined276 (momentValues f) = 0 := by
  rw [← combined276_checked, Certificate.Integer.Sparse.eval_merge,
    source99_zero f hcross, source132_zero f hcross, add_zero]

theorem combined277_checked : Certificate.Integer.Sparse.merge combined276 source205 = combined277 := by
  decide +kernel

theorem combined277_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined277 (momentValues f) = 0 := by
  rw [← combined277_checked, Certificate.Integer.Sparse.eval_merge,
    combined276_zero f hcross, source205_zero f hcross, add_zero]

theorem combined278_checked : Certificate.Integer.Sparse.merge combined277 source240 = combined278 := by
  decide +kernel

theorem combined278_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined278 (momentValues f) = 0 := by
  rw [← combined278_checked, Certificate.Integer.Sparse.eval_merge,
    combined277_zero f hcross, source240_zero f hcross, add_zero]

theorem combined279_checked : Certificate.Integer.Sparse.merge combined278 source313 = combined279 := by
  decide +kernel

theorem combined279_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined279 (momentValues f) = 0 := by
  rw [← combined279_checked, Certificate.Integer.Sparse.eval_merge,
    combined278_zero f hcross, source313_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined280_checked : Certificate.Integer.Sparse.merge source100 source134 = combined280 := by
  decide +kernel

theorem combined280_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined280 (momentValues f) = 0 := by
  rw [← combined280_checked, Certificate.Integer.Sparse.eval_merge,
    source100_zero f hcross, source134_zero f hcross, add_zero]

theorem combined281_checked : Certificate.Integer.Sparse.merge combined280 source217 = combined281 := by
  decide +kernel

theorem combined281_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined281 (momentValues f) = 0 := by
  rw [← combined281_checked, Certificate.Integer.Sparse.eval_merge,
    combined280_zero f hcross, source217_zero f hcross, add_zero]

theorem combined282_checked : Certificate.Integer.Sparse.merge combined281 source242 = combined282 := by
  decide +kernel

theorem combined282_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined282 (momentValues f) = 0 := by
  rw [← combined282_checked, Certificate.Integer.Sparse.eval_merge,
    combined281_zero f hcross, source242_zero f hcross, add_zero]

theorem combined283_checked : Certificate.Integer.Sparse.merge combined282 source373 = combined283 := by
  decide +kernel

theorem combined283_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined283 (momentValues f) = 0 := by
  rw [← combined283_checked, Certificate.Integer.Sparse.eval_merge,
    combined282_zero f hcross, source373_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined324_checked : Certificate.Integer.Sparse.merge source111 source138 = combined324 := by
  decide +kernel

theorem combined324_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined324 (momentValues f) = 0 := by
  rw [← combined324_checked, Certificate.Integer.Sparse.eval_merge,
    source111_zero f hcross, source138_zero f hcross, add_zero]

theorem combined325_checked : Certificate.Integer.Sparse.merge combined324 source246 = combined325 := by
  decide +kernel

theorem combined325_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined325 (momentValues f) = 0 := by
  rw [← combined325_checked, Certificate.Integer.Sparse.eval_merge,
    combined324_zero f hcross, source246_zero f hcross, add_zero]

theorem combined326_checked : Certificate.Integer.Sparse.merge combined325 source339 = combined326 := by
  decide +kernel

theorem combined326_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined326 (momentValues f) = 0 := by
  rw [← combined326_checked, Certificate.Integer.Sparse.eval_merge,
    combined325_zero f hcross, source339_zero f hcross, add_zero]

theorem combined327_checked : Certificate.Integer.Sparse.merge combined326 source399 = combined327 := by
  decide +kernel

theorem combined327_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined327 (momentValues f) = 0 := by
  rw [← combined327_checked, Certificate.Integer.Sparse.eval_merge,
    combined326_zero f hcross, source399_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined328_checked : Certificate.Integer.Sparse.merge source112 source140 = combined328 := by
  decide +kernel

theorem combined328_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined328 (momentValues f) = 0 := by
  rw [← combined328_checked, Certificate.Integer.Sparse.eval_merge,
    source112_zero f hcross, source140_zero f hcross, add_zero]

theorem combined329_checked : Certificate.Integer.Sparse.merge combined328 source248 = combined329 := by
  decide +kernel

theorem combined329_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined329 (momentValues f) = 0 := by
  rw [← combined329_checked, Certificate.Integer.Sparse.eval_merge,
    combined328_zero f hcross, source248_zero f hcross, add_zero]

theorem combined330_checked : Certificate.Integer.Sparse.merge combined329 source351 = combined330 := by
  decide +kernel

theorem combined330_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined330 (momentValues f) = 0 := by
  rw [← combined330_checked, Certificate.Integer.Sparse.eval_merge,
    combined329_zero f hcross, source351_zero f hcross, add_zero]

theorem combined331_checked : Certificate.Integer.Sparse.merge combined330 source459 = combined331 := by
  decide +kernel

theorem combined331_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined331 (momentValues f) = 0 := by
  rw [← combined331_checked, Certificate.Integer.Sparse.eval_merge,
    combined330_zero f hcross, source459_zero f hcross, add_zero]

theorem combined332_checked : Certificate.Integer.Sparse.merge source113 source142 = combined332 := by
  decide +kernel

theorem combined332_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined332 (momentValues f) = 0 := by
  rw [← combined332_checked, Certificate.Integer.Sparse.eval_merge,
    source113_zero f hcross, source142_zero f hcross, add_zero]

theorem combined333_checked : Certificate.Integer.Sparse.merge combined332 source250 = combined333 := by
  decide +kernel

theorem combined333_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined333 (momentValues f) = 0 := by
  rw [← combined333_checked, Certificate.Integer.Sparse.eval_merge,
    combined332_zero f hcross, source250_zero f hcross, add_zero]

theorem combined334_checked : Certificate.Integer.Sparse.merge combined333 source411 = combined334 := by
  decide +kernel

theorem combined334_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined334 (momentValues f) = 0 := by
  rw [← combined334_checked, Certificate.Integer.Sparse.eval_merge,
    combined333_zero f hcross, source411_zero f hcross, add_zero]

theorem combined335_checked : Certificate.Integer.Sparse.merge combined334 source471 = combined335 := by
  decide +kernel

theorem combined335_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined335 (momentValues f) = 0 := by
  rw [← combined335_checked, Certificate.Integer.Sparse.eval_merge,
    combined334_zero f hcross, source471_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined397_checked : Certificate.Integer.Sparse.merge combined396 combined231 = combined397 := by
  decide +kernel

theorem combined397_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined397 (momentValues f) = 0 := by
  rw [← combined397_checked, Certificate.Integer.Sparse.eval_merge,
    combined396_zero_e f hcross, combined231_zero f hcross, add_zero]

theorem combined398_checked : Certificate.Integer.Sparse.merge combined397 combined239 = combined398 := by
  decide +kernel

theorem combined398_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined398 (momentValues f) = 0 := by
  rw [← combined398_checked, Certificate.Integer.Sparse.eval_merge,
    combined397_zero f hcross, combined239_zero f hcross, add_zero]

theorem combined399_checked : Certificate.Integer.Sparse.merge combined398 combined335 = combined399 := by
  decide +kernel

theorem combined399_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined399 (momentValues f) = 0 := by
  rw [← combined399_checked, Certificate.Integer.Sparse.eval_merge,
    combined398_zero f hcross, combined335_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined400_checked : Certificate.Integer.Sparse.merge combined399 combined283 = combined400 := by
  decide +kernel

theorem combined400_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined400 (momentValues f) = 0 := by
  rw [← combined400_checked, Certificate.Integer.Sparse.eval_merge,
    combined399_zero f hcross, combined283_zero f hcross, add_zero]

theorem combined401_checked : Certificate.Integer.Sparse.merge combined400 combined279 = combined401 := by
  decide +kernel

theorem combined401_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined401 (momentValues f) = 0 := by
  rw [← combined401_checked, Certificate.Integer.Sparse.eval_merge,
    combined400_zero f hcross, combined279_zero f hcross, add_zero]

theorem combined402_checked : Certificate.Integer.Sparse.merge combined401 combined327 = combined402 := by
  decide +kernel

theorem combined402_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined402 (momentValues f) = 0 := by
  rw [← combined402_checked, Certificate.Integer.Sparse.eval_merge,
    combined401_zero f hcross, combined327_zero f hcross, add_zero]

theorem combined403_checked : Certificate.Integer.Sparse.merge combined402 combined331 = combined403 := by
  decide +kernel

theorem combined403_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined403 (momentValues f) = 0 := by
  rw [← combined403_checked, Certificate.Integer.Sparse.eval_merge,
    combined402_zero f hcross, combined331_zero f hcross, add_zero]

theorem combined404_checked : Certificate.Integer.Sparse.merge combined403 source13 = combined404 := by
  decide +kernel

theorem combined404_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined404 (momentValues f) = 0 := by
  rw [← combined404_checked, Certificate.Integer.Sparse.eval_merge,
    combined403_zero f hcross, source13_zero f hcross, add_zero]

theorem combined405_checked : Certificate.Integer.Sparse.merge combined404 combined91 = combined405 := by
  decide +kernel

theorem combined405_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined405 (momentValues f) = 0 := by
  rw [← combined405_checked, Certificate.Integer.Sparse.eval_merge,
    combined404_zero f hcross, combined91_zero f hcross, add_zero]

theorem combined406_checked : Certificate.Integer.Sparse.merge combined405 combined87 = combined406 := by
  decide +kernel

theorem combined406_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined406 (momentValues f) = 0 := by
  rw [← combined406_checked, Certificate.Integer.Sparse.eval_merge,
    combined405_zero f hcross, combined87_zero f hcross, add_zero]

theorem combined407_checked : Certificate.Integer.Sparse.merge combined406 combined95 = combined407 := by
  decide +kernel

theorem combined407_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined407 (momentValues f) = 0 := by
  rw [← combined407_checked, Certificate.Integer.Sparse.eval_merge,
    combined406_zero f hcross, combined95_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined408_checked : Certificate.Integer.Sparse.merge combined407 combined99 = combined408 := by
  decide +kernel

theorem combined408_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined408 (momentValues f) = 0 := by
  rw [← combined408_checked, Certificate.Integer.Sparse.eval_merge,
    combined407_zero f hcross, combined99_zero f hcross, add_zero]

theorem combined409_checked : Certificate.Integer.Sparse.merge combined408 combined223 = combined409 := by
  decide +kernel

theorem combined409_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined409 (momentValues f) = 0 := by
  rw [← combined409_checked, Certificate.Integer.Sparse.eval_merge,
    combined408_zero f hcross, combined223_zero f hcross, add_zero]

theorem combined410_checked : Certificate.Integer.Sparse.merge combined409 combined47 = combined410 := by
  decide +kernel

theorem combined410_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined410 (momentValues f) = 0 := by
  rw [← combined410_checked, Certificate.Integer.Sparse.eval_merge,
    combined409_zero f hcross, combined47_zero f hcross, add_zero]

theorem combined411_checked : Certificate.Integer.Sparse.merge combined410 source2 = combined411 := by
  decide +kernel

theorem combined411_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined411 (momentValues f) = 0 := by
  rw [← combined411_checked, Certificate.Integer.Sparse.eval_merge,
    combined410_zero f hcross, source2_zero f hcross, add_zero]

theorem combined412_checked : Certificate.Integer.Sparse.merge combined411 combined103 = combined412 := by
  decide +kernel

theorem combined412_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined412 (momentValues f) = 0 := by
  rw [← combined412_checked, Certificate.Integer.Sparse.eval_merge,
    combined411_zero f hcross, combined103_zero f hcross, add_zero]

theorem combined413_checked : Certificate.Integer.Sparse.merge combined412 combined107 = combined413 := by
  decide +kernel

theorem combined413_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined413 (momentValues f) = 0 := by
  rw [← combined413_checked, Certificate.Integer.Sparse.eval_merge,
    combined412_zero f hcross, combined107_zero f hcross, add_zero]

theorem combined414_checked : Certificate.Integer.Sparse.merge combined413 source4 = combined414 := by
  decide +kernel

theorem combined414_zero_e_oai (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined414 (momentValues f) = 0 := by
  rw [← combined414_checked, Certificate.Integer.Sparse.eval_merge,
    combined413_zero f hcross, source4_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

theorem solution : type_of% @OAI.MUB6.TaoCertificate.combined414_zero_e_oai := @OAI.MUB6.TaoCertificate.combined414_zero_e_oai
