-- Prove2me | solution 1 for OAI.MUB6.TaoCertificate.combined377_zero_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T15:48:44.210705+00:00
-- url     : https://prove2.me/submissions/2917a40f-4207-4878-9043-3997887a9154

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E158
import Definitions.Def_OAIQ106E160
import Definitions.Def_OAIQ106E164
import Definitions.Def_OAIQ106E167

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

theorem source0_checked : normalize (row ![-2, 0, 0, 0, 0, 2] ![-2, 0, 0, 0, 0, 2] (6, 0)) = source0 := by
  decide +kernel

theorem source0_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source0 (momentValues f) = 0 := by
  rw [← source0_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source3_checked : normalize (row ![-2, 0, 2, 0, 0, 0] ![-2, 0, 2, 0, 0, 0] (6, 0)) = source3 := by
  decide +kernel

theorem source3_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source3 (momentValues f) = 0 := by
  rw [← source3_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source5_checked : normalize (row ![0, -2, 0, 0, 0, 2] ![0, -2, 0, 0, 0, 2] (6, 0)) = source5 := by
  decide +kernel

theorem source5_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source5 (momentValues f) = 0 := by
  rw [← source5_checked, eval_normalize]
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

theorem source8_checked : normalize (row ![0, -2, 2, 0, 0, 0] ![0, -2, 2, 0, 0, 0] (6, 0)) = source8 := by
  decide +kernel

theorem source8_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source8 (momentValues f) = 0 := by
  rw [← source8_checked, eval_normalize]
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

theorem source121_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![1, -1, 0, 0, 0, 0] (0, -3)) = source121 := by
  decide +kernel

theorem source121_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source121 (momentValues f) = 0 := by
  rw [← source121_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source123_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![1, -1, 0, 0, 0, 0] (3, 3)) = source123 := by
  decide +kernel

theorem source123_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source123 (momentValues f) = 0 := by
  rw [← source123_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source125_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![1, -1, 0, 0, 0, 0] (3, 3)) = source125 := by
  decide +kernel

theorem source125_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source125 (momentValues f) = 0 := by
  rw [← source125_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source127_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![1, -1, 0, 0, 0, 0] (0, -3)) = source127 := by
  decide +kernel

theorem source127_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source127 (momentValues f) = 0 := by
  rw [← source127_checked, eval_normalize]
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

theorem source129_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![1, -1, 0, 0, 0, 0] (3, 3)) = source129 := by
  decide +kernel

theorem source129_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source129 (momentValues f) = 0 := by
  rw [← source129_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source131_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![1, -1, 0, 0, 0, 0] (0, -3)) = source131 := by
  decide +kernel

theorem source131_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source131 (momentValues f) = 0 := by
  rw [← source131_checked, eval_normalize]
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

theorem source153_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![1, 0, 0, -1, 0, 0] (3, 3)) = source153 := by
  decide +kernel

theorem source153_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source153 (momentValues f) = 0 := by
  rw [← source153_checked, eval_normalize]
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

theorem source163_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![1, 0, 0, 0, -1, 0] (0, -3)) = source163 := by
  decide +kernel

theorem source163_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source163 (momentValues f) = 0 := by
  rw [← source163_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source165_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![1, 0, 0, 0, -1, 0] (3, 3)) = source165 := by
  decide +kernel

theorem source165_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source165 (momentValues f) = 0 := by
  rw [← source165_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source167_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![1, 0, 0, 0, -1, 0] (3, 3)) = source167 := by
  decide +kernel

theorem source167_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source167 (momentValues f) = 0 := by
  rw [← source167_checked, eval_normalize]
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

theorem source181_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source181 := by
  decide +kernel

theorem source181_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source181 (momentValues f) = 0 := by
  rw [← source181_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source183_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source183 := by
  decide +kernel

theorem source183_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source183 (momentValues f) = 0 := by
  rw [← source183_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source185_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source185 := by
  decide +kernel

theorem source185_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source185 (momentValues f) = 0 := by
  rw [← source185_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source187_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source187 := by
  decide +kernel

theorem source187_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source187 (momentValues f) = 0 := by
  rw [← source187_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source189_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source189 := by
  decide +kernel

theorem source189_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source189 (momentValues f) = 0 := by
  rw [← source189_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source191_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source191 := by
  decide +kernel

theorem source191_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source191 (momentValues f) = 0 := by
  rw [← source191_checked, eval_normalize]
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

theorem source213_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, 1, 0, -1, 0, 0] (3, 3)) = source213 := by
  decide +kernel

theorem source213_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source213 (momentValues f) = 0 := by
  rw [← source213_checked, eval_normalize]
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

theorem source223_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, 1, 0, 0, -1, 0] (3, 3)) = source223 := by
  decide +kernel

theorem source223_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source223 (momentValues f) = 0 := by
  rw [← source223_checked, eval_normalize]
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

theorem source225_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, 1, 0, 0, -1, 0] (3, 3)) = source225 := by
  decide +kernel

theorem source225_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source225 (momentValues f) = 0 := by
  rw [← source225_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source227_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, 1, 0, 0, -1, 0] (0, -3)) = source227 := by
  decide +kernel

theorem source227_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source227 (momentValues f) = 0 := by
  rw [← source227_checked, eval_normalize]
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

theorem source30_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![-1, -1, 0, 0, 1, 1] (-12, 0)) = source30 := by
  decide +kernel

theorem source30_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source30 (momentValues f) = 0 := by
  rw [← source30_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source31_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![-1, -1, 0, 1, 0, 1] (-12, 0)) = source31 := by
  decide +kernel

theorem source31_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source31 (momentValues f) = 0 := by
  rw [← source31_checked, eval_normalize]
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

theorem source264_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![0, 0, -1, 1, 0, 0] (3, 3)) = source264 := by
  decide +kernel

theorem source264_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source264 (momentValues f) = 0 := by
  rw [← source264_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source266_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![0, 0, -1, 1, 0, 0] (0, -3)) = source266 := by
  decide +kernel

theorem source266_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source266 (momentValues f) = 0 := by
  rw [← source266_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source270_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, 0, -1, 1, 0, 0] (3, 3)) = source270 := by
  decide +kernel

theorem source270_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source270 (momentValues f) = 0 := by
  rw [← source270_checked, eval_normalize]
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

theorem source276_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![0, 0, -1, 0, 1, 0] (3, 3)) = source276 := by
  decide +kernel

theorem source276_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source276 (momentValues f) = 0 := by
  rw [← source276_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source288_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source288 := by
  decide +kernel

theorem source288_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source288 (momentValues f) = 0 := by
  rw [← source288_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source290_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source290 := by
  decide +kernel

theorem source290_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source290 (momentValues f) = 0 := by
  rw [← source290_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source292_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source292 := by
  decide +kernel

theorem source292_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source292 (momentValues f) = 0 := by
  rw [← source292_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source294_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source294 := by
  decide +kernel

theorem source294_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source294 (momentValues f) = 0 := by
  rw [← source294_checked, eval_normalize]
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

theorem source296_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, 0, -1, 0, 0, 1] (3, 3)) = source296 := by
  decide +kernel

theorem source296_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source296 (momentValues f) = 0 := by
  rw [← source296_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source298_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, -1, 0, 0, 1] (0, -3)) = source298 := by
  decide +kernel

theorem source298_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source298 (momentValues f) = 0 := by
  rw [← source298_checked, eval_normalize]
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

theorem source309_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source309 := by
  decide +kernel

theorem source309_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source309 (momentValues f) = 0 := by
  rw [← source309_checked, eval_normalize]
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

theorem source32_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![-1, -1, 0, 1, 1, 0] (-12, 0)) = source32 := by
  decide +kernel

theorem source32_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source32 (momentValues f) = 0 := by
  rw [← source32_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source33_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![-1, -1, 1, 0, 0, 1] (-12, 0)) = source33 := by
  decide +kernel

theorem source33_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source33 (momentValues f) = 0 := by
  rw [← source33_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source34_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![-1, -1, 1, 0, 1, 0] (-12, 0)) = source34 := by
  decide +kernel

theorem source34_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source34 (momentValues f) = 0 := by
  rw [← source34_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source35_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![-1, -1, 1, 1, 0, 0] (-12, 0)) = source35 := by
  decide +kernel

theorem source35_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source35 (momentValues f) = 0 := by
  rw [← source35_checked, eval_normalize]
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

theorem source321_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, -1, 0, 1, 0, 0] (0, -3)) = source321 := by
  decide +kernel

theorem source321_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source321 (momentValues f) = 0 := by
  rw [← source321_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source324_checked : normalize (row ![-1, -1, 1, 1, 0, 0] ![0, 0, 1, -1, 0, 0] (0, -3)) = source324 := by
  decide +kernel

theorem source324_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source324 (momentValues f) = 0 := by
  rw [← source324_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source326_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![0, 0, 1, -1, 0, 0] (3, 3)) = source326 := by
  decide +kernel

theorem source326_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source326 (momentValues f) = 0 := by
  rw [← source326_checked, eval_normalize]
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

theorem source330_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, 0, 1, -1, 0, 0] (3, 3)) = source330 := by
  decide +kernel

theorem source330_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source330 (momentValues f) = 0 := by
  rw [← source330_checked, eval_normalize]
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

theorem source336_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![0, 0, 0, -1, 1, 0] (0, -3)) = source336 := by
  decide +kernel

theorem source336_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source336 (momentValues f) = 0 := by
  rw [← source336_checked, eval_normalize]
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

theorem source347_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 0, 1, -1, 0] (0, -3)) = source347 := by
  decide +kernel

theorem source347_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source347 (momentValues f) = 0 := by
  rw [← source347_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source348_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source348 := by
  decide +kernel

theorem source348_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source348 (momentValues f) = 0 := by
  rw [← source348_checked, eval_normalize]
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

theorem source352_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source352 := by
  decide +kernel

theorem source352_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source352 (momentValues f) = 0 := by
  rw [← source352_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source356_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source356 := by
  decide +kernel

theorem source356_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source356 (momentValues f) = 0 := by
  rw [← source356_checked, eval_normalize]
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

theorem source367_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source367 := by
  decide +kernel

theorem source367_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source367 (momentValues f) = 0 := by
  rw [← source367_checked, eval_normalize]
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

theorem source369_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source369 := by
  decide +kernel

theorem source369_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source369 (momentValues f) = 0 := by
  rw [← source369_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source371_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![-1, 0, 0, 0, 1, 0] (3, 3)) = source371 := by
  decide +kernel

theorem source371_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source371 (momentValues f) = 0 := by
  rw [← source371_checked, eval_normalize]
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

theorem source379_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, -1, 0, 0, 1, 0] (3, 3)) = source379 := by
  decide +kernel

theorem source379_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source379 (momentValues f) = 0 := by
  rw [← source379_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source381_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, -1, 0, 0, 1, 0] (0, -3)) = source381 := by
  decide +kernel

theorem source381_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source381 (momentValues f) = 0 := by
  rw [← source381_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source383_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, -1, 0, 0, 1, 0] (3, 3)) = source383 := by
  decide +kernel

theorem source383_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source383 (momentValues f) = 0 := by
  rw [← source383_checked, eval_normalize]
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

theorem source384_checked : normalize (row ![-1, -1, 1, 0, 1, 0] ![0, 0, 1, 0, -1, 0] (0, -3)) = source384 := by
  decide +kernel

theorem source384_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source384 (momentValues f) = 0 := by
  rw [← source384_checked, eval_normalize]
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

theorem source396_checked : normalize (row ![-1, -1, 0, 1, 1, 0] ![0, 0, 0, 1, -1, 0] (0, -3)) = source396 := by
  decide +kernel

theorem source396_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source396 (momentValues f) = 0 := by
  rw [← source396_checked, eval_normalize]
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

theorem source40_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![-1, 0, 0, 1, -1, 1] (-12, 0)) = source40 := by
  decide +kernel

theorem source40_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source40 (momentValues f) = 0 := by
  rw [← source40_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source42_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![-1, 0, 1, -1, 0, 1] (-12, 0)) = source42 := by
  decide +kernel

theorem source42_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source42 (momentValues f) = 0 := by
  rw [← source42_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source44_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![-1, 0, 1, 0, -1, 1] (-12, 0)) = source44 := by
  decide +kernel

theorem source44_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source44 (momentValues f) = 0 := by
  rw [← source44_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source46_checked : normalize (row ![-1, 0, 1, 1, -1, 0] ![-1, 0, 1, 1, -1, 0] (-12, 0)) = source46 := by
  decide +kernel

theorem source46_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source46 (momentValues f) = 0 := by
  rw [← source46_checked, eval_normalize]
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

theorem source407_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 0, -1, 1, 0] (0, -3)) = source407 := by
  decide +kernel

theorem source407_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source407 (momentValues f) = 0 := by
  rw [← source407_checked, eval_normalize]
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

theorem source408_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source408 := by
  decide +kernel

theorem source408_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source408 (momentValues f) = 0 := by
  rw [← source408_checked, eval_normalize]
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

theorem source444_checked : normalize (row ![-1, -1, 1, 0, 0, 1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source444 := by
  decide +kernel

theorem source444_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source444 (momentValues f) = 0 := by
  rw [← source444_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source446_checked : normalize (row ![-1, 0, 1, -1, 0, 1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source446 := by
  decide +kernel

theorem source446_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source446 (momentValues f) = 0 := by
  rw [← source446_checked, eval_normalize]
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

theorem source448_checked : normalize (row ![-1, 0, 1, 0, -1, 1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source448 := by
  decide +kernel

theorem source448_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source448 (momentValues f) = 0 := by
  rw [← source448_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source450_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, 0, 1, 0, 0, -1] (3, 3)) = source450 := by
  decide +kernel

theorem source450_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source450 (momentValues f) = 0 := by
  rw [← source450_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source452_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source452 := by
  decide +kernel

theorem source452_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source452 (momentValues f) = 0 := by
  rw [← source452_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source454_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 1, 0, 0, -1] (0, -3)) = source454 := by
  decide +kernel

theorem source454_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source454 (momentValues f) = 0 := by
  rw [← source454_checked, eval_normalize]
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

theorem source456_checked : normalize (row ![-1, -1, 0, 1, 0, 1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source456 := by
  decide +kernel

theorem source456_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source456 (momentValues f) = 0 := by
  rw [← source456_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source460_checked : normalize (row ![-1, 0, 0, 1, -1, 1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source460 := by
  decide +kernel

theorem source460_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source460 (momentValues f) = 0 := by
  rw [← source460_checked, eval_normalize]
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

theorem source464_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, 0, 0, 1, 0, -1] (0, -3)) = source464 := by
  decide +kernel

theorem source464_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source464 (momentValues f) = 0 := by
  rw [← source464_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source468_checked : normalize (row ![-1, -1, 0, 0, 1, 1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source468 := by
  decide +kernel

theorem source468_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source468 (momentValues f) = 0 := by
  rw [← source468_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Rows8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source64_checked : normalize (row ![0, -1, 0, 1, -1, 1] ![0, -1, 0, 1, -1, 1] (-12, 0)) = source64 := by
  decide +kernel

theorem source64_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source64 (momentValues f) = 0 := by
  rw [← source64_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source66_checked : normalize (row ![0, -1, 1, -1, 0, 1] ![0, -1, 1, -1, 0, 1] (-12, 0)) = source66 := by
  decide +kernel

theorem source66_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source66 (momentValues f) = 0 := by
  rw [← source66_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source68_checked : normalize (row ![0, -1, 1, 0, -1, 1] ![0, -1, 1, 0, -1, 1] (-12, 0)) = source68 := by
  decide +kernel

theorem source68_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source68 (momentValues f) = 0 := by
  rw [← source68_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source70_checked : normalize (row ![0, -1, 1, 1, -1, 0] ![0, -1, 1, 1, -1, 0] (-12, 0)) = source70 := by
  decide +kernel

theorem source70_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source70 (momentValues f) = 0 := by
  rw [← source70_checked, eval_normalize]
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

theorem source75_checked : normalize (row ![0, 0, 1, -1, -1, 1] ![0, 0, 1, -1, -1, 1] (-12, 0)) = source75 := by
  decide +kernel

theorem source75_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source75 (momentValues f) = 0 := by
  rw [← source75_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined0_checked : Certificate.Integer.Sparse.merge source30 source131 = combined0 := by
  decide +kernel

theorem combined0_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined0 (momentValues f) = 0 := by
  rw [← combined0_checked, Certificate.Integer.Sparse.eval_merge,
    source30_zero f hcross, source131_zero f hcross, add_zero]

theorem combined1_checked : Certificate.Integer.Sparse.merge combined0 source191 = combined1 := by
  decide +kernel

theorem combined1_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined1 (momentValues f) = 0 := by
  rw [← combined1_checked, Certificate.Integer.Sparse.eval_merge,
    combined0_zero f hcross, source191_zero f hcross, add_zero]

theorem combined2_checked : Certificate.Integer.Sparse.merge combined1 source408 = combined2 := by
  decide +kernel

theorem combined2_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined2 (momentValues f) = 0 := by
  rw [← combined2_checked, Certificate.Integer.Sparse.eval_merge,
    combined1_zero f hcross, source408_zero f hcross, add_zero]

theorem combined3_checked : Certificate.Integer.Sparse.merge combined2 source468 = combined3 := by
  decide +kernel

theorem combined3_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined3 (momentValues f) = 0 := by
  rw [← combined3_checked, Certificate.Integer.Sparse.eval_merge,
    combined2_zero f hcross, source468_zero f hcross, add_zero]

theorem combined4_checked : Certificate.Integer.Sparse.merge source31 source129 = combined4 := by
  decide +kernel

theorem combined4_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined4 (momentValues f) = 0 := by
  rw [← combined4_checked, Certificate.Integer.Sparse.eval_merge,
    source31_zero f hcross, source129_zero f hcross, add_zero]

theorem combined5_checked : Certificate.Integer.Sparse.merge combined4 source189 = combined5 := by
  decide +kernel

theorem combined5_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined5 (momentValues f) = 0 := by
  rw [← combined5_checked, Certificate.Integer.Sparse.eval_merge,
    combined4_zero f hcross, source189_zero f hcross, add_zero]

theorem combined6_checked : Certificate.Integer.Sparse.merge combined5 source348 = combined6 := by
  decide +kernel

theorem combined6_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined6 (momentValues f) = 0 := by
  rw [← combined6_checked, Certificate.Integer.Sparse.eval_merge,
    combined5_zero f hcross, source348_zero f hcross, add_zero]

theorem combined7_checked : Certificate.Integer.Sparse.merge combined6 source456 = combined7 := by
  decide +kernel

theorem combined7_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined7 (momentValues f) = 0 := by
  rw [← combined7_checked, Certificate.Integer.Sparse.eval_merge,
    combined6_zero f hcross, source456_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined8_checked : Certificate.Integer.Sparse.merge source32 source127 = combined8 := by
  decide +kernel

theorem combined8_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined8 (momentValues f) = 0 := by
  rw [← combined8_checked, Certificate.Integer.Sparse.eval_merge,
    source32_zero f hcross, source127_zero f hcross, add_zero]

theorem combined9_checked : Certificate.Integer.Sparse.merge combined8 source187 = combined9 := by
  decide +kernel

theorem combined9_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined9 (momentValues f) = 0 := by
  rw [← combined9_checked, Certificate.Integer.Sparse.eval_merge,
    combined8_zero f hcross, source187_zero f hcross, add_zero]

theorem combined10_checked : Certificate.Integer.Sparse.merge combined9 source336 = combined10 := by
  decide +kernel

theorem combined10_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined10 (momentValues f) = 0 := by
  rw [← combined10_checked, Certificate.Integer.Sparse.eval_merge,
    combined9_zero f hcross, source336_zero f hcross, add_zero]

theorem combined11_checked : Certificate.Integer.Sparse.merge combined10 source396 = combined11 := by
  decide +kernel

theorem combined11_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined11 (momentValues f) = 0 := by
  rw [← combined11_checked, Certificate.Integer.Sparse.eval_merge,
    combined10_zero f hcross, source396_zero f hcross, add_zero]

theorem combined12_checked : Certificate.Integer.Sparse.merge source33 source125 = combined12 := by
  decide +kernel

theorem combined12_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined12 (momentValues f) = 0 := by
  rw [← combined12_checked, Certificate.Integer.Sparse.eval_merge,
    source33_zero f hcross, source125_zero f hcross, add_zero]

theorem combined13_checked : Certificate.Integer.Sparse.merge combined12 source185 = combined13 := by
  decide +kernel

theorem combined13_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined13 (momentValues f) = 0 := by
  rw [← combined13_checked, Certificate.Integer.Sparse.eval_merge,
    combined12_zero f hcross, source185_zero f hcross, add_zero]

theorem combined14_checked : Certificate.Integer.Sparse.merge combined13 source288 = combined14 := by
  decide +kernel

theorem combined14_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined14 (momentValues f) = 0 := by
  rw [← combined14_checked, Certificate.Integer.Sparse.eval_merge,
    combined13_zero f hcross, source288_zero f hcross, add_zero]

theorem combined15_checked : Certificate.Integer.Sparse.merge combined14 source444 = combined15 := by
  decide +kernel

theorem combined15_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined15 (momentValues f) = 0 := by
  rw [← combined15_checked, Certificate.Integer.Sparse.eval_merge,
    combined14_zero f hcross, source444_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined16_checked : Certificate.Integer.Sparse.merge source34 source123 = combined16 := by
  decide +kernel

theorem combined16_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined16 (momentValues f) = 0 := by
  rw [← combined16_checked, Certificate.Integer.Sparse.eval_merge,
    source34_zero f hcross, source123_zero f hcross, add_zero]

theorem combined17_checked : Certificate.Integer.Sparse.merge combined16 source183 = combined17 := by
  decide +kernel

theorem combined17_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined17 (momentValues f) = 0 := by
  rw [← combined17_checked, Certificate.Integer.Sparse.eval_merge,
    combined16_zero f hcross, source183_zero f hcross, add_zero]

theorem combined18_checked : Certificate.Integer.Sparse.merge combined17 source276 = combined18 := by
  decide +kernel

theorem combined18_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined18 (momentValues f) = 0 := by
  rw [← combined18_checked, Certificate.Integer.Sparse.eval_merge,
    combined17_zero f hcross, source276_zero f hcross, add_zero]

theorem combined19_checked : Certificate.Integer.Sparse.merge combined18 source384 = combined19 := by
  decide +kernel

theorem combined19_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined19 (momentValues f) = 0 := by
  rw [← combined19_checked, Certificate.Integer.Sparse.eval_merge,
    combined18_zero f hcross, source384_zero f hcross, add_zero]

theorem combined20_checked : Certificate.Integer.Sparse.merge source35 source121 = combined20 := by
  decide +kernel

theorem combined20_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined20 (momentValues f) = 0 := by
  rw [← combined20_checked, Certificate.Integer.Sparse.eval_merge,
    source35_zero f hcross, source121_zero f hcross, add_zero]

theorem combined21_checked : Certificate.Integer.Sparse.merge combined20 source181 = combined21 := by
  decide +kernel

theorem combined21_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined21 (momentValues f) = 0 := by
  rw [← combined21_checked, Certificate.Integer.Sparse.eval_merge,
    combined20_zero f hcross, source181_zero f hcross, add_zero]

theorem combined22_checked : Certificate.Integer.Sparse.merge combined21 source264 = combined22 := by
  decide +kernel

theorem combined22_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined22 (momentValues f) = 0 := by
  rw [← combined22_checked, Certificate.Integer.Sparse.eval_merge,
    combined21_zero f hcross, source264_zero f hcross, add_zero]

theorem combined23_checked : Certificate.Integer.Sparse.merge combined22 source324 = combined23 := by
  decide +kernel

theorem combined23_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined23 (momentValues f) = 0 := by
  rw [← combined23_checked, Certificate.Integer.Sparse.eval_merge,
    combined22_zero f hcross, source324_zero f hcross, add_zero]

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

theorem combined40_checked : Certificate.Integer.Sparse.merge source40 source167 = combined40 := by
  decide +kernel

theorem combined40_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined40 (momentValues f) = 0 := by
  rw [← combined40_checked, Certificate.Integer.Sparse.eval_merge,
    source40_zero f hcross, source167_zero f hcross, add_zero]

theorem combined41_checked : Certificate.Integer.Sparse.merge combined40 source352 = combined41 := by
  decide +kernel

theorem combined41_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined41 (momentValues f) = 0 := by
  rw [← combined41_checked, Certificate.Integer.Sparse.eval_merge,
    combined40_zero f hcross, source352_zero f hcross, add_zero]

theorem combined42_checked : Certificate.Integer.Sparse.merge combined41 source371 = combined42 := by
  decide +kernel

theorem combined42_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined42 (momentValues f) = 0 := by
  rw [← combined42_checked, Certificate.Integer.Sparse.eval_merge,
    combined41_zero f hcross, source371_zero f hcross, add_zero]

theorem combined43_checked : Certificate.Integer.Sparse.merge combined42 source460 = combined43 := by
  decide +kernel

theorem combined43_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined43 (momentValues f) = 0 := by
  rw [← combined43_checked, Certificate.Integer.Sparse.eval_merge,
    combined42_zero f hcross, source460_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined48_checked : Certificate.Integer.Sparse.merge source42 source153 = combined48 := by
  decide +kernel

theorem combined48_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined48 (momentValues f) = 0 := by
  rw [← combined48_checked, Certificate.Integer.Sparse.eval_merge,
    source42_zero f hcross, source153_zero f hcross, add_zero]

theorem combined49_checked : Certificate.Integer.Sparse.merge combined48 source290 = combined49 := by
  decide +kernel

theorem combined49_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined49 (momentValues f) = 0 := by
  rw [← combined49_checked, Certificate.Integer.Sparse.eval_merge,
    combined48_zero f hcross, source290_zero f hcross, add_zero]

theorem combined50_checked : Certificate.Integer.Sparse.merge combined49 source309 = combined50 := by
  decide +kernel

theorem combined50_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined50 (momentValues f) = 0 := by
  rw [← combined50_checked, Certificate.Integer.Sparse.eval_merge,
    combined49_zero f hcross, source309_zero f hcross, add_zero]

theorem combined51_checked : Certificate.Integer.Sparse.merge combined50 source446 = combined51 := by
  decide +kernel

theorem combined51_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined51 (momentValues f) = 0 := by
  rw [← combined51_checked, Certificate.Integer.Sparse.eval_merge,
    combined50_zero f hcross, source446_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined56_checked : Certificate.Integer.Sparse.merge source44 source165 = combined56 := by
  decide +kernel

theorem combined56_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined56 (momentValues f) = 0 := by
  rw [← combined56_checked, Certificate.Integer.Sparse.eval_merge,
    source44_zero f hcross, source165_zero f hcross, add_zero]

theorem combined57_checked : Certificate.Integer.Sparse.merge combined56 source292 = combined57 := by
  decide +kernel

theorem combined57_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined57 (momentValues f) = 0 := by
  rw [← combined57_checked, Certificate.Integer.Sparse.eval_merge,
    combined56_zero f hcross, source292_zero f hcross, add_zero]

theorem combined58_checked : Certificate.Integer.Sparse.merge combined57 source369 = combined58 := by
  decide +kernel

theorem combined58_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined58 (momentValues f) = 0 := by
  rw [← combined58_checked, Certificate.Integer.Sparse.eval_merge,
    combined57_zero f hcross, source369_zero f hcross, add_zero]

theorem combined59_checked : Certificate.Integer.Sparse.merge combined58 source448 = combined59 := by
  decide +kernel

theorem combined59_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined59 (momentValues f) = 0 := by
  rw [← combined59_checked, Certificate.Integer.Sparse.eval_merge,
    combined58_zero f hcross, source448_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined64_checked : Certificate.Integer.Sparse.merge source46 source163 = combined64 := by
  decide +kernel

theorem combined64_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined64 (momentValues f) = 0 := by
  rw [← combined64_checked, Certificate.Integer.Sparse.eval_merge,
    source46_zero f hcross, source163_zero f hcross, add_zero]

theorem combined65_checked : Certificate.Integer.Sparse.merge combined64 source266 = combined65 := by
  decide +kernel

theorem combined65_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined65 (momentValues f) = 0 := by
  rw [← combined65_checked, Certificate.Integer.Sparse.eval_merge,
    combined64_zero f hcross, source266_zero f hcross, add_zero]

theorem combined66_checked : Certificate.Integer.Sparse.merge combined65 source326 = combined66 := by
  decide +kernel

theorem combined66_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined66 (momentValues f) = 0 := by
  rw [← combined66_checked, Certificate.Integer.Sparse.eval_merge,
    combined65_zero f hcross, source326_zero f hcross, add_zero]

theorem combined67_checked : Certificate.Integer.Sparse.merge combined66 source367 = combined67 := by
  decide +kernel

theorem combined67_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined67 (momentValues f) = 0 := by
  rw [← combined67_checked, Certificate.Integer.Sparse.eval_merge,
    combined66_zero f hcross, source367_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined136_checked : Certificate.Integer.Sparse.merge source64 source227 = combined136 := by
  decide +kernel

theorem combined136_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined136 (momentValues f) = 0 := by
  rw [← combined136_checked, Certificate.Integer.Sparse.eval_merge,
    source64_zero f hcross, source227_zero f hcross, add_zero]

theorem combined137_checked : Certificate.Integer.Sparse.merge combined136 source356 = combined137 := by
  decide +kernel

theorem combined137_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined137 (momentValues f) = 0 := by
  rw [← combined137_checked, Certificate.Integer.Sparse.eval_merge,
    combined136_zero f hcross, source356_zero f hcross, add_zero]

theorem combined138_checked : Certificate.Integer.Sparse.merge combined137 source383 = combined138 := by
  decide +kernel

theorem combined138_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined138 (momentValues f) = 0 := by
  rw [← combined138_checked, Certificate.Integer.Sparse.eval_merge,
    combined137_zero f hcross, source383_zero f hcross, add_zero]

theorem combined139_checked : Certificate.Integer.Sparse.merge combined138 source464 = combined139 := by
  decide +kernel

theorem combined139_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined139 (momentValues f) = 0 := by
  rw [← combined139_checked, Certificate.Integer.Sparse.eval_merge,
    combined138_zero f hcross, source464_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined144_checked : Certificate.Integer.Sparse.merge source66 source213 = combined144 := by
  decide +kernel

theorem combined144_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined144 (momentValues f) = 0 := by
  rw [← combined144_checked, Certificate.Integer.Sparse.eval_merge,
    source66_zero f hcross, source213_zero f hcross, add_zero]

theorem combined145_checked : Certificate.Integer.Sparse.merge combined144 source294 = combined145 := by
  decide +kernel

theorem combined145_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined145 (momentValues f) = 0 := by
  rw [← combined145_checked, Certificate.Integer.Sparse.eval_merge,
    combined144_zero f hcross, source294_zero f hcross, add_zero]

theorem combined146_checked : Certificate.Integer.Sparse.merge combined145 source321 = combined146 := by
  decide +kernel

theorem combined146_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined146 (momentValues f) = 0 := by
  rw [← combined146_checked, Certificate.Integer.Sparse.eval_merge,
    combined145_zero f hcross, source321_zero f hcross, add_zero]

theorem combined147_checked : Certificate.Integer.Sparse.merge combined146 source450 = combined147 := by
  decide +kernel

theorem combined147_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined147 (momentValues f) = 0 := by
  rw [← combined147_checked, Certificate.Integer.Sparse.eval_merge,
    combined146_zero f hcross, source450_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined152_checked : Certificate.Integer.Sparse.merge source68 source225 = combined152 := by
  decide +kernel

theorem combined152_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined152 (momentValues f) = 0 := by
  rw [← combined152_checked, Certificate.Integer.Sparse.eval_merge,
    source68_zero f hcross, source225_zero f hcross, add_zero]

theorem combined153_checked : Certificate.Integer.Sparse.merge combined152 source296 = combined153 := by
  decide +kernel

theorem combined153_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined153 (momentValues f) = 0 := by
  rw [← combined153_checked, Certificate.Integer.Sparse.eval_merge,
    combined152_zero f hcross, source296_zero f hcross, add_zero]

theorem combined154_checked : Certificate.Integer.Sparse.merge combined153 source381 = combined154 := by
  decide +kernel

theorem combined154_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined154 (momentValues f) = 0 := by
  rw [← combined154_checked, Certificate.Integer.Sparse.eval_merge,
    combined153_zero f hcross, source381_zero f hcross, add_zero]

theorem combined155_checked : Certificate.Integer.Sparse.merge combined154 source452 = combined155 := by
  decide +kernel

theorem combined155_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined155 (momentValues f) = 0 := by
  rw [← combined155_checked, Certificate.Integer.Sparse.eval_merge,
    combined154_zero f hcross, source452_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined160_checked : Certificate.Integer.Sparse.merge source70 source223 = combined160 := by
  decide +kernel

theorem combined160_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined160 (momentValues f) = 0 := by
  rw [← combined160_checked, Certificate.Integer.Sparse.eval_merge,
    source70_zero f hcross, source223_zero f hcross, add_zero]

theorem combined161_checked : Certificate.Integer.Sparse.merge combined160 source270 = combined161 := by
  decide +kernel

theorem combined161_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined161 (momentValues f) = 0 := by
  rw [← combined161_checked, Certificate.Integer.Sparse.eval_merge,
    combined160_zero f hcross, source270_zero f hcross, add_zero]

theorem combined162_checked : Certificate.Integer.Sparse.merge combined161 source330 = combined162 := by
  decide +kernel

theorem combined162_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined162 (momentValues f) = 0 := by
  rw [← combined162_checked, Certificate.Integer.Sparse.eval_merge,
    combined161_zero f hcross, source330_zero f hcross, add_zero]

theorem combined163_checked : Certificate.Integer.Sparse.merge combined162 source379 = combined163 := by
  decide +kernel

theorem combined163_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined163 (momentValues f) = 0 := by
  rw [← combined163_checked, Certificate.Integer.Sparse.eval_merge,
    combined162_zero f hcross, source379_zero f hcross, add_zero]

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

theorem combined180_checked : Certificate.Integer.Sparse.merge source75 source298 = combined180 := by
  decide +kernel

theorem combined180_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined180 (momentValues f) = 0 := by
  rw [← combined180_checked, Certificate.Integer.Sparse.eval_merge,
    source75_zero f hcross, source298_zero f hcross, add_zero]

theorem combined181_checked : Certificate.Integer.Sparse.merge combined180 source347 = combined181 := by
  decide +kernel

theorem combined181_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined181 (momentValues f) = 0 := by
  rw [← combined181_checked, Certificate.Integer.Sparse.eval_merge,
    combined180_zero f hcross, source347_zero f hcross, add_zero]

theorem combined182_checked : Certificate.Integer.Sparse.merge combined181 source407 = combined182 := by
  decide +kernel

theorem combined182_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined182 (momentValues f) = 0 := by
  rw [← combined182_checked, Certificate.Integer.Sparse.eval_merge,
    combined181_zero f hcross, source407_zero f hcross, add_zero]

theorem combined183_checked : Certificate.Integer.Sparse.merge combined182 source454 = combined183 := by
  decide +kernel

theorem combined183_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined183 (momentValues f) = 0 := by
  rw [← combined183_checked, Certificate.Integer.Sparse.eval_merge,
    combined182_zero f hcross, source454_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined360_checked : Certificate.Integer.Sparse.merge source0 combined15 = combined360 := by
  decide +kernel

theorem combined360_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined360 (momentValues f) = 0 := by
  rw [← combined360_checked, Certificate.Integer.Sparse.eval_merge,
    source0_zero f hcross, combined15_zero f hcross, add_zero]

theorem combined361_checked : Certificate.Integer.Sparse.merge combined360 combined43 = combined361 := by
  decide +kernel

theorem combined361_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined361 (momentValues f) = 0 := by
  rw [← combined361_checked, Certificate.Integer.Sparse.eval_merge,
    combined360_zero f hcross, combined43_zero f hcross, add_zero]

theorem combined362_checked : Certificate.Integer.Sparse.merge combined361 combined7 = combined362 := by
  decide +kernel

theorem combined362_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined362 (momentValues f) = 0 := by
  rw [← combined362_checked, Certificate.Integer.Sparse.eval_merge,
    combined361_zero f hcross, combined7_zero f hcross, add_zero]

theorem combined363_checked : Certificate.Integer.Sparse.merge combined362 combined59 = combined363 := by
  decide +kernel

theorem combined363_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined363 (momentValues f) = 0 := by
  rw [← combined363_checked, Certificate.Integer.Sparse.eval_merge,
    combined362_zero f hcross, combined59_zero f hcross, add_zero]

theorem combined364_checked : Certificate.Integer.Sparse.merge combined363 combined23 = combined364 := by
  decide +kernel

theorem combined364_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined364 (momentValues f) = 0 := by
  rw [← combined364_checked, Certificate.Integer.Sparse.eval_merge,
    combined363_zero f hcross, combined23_zero f hcross, add_zero]

theorem combined365_checked : Certificate.Integer.Sparse.merge combined364 combined67 = combined365 := by
  decide +kernel

theorem combined365_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined365 (momentValues f) = 0 := by
  rw [← combined365_checked, Certificate.Integer.Sparse.eval_merge,
    combined364_zero f hcross, combined67_zero f hcross, add_zero]

theorem combined366_checked : Certificate.Integer.Sparse.merge combined365 combined139 = combined366 := by
  decide +kernel

theorem combined366_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined366 (momentValues f) = 0 := by
  rw [← combined366_checked, Certificate.Integer.Sparse.eval_merge,
    combined365_zero f hcross, combined139_zero f hcross, add_zero]

theorem combined367_checked : Certificate.Integer.Sparse.merge combined366 combined155 = combined367 := by
  decide +kernel

theorem combined367_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined367 (momentValues f) = 0 := by
  rw [← combined367_checked, Certificate.Integer.Sparse.eval_merge,
    combined366_zero f hcross, combined155_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined368_checked : Certificate.Integer.Sparse.merge combined367 combined163 = combined368 := by
  decide +kernel

theorem combined368_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined368 (momentValues f) = 0 := by
  rw [← combined368_checked, Certificate.Integer.Sparse.eval_merge,
    combined367_zero f hcross, combined163_zero f hcross, add_zero]

theorem combined369_checked : Certificate.Integer.Sparse.merge combined368 source8 = combined369 := by
  decide +kernel

theorem combined369_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined369 (momentValues f) = 0 := by
  rw [← combined369_checked, Certificate.Integer.Sparse.eval_merge,
    combined368_zero f hcross, source8_zero f hcross, add_zero]

theorem combined370_checked : Certificate.Integer.Sparse.merge combined369 source3 = combined370 := by
  decide +kernel

theorem combined370_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined370 (momentValues f) = 0 := by
  rw [← combined370_checked, Certificate.Integer.Sparse.eval_merge,
    combined369_zero f hcross, source3_zero f hcross, add_zero]

theorem combined371_checked : Certificate.Integer.Sparse.merge combined370 combined19 = combined371 := by
  decide +kernel

theorem combined371_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined371 (momentValues f) = 0 := by
  rw [← combined371_checked, Certificate.Integer.Sparse.eval_merge,
    combined370_zero f hcross, combined19_zero f hcross, add_zero]

theorem combined372_checked : Certificate.Integer.Sparse.merge combined371 combined51 = combined372 := by
  decide +kernel

theorem combined372_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined372 (momentValues f) = 0 := by
  rw [← combined372_checked, Certificate.Integer.Sparse.eval_merge,
    combined371_zero f hcross, combined51_zero f hcross, add_zero]

theorem combined373_checked : Certificate.Integer.Sparse.merge combined372 combined3 = combined373 := by
  decide +kernel

theorem combined373_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined373 (momentValues f) = 0 := by
  rw [← combined373_checked, Certificate.Integer.Sparse.eval_merge,
    combined372_zero f hcross, combined3_zero f hcross, add_zero]

theorem combined374_checked : Certificate.Integer.Sparse.merge combined373 combined11 = combined374 := by
  decide +kernel

theorem combined374_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined374 (momentValues f) = 0 := by
  rw [← combined374_checked, Certificate.Integer.Sparse.eval_merge,
    combined373_zero f hcross, combined11_zero f hcross, add_zero]

theorem combined375_checked : Certificate.Integer.Sparse.merge combined374 combined147 = combined375 := by
  decide +kernel

theorem combined375_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined375 (momentValues f) = 0 := by
  rw [← combined375_checked, Certificate.Integer.Sparse.eval_merge,
    combined374_zero f hcross, combined147_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined376_checked : Certificate.Integer.Sparse.merge combined375 combined183 = combined376 := by
  decide +kernel

theorem combined376_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined376 (momentValues f) = 0 := by
  rw [← combined376_checked, Certificate.Integer.Sparse.eval_merge,
    combined375_zero f hcross, combined183_zero f hcross, add_zero]

theorem combined377_checked : Certificate.Integer.Sparse.merge combined376 source5 = combined377 := by
  decide +kernel

theorem combined377_zero_e_oai (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined377 (momentValues f) = 0 := by
  rw [← combined377_checked, Certificate.Integer.Sparse.eval_merge,
    combined376_zero f hcross, source5_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

theorem solution : type_of% @OAI.MUB6.TaoCertificate.combined377_zero_e_oai := @OAI.MUB6.TaoCertificate.combined377_zero_e_oai
