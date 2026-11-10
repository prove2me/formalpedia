-- Prove2me | solution 1 for OAI.MUB6.TaoCertificate.combined396_zero_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T06:30:34.788482+00:00
-- url     : https://prove2.me/submissions/2c92f000-788c-4475-8b04-2a3d09883304

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E161
import Definitions.Def_OAIQ106E166
import Definitions.Def_OAIQ106E167
import Theorems.Thm_OAI_MUB6_TaoCertificate_combined377_zero_e

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

theorem source1_checked : normalize (row ![-2, 0, 0, 0, 2, 0] ![-2, 0, 0, 0, 2, 0] (6, 0)) = source1 := by
  decide +kernel

theorem source1_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source1 (momentValues f) = 0 := by
  rw [← source1_checked, eval_normalize]
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

theorem source88_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 1, 1, -1, 0, -1] (-12, 0)) = source88 := by
  decide +kernel

theorem source88_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source88 (momentValues f) = 0 := by
  rw [← source88_checked, eval_normalize]
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

theorem source101_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![1, -1, 1, 0, 0, -1] (-12, 0)) = source101 := by
  decide +kernel

theorem source101_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source101 (momentValues f) = 0 := by
  rw [← source101_checked, eval_normalize]
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

theorem source136_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![-1, 0, 1, 0, 0, 0] (3, 3)) = source136 := by
  decide +kernel

theorem source136_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source136 (momentValues f) = 0 := by
  rw [← source136_checked, eval_normalize]
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

theorem source145_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![1, 0, 0, -1, 0, 0] (0, -3)) = source145 := by
  decide +kernel

theorem source145_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source145 (momentValues f) = 0 := by
  rw [← source145_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source151_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![1, 0, 0, -1, 0, 0] (3, 3)) = source151 := by
  decide +kernel

theorem source151_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source151 (momentValues f) = 0 := by
  rw [← source151_checked, eval_normalize]
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

theorem source155_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![1, 0, 0, -1, 0, 0] (0, -3)) = source155 := by
  decide +kernel

theorem source155_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source155 (momentValues f) = 0 := by
  rw [← source155_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source157_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![1, 0, 0, 0, -1, 0] (0, -3)) = source157 := by
  decide +kernel

theorem source157_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source157 (momentValues f) = 0 := by
  rw [← source157_checked, eval_normalize]
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

theorem source18_checked : normalize (row ![0, 0, 2, -2, 0, 0] ![0, 0, 2, -2, 0, 0] (6, 0)) = source18 := by
  decide +kernel

theorem source18_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source18 (momentValues f) = 0 := by
  rw [← source18_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source19_checked : normalize (row ![0, 0, 2, 0, -2, 0] ![0, 0, 2, 0, -2, 0] (6, 0)) = source19 := by
  decide +kernel

theorem source19_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source19 (momentValues f) = 0 := by
  rw [← source19_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source20_checked : normalize (row ![0, 0, 2, 0, 0, -2] ![0, 0, 2, 0, 0, -2] (6, 0)) = source20 := by
  decide +kernel

theorem source20_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source20 (momentValues f) = 0 := by
  rw [← source20_checked, eval_normalize]
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

theorem source169_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source169 := by
  decide +kernel

theorem source169_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source169 (momentValues f) = 0 := by
  rw [← source169_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source175_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source175 := by
  decide +kernel

theorem source175_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source175 (momentValues f) = 0 := by
  rw [← source175_checked, eval_normalize]
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

theorem source177_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source177 := by
  decide +kernel

theorem source177_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source177 (momentValues f) = 0 := by
  rw [← source177_checked, eval_normalize]
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

theorem source192_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![0, -1, 1, 0, 0, 0] (0, -3)) = source192 := by
  decide +kernel

theorem source192_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source192 (momentValues f) = 0 := by
  rw [← source192_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source194_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![0, -1, 1, 0, 0, 0] (0, -3)) = source194 := by
  decide +kernel

theorem source194_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source194 (momentValues f) = 0 := by
  rw [← source194_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source196_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![0, -1, 1, 0, 0, 0] (3, 3)) = source196 := by
  decide +kernel

theorem source196_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source196 (momentValues f) = 0 := by
  rw [← source196_checked, eval_normalize]
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

theorem source200_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, -1, 1, 0, 0, 0] (3, 3)) = source200 := by
  decide +kernel

theorem source200_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source200 (momentValues f) = 0 := by
  rw [← source200_checked, eval_normalize]
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

theorem source211_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, 1, 0, -1, 0, 0] (0, -3)) = source211 := by
  decide +kernel

theorem source211_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source211 (momentValues f) = 0 := by
  rw [← source211_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source215_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, 1, 0, -1, 0, 0] (3, 3)) = source215 := by
  decide +kernel

theorem source215_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source215 (momentValues f) = 0 := by
  rw [← source215_checked, eval_normalize]
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

theorem source229_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source229 := by
  decide +kernel

theorem source229_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source229 (momentValues f) = 0 := by
  rw [← source229_checked, eval_normalize]
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

theorem source235_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source235 := by
  decide +kernel

theorem source235_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source235 (momentValues f) = 0 := by
  rw [← source235_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source237_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source237 := by
  decide +kernel

theorem source237_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source237 (momentValues f) = 0 := by
  rw [← source237_checked, eval_normalize]
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

theorem source244_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![1, 0, -1, 0, 0, 0] (0, -3)) = source244 := by
  decide +kernel

theorem source244_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source244 (momentValues f) = 0 := by
  rw [← source244_checked, eval_normalize]
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

theorem source252_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![0, 1, -1, 0, 0, 0] (3, 3)) = source252 := by
  decide +kernel

theorem source252_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source252 (momentValues f) = 0 := by
  rw [← source252_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source254_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![0, 1, -1, 0, 0, 0] (0, -3)) = source254 := by
  decide +kernel

theorem source254_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source254 (momentValues f) = 0 := by
  rw [← source254_checked, eval_normalize]
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

theorem source256_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![0, 1, -1, 0, 0, 0] (0, -3)) = source256 := by
  decide +kernel

theorem source256_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source256 (momentValues f) = 0 := by
  rw [← source256_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source260_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 1, -1, 0, 0, 0] (3, 3)) = source260 := by
  decide +kernel

theorem source260_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source260 (momentValues f) = 0 := by
  rw [← source260_checked, eval_normalize]
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

theorem source268_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![0, 0, -1, 1, 0, 0] (0, -3)) = source268 := by
  decide +kernel

theorem source268_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source268 (momentValues f) = 0 := by
  rw [← source268_checked, eval_normalize]
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

theorem source272_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, 0, -1, 1, 0, 0] (0, -3)) = source272 := by
  decide +kernel

theorem source272_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source272 (momentValues f) = 0 := by
  rw [← source272_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source274_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, -1, 1, 0, 0] (3, 3)) = source274 := by
  decide +kernel

theorem source274_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source274 (momentValues f) = 0 := by
  rw [← source274_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source278_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![0, 0, -1, 0, 1, 0] (3, 3)) = source278 := by
  decide +kernel

theorem source278_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source278 (momentValues f) = 0 := by
  rw [← source278_checked, eval_normalize]
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

theorem source280_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![0, 0, -1, 0, 1, 0] (0, -3)) = source280 := by
  decide +kernel

theorem source280_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source280 (momentValues f) = 0 := by
  rw [← source280_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source282_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, 0, -1, 0, 1, 0] (0, -3)) = source282 := by
  decide +kernel

theorem source282_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source282 (momentValues f) = 0 := by
  rw [← source282_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source284_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, 0, -1, 0, 1, 0] (0, -3)) = source284 := by
  decide +kernel

theorem source284_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source284 (momentValues f) = 0 := by
  rw [← source284_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source286_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, -1, 0, 1, 0] (3, 3)) = source286 := by
  decide +kernel

theorem source286_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source286 (momentValues f) = 0 := by
  rw [← source286_checked, eval_normalize]
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

theorem source301_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source301 := by
  decide +kernel

theorem source301_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source301 (momentValues f) = 0 := by
  rw [← source301_checked, eval_normalize]
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

theorem source307_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source307 := by
  decide +kernel

theorem source307_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source307 (momentValues f) = 0 := by
  rw [← source307_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source311_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source311 := by
  decide +kernel

theorem source311_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source311 (momentValues f) = 0 := by
  rw [← source311_checked, eval_normalize]
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

theorem source319_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, -1, 0, 1, 0, 0] (3, 3)) = source319 := by
  decide +kernel

theorem source319_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source319 (momentValues f) = 0 := by
  rw [← source319_checked, eval_normalize]
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

theorem source39_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![-1, 0, 0, -1, 1, 1] (-12, 0)) = source39 := by
  decide +kernel

theorem source39_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source39 (momentValues f) = 0 := by
  rw [← source39_checked, eval_normalize]
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

theorem source323_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, -1, 0, 1, 0, 0] (3, 3)) = source323 := by
  decide +kernel

theorem source323_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source323 (momentValues f) = 0 := by
  rw [← source323_checked, eval_normalize]
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

theorem source328_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![0, 0, 1, -1, 0, 0] (0, -3)) = source328 := by
  decide +kernel

theorem source328_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source328 (momentValues f) = 0 := by
  rw [← source328_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source332_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, 0, 1, -1, 0, 0] (3, 3)) = source332 := by
  decide +kernel

theorem source332_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source332 (momentValues f) = 0 := by
  rw [← source332_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source334_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 1, -1, 0, 0] (0, -3)) = source334 := by
  decide +kernel

theorem source334_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source334 (momentValues f) = 0 := by
  rw [← source334_checked, eval_normalize]
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

theorem source355_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source355 := by
  decide +kernel

theorem source355_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source355 (momentValues f) = 0 := by
  rw [← source355_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source359_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source359 := by
  decide +kernel

theorem source359_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source359 (momentValues f) = 0 := by
  rw [← source359_checked, eval_normalize]
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

theorem source361_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![-1, 0, 0, 0, 1, 0] (0, -3)) = source361 := by
  decide +kernel

theorem source361_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source361 (momentValues f) = 0 := by
  rw [← source361_checked, eval_normalize]
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

theorem source386_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![0, 0, 1, 0, -1, 0] (3, 3)) = source386 := by
  decide +kernel

theorem source386_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source386 (momentValues f) = 0 := by
  rw [← source386_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source388_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![0, 0, 1, 0, -1, 0] (3, 3)) = source388 := by
  decide +kernel

theorem source388_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source388 (momentValues f) = 0 := by
  rw [← source388_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source390_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, 0, 1, 0, -1, 0] (3, 3)) = source390 := by
  decide +kernel

theorem source390_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source390 (momentValues f) = 0 := by
  rw [← source390_checked, eval_normalize]
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

theorem source392_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, 0, 1, 0, -1, 0] (0, -3)) = source392 := by
  decide +kernel

theorem source392_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source392 (momentValues f) = 0 := by
  rw [← source392_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source394_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 1, 0, -1, 0] (0, -3)) = source394 := by
  decide +kernel

theorem source394_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source394 (momentValues f) = 0 := by
  rw [← source394_checked, eval_normalize]
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

theorem source43_checked : normalize (row ![-1, 0, 1, -1, 1, 0] ![-1, 0, 1, -1, 1, 0] (-12, 0)) = source43 := by
  decide +kernel

theorem source43_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source43 (momentValues f) = 0 := by
  rw [← source43_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source45_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![-1, 0, 1, 0, 1, -1] (-12, 0)) = source45 := by
  decide +kernel

theorem source45_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source45 (momentValues f) = 0 := by
  rw [← source45_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source47_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![-1, 0, 1, 1, 0, -1] (-12, 0)) = source47 := by
  decide +kernel

theorem source47_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source47 (momentValues f) = 0 := by
  rw [← source47_checked, eval_normalize]
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

theorem source412_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source412 := by
  decide +kernel

theorem source412_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source412 (momentValues f) = 0 := by
  rw [← source412_checked, eval_normalize]
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

theorem source416_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source416 := by
  decide +kernel

theorem source416_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source416 (momentValues f) = 0 := by
  rw [← source416_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source419_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source419 := by
  decide +kernel

theorem source419_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source419 (momentValues f) = 0 := by
  rw [← source419_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source421_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source421 := by
  decide +kernel

theorem source421_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source421 (momentValues f) = 0 := by
  rw [← source421_checked, eval_normalize]
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

theorem source427_checked : normalize (row ![-1, 0, 1, 1, 0, -1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source427 := by
  decide +kernel

theorem source427_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source427 (momentValues f) = 0 := by
  rw [← source427_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source429_checked : normalize (row ![-1, 0, 1, 0, 1, -1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source429 := by
  decide +kernel

theorem source429_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source429 (momentValues f) = 0 := by
  rw [← source429_checked, eval_normalize]
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

theorem source433_checked : normalize (row ![1, -1, 1, 0, 0, -1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source433 := by
  decide +kernel

theorem source433_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source433 (momentValues f) = 0 := by
  rw [← source433_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source439_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source439 := by
  decide +kernel

theorem source439_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source439 (momentValues f) = 0 := by
  rw [← source439_checked, eval_normalize]
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

theorem source441_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, -1, 0, 0, 0, 1] (0, -3)) = source441 := by
  decide +kernel

theorem source441_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source441 (momentValues f) = 0 := by
  rw [← source441_checked, eval_normalize]
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

theorem source463_checked : normalize (row ![0, 1, 1, -1, 0, -1] ![0, 0, 0, -1, 0, 1] (3, 3)) = source463 := by
  decide +kernel

theorem source463_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source463 (momentValues f) = 0 := by
  rw [← source463_checked, eval_normalize]
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

theorem source467_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source467 := by
  decide +kernel

theorem source467_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source467 (momentValues f) = 0 := by
  rw [← source467_checked, eval_normalize]
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

theorem source472_checked : normalize (row ![-1, 0, 0, -1, 1, 1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source472 := by
  decide +kernel

theorem source472_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source472 (momentValues f) = 0 := by
  rw [← source472_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source476_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source476 := by
  decide +kernel

theorem source476_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source476 (momentValues f) = 0 := by
  rw [← source476_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source479_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source479 := by
  decide +kernel

theorem source479_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source479 (momentValues f) = 0 := by
  rw [← source479_checked, eval_normalize]
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

theorem source57_checked : normalize (row ![-1, 1, 1, -1, 0, 0] ![-1, 1, 1, -1, 0, 0] (-12, 0)) = source57 := by
  decide +kernel

theorem source57_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source57 (momentValues f) = 0 := by
  rw [← source57_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source58_checked : normalize (row ![-1, 1, 1, 0, -1, 0] ![-1, 1, 1, 0, -1, 0] (-12, 0)) = source58 := by
  decide +kernel

theorem source58_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source58 (momentValues f) = 0 := by
  rw [← source58_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source59_checked : normalize (row ![-1, 1, 1, 0, 0, -1] ![-1, 1, 1, 0, 0, -1] (-12, 0)) = source59 := by
  decide +kernel

theorem source59_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source59 (momentValues f) = 0 := by
  rw [← source59_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source63_checked : normalize (row ![0, -1, 0, -1, 1, 1] ![0, -1, 0, -1, 1, 1] (-12, 0)) = source63 := by
  decide +kernel

theorem source63_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source63 (momentValues f) = 0 := by
  rw [← source63_checked, eval_normalize]
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

theorem source67_checked : normalize (row ![0, -1, 1, -1, 1, 0] ![0, -1, 1, -1, 1, 0] (-12, 0)) = source67 := by
  decide +kernel

theorem source67_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source67 (momentValues f) = 0 := by
  rw [← source67_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source69_checked : normalize (row ![0, -1, 1, 0, 1, -1] ![0, -1, 1, 0, 1, -1] (-12, 0)) = source69 := by
  decide +kernel

theorem source69_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source69 (momentValues f) = 0 := by
  rw [← source69_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source71_checked : normalize (row ![0, -1, 1, 1, 0, -1] ![0, -1, 1, 1, 0, -1] (-12, 0)) = source71 := by
  decide +kernel

theorem source71_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source71 (momentValues f) = 0 := by
  rw [← source71_checked, eval_normalize]
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

theorem source76_checked : normalize (row ![0, 0, 1, -1, 1, -1] ![0, 0, 1, -1, 1, -1] (-12, 0)) = source76 := by
  decide +kernel

theorem source76_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source76 (momentValues f) = 0 := by
  rw [← source76_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source77_checked : normalize (row ![0, 0, 1, 1, -1, -1] ![0, 0, 1, 1, -1, -1] (-12, 0)) = source77 := by
  decide +kernel

theorem source77_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source77 (momentValues f) = 0 := by
  rw [← source77_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

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

theorem combined36_checked : Certificate.Integer.Sparse.merge source39 source155 = combined36 := by
  decide +kernel

theorem combined36_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined36 (momentValues f) = 0 := by
  rw [← combined36_checked, Certificate.Integer.Sparse.eval_merge,
    source39_zero f hcross, source155_zero f hcross, add_zero]

theorem combined37_checked : Certificate.Integer.Sparse.merge combined36 source311 = combined37 := by
  decide +kernel

theorem combined37_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined37 (momentValues f) = 0 := by
  rw [← combined37_checked, Certificate.Integer.Sparse.eval_merge,
    combined36_zero f hcross, source311_zero f hcross, add_zero]

theorem combined38_checked : Certificate.Integer.Sparse.merge combined37 source412 = combined38 := by
  decide +kernel

theorem combined38_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined38 (momentValues f) = 0 := by
  rw [← combined38_checked, Certificate.Integer.Sparse.eval_merge,
    combined37_zero f hcross, source412_zero f hcross, add_zero]

theorem combined39_checked : Certificate.Integer.Sparse.merge combined38 source472 = combined39 := by
  decide +kernel

theorem combined39_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined39 (momentValues f) = 0 := by
  rw [← combined39_checked, Certificate.Integer.Sparse.eval_merge,
    combined38_zero f hcross, source472_zero f hcross, add_zero]

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

theorem combined52_checked : Certificate.Integer.Sparse.merge source43 source151 = combined52 := by
  decide +kernel

theorem combined52_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined52 (momentValues f) = 0 := by
  rw [← combined52_checked, Certificate.Integer.Sparse.eval_merge,
    source43_zero f hcross, source151_zero f hcross, add_zero]

theorem combined53_checked : Certificate.Integer.Sparse.merge combined52 source278 = combined53 := by
  decide +kernel

theorem combined53_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined53 (momentValues f) = 0 := by
  rw [← combined53_checked, Certificate.Integer.Sparse.eval_merge,
    combined52_zero f hcross, source278_zero f hcross, add_zero]

theorem combined54_checked : Certificate.Integer.Sparse.merge combined53 source307 = combined54 := by
  decide +kernel

theorem combined54_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined54 (momentValues f) = 0 := by
  rw [← combined54_checked, Certificate.Integer.Sparse.eval_merge,
    combined53_zero f hcross, source307_zero f hcross, add_zero]

theorem combined55_checked : Certificate.Integer.Sparse.merge combined54 source386 = combined55 := by
  decide +kernel

theorem combined55_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined55 (momentValues f) = 0 := by
  rw [← combined55_checked, Certificate.Integer.Sparse.eval_merge,
    combined54_zero f hcross, source386_zero f hcross, add_zero]

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

theorem combined60_checked : Certificate.Integer.Sparse.merge source45 source177 = combined60 := by
  decide +kernel

theorem combined60_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined60 (momentValues f) = 0 := by
  rw [← combined60_checked, Certificate.Integer.Sparse.eval_merge,
    source45_zero f hcross, source177_zero f hcross, add_zero]

theorem combined61_checked : Certificate.Integer.Sparse.merge combined60 source280 = combined61 := by
  decide +kernel

theorem combined61_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined61 (momentValues f) = 0 := by
  rw [← combined61_checked, Certificate.Integer.Sparse.eval_merge,
    combined60_zero f hcross, source280_zero f hcross, add_zero]

theorem combined62_checked : Certificate.Integer.Sparse.merge combined61 source388 = combined62 := by
  decide +kernel

theorem combined62_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined62 (momentValues f) = 0 := by
  rw [← combined62_checked, Certificate.Integer.Sparse.eval_merge,
    combined61_zero f hcross, source388_zero f hcross, add_zero]

theorem combined63_checked : Certificate.Integer.Sparse.merge combined62 source429 = combined63 := by
  decide +kernel

theorem combined63_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined63 (momentValues f) = 0 := by
  rw [← combined63_checked, Certificate.Integer.Sparse.eval_merge,
    combined62_zero f hcross, source429_zero f hcross, add_zero]

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

theorem combined68_checked : Certificate.Integer.Sparse.merge source47 source175 = combined68 := by
  decide +kernel

theorem combined68_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined68 (momentValues f) = 0 := by
  rw [← combined68_checked, Certificate.Integer.Sparse.eval_merge,
    source47_zero f hcross, source175_zero f hcross, add_zero]

theorem combined69_checked : Certificate.Integer.Sparse.merge combined68 source268 = combined69 := by
  decide +kernel

theorem combined69_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined69 (momentValues f) = 0 := by
  rw [← combined69_checked, Certificate.Integer.Sparse.eval_merge,
    combined68_zero f hcross, source268_zero f hcross, add_zero]

theorem combined70_checked : Certificate.Integer.Sparse.merge combined69 source328 = combined70 := by
  decide +kernel

theorem combined70_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined70 (momentValues f) = 0 := by
  rw [← combined70_checked, Certificate.Integer.Sparse.eval_merge,
    combined69_zero f hcross, source328_zero f hcross, add_zero]

theorem combined71_checked : Certificate.Integer.Sparse.merge combined70 source427 = combined71 := by
  decide +kernel

theorem combined71_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined71 (momentValues f) = 0 := by
  rw [← combined71_checked, Certificate.Integer.Sparse.eval_merge,
    combined70_zero f hcross, source427_zero f hcross, add_zero]

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

theorem combined108_checked : Certificate.Integer.Sparse.merge source57 source145 = combined108 := by
  decide +kernel

theorem combined108_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined108 (momentValues f) = 0 := by
  rw [← combined108_checked, Certificate.Integer.Sparse.eval_merge,
    source57_zero f hcross, source145_zero f hcross, add_zero]

theorem combined109_checked : Certificate.Integer.Sparse.merge combined108 source192 = combined109 := by
  decide +kernel

theorem combined109_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined109 (momentValues f) = 0 := by
  rw [← combined109_checked, Certificate.Integer.Sparse.eval_merge,
    combined108_zero f hcross, source192_zero f hcross, add_zero]

theorem combined110_checked : Certificate.Integer.Sparse.merge combined109 source252 = combined110 := by
  decide +kernel

theorem combined110_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined110 (momentValues f) = 0 := by
  rw [← combined110_checked, Certificate.Integer.Sparse.eval_merge,
    combined109_zero f hcross, source252_zero f hcross, add_zero]

theorem combined111_checked : Certificate.Integer.Sparse.merge combined110 source301 = combined111 := by
  decide +kernel

theorem combined111_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined111 (momentValues f) = 0 := by
  rw [← combined111_checked, Certificate.Integer.Sparse.eval_merge,
    combined110_zero f hcross, source301_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined112_checked : Certificate.Integer.Sparse.merge source58 source157 = combined112 := by
  decide +kernel

theorem combined112_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined112 (momentValues f) = 0 := by
  rw [← combined112_checked, Certificate.Integer.Sparse.eval_merge,
    source58_zero f hcross, source157_zero f hcross, add_zero]

theorem combined113_checked : Certificate.Integer.Sparse.merge combined112 source194 = combined113 := by
  decide +kernel

theorem combined113_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined113 (momentValues f) = 0 := by
  rw [← combined113_checked, Certificate.Integer.Sparse.eval_merge,
    combined112_zero f hcross, source194_zero f hcross, add_zero]

theorem combined114_checked : Certificate.Integer.Sparse.merge combined113 source254 = combined114 := by
  decide +kernel

theorem combined114_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined114 (momentValues f) = 0 := by
  rw [← combined114_checked, Certificate.Integer.Sparse.eval_merge,
    combined113_zero f hcross, source254_zero f hcross, add_zero]

theorem combined115_checked : Certificate.Integer.Sparse.merge combined114 source361 = combined115 := by
  decide +kernel

theorem combined115_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined115 (momentValues f) = 0 := by
  rw [← combined115_checked, Certificate.Integer.Sparse.eval_merge,
    combined114_zero f hcross, source361_zero f hcross, add_zero]

theorem combined116_checked : Certificate.Integer.Sparse.merge source59 source169 = combined116 := by
  decide +kernel

theorem combined116_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined116 (momentValues f) = 0 := by
  rw [← combined116_checked, Certificate.Integer.Sparse.eval_merge,
    source59_zero f hcross, source169_zero f hcross, add_zero]

theorem combined117_checked : Certificate.Integer.Sparse.merge combined116 source196 = combined117 := by
  decide +kernel

theorem combined117_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined117 (momentValues f) = 0 := by
  rw [← combined117_checked, Certificate.Integer.Sparse.eval_merge,
    combined116_zero f hcross, source196_zero f hcross, add_zero]

theorem combined118_checked : Certificate.Integer.Sparse.merge combined117 source256 = combined118 := by
  decide +kernel

theorem combined118_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined118 (momentValues f) = 0 := by
  rw [← combined118_checked, Certificate.Integer.Sparse.eval_merge,
    combined117_zero f hcross, source256_zero f hcross, add_zero]

theorem combined119_checked : Certificate.Integer.Sparse.merge combined118 source421 = combined119 := by
  decide +kernel

theorem combined119_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined119 (momentValues f) = 0 := by
  rw [← combined119_checked, Certificate.Integer.Sparse.eval_merge,
    combined118_zero f hcross, source421_zero f hcross, add_zero]

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

theorem combined132_checked : Certificate.Integer.Sparse.merge source63 source215 = combined132 := by
  decide +kernel

theorem combined132_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined132 (momentValues f) = 0 := by
  rw [← combined132_checked, Certificate.Integer.Sparse.eval_merge,
    source63_zero f hcross, source215_zero f hcross, add_zero]

theorem combined133_checked : Certificate.Integer.Sparse.merge combined132 source323 = combined133 := by
  decide +kernel

theorem combined133_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined133 (momentValues f) = 0 := by
  rw [← combined133_checked, Certificate.Integer.Sparse.eval_merge,
    combined132_zero f hcross, source323_zero f hcross, add_zero]

theorem combined134_checked : Certificate.Integer.Sparse.merge combined133 source416 = combined134 := by
  decide +kernel

theorem combined134_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined134 (momentValues f) = 0 := by
  rw [← combined134_checked, Certificate.Integer.Sparse.eval_merge,
    combined133_zero f hcross, source416_zero f hcross, add_zero]

theorem combined135_checked : Certificate.Integer.Sparse.merge combined134 source476 = combined135 := by
  decide +kernel

theorem combined135_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined135 (momentValues f) = 0 := by
  rw [← combined135_checked, Certificate.Integer.Sparse.eval_merge,
    combined134_zero f hcross, source476_zero f hcross, add_zero]

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

theorem combined148_checked : Certificate.Integer.Sparse.merge source67 source211 = combined148 := by
  decide +kernel

theorem combined148_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined148 (momentValues f) = 0 := by
  rw [← combined148_checked, Certificate.Integer.Sparse.eval_merge,
    source67_zero f hcross, source211_zero f hcross, add_zero]

theorem combined149_checked : Certificate.Integer.Sparse.merge combined148 source282 = combined149 := by
  decide +kernel

theorem combined149_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined149 (momentValues f) = 0 := by
  rw [← combined149_checked, Certificate.Integer.Sparse.eval_merge,
    combined148_zero f hcross, source282_zero f hcross, add_zero]

theorem combined150_checked : Certificate.Integer.Sparse.merge combined149 source319 = combined150 := by
  decide +kernel

theorem combined150_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined150 (momentValues f) = 0 := by
  rw [← combined150_checked, Certificate.Integer.Sparse.eval_merge,
    combined149_zero f hcross, source319_zero f hcross, add_zero]

theorem combined151_checked : Certificate.Integer.Sparse.merge combined150 source390 = combined151 := by
  decide +kernel

theorem combined151_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined151 (momentValues f) = 0 := by
  rw [← combined151_checked, Certificate.Integer.Sparse.eval_merge,
    combined150_zero f hcross, source390_zero f hcross, add_zero]

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

theorem combined156_checked : Certificate.Integer.Sparse.merge source69 source237 = combined156 := by
  decide +kernel

theorem combined156_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined156 (momentValues f) = 0 := by
  rw [← combined156_checked, Certificate.Integer.Sparse.eval_merge,
    source69_zero f hcross, source237_zero f hcross, add_zero]

theorem combined157_checked : Certificate.Integer.Sparse.merge combined156 source284 = combined157 := by
  decide +kernel

theorem combined157_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined157 (momentValues f) = 0 := by
  rw [← combined157_checked, Certificate.Integer.Sparse.eval_merge,
    combined156_zero f hcross, source284_zero f hcross, add_zero]

theorem combined158_checked : Certificate.Integer.Sparse.merge combined157 source392 = combined158 := by
  decide +kernel

theorem combined158_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined158 (momentValues f) = 0 := by
  rw [← combined158_checked, Certificate.Integer.Sparse.eval_merge,
    combined157_zero f hcross, source392_zero f hcross, add_zero]

theorem combined159_checked : Certificate.Integer.Sparse.merge combined158 source441 = combined159 := by
  decide +kernel

theorem combined159_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined159 (momentValues f) = 0 := by
  rw [← combined159_checked, Certificate.Integer.Sparse.eval_merge,
    combined158_zero f hcross, source441_zero f hcross, add_zero]

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

theorem combined164_checked : Certificate.Integer.Sparse.merge source71 source235 = combined164 := by
  decide +kernel

theorem combined164_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined164 (momentValues f) = 0 := by
  rw [← combined164_checked, Certificate.Integer.Sparse.eval_merge,
    source71_zero f hcross, source235_zero f hcross, add_zero]

theorem combined165_checked : Certificate.Integer.Sparse.merge combined164 source272 = combined165 := by
  decide +kernel

theorem combined165_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined165 (momentValues f) = 0 := by
  rw [← combined165_checked, Certificate.Integer.Sparse.eval_merge,
    combined164_zero f hcross, source272_zero f hcross, add_zero]

theorem combined166_checked : Certificate.Integer.Sparse.merge combined165 source332 = combined166 := by
  decide +kernel

theorem combined166_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined166 (momentValues f) = 0 := by
  rw [← combined166_checked, Certificate.Integer.Sparse.eval_merge,
    combined165_zero f hcross, source332_zero f hcross, add_zero]

theorem combined167_checked : Certificate.Integer.Sparse.merge combined166 source439 = combined167 := by
  decide +kernel

theorem combined167_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined167 (momentValues f) = 0 := by
  rw [← combined167_checked, Certificate.Integer.Sparse.eval_merge,
    combined166_zero f hcross, source439_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined184_checked : Certificate.Integer.Sparse.merge source76 source286 = combined184 := by
  decide +kernel

theorem combined184_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined184 (momentValues f) = 0 := by
  rw [← combined184_checked, Certificate.Integer.Sparse.eval_merge,
    source76_zero f hcross, source286_zero f hcross, add_zero]

theorem combined185_checked : Certificate.Integer.Sparse.merge combined184 source359 = combined185 := by
  decide +kernel

theorem combined185_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined185 (momentValues f) = 0 := by
  rw [← combined185_checked, Certificate.Integer.Sparse.eval_merge,
    combined184_zero f hcross, source359_zero f hcross, add_zero]

theorem combined186_checked : Certificate.Integer.Sparse.merge combined185 source394 = combined186 := by
  decide +kernel

theorem combined186_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined186 (momentValues f) = 0 := by
  rw [← combined186_checked, Certificate.Integer.Sparse.eval_merge,
    combined185_zero f hcross, source394_zero f hcross, add_zero]

theorem combined187_checked : Certificate.Integer.Sparse.merge combined186 source467 = combined187 := by
  decide +kernel

theorem combined187_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined187 (momentValues f) = 0 := by
  rw [← combined187_checked, Certificate.Integer.Sparse.eval_merge,
    combined186_zero f hcross, source467_zero f hcross, add_zero]

theorem combined188_checked : Certificate.Integer.Sparse.merge source77 source274 = combined188 := by
  decide +kernel

theorem combined188_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined188 (momentValues f) = 0 := by
  rw [← combined188_checked, Certificate.Integer.Sparse.eval_merge,
    source77_zero f hcross, source274_zero f hcross, add_zero]

theorem combined189_checked : Certificate.Integer.Sparse.merge combined188 source334 = combined189 := by
  decide +kernel

theorem combined189_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined189 (momentValues f) = 0 := by
  rw [← combined189_checked, Certificate.Integer.Sparse.eval_merge,
    combined188_zero f hcross, source334_zero f hcross, add_zero]

theorem combined190_checked : Certificate.Integer.Sparse.merge combined189 source419 = combined190 := by
  decide +kernel

theorem combined190_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined190 (momentValues f) = 0 := by
  rw [← combined190_checked, Certificate.Integer.Sparse.eval_merge,
    combined189_zero f hcross, source419_zero f hcross, add_zero]

theorem combined191_checked : Certificate.Integer.Sparse.merge combined190 source479 = combined191 := by
  decide +kernel

theorem combined191_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined191 (momentValues f) = 0 := by
  rw [← combined191_checked, Certificate.Integer.Sparse.eval_merge,
    combined190_zero f hcross, source479_zero f hcross, add_zero]

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

theorem combined232_checked : Certificate.Integer.Sparse.merge source88 source200 = combined232 := by
  decide +kernel

theorem combined232_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined232 (momentValues f) = 0 := by
  rw [← combined232_checked, Certificate.Integer.Sparse.eval_merge,
    source88_zero f hcross, source200_zero f hcross, add_zero]

theorem combined233_checked : Certificate.Integer.Sparse.merge combined232 source260 = combined233 := by
  decide +kernel

theorem combined233_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined233 (momentValues f) = 0 := by
  rw [← combined233_checked, Certificate.Integer.Sparse.eval_merge,
    combined232_zero f hcross, source260_zero f hcross, add_zero]

theorem combined234_checked : Certificate.Integer.Sparse.merge combined233 source355 = combined234 := by
  decide +kernel

theorem combined234_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined234 (momentValues f) = 0 := by
  rw [← combined234_checked, Certificate.Integer.Sparse.eval_merge,
    combined233_zero f hcross, source355_zero f hcross, add_zero]

theorem combined235_checked : Certificate.Integer.Sparse.merge combined234 source463 = combined235 := by
  decide +kernel

theorem combined235_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined235 (momentValues f) = 0 := by
  rw [← combined235_checked, Certificate.Integer.Sparse.eval_merge,
    combined234_zero f hcross, source463_zero f hcross, add_zero]

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

theorem combined284_checked : Certificate.Integer.Sparse.merge source101 source136 = combined284 := by
  decide +kernel

theorem combined284_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined284 (momentValues f) = 0 := by
  rw [← combined284_checked, Certificate.Integer.Sparse.eval_merge,
    source101_zero f hcross, source136_zero f hcross, add_zero]

theorem combined285_checked : Certificate.Integer.Sparse.merge combined284 source229 = combined285 := by
  decide +kernel

theorem combined285_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined285 (momentValues f) = 0 := by
  rw [← combined285_checked, Certificate.Integer.Sparse.eval_merge,
    combined284_zero f hcross, source229_zero f hcross, add_zero]

theorem combined286_checked : Certificate.Integer.Sparse.merge combined285 source244 = combined286 := by
  decide +kernel

theorem combined286_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined286 (momentValues f) = 0 := by
  rw [← combined286_checked, Certificate.Integer.Sparse.eval_merge,
    combined285_zero f hcross, source244_zero f hcross, add_zero]

theorem combined287_checked : Certificate.Integer.Sparse.merge combined286 source433 = combined287 := by
  decide +kernel

theorem combined287_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined287 (momentValues f) = 0 := by
  rw [← combined287_checked, Certificate.Integer.Sparse.eval_merge,
    combined286_zero f hcross, source433_zero f hcross, add_zero]

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

theorem combined378_checked : Certificate.Integer.Sparse.merge combined377 combined39 = combined378 := by
  decide +kernel

theorem combined378_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined378 (momentValues f) = 0 := by
  rw [← combined378_checked, Certificate.Integer.Sparse.eval_merge,
    combined377_zero_e f hcross, combined39_zero f hcross, add_zero]

theorem combined379_checked : Certificate.Integer.Sparse.merge combined378 combined55 = combined379 := by
  decide +kernel

theorem combined379_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined379 (momentValues f) = 0 := by
  rw [← combined379_checked, Certificate.Integer.Sparse.eval_merge,
    combined378_zero f hcross, combined55_zero f hcross, add_zero]

theorem combined380_checked : Certificate.Integer.Sparse.merge combined379 combined151 = combined380 := by
  decide +kernel

theorem combined380_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined380 (momentValues f) = 0 := by
  rw [← combined380_checked, Certificate.Integer.Sparse.eval_merge,
    combined379_zero f hcross, combined151_zero f hcross, add_zero]

theorem combined381_checked : Certificate.Integer.Sparse.merge combined380 combined135 = combined381 := by
  decide +kernel

theorem combined381_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined381 (momentValues f) = 0 := by
  rw [← combined381_checked, Certificate.Integer.Sparse.eval_merge,
    combined380_zero f hcross, combined135_zero f hcross, add_zero]

theorem combined382_checked : Certificate.Integer.Sparse.merge combined381 source1 = combined382 := by
  decide +kernel

theorem combined382_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined382 (momentValues f) = 0 := by
  rw [← combined382_checked, Certificate.Integer.Sparse.eval_merge,
    combined381_zero f hcross, source1_zero f hcross, add_zero]

theorem combined383_checked : Certificate.Integer.Sparse.merge combined382 combined63 = combined383 := by
  decide +kernel

theorem combined383_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined383 (momentValues f) = 0 := by
  rw [← combined383_checked, Certificate.Integer.Sparse.eval_merge,
    combined382_zero f hcross, combined63_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined384_checked : Certificate.Integer.Sparse.merge combined383 combined71 = combined384 := by
  decide +kernel

theorem combined384_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined384 (momentValues f) = 0 := by
  rw [← combined384_checked, Certificate.Integer.Sparse.eval_merge,
    combined383_zero f hcross, combined71_zero f hcross, add_zero]

theorem combined385_checked : Certificate.Integer.Sparse.merge combined384 combined159 = combined385 := by
  decide +kernel

theorem combined385_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined385 (momentValues f) = 0 := by
  rw [← combined385_checked, Certificate.Integer.Sparse.eval_merge,
    combined384_zero f hcross, combined159_zero f hcross, add_zero]

theorem combined386_checked : Certificate.Integer.Sparse.merge combined385 combined167 = combined386 := by
  decide +kernel

theorem combined386_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined386 (momentValues f) = 0 := by
  rw [← combined386_checked, Certificate.Integer.Sparse.eval_merge,
    combined385_zero f hcross, combined167_zero f hcross, add_zero]

theorem combined387_checked : Certificate.Integer.Sparse.merge combined386 combined187 = combined387 := by
  decide +kernel

theorem combined387_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined387 (momentValues f) = 0 := by
  rw [← combined387_checked, Certificate.Integer.Sparse.eval_merge,
    combined386_zero f hcross, combined187_zero f hcross, add_zero]

theorem combined388_checked : Certificate.Integer.Sparse.merge combined387 combined191 = combined388 := by
  decide +kernel

theorem combined388_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined388 (momentValues f) = 0 := by
  rw [← combined388_checked, Certificate.Integer.Sparse.eval_merge,
    combined387_zero f hcross, combined191_zero f hcross, add_zero]

theorem combined389_checked : Certificate.Integer.Sparse.merge combined388 combined119 = combined389 := by
  decide +kernel

theorem combined389_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined389 (momentValues f) = 0 := by
  rw [← combined389_checked, Certificate.Integer.Sparse.eval_merge,
    combined388_zero f hcross, combined119_zero f hcross, add_zero]

theorem combined390_checked : Certificate.Integer.Sparse.merge combined389 combined287 = combined390 := by
  decide +kernel

theorem combined390_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined390 (momentValues f) = 0 := by
  rw [← combined390_checked, Certificate.Integer.Sparse.eval_merge,
    combined389_zero f hcross, combined287_zero f hcross, add_zero]

theorem combined391_checked : Certificate.Integer.Sparse.merge combined390 source20 = combined391 := by
  decide +kernel

theorem combined391_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined391 (momentValues f) = 0 := by
  rw [← combined391_checked, Certificate.Integer.Sparse.eval_merge,
    combined390_zero f hcross, source20_zero f hcross, add_zero]

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

theorem combined392_checked : Certificate.Integer.Sparse.merge combined391 source18 = combined392 := by
  decide +kernel

theorem combined392_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined392 (momentValues f) = 0 := by
  rw [← combined392_checked, Certificate.Integer.Sparse.eval_merge,
    combined391_zero f hcross, source18_zero f hcross, add_zero]

theorem combined393_checked : Certificate.Integer.Sparse.merge combined392 source19 = combined393 := by
  decide +kernel

theorem combined393_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined393 (momentValues f) = 0 := by
  rw [← combined393_checked, Certificate.Integer.Sparse.eval_merge,
    combined392_zero f hcross, source19_zero f hcross, add_zero]

theorem combined394_checked : Certificate.Integer.Sparse.merge combined393 combined235 = combined394 := by
  decide +kernel

theorem combined394_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined394 (momentValues f) = 0 := by
  rw [← combined394_checked, Certificate.Integer.Sparse.eval_merge,
    combined393_zero f hcross, combined235_zero f hcross, add_zero]

theorem combined395_checked : Certificate.Integer.Sparse.merge combined394 combined111 = combined395 := by
  decide +kernel

theorem combined395_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined395 (momentValues f) = 0 := by
  rw [← combined395_checked, Certificate.Integer.Sparse.eval_merge,
    combined394_zero f hcross, combined111_zero f hcross, add_zero]

theorem combined396_checked : Certificate.Integer.Sparse.merge combined395 combined115 = combined396 := by
  decide +kernel

theorem combined396_zero_e_oai (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined396 (momentValues f) = 0 := by
  rw [← combined396_checked, Certificate.Integer.Sparse.eval_merge,
    combined395_zero f hcross, combined115_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

theorem solution : type_of% @OAI.MUB6.TaoCertificate.combined396_zero_e_oai := @OAI.MUB6.TaoCertificate.combined396_zero_e_oai
