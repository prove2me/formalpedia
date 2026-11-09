-- Prove2me | solution 1 for OAI.MUB6.TaoCertificate.combined438_zero_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:20:20.584533+00:00
-- url     : https://prove2.me/submissions/8f3d8f33-86cf-403b-b2dc-771f599e4de6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E156
import Definitions.Def_OAIQ106E157
import Definitions.Def_OAIQ106E158
import Definitions.Def_OAIQ106E160
import Definitions.Def_OAIQ106E164
import Definitions.Def_OAIQ106E167
import Theorems.Thm_OAI_MUB6_TaoCertificate_combined414_zero_e

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

theorem source6_checked : normalize (row ![0, -2, 0, 0, 2, 0] ![0, -2, 0, 0, 2, 0] (6, 0)) = source6 := by
  decide +kernel

theorem source6_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source6 (momentValues f) = 0 := by
  rw [← source6_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source7_checked : normalize (row ![0, -2, 0, 2, 0, 0] ![0, -2, 0, 2, 0, 0] (6, 0)) = source7 := by
  decide +kernel

theorem source7_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source7 (momentValues f) = 0 := by
  rw [← source7_checked, eval_normalize]
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

theorem source12_checked : normalize (row ![0, 0, 0, -2, 0, 2] ![0, 0, 0, -2, 0, 2] (6, 0)) = source12 := by
  decide +kernel

theorem source12_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source12 (momentValues f) = 0 := by
  rw [← source12_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source14_checked : normalize (row ![0, 0, 0, 0, -2, 2] ![0, 0, 0, 0, -2, 2] (6, 0)) = source14 := by
  decide +kernel

theorem source14_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source14 (momentValues f) = 0 := by
  rw [← source14_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source15_checked : normalize (row ![0, 0, 0, 0, 2, -2] ![0, 0, 0, 0, 2, -2] (6, 0)) = source15 := by
  decide +kernel

theorem source15_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source15 (momentValues f) = 0 := by
  rw [← source15_checked, eval_normalize]
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

theorem source84_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 1, 0, -1, -1, 1] (-12, 0)) = source84 := by
  decide +kernel

theorem source84_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source84 (momentValues f) = 0 := by
  rw [← source84_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source86_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 1, 0, 1, -1, -1] (-12, 0)) = source86 := by
  decide +kernel

theorem source86_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source86 (momentValues f) = 0 := by
  rw [← source86_checked, eval_normalize]
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

theorem source93_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![1, -1, 0, -1, 0, 1] (-12, 0)) = source93 := by
  decide +kernel

theorem source93_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source93 (momentValues f) = 0 := by
  rw [← source93_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source95_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![1, -1, 0, 0, -1, 1] (-12, 0)) = source95 := by
  decide +kernel

theorem source95_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source95 (momentValues f) = 0 := by
  rw [← source95_checked, eval_normalize]
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

theorem source97_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![1, -1, 0, 1, -1, 0] (-12, 0)) = source97 := by
  decide +kernel

theorem source97_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source97 (momentValues f) = 0 := by
  rw [← source97_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source98_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![1, -1, 0, 1, 0, -1] (-12, 0)) = source98 := by
  decide +kernel

theorem source98_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source98 (momentValues f) = 0 := by
  rw [← source98_checked, eval_normalize]
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

theorem source108_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![1, 0, 0, -1, -1, 1] (-12, 0)) = source108 := by
  decide +kernel

theorem source108_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source108 (momentValues f) = 0 := by
  rw [← source108_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source110_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![1, 0, 0, 1, -1, -1] (-12, 0)) = source110 := by
  decide +kernel

theorem source110_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source110 (momentValues f) = 0 := by
  rw [← source110_checked, eval_normalize]
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

theorem source117_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![1, 1, 0, -1, -1, 0] (-12, 0)) = source117 := by
  decide +kernel

theorem source117_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source117 (momentValues f) = 0 := by
  rw [← source117_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source118_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![1, 1, 0, -1, 0, -1] (-12, 0)) = source118 := by
  decide +kernel

theorem source118_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source118 (momentValues f) = 0 := by
  rw [← source118_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source119_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![1, 1, 0, 0, -1, -1] (-12, 0)) = source119 := by
  decide +kernel

theorem source119_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source119 (momentValues f) = 0 := by
  rw [← source119_checked, eval_normalize]
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

theorem source126_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source126 := by
  decide +kernel

theorem source126_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source126 (momentValues f) = 0 := by
  rw [← source126_checked, eval_normalize]
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

theorem source128_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![-1, 1, 0, 0, 0, 0] (0, -3)) = source128 := by
  decide +kernel

theorem source128_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source128 (momentValues f) = 0 := by
  rw [← source128_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source130_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![-1, 1, 0, 0, 0, 0] (3, 3)) = source130 := by
  decide +kernel

theorem source130_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source130 (momentValues f) = 0 := by
  rw [← source130_checked, eval_normalize]
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

theorem source146_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![-1, 0, 0, 1, 0, 0] (0, -3)) = source146 := by
  decide +kernel

theorem source146_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source146 (momentValues f) = 0 := by
  rw [← source146_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source148_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source148 := by
  decide +kernel

theorem source148_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source148 (momentValues f) = 0 := by
  rw [← source148_checked, eval_normalize]
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

theorem source154_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![-1, 0, 0, 1, 0, 0] (3, 3)) = source154 := by
  decide +kernel

theorem source154_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source154 (momentValues f) = 0 := by
  rw [← source154_checked, eval_normalize]
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

theorem source16_checked : normalize (row ![0, 0, 0, 2, -2, 0] ![0, 0, 0, 2, -2, 0] (6, 0)) = source16 := by
  decide +kernel

theorem source16_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source16 (momentValues f) = 0 := by
  rw [← source16_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source17_checked : normalize (row ![0, 0, 0, 2, 0, -2] ![0, 0, 0, 2, 0, -2] (6, 0)) = source17 := by
  decide +kernel

theorem source17_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source17 (momentValues f) = 0 := by
  rw [← source17_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source22_checked : normalize (row ![0, 2, 0, -2, 0, 0] ![0, 2, 0, -2, 0, 0] (6, 0)) = source22 := by
  decide +kernel

theorem source22_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source22 (momentValues f) = 0 := by
  rw [← source22_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source23_checked : normalize (row ![0, 2, 0, 0, -2, 0] ![0, 2, 0, 0, -2, 0] (6, 0)) = source23 := by
  decide +kernel

theorem source23_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source23 (momentValues f) = 0 := by
  rw [← source23_checked, eval_normalize]
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

theorem source170_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source170 := by
  decide +kernel

theorem source170_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source170 (momentValues f) = 0 := by
  rw [← source170_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source172_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![-1, 0, 0, 0, 0, 1] (0, -3)) = source172 := by
  decide +kernel

theorem source172_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source172 (momentValues f) = 0 := by
  rw [← source172_checked, eval_normalize]
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

theorem source178_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![-1, 0, 0, 0, 0, 1] (3, 3)) = source178 := by
  decide +kernel

theorem source178_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source178 (momentValues f) = 0 := by
  rw [← source178_checked, eval_normalize]
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

theorem source186_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![1, -1, 0, 0, 0, 0] (3, 3)) = source186 := by
  decide +kernel

theorem source186_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source186 (momentValues f) = 0 := by
  rw [← source186_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source188_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![1, -1, 0, 0, 0, 0] (3, 3)) = source188 := by
  decide +kernel

theorem source188_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source188 (momentValues f) = 0 := by
  rw [← source188_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source190_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![1, -1, 0, 0, 0, 0] (0, -3)) = source190 := by
  decide +kernel

theorem source190_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source190 (momentValues f) = 0 := by
  rw [← source190_checked, eval_normalize]
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

theorem source209_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![0, 1, 0, -1, 0, 0] (0, -3)) = source209 := by
  decide +kernel

theorem source209_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source209 (momentValues f) = 0 := by
  rw [← source209_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source214_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, -1, 0, 1, 0, 0] (0, -3)) = source214 := by
  decide +kernel

theorem source214_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source214 (momentValues f) = 0 := by
  rw [← source214_checked, eval_normalize]
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

theorem source219_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![0, 1, 0, 0, -1, 0] (3, 3)) = source219 := by
  decide +kernel

theorem source219_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source219 (momentValues f) = 0 := by
  rw [← source219_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source221_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![0, 1, 0, 0, -1, 0] (0, -3)) = source221 := by
  decide +kernel

theorem source221_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source221 (momentValues f) = 0 := by
  rw [← source221_checked, eval_normalize]
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

theorem source231_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![0, 1, 0, 0, 0, -1] (3, 3)) = source231 := by
  decide +kernel

theorem source231_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source231 (momentValues f) = 0 := by
  rw [← source231_checked, eval_normalize]
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

theorem source238_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source238 := by
  decide +kernel

theorem source238_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source238 (momentValues f) = 0 := by
  rw [← source238_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source239_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source239 := by
  decide +kernel

theorem source239_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source239 (momentValues f) = 0 := by
  rw [← source239_checked, eval_normalize]
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

theorem source24_checked : normalize (row ![0, 2, 0, 0, 0, -2] ![0, 2, 0, 0, 0, -2] (6, 0)) = source24 := by
  decide +kernel

theorem source24_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source24 (momentValues f) = 0 := by
  rw [← source24_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source28_checked : normalize (row ![2, 0, 0, 0, -2, 0] ![2, 0, 0, 0, -2, 0] (6, 0)) = source28 := by
  decide +kernel

theorem source28_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source28 (momentValues f) = 0 := by
  rw [← source28_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source29_checked : normalize (row ![2, 0, 0, 0, 0, -2] ![2, 0, 0, 0, 0, -2] (6, 0)) = source29 := by
  decide +kernel

theorem source29_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source29 (momentValues f) = 0 := by
  rw [← source29_checked, eval_normalize]
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

theorem source302_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![1, 0, 0, -1, 0, 0] (3, 3)) = source302 := by
  decide +kernel

theorem source302_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source302 (momentValues f) = 0 := by
  rw [← source302_checked, eval_normalize]
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

theorem source304_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![1, 0, 0, -1, 0, 0] (3, 3)) = source304 := by
  decide +kernel

theorem source304_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source304 (momentValues f) = 0 := by
  rw [← source304_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source310_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![1, 0, 0, -1, 0, 0] (0, -3)) = source310 := by
  decide +kernel

theorem source310_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source310 (momentValues f) = 0 := by
  rw [← source310_checked, eval_normalize]
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

theorem source317_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![0, -1, 0, 1, 0, 0] (3, 3)) = source317 := by
  decide +kernel

theorem source317_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source317 (momentValues f) = 0 := by
  rw [← source317_checked, eval_normalize]
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

theorem source322_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 1, 0, -1, 0, 0] (0, -3)) = source322 := by
  decide +kernel

theorem source322_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source322 (momentValues f) = 0 := by
  rw [← source322_checked, eval_normalize]
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

theorem source337_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![0, 0, 0, 1, -1, 0] (3, 3)) = source337 := by
  decide +kernel

theorem source337_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source337 (momentValues f) = 0 := by
  rw [← source337_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source341_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![0, 0, 0, 1, -1, 0] (3, 3)) = source341 := by
  decide +kernel

theorem source341_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source341 (momentValues f) = 0 := by
  rw [← source341_checked, eval_normalize]
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

theorem source344_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, 0, 0, -1, 1, 0] (3, 3)) = source344 := by
  decide +kernel

theorem source344_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source344 (momentValues f) = 0 := by
  rw [← source344_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source345_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 0, 0, 1, -1, 0] (0, -3)) = source345 := by
  decide +kernel

theorem source345_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source345 (momentValues f) = 0 := by
  rw [← source345_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source349_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![0, 0, 0, 1, 0, -1] (3, 3)) = source349 := by
  decide +kernel

theorem source349_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source349 (momentValues f) = 0 := by
  rw [← source349_checked, eval_normalize]
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

theorem source375_checked : normalize (row ![1, -1, 0, 1, -1, 0] ![0, -1, 0, 0, 1, 0] (0, -3)) = source375 := by
  decide +kernel

theorem source375_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source375 (momentValues f) = 0 := by
  rw [← source375_checked, eval_normalize]
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

theorem source377_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![0, -1, 0, 0, 1, 0] (0, -3)) = source377 := by
  decide +kernel

theorem source377_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source377 (momentValues f) = 0 := by
  rw [← source377_checked, eval_normalize]
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

theorem source397_checked : normalize (row ![1, 1, 0, -1, -1, 0] ![0, 0, 0, -1, 1, 0] (3, 3)) = source397 := by
  decide +kernel

theorem source397_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source397 (momentValues f) = 0 := by
  rw [← source397_checked, eval_normalize]
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

theorem source401_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![0, 0, 0, -1, 1, 0] (0, -3)) = source401 := by
  decide +kernel

theorem source401_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source401 (momentValues f) = 0 := by
  rw [← source401_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source404_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, 0, 0, 1, -1, 0] (0, -3)) = source404 := by
  decide +kernel

theorem source404_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source404 (momentValues f) = 0 := by
  rw [← source404_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source405_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 0, 0, -1, 1, 0] (3, 3)) = source405 := by
  decide +kernel

theorem source405_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source405 (momentValues f) = 0 := by
  rw [← source405_checked, eval_normalize]
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

theorem source409_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![0, 0, 0, 0, 1, -1] (3, 3)) = source409 := by
  decide +kernel

theorem source409_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source409 (momentValues f) = 0 := by
  rw [← source409_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source413_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source413 := by
  decide +kernel

theorem source413_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source413 (momentValues f) = 0 := by
  rw [← source413_checked, eval_normalize]
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

theorem source417_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 0, 0, 0, 1, -1] (0, -3)) = source417 := by
  decide +kernel

theorem source417_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source417 (momentValues f) = 0 := by
  rw [← source417_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source422_checked : normalize (row ![1, -1, 0, -1, 0, 1] ![1, 0, 0, 0, 0, -1] (3, 3)) = source422 := by
  decide +kernel

theorem source422_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source422 (momentValues f) = 0 := by
  rw [← source422_checked, eval_normalize]
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

theorem source424_checked : normalize (row ![1, -1, 0, 0, -1, 1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source424 := by
  decide +kernel

theorem source424_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source424 (momentValues f) = 0 := by
  rw [← source424_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source430_checked : normalize (row ![1, 0, 0, -1, -1, 1] ![1, 0, 0, 0, 0, -1] (0, -3)) = source430 := by
  decide +kernel

theorem source430_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source430 (momentValues f) = 0 := by
  rw [← source430_checked, eval_normalize]
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

theorem source435_checked : normalize (row ![1, -1, 0, 1, 0, -1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source435 := by
  decide +kernel

theorem source435_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source435 (momentValues f) = 0 := by
  rw [← source435_checked, eval_normalize]
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

theorem source442_checked : normalize (row ![0, 1, 0, -1, -1, 1] ![0, 1, 0, 0, 0, -1] (0, -3)) = source442 := by
  decide +kernel

theorem source442_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source442 (momentValues f) = 0 := by
  rw [← source442_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source443_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, -1, 0, 0, 0, 1] (3, 3)) = source443 := by
  decide +kernel

theorem source443_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source443 (momentValues f) = 0 := by
  rw [← source443_checked, eval_normalize]
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

theorem source457_checked : normalize (row ![1, 1, 0, -1, 0, -1] ![0, 0, 0, -1, 0, 1] (0, -3)) = source457 := by
  decide +kernel

theorem source457_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source457 (momentValues f) = 0 := by
  rw [← source457_checked, eval_normalize]
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

theorem source469_checked : normalize (row ![1, 1, 0, 0, -1, -1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source469 := by
  decide +kernel

theorem source469_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source469 (momentValues f) = 0 := by
  rw [← source469_checked, eval_normalize]
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

theorem source473_checked : normalize (row ![1, 0, 0, 1, -1, -1] ![0, 0, 0, 0, -1, 1] (3, 3)) = source473 := by
  decide +kernel

theorem source473_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source473 (momentValues f) = 0 := by
  rw [← source473_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

theorem source477_checked : normalize (row ![0, 1, 0, 1, -1, -1] ![0, 0, 0, 0, -1, 1] (0, -3)) = source477 := by
  decide +kernel

theorem source477_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source477 (momentValues f) = 0 := by
  rw [← source477_checked, eval_normalize]
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

theorem source65_checked : normalize (row ![0, -1, 0, 1, 1, -1] ![0, -1, 0, 1, 1, -1] (-12, 0)) = source65 := by
  decide +kernel

theorem source65_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval source65 (momentValues f) = 0 := by
  rw [← source65_checked, eval_normalize]
  apply eval_row_zero f hcross
  · unfold Balanced; decide +kernel
  · unfold Balanced; decide +kernel

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

theorem combined140_checked : Certificate.Integer.Sparse.merge source65 source239 = combined140 := by
  decide +kernel

theorem combined140_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined140 (momentValues f) = 0 := by
  rw [← combined140_checked, Certificate.Integer.Sparse.eval_merge,
    source65_zero f hcross, source239_zero f hcross, add_zero]

theorem combined141_checked : Certificate.Integer.Sparse.merge combined140 source344 = combined141 := by
  decide +kernel

theorem combined141_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined141 (momentValues f) = 0 := by
  rw [← combined141_checked, Certificate.Integer.Sparse.eval_merge,
    combined140_zero f hcross, source344_zero f hcross, add_zero]

theorem combined142_checked : Certificate.Integer.Sparse.merge combined141 source404 = combined142 := by
  decide +kernel

theorem combined142_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined142 (momentValues f) = 0 := by
  rw [← combined142_checked, Certificate.Integer.Sparse.eval_merge,
    combined141_zero f hcross, source404_zero f hcross, add_zero]

theorem combined143_checked : Certificate.Integer.Sparse.merge combined142 source443 = combined143 := by
  decide +kernel

theorem combined143_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined143 (momentValues f) = 0 := by
  rw [← combined143_checked, Certificate.Integer.Sparse.eval_merge,
    combined142_zero f hcross, source443_zero f hcross, add_zero]

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

theorem combined216_checked : Certificate.Integer.Sparse.merge source84 source238 = combined216 := by
  decide +kernel

theorem combined216_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined216 (momentValues f) = 0 := by
  rw [← combined216_checked, Certificate.Integer.Sparse.eval_merge,
    source84_zero f hcross, source238_zero f hcross, add_zero]

theorem combined217_checked : Certificate.Integer.Sparse.merge combined216 source345 = combined217 := by
  decide +kernel

theorem combined217_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined217 (momentValues f) = 0 := by
  rw [← combined217_checked, Certificate.Integer.Sparse.eval_merge,
    combined216_zero f hcross, source345_zero f hcross, add_zero]

theorem combined218_checked : Certificate.Integer.Sparse.merge combined217 source405 = combined218 := by
  decide +kernel

theorem combined218_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined218 (momentValues f) = 0 := by
  rw [← combined218_checked, Certificate.Integer.Sparse.eval_merge,
    combined217_zero f hcross, source405_zero f hcross, add_zero]

theorem combined219_checked : Certificate.Integer.Sparse.merge combined218 source442 = combined219 := by
  decide +kernel

theorem combined219_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined219 (momentValues f) = 0 := by
  rw [← combined219_checked, Certificate.Integer.Sparse.eval_merge,
    combined218_zero f hcross, source442_zero f hcross, add_zero]

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

theorem combined224_checked : Certificate.Integer.Sparse.merge source86 source214 = combined224 := by
  decide +kernel

theorem combined224_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined224 (momentValues f) = 0 := by
  rw [← combined224_checked, Certificate.Integer.Sparse.eval_merge,
    source86_zero f hcross, source214_zero f hcross, add_zero]

theorem combined225_checked : Certificate.Integer.Sparse.merge combined224 source322 = combined225 := by
  decide +kernel

theorem combined225_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined225 (momentValues f) = 0 := by
  rw [← combined225_checked, Certificate.Integer.Sparse.eval_merge,
    combined224_zero f hcross, source322_zero f hcross, add_zero]

theorem combined226_checked : Certificate.Integer.Sparse.merge combined225 source417 = combined226 := by
  decide +kernel

theorem combined226_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined226 (momentValues f) = 0 := by
  rw [← combined226_checked, Certificate.Integer.Sparse.eval_merge,
    combined225_zero f hcross, source417_zero f hcross, add_zero]

theorem combined227_checked : Certificate.Integer.Sparse.merge combined226 source477 = combined227 := by
  decide +kernel

theorem combined227_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined227 (momentValues f) = 0 := by
  rw [← combined227_checked, Certificate.Integer.Sparse.eval_merge,
    combined226_zero f hcross, source477_zero f hcross, add_zero]

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

theorem combined252_checked : Certificate.Integer.Sparse.merge source93 source170 = combined252 := by
  decide +kernel

theorem combined252_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined252 (momentValues f) = 0 := by
  rw [← combined252_checked, Certificate.Integer.Sparse.eval_merge,
    source93_zero f hcross, source170_zero f hcross, add_zero]

theorem combined253_checked : Certificate.Integer.Sparse.merge combined252 source209 = combined253 := by
  decide +kernel

theorem combined253_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined253 (momentValues f) = 0 := by
  rw [← combined253_checked, Certificate.Integer.Sparse.eval_merge,
    combined252_zero f hcross, source209_zero f hcross, add_zero]

theorem combined254_checked : Certificate.Integer.Sparse.merge combined253 source317 = combined254 := by
  decide +kernel

theorem combined254_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined254 (momentValues f) = 0 := by
  rw [← combined254_checked, Certificate.Integer.Sparse.eval_merge,
    combined253_zero f hcross, source317_zero f hcross, add_zero]

theorem combined255_checked : Certificate.Integer.Sparse.merge combined254 source422 = combined255 := by
  decide +kernel

theorem combined255_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined255 (momentValues f) = 0 := by
  rw [← combined255_checked, Certificate.Integer.Sparse.eval_merge,
    combined254_zero f hcross, source422_zero f hcross, add_zero]

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

theorem combined260_checked : Certificate.Integer.Sparse.merge source95 source172 = combined260 := by
  decide +kernel

theorem combined260_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined260 (momentValues f) = 0 := by
  rw [← combined260_checked, Certificate.Integer.Sparse.eval_merge,
    source95_zero f hcross, source172_zero f hcross, add_zero]

theorem combined261_checked : Certificate.Integer.Sparse.merge combined260 source221 = combined261 := by
  decide +kernel

theorem combined261_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined261 (momentValues f) = 0 := by
  rw [← combined261_checked, Certificate.Integer.Sparse.eval_merge,
    combined260_zero f hcross, source221_zero f hcross, add_zero]

theorem combined262_checked : Certificate.Integer.Sparse.merge combined261 source377 = combined262 := by
  decide +kernel

theorem combined262_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined262 (momentValues f) = 0 := by
  rw [← combined262_checked, Certificate.Integer.Sparse.eval_merge,
    combined261_zero f hcross, source377_zero f hcross, add_zero]

theorem combined263_checked : Certificate.Integer.Sparse.merge combined262 source424 = combined263 := by
  decide +kernel

theorem combined263_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined263 (momentValues f) = 0 := by
  rw [← combined263_checked, Certificate.Integer.Sparse.eval_merge,
    combined262_zero f hcross, source424_zero f hcross, add_zero]

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

theorem combined268_checked : Certificate.Integer.Sparse.merge source97 source146 = combined268 := by
  decide +kernel

theorem combined268_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined268 (momentValues f) = 0 := by
  rw [← combined268_checked, Certificate.Integer.Sparse.eval_merge,
    source97_zero f hcross, source146_zero f hcross, add_zero]

theorem combined269_checked : Certificate.Integer.Sparse.merge combined268 source219 = combined269 := by
  decide +kernel

theorem combined269_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined269 (momentValues f) = 0 := by
  rw [← combined269_checked, Certificate.Integer.Sparse.eval_merge,
    combined268_zero f hcross, source219_zero f hcross, add_zero]

theorem combined270_checked : Certificate.Integer.Sparse.merge combined269 source302 = combined270 := by
  decide +kernel

theorem combined270_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined270 (momentValues f) = 0 := by
  rw [← combined270_checked, Certificate.Integer.Sparse.eval_merge,
    combined269_zero f hcross, source302_zero f hcross, add_zero]

theorem combined271_checked : Certificate.Integer.Sparse.merge combined270 source375 = combined271 := by
  decide +kernel

theorem combined271_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined271 (momentValues f) = 0 := by
  rw [← combined271_checked, Certificate.Integer.Sparse.eval_merge,
    combined270_zero f hcross, source375_zero f hcross, add_zero]

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

theorem combined272_checked : Certificate.Integer.Sparse.merge source98 source148 = combined272 := by
  decide +kernel

theorem combined272_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined272 (momentValues f) = 0 := by
  rw [← combined272_checked, Certificate.Integer.Sparse.eval_merge,
    source98_zero f hcross, source148_zero f hcross, add_zero]

theorem combined273_checked : Certificate.Integer.Sparse.merge combined272 source231 = combined273 := by
  decide +kernel

theorem combined273_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined273 (momentValues f) = 0 := by
  rw [← combined273_checked, Certificate.Integer.Sparse.eval_merge,
    combined272_zero f hcross, source231_zero f hcross, add_zero]

theorem combined274_checked : Certificate.Integer.Sparse.merge combined273 source304 = combined274 := by
  decide +kernel

theorem combined274_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined274 (momentValues f) = 0 := by
  rw [← combined274_checked, Certificate.Integer.Sparse.eval_merge,
    combined273_zero f hcross, source304_zero f hcross, add_zero]

theorem combined275_checked : Certificate.Integer.Sparse.merge combined274 source435 = combined275 := by
  decide +kernel

theorem combined275_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined275 (momentValues f) = 0 := by
  rw [← combined275_checked, Certificate.Integer.Sparse.eval_merge,
    combined274_zero f hcross, source435_zero f hcross, add_zero]

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

theorem combined312_checked : Certificate.Integer.Sparse.merge source108 source178 = combined312 := by
  decide +kernel

theorem combined312_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined312 (momentValues f) = 0 := by
  rw [← combined312_checked, Certificate.Integer.Sparse.eval_merge,
    source108_zero f hcross, source178_zero f hcross, add_zero]

theorem combined313_checked : Certificate.Integer.Sparse.merge combined312 source341 = combined313 := by
  decide +kernel

theorem combined313_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined313 (momentValues f) = 0 := by
  rw [← combined313_checked, Certificate.Integer.Sparse.eval_merge,
    combined312_zero f hcross, source341_zero f hcross, add_zero]

theorem combined314_checked : Certificate.Integer.Sparse.merge combined313 source401 = combined314 := by
  decide +kernel

theorem combined314_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined314 (momentValues f) = 0 := by
  rw [← combined314_checked, Certificate.Integer.Sparse.eval_merge,
    combined313_zero f hcross, source401_zero f hcross, add_zero]

theorem combined315_checked : Certificate.Integer.Sparse.merge combined314 source430 = combined315 := by
  decide +kernel

theorem combined315_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined315 (momentValues f) = 0 := by
  rw [← combined315_checked, Certificate.Integer.Sparse.eval_merge,
    combined314_zero f hcross, source430_zero f hcross, add_zero]

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

theorem combined320_checked : Certificate.Integer.Sparse.merge source110 source154 = combined320 := by
  decide +kernel

theorem combined320_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined320 (momentValues f) = 0 := by
  rw [← combined320_checked, Certificate.Integer.Sparse.eval_merge,
    source110_zero f hcross, source154_zero f hcross, add_zero]

theorem combined321_checked : Certificate.Integer.Sparse.merge combined320 source310 = combined321 := by
  decide +kernel

theorem combined321_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined321 (momentValues f) = 0 := by
  rw [← combined321_checked, Certificate.Integer.Sparse.eval_merge,
    combined320_zero f hcross, source310_zero f hcross, add_zero]

theorem combined322_checked : Certificate.Integer.Sparse.merge combined321 source413 = combined322 := by
  decide +kernel

theorem combined322_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined322 (momentValues f) = 0 := by
  rw [← combined322_checked, Certificate.Integer.Sparse.eval_merge,
    combined321_zero f hcross, source413_zero f hcross, add_zero]

theorem combined323_checked : Certificate.Integer.Sparse.merge combined322 source473 = combined323 := by
  decide +kernel

theorem combined323_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined323 (momentValues f) = 0 := by
  rw [← combined323_checked, Certificate.Integer.Sparse.eval_merge,
    combined322_zero f hcross, source473_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined348_checked : Certificate.Integer.Sparse.merge source117 source126 = combined348 := by
  decide +kernel

theorem combined348_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined348 (momentValues f) = 0 := by
  rw [← combined348_checked, Certificate.Integer.Sparse.eval_merge,
    source117_zero f hcross, source126_zero f hcross, add_zero]

theorem combined349_checked : Certificate.Integer.Sparse.merge combined348 source186 = combined349 := by
  decide +kernel

theorem combined349_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined349 (momentValues f) = 0 := by
  rw [← combined349_checked, Certificate.Integer.Sparse.eval_merge,
    combined348_zero f hcross, source186_zero f hcross, add_zero]

theorem combined350_checked : Certificate.Integer.Sparse.merge combined349 source337 = combined350 := by
  decide +kernel

theorem combined350_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined350 (momentValues f) = 0 := by
  rw [← combined350_checked, Certificate.Integer.Sparse.eval_merge,
    combined349_zero f hcross, source337_zero f hcross, add_zero]

theorem combined351_checked : Certificate.Integer.Sparse.merge combined350 source397 = combined351 := by
  decide +kernel

theorem combined351_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined351 (momentValues f) = 0 := by
  rw [← combined351_checked, Certificate.Integer.Sparse.eval_merge,
    combined350_zero f hcross, source397_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined352_checked : Certificate.Integer.Sparse.merge source118 source128 = combined352 := by
  decide +kernel

theorem combined352_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined352 (momentValues f) = 0 := by
  rw [← combined352_checked, Certificate.Integer.Sparse.eval_merge,
    source118_zero f hcross, source128_zero f hcross, add_zero]

theorem combined353_checked : Certificate.Integer.Sparse.merge combined352 source188 = combined353 := by
  decide +kernel

theorem combined353_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined353 (momentValues f) = 0 := by
  rw [← combined353_checked, Certificate.Integer.Sparse.eval_merge,
    combined352_zero f hcross, source188_zero f hcross, add_zero]

theorem combined354_checked : Certificate.Integer.Sparse.merge combined353 source349 = combined354 := by
  decide +kernel

theorem combined354_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined354 (momentValues f) = 0 := by
  rw [← combined354_checked, Certificate.Integer.Sparse.eval_merge,
    combined353_zero f hcross, source349_zero f hcross, add_zero]

theorem combined355_checked : Certificate.Integer.Sparse.merge combined354 source457 = combined355 := by
  decide +kernel

theorem combined355_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined355 (momentValues f) = 0 := by
  rw [← combined355_checked, Certificate.Integer.Sparse.eval_merge,
    combined354_zero f hcross, source457_zero f hcross, add_zero]

theorem combined356_checked : Certificate.Integer.Sparse.merge source119 source130 = combined356 := by
  decide +kernel

theorem combined356_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined356 (momentValues f) = 0 := by
  rw [← combined356_checked, Certificate.Integer.Sparse.eval_merge,
    source119_zero f hcross, source130_zero f hcross, add_zero]

theorem combined357_checked : Certificate.Integer.Sparse.merge combined356 source190 = combined357 := by
  decide +kernel

theorem combined357_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined357 (momentValues f) = 0 := by
  rw [← combined357_checked, Certificate.Integer.Sparse.eval_merge,
    combined356_zero f hcross, source190_zero f hcross, add_zero]

theorem combined358_checked : Certificate.Integer.Sparse.merge combined357 source409 = combined358 := by
  decide +kernel

theorem combined358_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined358 (momentValues f) = 0 := by
  rw [← combined358_checked, Certificate.Integer.Sparse.eval_merge,
    combined357_zero f hcross, source409_zero f hcross, add_zero]

theorem combined359_checked : Certificate.Integer.Sparse.merge combined358 source469 = combined359 := by
  decide +kernel

theorem combined359_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined359 (momentValues f) = 0 := by
  rw [← combined359_checked, Certificate.Integer.Sparse.eval_merge,
    combined358_zero f hcross, source469_zero f hcross, add_zero]

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

theorem combined415_checked : Certificate.Integer.Sparse.merge combined414 combined227 = combined415 := by
  decide +kernel

theorem combined415_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined415 (momentValues f) = 0 := by
  rw [← combined415_checked, Certificate.Integer.Sparse.eval_merge,
    combined414_zero_e f hcross, combined227_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined416_checked : Certificate.Integer.Sparse.merge combined415 source16 = combined416 := by
  decide +kernel

theorem combined416_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined416 (momentValues f) = 0 := by
  rw [← combined416_checked, Certificate.Integer.Sparse.eval_merge,
    combined415_zero f hcross, source16_zero f hcross, add_zero]

theorem combined417_checked : Certificate.Integer.Sparse.merge combined416 source24 = combined417 := by
  decide +kernel

theorem combined417_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined417 (momentValues f) = 0 := by
  rw [← combined417_checked, Certificate.Integer.Sparse.eval_merge,
    combined416_zero f hcross, source24_zero f hcross, add_zero]

theorem combined418_checked : Certificate.Integer.Sparse.merge combined417 source7 = combined418 := by
  decide +kernel

theorem combined418_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined418 (momentValues f) = 0 := by
  rw [← combined418_checked, Certificate.Integer.Sparse.eval_merge,
    combined417_zero f hcross, source7_zero f hcross, add_zero]

theorem combined419_checked : Certificate.Integer.Sparse.merge combined418 source14 = combined419 := by
  decide +kernel

theorem combined419_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined419 (momentValues f) = 0 := by
  rw [← combined419_checked, Certificate.Integer.Sparse.eval_merge,
    combined418_zero f hcross, source14_zero f hcross, add_zero]

theorem combined420_checked : Certificate.Integer.Sparse.merge combined419 source15 = combined420 := by
  decide +kernel

theorem combined420_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined420 (momentValues f) = 0 := by
  rw [← combined420_checked, Certificate.Integer.Sparse.eval_merge,
    combined419_zero f hcross, source15_zero f hcross, add_zero]

theorem combined421_checked : Certificate.Integer.Sparse.merge combined420 source6 = combined421 := by
  decide +kernel

theorem combined421_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined421 (momentValues f) = 0 := by
  rw [← combined421_checked, Certificate.Integer.Sparse.eval_merge,
    combined420_zero f hcross, source6_zero f hcross, add_zero]

theorem combined422_checked : Certificate.Integer.Sparse.merge combined421 combined143 = combined422 := by
  decide +kernel

theorem combined422_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined422 (momentValues f) = 0 := by
  rw [← combined422_checked, Certificate.Integer.Sparse.eval_merge,
    combined421_zero f hcross, combined143_zero f hcross, add_zero]

theorem combined423_checked : Certificate.Integer.Sparse.merge combined422 source17 = combined423 := by
  decide +kernel

theorem combined423_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined423 (momentValues f) = 0 := by
  rw [← combined423_checked, Certificate.Integer.Sparse.eval_merge,
    combined422_zero f hcross, source17_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_TaoCertificate_Merge53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined424_checked : Certificate.Integer.Sparse.merge combined423 combined323 = combined424 := by
  decide +kernel

theorem combined424_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined424 (momentValues f) = 0 := by
  rw [← combined424_checked, Certificate.Integer.Sparse.eval_merge,
    combined423_zero f hcross, combined323_zero f hcross, add_zero]

theorem combined425_checked : Certificate.Integer.Sparse.merge combined424 combined271 = combined425 := by
  decide +kernel

theorem combined425_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined425 (momentValues f) = 0 := by
  rw [← combined425_checked, Certificate.Integer.Sparse.eval_merge,
    combined424_zero f hcross, combined271_zero f hcross, add_zero]

theorem combined426_checked : Certificate.Integer.Sparse.merge combined425 combined275 = combined426 := by
  decide +kernel

theorem combined426_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined426 (momentValues f) = 0 := by
  rw [← combined426_checked, Certificate.Integer.Sparse.eval_merge,
    combined425_zero f hcross, combined275_zero f hcross, add_zero]

theorem combined427_checked : Certificate.Integer.Sparse.merge combined426 combined263 = combined427 := by
  decide +kernel

theorem combined427_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined427 (momentValues f) = 0 := by
  rw [← combined427_checked, Certificate.Integer.Sparse.eval_merge,
    combined426_zero f hcross, combined263_zero f hcross, add_zero]

theorem combined428_checked : Certificate.Integer.Sparse.merge combined427 combined359 = combined428 := by
  decide +kernel

theorem combined428_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined428 (momentValues f) = 0 := by
  rw [← combined428_checked, Certificate.Integer.Sparse.eval_merge,
    combined427_zero f hcross, combined359_zero f hcross, add_zero]

theorem combined429_checked : Certificate.Integer.Sparse.merge combined428 source28 = combined429 := by
  decide +kernel

theorem combined429_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined429 (momentValues f) = 0 := by
  rw [← combined429_checked, Certificate.Integer.Sparse.eval_merge,
    combined428_zero f hcross, source28_zero f hcross, add_zero]

theorem combined430_checked : Certificate.Integer.Sparse.merge combined429 source29 = combined430 := by
  decide +kernel

theorem combined430_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined430 (momentValues f) = 0 := by
  rw [← combined430_checked, Certificate.Integer.Sparse.eval_merge,
    combined429_zero f hcross, source29_zero f hcross, add_zero]

theorem combined431_checked : Certificate.Integer.Sparse.merge combined430 source23 = combined431 := by
  decide +kernel

theorem combined431_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined431 (momentValues f) = 0 := by
  rw [← combined431_checked, Certificate.Integer.Sparse.eval_merge,
    combined430_zero f hcross, source23_zero f hcross, add_zero]

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

theorem combined432_checked : Certificate.Integer.Sparse.merge combined431 combined219 = combined432 := by
  decide +kernel

theorem combined432_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined432 (momentValues f) = 0 := by
  rw [← combined432_checked, Certificate.Integer.Sparse.eval_merge,
    combined431_zero f hcross, combined219_zero f hcross, add_zero]

theorem combined433_checked : Certificate.Integer.Sparse.merge combined432 combined351 = combined433 := by
  decide +kernel

theorem combined433_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined433 (momentValues f) = 0 := by
  rw [← combined433_checked, Certificate.Integer.Sparse.eval_merge,
    combined432_zero f hcross, combined351_zero f hcross, add_zero]

theorem combined434_checked : Certificate.Integer.Sparse.merge combined433 combined315 = combined434 := by
  decide +kernel

theorem combined434_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined434 (momentValues f) = 0 := by
  rw [← combined434_checked, Certificate.Integer.Sparse.eval_merge,
    combined433_zero f hcross, combined315_zero f hcross, add_zero]

theorem combined435_checked : Certificate.Integer.Sparse.merge combined434 combined355 = combined435 := by
  decide +kernel

theorem combined435_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined435 (momentValues f) = 0 := by
  rw [← combined435_checked, Certificate.Integer.Sparse.eval_merge,
    combined434_zero f hcross, combined355_zero f hcross, add_zero]

theorem combined436_checked : Certificate.Integer.Sparse.merge combined435 source22 = combined436 := by
  decide +kernel

theorem combined436_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined436 (momentValues f) = 0 := by
  rw [← combined436_checked, Certificate.Integer.Sparse.eval_merge,
    combined435_zero f hcross, source22_zero f hcross, add_zero]

theorem combined437_checked : Certificate.Integer.Sparse.merge combined436 combined255 = combined437 := by
  decide +kernel

theorem combined437_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined437 (momentValues f) = 0 := by
  rw [← combined437_checked, Certificate.Integer.Sparse.eval_merge,
    combined436_zero f hcross, combined255_zero f hcross, add_zero]

theorem combined438_checked : Certificate.Integer.Sparse.merge combined437 source12 = combined438 := by
  decide +kernel

theorem combined438_zero_e_oai (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined438 (momentValues f) = 0 := by
  rw [← combined438_checked, Certificate.Integer.Sparse.eval_merge,
    combined437_zero f hcross, source12_zero f hcross, add_zero]

end MUB6.TaoCertificate

end OAI
end

theorem solution : type_of% @OAI.MUB6.TaoCertificate.combined438_zero_e_oai := @OAI.MUB6.TaoCertificate.combined438_zero_e_oai
