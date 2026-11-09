-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:46:18.206554+00:00
-- url     : https://prove2.me/submissions/6d35f015-e273-40b6-8fa6-b9379167443f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E119
import Definitions.Def_OAIQ106E122
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E139
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E141
import Definitions.Def_OAIQ106E142
import Definitions.Def_OAIQ106E144
import Definitions.Def_OAIQ106E145
import Definitions.Def_OAIQ106E146
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E148
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E171

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mathematical definitions for the exact Fourier companion.

The character normalization is exactly 1/6, not an unnormalized sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_ne_zero {z : ℂ} (hz : Complex.normSq z = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem character_add (x : Coord → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply, zpow_add₀ (hx _), Finset.prod_mul_distrib]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem unit_inv_eq_conj {z : ℂ} (hz : Complex.normSq z = 1) : z⁻¹ = conj z := by
  simp [Complex.inv_def, hz]

theorem character_neg (x : Coord → ℂ) (hx : ∀ i, Complex.normSq (x i) = 1)
    (a : Charge) : character x (-a) = conj (character x a) := by
  simp only [character, Pi.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro i _
  rw [← unit_inv_eq_conj (hx i), inv_zpow]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Hadamard
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

theorem IsHadamard.row_gram {H : CMatrix} (hH : IsHadamard H) :
    H * Hᴴ = (6 : ℂ) • (1 : CMatrix) := by
  have hl : ((6 : ℂ)⁻¹ • Hᴴ) * H = (1 : CMatrix) := by
    rw [smul_mul_assoc, hH.2, smul_smul]
    norm_num
  have hr := mul_eq_one_comm.mp hl
  rw [mul_smul_comm] at hr
  have hs := congrArg (fun M : CMatrix => (6 : ℂ) • M) hr
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul]
    using hs

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.row_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, H i k * conj (H j k) = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.row_gram
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem IsHadamard.transpose {H : CMatrix} (hH : IsHadamard H) :
    IsHadamard H.transpose := by
  refine ⟨fun i j => hH.1 j i, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm] using
    hH.row_orthogonal j i

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

theorem g_difference {H : CMatrix} (hH : IsHadamard H) (i j : Coord) :
    g H (difference i j) = if i = j then 1 else 0 := by
  simp only [g, character_difference _ (fun k => hH.1 k _)]
  rw [hH.row_orthogonal]
  split_ifs <;> norm_num

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_Transitions
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sqrt_six_square : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
  have h : Real.sqrt 6 ^ 2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  exact_mod_cast h

theorem sqrt_six_normSq : Complex.normSq (Real.sqrt 6 : ℂ) = 6 := by
  rw [Complex.normSq_ofReal]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]

theorem transition_column_inner (b c d : Basis) (k l : Coord) :
    (∑ i, conj (transition b c i k) * transition b d i l) =
      6 * inner ℂ (c k) (d l) := by
  have hterm (i : Coord) : conj (transition b c i k) * transition b d i l =
      6 * (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by
    simp only [transition, map_mul, Complex.conj_ofReal, inner_conj_symm]
    calc
      _ = (Real.sqrt 6 : ℂ) ^ 2 *
        (inner ℂ (c k) (b i) * inner ℂ (b i) (d l)) := by ring
      _ = _ := by rw [sqrt_six_square]
  simp_rw [hterm]
  rw [← Finset.mul_sum, b.sum_inner_mul_inner]

theorem transition_isHadamard {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (r s : Fin m) (hrs : r ≠ s) : IsHadamard (transition (B r) (B s)) := by
  refine ⟨?_, ?_⟩
  · intro i k
    rw [transition, map_mul, sqrt_six_normSq, hB r s hrs i k]
    norm_num
  · ext i j
    change (∑ k, conj (transition (B r) (B s) k i) * transition (B r) (B s) k j) =
      (6 : ℂ) * (if i = j then 1 else 0)
    rw [transition_column_inner, (B s).inner_eq_ite]

theorem transition_reverse (b c : Basis) :
    transition c b = (transition b c).conjTranspose := by
  ext i j
  simp [transition, Matrix.conjTranspose_apply]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Fourier_ChargeDecomposition
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem weightMultiset_card (w : Coord → ℕ) :
    (weightMultiset w).card = ∑ i, w i := by
  have h (s : Finset Coord) : (∑ i ∈ s, Multiset.replicate (w i) i).card = ∑ i ∈ s, w i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.card_add, ih]
  exact h Finset.univ

theorem weightMultiset_count (w : Coord → ℕ) (k : Coord) :
    (weightMultiset w).count k = w k := by
  have h (s : Finset Coord) :
      (∑ i ∈ s, Multiset.replicate (w i) i).count k = ∑ i ∈ s, if i = k then w i else 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.sum_insert hi, Multiset.count_add, Multiset.count_replicate, ih]
  simpa [weightMultiset] using h Finset.univ

theorem positivePositions_card (a : Charge) : (positivePositions a).card = order a :=
  weightMultiset_card _

theorem negativePositions_card {a : Charge} (ha : Balanced a) :
    (negativePositions a).card = order a := by
  have h : (∑ i, ((a i).toNat : ℤ)) - ∑ i, ((-a i).toNat : ℤ) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [Int.toNat_sub_toNat_neg] using (show ∑ i, a i = 0 from ha)
  rw [negativePositions, weightMultiset_card, order]
  exact_mod_cast (sub_eq_zero.mp h).symm

theorem charge_eq_counts (a : Charge) (k : Coord) :
    a k = ((positivePositions a).count k : ℤ) - (negativePositions a).count k := by
  rw [positivePositions, negativePositions, weightMultiset_count, weightMultiset_count]
  exact (Int.toNat_sub_toNat_neg _).symm

theorem positive_negative_ne {a : Charge} {i j : Coord}
    (hi : i ∈ positivePositions a) (hj : j ∈ negativePositions a) : i ≠ j := by
  intro h
  subst j
  rw [← Multiset.count_pos, positivePositions, weightMultiset_count] at hi
  rw [← Multiset.count_pos, negativePositions, weightMultiset_count] at hj
  have hp := Int.pos_iff_toNat_pos.mpr hi
  have hn := Int.pos_iff_toNat_pos.mpr hj
  omega

/-- A balanced charge of order one is one positive and one negative coordinate. -/
theorem order_one_decomposition {a : Charge} (ha : Balanced a) (ho : order a = 1) :
    ∃ i j, i ≠ j ∧ a = difference i j := by
  obtain ⟨i, hi⟩ := Multiset.card_eq_one.mp ((positivePositions_card a).trans ho)
  obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp ((negativePositions_card ha).trans ho)
  refine ⟨i, j, positive_negative_ne (a := a) (by simp [hi]) (by simp [hj]), ?_⟩
  funext k
  rw [charge_eq_counts a k, hi, hj]
  simp [difference, Pi.single_apply, Multiset.count_singleton, eq_comm]

theorem g_order_one {H : CMatrix} (hH : IsHadamard H) {a : Charge}
    (ha : Balanced a) (ho : order a = 1) : g H a = 0 := by
  obtain ⟨i, j, hij, rfl⟩ := order_one_decomposition ha ho
  simp [g_difference hH, hij]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Bases_CompleteFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem relativeMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : IsHadamard (relativeMatrix B r s) :=
  transition_isHadamard B hB r (r.succAbove s) (r.ne_succAbove s)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Averages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MUB6

theorem average_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → ℝ) : average (f ∘ e) = average f := by
  simp only [average, Fintype.card_congr e, Function.comp_apply, e.sum_comp]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem average_congr {f g : ι → ℝ} (h : ∀ i, f i = g i) :
    average f = average g := by
  congr 1
  exact funext h

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

theorem average_comm (f : ι → κ → ℝ) :
    average (fun i => average (fun k => f i k)) =
      average (fun k => average (fun i => f i k)) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_eq_card_mul_average (f : ι → ℝ) :
    (∑ i, f i) = (Fintype.card ι : ℝ) * average f := by
  classical
  by_cases hc : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    simp [average]
  · have hcr : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hc
    simp only [average, ← mul_assoc, mul_inv_cancel₀ hcr, one_mul]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sampling identities. The splitting theorem below is the counting
step behind contraction of an order-one row; it is independent of the values
of the matrix entries and uses no certificate data. -/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

variable {A B V : Type*} [Fintype A] [Fintype B] [AddCommMonoid V]

theorem sum_split_embedding (e : A ↪ B) (f : B → V) :
    (∑ b, f b) = (∑ a, f (e a)) + ∑ b : {b // b ∉ Set.range e}, f b := by
  classical
  let E : A ⊕ {b // b ∉ Set.range e} ≃ B :=
    (e.toEquivRange.sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range e))
  have h := E.sum_comp f
  simpa [E, Fintype.sum_sum_type, Equiv.trans_apply, Equiv.sumCongr_apply] using h.symm

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

theorem sum_samples_split {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin p ↪ B, ∑ b, f e b) =
      (∑ e : Fin p ↪ B, ∑ j, f e (e j)) +
      ∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0) := by
  classical
  calc
    _ = ∑ e : Fin p ↪ B,
        ((∑ j, f e (e j)) + ∑ b : {b // b ∉ Set.range e}, f e b) := by
      apply Finset.sum_congr rfl
      intro e _
      exact sum_split_embedding e (f e)
    _ = _ := by rw [Finset.sum_add_distrib, sum_injective_extension]

theorem sum_contraction {p : ℕ} (f : (Fin p ↪ B) → B → V)
    (h : ∀ e, ∑ b, f e b = 0) :
    (∑ j : Fin p, ∑ e : Fin p ↪ B, f e (e j)) +
      (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) = 0 := by
  classical
  rw [Finset.sum_comm]
  rw [← sum_samples_split]
  simp [h]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SamplingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.Sampling

theorem unused_card {p n : ℕ} (e : Fin p ↪ Fin n)
    [Fintype {i // i ∉ Set.range e}] :
    Fintype.card {i // i ∉ Set.range e} = n - p := by
  rw [Fintype.card_subtype_compl]
  have hr : Fintype.card {i // i ∈ Set.range e} = p := by
    rw [Fintype.card_range, Fintype.card_fin]
  rw [hr, Fintype.card_fin]

theorem embedding_succ_card (p n : ℕ) :
    Fintype.card (Fin (p + 1) ↪ Fin n) =
      Fintype.card (Fin p ↪ Fin n) * (n - p) := by
  rw [Fintype.card_congr (Equiv.embeddingFinSucc p (Fin n)), Fintype.card_sigma]
  simp only [unused_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]

theorem sum_dropFirst {p n : ℕ} (f : (Fin p ↪ Fin n) → ℝ) :
    (∑ e : Fin (p + 1) ↪ Fin n, f (dropFirst e)) =
      (n - p : ℕ) * ∑ e, f e := by
  have hs := sum_injective_extension (fun e (_ : Fin n) => f e)
  rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.card_subtype_compl, Fintype.card_range, Fintype.card_fin, Fintype.card_fin]

/-- Deleting a coordinate of a uniform injection leaves a uniform injection. -/
theorem average_dropFirst {p n : ℕ} (hp : p < n) (f : (Fin p ↪ Fin n) → ℝ) :
    average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e)) = average f := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  unfold average
  rw [embedding_succ_card, Nat.cast_mul, sum_dropFirst, mul_inv_rev]
  calc
    _ = (((n - p : ℕ) : ℝ)⁻¹ * (n - p : ℕ)) *
        ((Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ * ∑ e, f e) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

/-- The normalized counting identity used for an order-one contraction.
At most n rows are sampled; the saturated boundary case is separate. -/
theorem average_contraction {p n : ℕ} (hp : p < n)
    (f : (Fin p ↪ Fin n) → Fin n → ℝ) (h : ∀ e, ∑ b, f e b = 0) :
    ((n - p : ℕ) : ℝ) *
      average (fun e : Fin (p + 1) ↪ Fin n => f (dropFirst e) (e 0)) +
      (∑ j : Fin p, average (fun e : Fin p ↪ Fin n => f e (e j))) = 0 := by
  have hd : ((n - p : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hp)
  have hc : ((n - p : ℕ) : ℝ) * (Fintype.card (Fin (p + 1) ↪ Fin n) : ℝ)⁻¹ =
      (Fintype.card (Fin p ↪ Fin n) : ℝ)⁻¹ := by
    rw [embedding_succ_card, Nat.cast_mul, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  have hs := sum_contraction f h
  simp only [average]
  rw [← mul_assoc, hc, ← Finset.mul_sum, ← mul_add]
  rw [add_comm] at hs
  rw [hs, mul_zero]

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentSymmetry
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem injectiveMoment_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A = average (fun ρ : Fin p ↪ Coord =>
      average (fun κ : Fin q ↪ Coord =>
        ((exponentMonomial H A ρ κ).re +
          (exponentMonomial H.transpose A ρ κ).re) / 2)) :=
  average_prod _

theorem injectiveMoment_reverse_iterated {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    (average (fun κ : Fin q ↪ Coord => average (fun ρ : Fin p ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))) = injectiveMoment H A := by
  rw [average_comm]
  exact (injectiveMoment_iterated H A).symm

theorem exponentMonomial_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A.transpose κ ρ = exponentMonomial H.transpose A ρ κ := by
  exact Finset.prod_comm

theorem injectiveMoment_transpose {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    injectiveMoment H A.transpose = injectiveMoment H A := by
  rw [injectiveMoment_iterated, injectiveMoment_iterated, average_comm]
  apply average_congr
  intro ρ
  apply average_congr
  intro κ
  rw [exponentMonomial_transpose, exponentMonomial_transpose]
  simp only [Matrix.transpose_transpose, add_comm]

theorem exponentMonomial_neg {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (A : Matrix (Fin p) (Fin q) ℤ) (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (-A) ρ κ = conj (exponentMonomial H A ρ κ) := by
  simp only [exponentMonomial, Matrix.neg_apply, zpow_neg, map_prod, map_zpow₀]
  apply Finset.prod_congr rfl
  intro u _
  apply Finset.prod_congr rfl
  intro v _
  rw [← unit_inv_eq_conj (hH (ρ u) (κ v)), inv_zpow]

theorem injectiveMoment_neg {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : injectiveMoment H (-A) = injectiveMoment H A := by
  apply average_congr
  intro s
  rw [exponentMonomial_neg H hH.1, exponentMonomial_neg H.transpose hH.transpose.1]
  simp

theorem exponentMonomial_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p))
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H (fun i j => A (σ i) j) ρ κ =
      exponentMonomial H A (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) κ := by
  unfold exponentMonomial
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => ∏ j, H (ρ (σ.symm i)) (κ j) ^ A i j)

theorem injectiveMoment_row_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin p)) :
    injectiveMoment H (fun i j => A (σ i) j) = injectiveMoment H A := by
  rw [injectiveMoment_iterated H (fun i j => A (σ i) j), injectiveMoment_iterated H A]
  simp_rw [exponentMonomial_row_permutation H A σ,
    exponentMonomial_row_permutation H.transpose A σ]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2))

theorem injectiveMoment_column_permutation {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) (σ : Equiv.Perm (Fin q)) :
    injectiveMoment H (fun i j => A i (σ j)) = injectiveMoment H A := by
  rw [← injectiveMoment_transpose H (fun i j => A i (σ j))]
  change injectiveMoment H (fun i j => A.transpose (σ i) j) = _
  rw [injectiveMoment_row_permutation, injectiveMoment_transpose]

theorem exponentMonomial_zero_first_row {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    exponentMonomial H A ρ κ =
      exponentMonomial H (fun i j => A i.succ j) (Sampling.dropFirst ρ) κ := by
  simp only [exponentMonomial, Fin.prod_univ_succ, hA, zpow_zero,
    Finset.prod_const_one, one_mul]
  rfl

theorem injectiveMoment_zero_first_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (hA : ∀ j, A 0 j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i.succ j) := by
  rw [injectiveMoment_iterated H A,
    injectiveMoment_iterated H (fun i j => A i.succ j)]
  simp_rw [exponentMonomial_zero_first_row H A hA,
    exponentMonomial_zero_first_row H.transpose A hA]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H (fun i j => A i.succ j) ρ κ).re +
        (exponentMonomial H.transpose (fun i j => A i.succ j) ρ κ).re) / 2))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Canonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small semantic steps used by the generated canonicalization traces. Each
step preserves the actual averaged injective moment. The finite side conditions
(state dimensions, permutation inverses, and zero entries) are checked separately.
-/
noncomputable section
namespace MUB6.Certificate

/-- Move a zero row to the front and delete it. -/
theorem moment_delete_zero_row {p q : ℕ} (hp : p < 6) (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (σ : Equiv.Perm (Fin (p + 1)))
    (hzero : ∀ j, A (σ 0) j = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i.succ) j) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i.succ) j) :=
      injectiveMoment_zero_first_row hp H _ hzero

/-- The column version uses the transpose symmetry already present in the
manuscript's normalization. -/
theorem moment_delete_zero_column {p q : ℕ} (hq : q < 6) (H : CMatrix)
    (A : Matrix (Fin p) (Fin (q + 1)) ℤ) (σ : Equiv.Perm (Fin (q + 1)))
    (hzero : ∀ i, A i (σ 0) = 0) :
    injectiveMoment H A = injectiveMoment H (fun i j => A i (σ j.succ)) := by
  calc
    injectiveMoment H A = injectiveMoment H A.transpose :=
      (injectiveMoment_transpose H A).symm
    _ = injectiveMoment H (fun i j => A.transpose (σ i.succ) j) :=
      moment_delete_zero_row hq H A.transpose σ hzero
    _ = injectiveMoment H (fun i j => A i (σ j.succ)) :=
      injectiveMoment_transpose H (fun i j => A i (σ j.succ))

/-- Simultaneous row and column relabeling. -/
theorem moment_permute {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ)
    (σ : Equiv.Perm (Fin p)) (τ : Equiv.Perm (Fin q)) :
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) (τ j)) := by
  calc
    injectiveMoment H A = injectiveMoment H (fun i j => A (σ i) j) :=
      (injectiveMoment_row_permutation H A σ).symm
    _ = injectiveMoment H (fun i j => A (σ i) (τ j)) :=
      (injectiveMoment_column_permutation H (fun i j => A (σ i) j) τ).symm

end MUB6.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
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

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_Interpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reindexing and averaging preserve the interpretation of sparse forms.
These algebraic facts connect finite checked coefficients to actual moments. -/
namespace MUB6.Certificate

namespace Sparse

variable {ι κ Ω : Type*}

theorem eval_average [Fintype Ω] (v : Sparse ι) (x : Ω → ι → ℝ) :
    eval v (fun i => average (fun ω => x ω i)) =
      average (fun ω => eval v (x ω)) := by
  induction v with
  | nil => simp
  | cons p v ih =>
    simp only [eval_cons, average_add, average_mul, ih]

end Sparse

end MUB6.Certificate

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_PartitionExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    {z : ℂ} (hz : z ≠ 0) : (∏ i ∈ s, z ^ a i) = z ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]

theorem product_grouped {n k : ℕ} (label : Fin n → Fin k)
    (x : Fin k → ℂ) (hx : ∀ b, x b ≠ 0) (a : Fin n → ℤ) :
    (∏ j, x (label j) ^ a j) = ∏ b, x b ^ (∑ j with label j = b, a j) := by
  rw [← Finset.prod_fiberwise Finset.univ label]
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_zpow_eq_zpow_sum _ a (hx b)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [(Finset.mem_filter.mp hj).2]

theorem rawMonomial_grouped {p n k : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (ρ : Fin p ↪ Coord) (κ : Fin k ↪ Coord) :
    rawMonomial H A ρ (fun j => κ (label j)) =
      exponentMonomial H (groupedColumns A label) ρ κ := by
  unfold rawMonomial exponentMonomial groupedColumns
  apply Finset.prod_congr rfl
  intro i _
  exact product_grouped label (fun b => H (ρ i) (κ b))
    (fun b => unit_ne_zero (hH.1 _ _)) (fun j => A i j)

theorem rowFourier_product_expand {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) (ρ : Fin p ↪ Coord) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ κ : Fin n → Coord, rawMonomial H A ρ κ := by
  simp only [rowFourier, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  exact Finset.prod_comm

/-- The unnormalized equality-partition identity. The factor `(6)_k` in
the manuscript is exactly the cardinality of the inner injection type. -/
theorem rowFourier_partition_expand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    (∏ j, rowFourier H ρ (fun i => A i j)) =
      (6 : ℂ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        exponentMonomial H (groupedColumns A (F.label s)) ρ κ := by
  rw [rowFourier_product_expand]
  have hs := (F.assignmentsEquiv cover).sum_comp
    (fun κ : Fin n → Coord => rawMonomial H A ρ κ)
  change (∑ s : Σ s, Fin (F.blocks s) ↪ Coord,
    rawMonomial H A ρ (fun i => s.2 (F.label s.1 i))) = _ at hs
  rw [Fintype.sum_sigma] at hs
  rw [← hs]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro κ _
  exact rawMonomial_grouped hH A (F.label s) ρ κ

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem embedCharge_outside {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (i : Coord)
    (hi : i ∉ Set.range ρ) : embedCharge ρ a i = 0 :=
  Function.extend_apply' _ _ _ hi

theorem embedCharge_sum {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    ∑ i, embedCharge ρ a i = ∑ i, a i := by
  symm
  exact Fintype.sum_of_injective ρ ρ.injective a (embedCharge ρ a)
    (embedCharge_outside ρ a) (fun i => (embedCharge_apply ρ a i).symm)

theorem embedCharge_order {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    order (embedCharge ρ a) = ∑ i, (a i).toNat := by
  symm
  apply Fintype.sum_of_injective ρ ρ.injective (fun i => (a i).toNat)
    (fun i => (embedCharge ρ a i).toNat)
  · intro i hi
    rw [embedCharge_outside ρ a i hi]
    rfl
  · intro i
    rw [embedCharge_apply]

theorem character_embedCharge {p : ℕ} (x : Coord → ℂ) (ρ : Fin p ↪ Coord)
    (a : Fin p → ℤ) : character x (embedCharge ρ a) = ∏ i, x (ρ i) ^ a i := by
  symm
  apply Fintype.prod_of_injective ρ ρ.injective (fun i => x (ρ i) ^ a i)
    (fun i => x i ^ embedCharge ρ a i)
  · intro i hi
    rw [embedCharge_outside ρ a i hi, zpow_zero]
  · intro i
    rw [embedCharge_apply]

theorem rowFourier_eq_g {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ a = g H (embedCharge ρ a) := by
  simp only [rowFourier, g, character_embedCharge]

theorem rowFourier_order_one {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) (ha : ∑ i, a i = 0)
    (ho : ∑ i, (a i).toNat = 1) : rowFourier H ρ a = 0 := by
  rw [rowFourier_eq_g]
  apply g_order_one hH
  · exact (embedCharge_sum ρ a).trans ha
  · exact (embedCharge_order ρ a).trans ho

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_order_one {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (ha : ∑ i, A i j = 0) (ho : ∑ i, (A i j).toNat = 1) : mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact rowFourier_order_one (relativeMatrix_isHadamard B hB r _) ρ _ ha ho
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_FiniteSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sum_fin_five {R : Type*} [AddCommMonoid R] (f : Fin 5 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_SmallPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.EqualityPatterns

theorem pattern3_0 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (_h20 : f 2 = f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 0 i = family3.label 0 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_1 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 = f 0)
    (h20 : f 2 ≠ f 0)
    (_h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 1 i = family3.label 1 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_2 {B : Type*} (f : Fin 3 → B)
    (_h10 : f 1 ≠ f 0)
    (h20 : f 2 = f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 2 i = family3.label 2 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_3 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (_h20 : f 2 ≠ f 0)
    (h21 : f 2 = f 1)
    : ∀ i j, family3.label 3 i = family3.label 3 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm]

theorem pattern3_4 {B : Type*} (f : Fin 3 → B)
    (h10 : f 1 ≠ f 0)
    (h20 : f 2 ≠ f 0)
    (h21 : f 2 ≠ f 1)
    : ∀ i j, family3.label 4 i = family3.label 4 j ↔ f i = f j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [family3, label3, raw3, blocks3, eq_comm] <;> grind

theorem covers3 {B : Type*} (f : Fin 3 → B) :
    ∃ p, ∀ i j, (family3.label p i = family3.label p j ↔ f i = f j) := by
  classical
  by_cases h10 : f 1 = f 0
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨0, ?_⟩
      apply pattern3_0 f <;> simp_all [eq_comm]
    ·
      refine ⟨1, ?_⟩
      apply pattern3_1 f <;> simp_all [eq_comm]
  ·
    by_cases h20 : f 2 = f 0
    ·
      refine ⟨2, ?_⟩
      apply pattern3_2 f <;> simp_all [eq_comm]
    ·
      by_cases h21 : f 2 = f 1
      ·
        refine ⟨3, ?_⟩
        apply pattern3_3 f <;> simp_all [eq_comm]
      ·
        refine ⟨4, ?_⟩
        apply pattern3_4 f <;> simp_all [eq_comm]

end MUB6.EqualityPatterns

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_GroupedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit grouping formulas for the two- and three-column equality
patterns. These discharge the dependent finite-label calculations once,
so concrete certificate rows need only ordinary integer arithmetic. -/

open scoped BigOperators
namespace MUB6

theorem groupedColumns_family3_0 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 0) =
      (fun i (_ : Fin 1) => A i 0 + A i 1 + A i 2) := by
  change groupedColumns A (fun _ : Fin 3 => (0 : Fin 1)) = _
  ext i b
  have hb : b = 0 := Subsingleton.elim _ _
  subst b
  simp [groupedColumns, Fin.sum_univ_succ, add_assoc]

theorem groupedColumns_family3_1 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 1) =
      (fun i => ![A i 0 + A i 1, A i 2]) := by
  change groupedColumns A (![0, 0, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_2 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 2) =
      (fun i => ![A i 0 + A i 2, A i 1]) := by
  change groupedColumns A (![0, 1, 0] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_3 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 3) =
      (fun i => ![A i 0, A i 1 + A i 2]) := by
  change groupedColumns A (![0, 1, 1] : Fin 3 → Fin 2) = _
  ext i b
  fin_cases b <;> simp [groupedColumns, Finset.sum_filter, Fin.sum_univ_succ]

theorem groupedColumns_family3_4 {p : ℕ} (A : Matrix (Fin p) (Fin 3) ℤ) :
    groupedColumns A (EqualityPatterns.family3.label 4) = A := by
  change groupedColumns A (fun j : Fin 3 => j) = _
  ext i b
  simp [groupedColumns, Finset.sum_filter]

end MUB6

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_NormalizedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

namespace MUB6

theorem inverse_six_pow_real (n : ℕ) :
    (6 : ℂ)⁻¹ ^ n = (((6 : ℝ)⁻¹ ^ n : ℝ) : ℂ) := by
  simp

theorem partition_integrand {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (ρ : Fin p ↪ Coord) (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    ((∏ j, rowFourier H ρ (fun i => A i j)).re +
      (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (6 : ℝ)⁻¹ ^ n * ∑ s, ∑ κ : Fin (F.blocks s) ↪ Coord,
        ((exponentMonomial H (groupedColumns A (F.label s)) ρ κ).re +
          (exponentMonomial H.transpose (groupedColumns A (F.label s)) ρ κ).re) / 2 := by
  rw [rowFourier_partition_expand hH A ρ F cover,
    rowFourier_partition_expand hH.transpose A ρ F cover, inverse_six_pow_real]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_add_distrib]
  ring

theorem average_injection_sum {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin q) ℤ) :
    average (fun ρ : Fin p ↪ Coord => ∑ κ : Fin q ↪ Coord,
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2) =
      (Fintype.card (Fin q ↪ Coord) : ℝ) * injectiveMoment H A := by
  have he (ρ : Fin p ↪ Coord) := sum_eq_card_mul_average
    (fun κ : Fin q ↪ Coord =>
      ((exponentMonomial H A ρ κ).re +
        (exponentMonomial H.transpose A ρ κ).re) / 2)
  simp_rw [he]
  rw [average_mul, ← injectiveMoment_iterated H A]

/-- The normalized equality-pattern expansion. For k blocks the coefficient
is `card (Fin k ↪ Fin 6) / 6^n`, exactly `(6)_k / 6^n` in the source. -/
theorem averagedRowProducts_partition {p n : ℕ} {P : Type*} [Fintype P]
    {H : CMatrix} (hH : IsHadamard H) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    averagedRowProducts H A =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        injectiveMoment H (groupedColumns A (F.label s)) := by
  unfold averagedRowProducts
  simp_rw [partition_integrand hH A _ F cover]
  rw [average_mul, average_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [average_injection_sum H (groupedColumns A (F.label s))]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_OrderedPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem familyAverage_add (B : Fin 7 → Basis) (F G : CMatrix → ℝ) :
    familyAverage B (fun H => F H + G H) = familyAverage B F + familyAverage B G := by
  simp only [familyAverage, average_add]

theorem familyAverage_mul (B : Fin 7 → Basis) (c : ℝ) (F : CMatrix → ℝ) :
    familyAverage B (fun H => c * F H) = c * familyAverage B F := by
  simp only [familyAverage, average_mul]

theorem relativeMatrix_reverse (B : Fin 7 → Basis) (p : Fin 7 × Coord) :
    relativeMatrix B (reversePair p).1 (reversePair p).2 =
      (relativeMatrix B p.1 p.2).conjTranspose := by
  simp only [relativeMatrix, reversePair, Fin.succAbove_succAbove_predAbove]
  exact transition_reverse _ _

theorem familyAverage_transpose (B : Fin 7 → Basis) (F : CMatrix → ℝ)
    (hF : ∀ H, F (fun i j => conj (H i j)) = F H) :
    familyAverage B (fun H => F H.transpose) = familyAverage B F := by
  change (average (fun r : Fin 7 => average (fun s : Coord => F ((relativeMatrix B r s).transpose)))) =
    average (fun r : Fin 7 => average (fun s : Coord => F (relativeMatrix B r s)))
  rw [← average_prod (fun p : Fin 7 × Coord => F ((relativeMatrix B p.1 p.2).transpose)),
    ← average_prod (fun p : Fin 7 × Coord => F (relativeMatrix B p.1 p.2))]
  have h (p : Fin 7 × Coord) :
      F ((relativeMatrix B p.1 p.2).transpose) =
        F (relativeMatrix B (reversePair p).1 (reversePair p).2) := by
    rw [relativeMatrix_reverse]
    exact (hF ((relativeMatrix B p.1 p.2).transpose)).symm
  simp_rw [h]
  exact average_equiv reversePairEquiv (fun p => F (relativeMatrix B p.1 p.2))

theorem rowFourier_conjugate {p : ℕ} (H : CMatrix) (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier (fun i j => conj (H i j)) ρ a = conj (rowFourier H ρ a) := by
  simp only [rowFourier, map_mul, map_sum, map_prod, map_zpow₀, map_inv₀, map_ofNat]

theorem unorientedRowProducts_conjugate {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    unorientedRowProducts (fun i j => conj (H i j)) A = unorientedRowProducts H A := by
  apply average_congr
  intro ρ
  simp only [rowFourier_conjugate, ← map_prod, Complex.conj_re]

theorem averagedRowProducts_split {p n : ℕ} (H : CMatrix)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    averagedRowProducts H A =
      (1 / 2 : ℝ) * unorientedRowProducts H A +
        (1 / 2 : ℝ) * unorientedRowProducts H.transpose A := by
  have h (ρ : Fin p ↪ Coord) :
      ((∏ j, rowFourier H ρ (fun i => A i j)).re +
        (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re) / 2 =
      (1 / 2 : ℝ) * (∏ j, rowFourier H ρ (fun i => A i j)).re +
        (1 / 2 : ℝ) * (∏ j, rowFourier H.transpose ρ (fun i => A i j)).re := by ring
  simp only [averagedRowProducts, h, average_add, average_mul, unorientedRowProducts]

theorem familyAverage_averagedRowProducts {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    familyAverage B (fun H => averagedRowProducts H A) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  simp only [averagedRowProducts_split, familyAverage_add, familyAverage_mul]
  rw [familyAverage_transpose B (fun H => unorientedRowProducts H A)
    (fun H => unorientedRowProducts_conjugate H A)]
  ring

theorem mixedMoment_single_label {p n : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      familyAverage B (fun H => unorientedRowProducts H A) := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) :
      average (fun τ : Fin 1 ↪ Coord =>
        (mixedIntegrand B A (fun _ => (0 : Fin 1)) r ρ τ).re) =
      average (fun s : Coord => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re) := by
    exact average_equiv singletonEmbeddingEquiv
      (fun s => (∏ j, rowFourier (relativeMatrix B r s) ρ (fun i => A i j)).re)
  simp_rw [h]
  exact average_comm _

/-- Single-label mixed moments expand into the manuscript's transpose-averaged
pair moments with the exact falling-factorial weights. -/
theorem mixedMoment_single_label_partition {p n : ℕ} {P : Type*} [Fintype P]
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ)
    (F : EqualityPatterns.Family (Fin n) P)
    (cover : ∀ f : Fin n → Coord, ∃ s, ∀ i j,
      F.label s i = F.label s j ↔ f i = f j) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      ∑ s, ((Fintype.card (Fin (F.blocks s) ↪ Coord) : ℝ) / 6 ^ n) *
        familyPairMoment B (groupedColumns A (F.label s)) := by
  rw [mixedMoment_single_label, ← familyAverage_averagedRowProducts]
  unfold familyAverage
  simp_rw [averagedRowProducts_partition (relativeMatrix_isHadamard B hB _ _) A F cover,
    average_sum, average_mul]
  rfl

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_PairAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem eval_familyPairVector (B : Fin 7 → Basis) (v : Sparse (Fin 909)) :
    Sparse.eval v (familyPairVector B) =
      familyAverage B (fun H => Sparse.eval v (PairSemantics.momentVector H)) := by
  unfold familyPairVector familyAverage
  rw [Sparse.eval_average]
  apply average_congr
  intro r
  exact Sparse.eval_average v _

theorem familyPairMoment_of_pointwise {p n : ℕ} (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) (A : Matrix (Fin p) (Fin n) ℤ) (v : Sparse (Fin 909))
    (h : ∀ H, IsHadamard H →
      injectiveMoment H A = Sparse.eval v (PairSemantics.momentVector H)) :
    familyPairMoment B A = Sparse.eval v (familyPairVector B) := by
  rw [eval_familyPairVector]
  unfold familyPairMoment familyAverage
  apply average_congr
  intro r
  apply average_congr
  intro s
  exact h _ (relativeMatrix_isHadamard B hB r s)

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleRules
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

/-- The five equality patterns for three sampled column indices. -/
theorem single_label_three {p : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin 3) ℤ) :
    mixedMoment B A (fun _ => (0 : Fin 1)) =
      (1 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * familyPairMoment B (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := mixedMoment_single_label_partition B hB A
    EqualityPatterns.family3 EqualityPatterns.covers3
  rw [sum_fin_five] at h
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3,
    EqualityPatterns.blocks3, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Nat.descFactorial] at h
  exact h

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical154
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4941 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4941 = injectiveMoment H node711 := by
  rfl

theorem canonical4943 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4943 = injectiveMoment H node227 := by
  rfl

theorem canonical4946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4946 = injectiveMoment H node230 := by
  rfl

theorem canonical4949 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4949 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4949 = injectiveMoment H raw4949step0 := by
      have heq : raw4949step0 = -raw4949 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4949).symm
    injectiveMoment H raw4949step0 = injectiveMoment H raw4949step1 := by
      have hz : ∀ j, raw4949step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw4949step1 = (fun i j => raw4949step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw4949step0 permutation15 hz
    injectiveMoment H raw4949step1 = injectiveMoment H raw4949step2 := by
      have heq : raw4949step2 = (fun i j => raw4949step1 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4949step1 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

theorem canonical4950 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4950 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw4950 = injectiveMoment H raw4950step0 := by
      have heq : raw4950step0 = raw4950.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw4950).symm
    injectiveMoment H raw4950step0 = injectiveMoment H raw4950step1 := by
      have hz : ∀ i, raw4950step0 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw4950step1 = (fun i j => raw4950step0 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw4950step0 permutation5 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical4954 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4954 = injectiveMoment H node230 := by
  calc
    injectiveMoment H raw4954 = injectiveMoment H raw4954step0 := by
      have heq : raw4954step0 = (fun i j => raw4954 (permutation10 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4954 permutation10 permutation4
    _ = injectiveMoment H node230 := by rfl

theorem canonical4955 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4955 = injectiveMoment H node287 := by
  calc
    injectiveMoment H raw4955 = injectiveMoment H raw4955step0 := by
      have heq : raw4955step0 = -raw4955 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4955).symm
    injectiveMoment H raw4955step0 = injectiveMoment H raw4955step1 := by
      have heq : raw4955step1 = (fun i j => raw4955step0 (permutation12 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4955step0 permutation12 permutation8
    _ = injectiveMoment H node287 := by rfl

theorem canonical4956 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4956 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4956 = injectiveMoment H raw4956step0 := by
      have heq : raw4956step0 = -raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4956).symm
    injectiveMoment H raw4956step0 = injectiveMoment H raw4956step1 := by
      have heq : raw4956step1 = (fun i j => raw4956step0 (permutation4 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4956step0 permutation4 permutation8
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical155
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4966 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4966 = injectiveMoment H node44 := by
  rfl

theorem canonical4967 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4967 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw4967 = injectiveMoment H raw4967step0 := by
      have heq : raw4967step0 = -raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4967).symm
    injectiveMoment H raw4967step0 = injectiveMoment H raw4967step1 := by
      have heq : raw4967step1 = (fun i j => raw4967step0 (permutation4 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4967step0 permutation4 permutation6
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical161
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5167 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5167 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5167 = injectiveMoment H raw5167step0 := by
      have hz : ∀ j, raw5167 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw5167step0 = (fun i j => raw5167 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5167 permutation80 hz
    injectiveMoment H raw5167step0 = injectiveMoment H raw5167step1 := by
      have hz : ∀ j, raw5167step0 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5167step1 = (fun i j => raw5167step0 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5167step0 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

theorem canonical5169 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5169 = injectiveMoment H node4 := by
  clear _hH
  calc
    injectiveMoment H raw5169 = injectiveMoment H raw5169step0 := by
      have hz : ∀ j, raw5169 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw5169step0 = (fun i j => raw5169 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169 permutation21 hz
    injectiveMoment H raw5169step0 = injectiveMoment H raw5169step1 := by
      have hz : ∀ j, raw5169step0 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw5169step1 = (fun i j => raw5169step0 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5169step0 permutation5 hz
    _ = injectiveMoment H node4 := by rfl

theorem canonical5177 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5177 = injectiveMoment H node11 := by
  clear _hH
  calc
    injectiveMoment H raw5177 = injectiveMoment H raw5177step0 := by
      have hz : ∀ j, raw5177 (permutation15 0) j = 0 := by decide +kernel
      have heq : raw5177step0 = (fun i j => raw5177 (permutation15 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw5177 permutation15 hz
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical162
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical5199 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5199 = injectiveMoment H node11 := by
  rfl

theorem canonical5210 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw5210 = injectiveMoment H node4 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7385 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7385 = injectiveMoment H node2792 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical231
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7392 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7392 = injectiveMoment H node2796 := by
  rfl

theorem canonical7396 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7396 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7396 = injectiveMoment H raw7396step0 := by
      have heq : raw7396step0 = (fun i j => raw7396 (permutation89 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7396 permutation89 permutation7
    _ = injectiveMoment H node1294 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical239
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7668 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7668 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7668 = injectiveMoment H raw7668step0 := by
      have hz : ∀ j, raw7668 (permutation241 0) j = 0 := by decide +kernel
      have heq : raw7668step0 = (fun i j => raw7668 (permutation241 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668 permutation241 hz
    injectiveMoment H raw7668step0 = injectiveMoment H raw7668step1 := by
      have hz : ∀ j, raw7668step0 (permutation80 0) j = 0 := by decide +kernel
      have heq : raw7668step1 = (fun i j => raw7668step0 (permutation80 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7668step0 permutation80 hz
    _ = injectiveMoment H node65 := by rfl

theorem canonical7671 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7671 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7671 = injectiveMoment H raw7671step0 := by
      have hz : ∀ j, raw7671 (permutation21 0) j = 0 := by decide +kernel
      have heq : raw7671step0 = (fun i j => raw7671 (permutation21 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7671 permutation21 hz
    injectiveMoment H raw7671step0 = injectiveMoment H raw7671step1 := by
      have heq : raw7671step1 = (fun i j => raw7671step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7671step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

theorem canonical7677 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7677 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7677 = injectiveMoment H raw7677step0 := by
      have hz : ∀ j, raw7677 (permutation104 0) j = 0 := by decide +kernel
      have heq : raw7677step0 = (fun i j => raw7677 (permutation104 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7677 permutation104 hz
    _ = injectiveMoment H node65 := by rfl

theorem canonical7678 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7678 = injectiveMoment H node65 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical240
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7680 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7680 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7680 = injectiveMoment H raw7680step0 := by
      have hz : ∀ j, raw7680 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7680step0 = (fun i j => raw7680 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7680 permutation308 hz
    injectiveMoment H raw7680step0 = injectiveMoment H raw7680step1 := by
      have hz : ∀ j, raw7680step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7680step1 = (fun i j => raw7680step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7680step0 permutation128 hz
    _ = injectiveMoment H node65 := by rfl

theorem canonical7683 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7683 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7683 = injectiveMoment H raw7683step0 := by
      have heq : raw7683step0 = (fun i j => raw7683 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7683 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

theorem canonical7702 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7702 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7702 = injectiveMoment H raw7702step0 := by
      have hz : ∀ j, raw7702 (permutation258 0) j = 0 := by decide +kernel
      have heq : raw7702step0 = (fun i j => raw7702 (permutation258 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7702 permutation258 hz
    injectiveMoment H raw7702step0 = injectiveMoment H raw7702step1 := by
      have hz : ∀ j, raw7702step0 (permutation57 0) j = 0 := by decide +kernel
      have heq : raw7702step1 = (fun i j => raw7702step0 (permutation57 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7702step0 permutation57 hz
    _ = injectiveMoment H node65 := by rfl

theorem canonical7709 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7709 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7709 = injectiveMoment H raw7709step0 := by
      have hz : ∀ j, raw7709 (permutation5 0) j = 0 := by decide +kernel
      have heq : raw7709step0 = (fun i j => raw7709 (permutation5 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7709 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical241
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7718 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7718 = injectiveMoment H node5 := by
  rfl

theorem canonical7731 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7731 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7731 = injectiveMoment H raw7731step0 := by
      have heq : raw7731step0 = (fun i j => raw7731 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7731 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

theorem canonical7732 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7732 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7732 = injectiveMoment H raw7732step0 := by
      have hz : ∀ j, raw7732 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7732step0 = (fun i j => raw7732 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7732 permutation128 hz
    injectiveMoment H raw7732step0 = injectiveMoment H raw7732step1 := by
      have heq : raw7732step1 = (fun i j => raw7732step0 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7732step0 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

theorem canonical7735 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7735 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7735 = injectiveMoment H raw7735step0 := by
      have hz : ∀ j, raw7735 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7735step0 = (fun i j => raw7735 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7735 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

theorem canonical7738 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7738 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw7738 = injectiveMoment H raw7738step0 := by
      have heq : raw7738step0 = (fun i j => raw7738 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7738 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical242
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7749 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7749 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw7749 = injectiveMoment H raw7749step0 := by
      have heq : raw7749step0 = (fun i j => raw7749 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7749 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7979 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7979 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7979 = injectiveMoment H raw7979step0 := by
      have hz : ∀ j, raw7979 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7979step0 = (fun i j => raw7979 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979 permutation7 hz
    injectiveMoment H raw7979step0 = injectiveMoment H raw7979step1 := by
      have hz : ∀ j, raw7979step0 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7979step1 = (fun i j => raw7979step0 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step0 permutation2 hz
    injectiveMoment H raw7979step1 = injectiveMoment H raw7979step2 := by
      have hz : ∀ j, raw7979step1 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7979step2 = (fun i j => raw7979step1 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7979step1 permutation0 hz
    injectiveMoment H raw7979step2 = injectiveMoment H raw7979step3 := by
      have hz : ∀ i, raw7979step2 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7979step3 = (fun i j => raw7979step2 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7979step2 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7980 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7980 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7980 = injectiveMoment H raw7980step0 := by
      have hz : ∀ j, raw7980 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7980step0 = (fun i j => raw7980 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980 permutation27 hz
    injectiveMoment H raw7980step0 = injectiveMoment H raw7980step1 := by
      have hz : ∀ j, raw7980step0 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7980step1 = (fun i j => raw7980step0 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step0 permutation7 hz
    injectiveMoment H raw7980step1 = injectiveMoment H raw7980step2 := by
      have hz : ∀ j, raw7980step1 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7980step2 = (fun i j => raw7980step1 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step1 permutation2 hz
    injectiveMoment H raw7980step2 = injectiveMoment H raw7980step3 := by
      have hz : ∀ j, raw7980step2 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7980step3 = (fun i j => raw7980step2 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7980step2 permutation0 hz
    injectiveMoment H raw7980step3 = injectiveMoment H raw7980step4 := by
      have hz : ∀ i, raw7980step3 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7980step4 = (fun i j => raw7980step3 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7980step3 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7981 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7981 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7981 = injectiveMoment H raw7981step0 := by
      have hz : ∀ j, raw7981 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7981step0 = (fun i j => raw7981 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981 permutation128 hz
    injectiveMoment H raw7981step0 = injectiveMoment H raw7981step1 := by
      have hz : ∀ j, raw7981step0 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7981step1 = (fun i j => raw7981step0 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step0 permutation27 hz
    injectiveMoment H raw7981step1 = injectiveMoment H raw7981step2 := by
      have hz : ∀ j, raw7981step1 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7981step2 = (fun i j => raw7981step1 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step1 permutation7 hz
    injectiveMoment H raw7981step2 = injectiveMoment H raw7981step3 := by
      have hz : ∀ j, raw7981step2 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7981step3 = (fun i j => raw7981step2 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step2 permutation2 hz
    injectiveMoment H raw7981step3 = injectiveMoment H raw7981step4 := by
      have hz : ∀ j, raw7981step3 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7981step4 = (fun i j => raw7981step3 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7981step3 permutation0 hz
    injectiveMoment H raw7981step4 = injectiveMoment H raw7981step5 := by
      have hz : ∀ i, raw7981step4 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7981step5 = (fun i j => raw7981step4 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7981step4 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

theorem canonical7982 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7982 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw7982 = injectiveMoment H raw7982step0 := by
      have hz : ∀ j, raw7982 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw7982step0 = (fun i j => raw7982 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982 permutation308 hz
    injectiveMoment H raw7982step0 = injectiveMoment H raw7982step1 := by
      have hz : ∀ j, raw7982step0 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7982step1 = (fun i j => raw7982step0 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step0 permutation128 hz
    injectiveMoment H raw7982step1 = injectiveMoment H raw7982step2 := by
      have hz : ∀ j, raw7982step1 (permutation27 0) j = 0 := by decide +kernel
      have heq : raw7982step2 = (fun i j => raw7982step1 (permutation27 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step1 permutation27 hz
    injectiveMoment H raw7982step2 = injectiveMoment H raw7982step3 := by
      have hz : ∀ j, raw7982step2 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw7982step3 = (fun i j => raw7982step2 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step2 permutation7 hz
    injectiveMoment H raw7982step3 = injectiveMoment H raw7982step4 := by
      have hz : ∀ j, raw7982step3 (permutation2 0) j = 0 := by decide +kernel
      have heq : raw7982step4 = (fun i j => raw7982step3 (permutation2 i.succ) j) := by ext i j; fin_cases i; fin_cases j; decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step3 permutation2 hz
    injectiveMoment H raw7982step4 = injectiveMoment H raw7982step5 := by
      have hz : ∀ j, raw7982step4 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw7982step5 = (fun i j => raw7982step4 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7982step4 permutation0 hz
    injectiveMoment H raw7982step5 = injectiveMoment H raw7982step6 := by
      have hz : ∀ i, raw7982step5 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw7982step6 = (fun i j => raw7982step5 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7982step5 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical282
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical9026 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9026 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9026 = injectiveMoment H raw9026step0 := by
      have hz : ∀ j, raw9026 (permutation308 0) j = 0 := by decide +kernel
      have heq : raw9026step0 = (fun i j => raw9026 (permutation308 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9026 permutation308 hz
    injectiveMoment H raw9026step0 = injectiveMoment H raw9026step1 := by
      have hz : ∀ j, raw9026step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9026step1 = (fun i j => raw9026step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9026step0 permutation33 hz
    injectiveMoment H raw9026step1 = injectiveMoment H raw9026step2 := by
      have heq : raw9026step2 = (fun i j => raw9026step1 (permutation11 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw9026step1 permutation11 permutation1
    _ = injectiveMoment H node65 := by rfl

theorem canonical9044 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw9044 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw9044 = injectiveMoment H raw9044step0 := by
      have hz : ∀ j, raw9044 (permutation202 0) j = 0 := by decide +kernel
      have heq : raw9044step0 = (fun i j => raw9044 (permutation202 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9044 permutation202 hz
    injectiveMoment H raw9044step0 = injectiveMoment H raw9044step1 := by
      have hz : ∀ j, raw9044step0 (permutation33 0) j = 0 := by decide +kernel
      have heq : raw9044step1 = (fun i j => raw9044step0 (permutation33 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw9044step0 permutation33 hz
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_MomentContraction
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonality relations for injective moments. The saturated relation uses
only six-row moments, even though its generating exponent array has seven rows. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowMonomial_difference {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (t : Coord) (κ : Fin q ↪ Coord) :
    rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ =
      H t (κ v) * conj (H t (κ w)) := by
  classical
  simp only [rowMonomial, Pi.sub_apply, zpow_sub₀ (unit_ne_zero (hH.1 _ _)),
    Finset.prod_div_distrib]
  have hv : (∏ j, H t (κ j) ^ ((Pi.single v 1 : Fin q → ℤ) j)) = H t (κ v) := by
    simp [Pi.single_apply]
  have hw : (∏ j, H t (κ j) ^ ((Pi.single w 1 : Fin q → ℤ) j)) = H t (κ w) := by
    simp [Pi.single_apply]
  rw [hv, hw, div_eq_mul_inv, unit_inv_eq_conj (hH.1 _ _)]

theorem rowMonomial_sum_zero {q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (v w : Fin q) (hvw : v ≠ w) (κ : Fin q ↪ Coord) :
    (∑ t, rowMonomial H (Pi.single v 1 - Pi.single w 1) t κ) = 0 := by
  simp_rw [rowMonomial_difference hH]
  have hkwv : κ w ≠ κ v := fun h => hvw (κ.injective h.symm)
  simpa only [hkwv, ite_false, if_false, mul_comm] using hH.column_orthogonal (κ w) (κ v)

theorem contractionMonomial_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionMonomial H A ρ κ t) = 0 := by
  simp only [contractionMonomial, hA, ← Finset.mul_sum, rowMonomial_sum_zero hH v w hvw,
    mul_zero]

theorem contractionMonomial_new {p q : ℕ} (H : CMatrix)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin (p + 1) ↪ Coord) (κ : Fin q ↪ Coord) :
    contractionMonomial H A (Sampling.dropFirst ρ) κ (ρ 0) =
      exponentMonomial H A ρ κ := by
  simp only [contractionMonomial, exponentMonomial, rowMonomial, Fin.prod_univ_succ,
    Sampling.dropFirst_apply]
  exact mul_comm _ _

theorem contractionMonomial_occupied {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) (j : Fin p) :
    contractionMonomial H A ρ κ (ρ j) = exponentMonomial H (mergeFirst A j) ρ κ := by
  classical
  simp only [contractionMonomial, exponentMonomial, mergeFirst,
    zpow_add₀ (unit_ne_zero (hH.1 _ _)), Finset.prod_mul_distrib]
  congr 1
  simp [rowMonomial]

theorem contractionIntegrand_sum_zero {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    (∑ t, contractionIntegrand H A ρ κ t) = 0 := by
  simp only [contractionIntegrand, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Complex.re_sum, contractionMonomial_sum_zero hH A v w hvw hA,
    contractionMonomial_sum_zero hH.transpose A v w hvw hA, Complex.zero_re,
    zero_add, zero_mul]

/-- The coefficient is 6-p, where p is the number of rows other than the
contracted row. Equivalently it is 7 minus the original row count. -/
theorem injectiveMoment_first_row_contraction {p q : ℕ} (hp : p < 6)
    {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin (p + 1)) (Fin q) ℤ) (v w : Fin q) (hvw : v ≠ w)
    (hA : A 0 = Pi.single v 1 - Pi.single w 1) :
    ((6 - p : ℕ) : ℝ) * injectiveMoment H A +
      (∑ j, injectiveMoment H (mergeFirst A j)) = 0 := by
  have ht (κ : Fin q ↪ Coord) := Sampling.average_contraction hp
    (fun ρ t => contractionIntegrand H A ρ κ t)
    (fun ρ => contractionIntegrand_sum_zero hH A v w hvw hA ρ κ)
  have hav : average (fun κ : Fin q ↪ Coord =>
      ((6 - p : ℕ) : ℝ) *
        average (fun ρ : Fin (p + 1) ↪ Coord =>
          contractionIntegrand H A (Sampling.dropFirst ρ) κ (ρ 0)) +
        ∑ j : Fin p, average (fun ρ : Fin p ↪ Coord =>
          contractionIntegrand H A ρ κ (ρ j))) = 0 := by
    simp only [ht, average_zero]
  rw [average_add, average_mul, average_sum] at hav
  simp only [contractionIntegrand, contractionMonomial_new,
    contractionMonomial_occupied hH, contractionMonomial_occupied hH.transpose] at hav
  simp only [injectiveMoment_reverse_iterated] at hav
  exact hav

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6885 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6885 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw6885 = injectiveMoment H raw6885step0 := by
      have heq : raw6885step0 = raw6885.transpose := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_transpose H raw6885).symm
    injectiveMoment H raw6885step0 = injectiveMoment H raw6885step1 := by
      have heq : raw6885step1 = (fun i j => raw6885step0 (permutation7 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw6885step0 permutation7 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical233
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7462 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7462 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7462 = injectiveMoment H raw7462step0 := by
      have hz : ∀ i, raw7462 i (permutation5 0) = 0 := by decide +kernel
      have heq : raw7462step0 = (fun i j => raw7462 i (permutation5 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7462 permutation5 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical256
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8215 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8215 = injectiveMoment H node4 := by
  calc
    injectiveMoment H raw8215 = injectiveMoment H raw8215step0 := by
      have hz : ∀ i, raw8215 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8215step0 = (fun i j => raw8215 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8215 permutation3 hz
    _ = injectiveMoment H node4 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical279
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8946 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8946 = injectiveMoment H node0 := by
  calc
    injectiveMoment H raw8946 = injectiveMoment H raw8946step0 := by
      have hz : ∀ j, raw8946 (permutation0 0) j = 0 := by decide +kernel
      have heq : raw8946step0 = (fun i j => raw8946 (permutation0 i.succ) j) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8946 permutation0 hz
    injectiveMoment H raw8946step0 = injectiveMoment H raw8946step1 := by
      have hz : ∀ i, raw8946step0 i (permutation2 0) = 0 := by decide +kernel
      have heq : raw8946step1 = (fun i j => raw8946step0 i (permutation2 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step0 permutation2 hz
    injectiveMoment H raw8946step1 = injectiveMoment H raw8946step2 := by
      have hz : ∀ i, raw8946step1 i (permutation0 0) = 0 := by decide +kernel
      have heq : raw8946step2 = (fun i j => raw8946step1 i (permutation0 j.succ)) := by ext i j; fin_cases i
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8946step1 permutation0 hz
    _ = injectiveMoment H node0 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound0
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound0 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node0 = Sparse.eval value0 (momentVector H) := by
  have hc : momentVector H 0 = injectiveMoment H node0 := rfl
  simp [value0, Sparse.eval, hc]

theorem sound4 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node4 = Sparse.eval value4 (momentVector H) := by
  have hc : momentVector H 1 = injectiveMoment H node4 := rfl
  simp [value4, Sparse.eval, hc]

theorem sound5 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node5 = Sparse.eval value5 (momentVector H) := by
  have heq : pivotMatrix5 = (fun u v => node5 (pivotPermutation5 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node5 = injectiveMoment H pivotMatrix5 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix5 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 1 < 6) hH pivotMatrix5 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : mergeFirst pivotMatrix5 (0 : Fin 1) = raw8946 := by ext i j; fin_cases i; fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8946 hH).trans (sound0 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (5 : ℝ) * injectiveMoment H node5 + (injectiveMoment H (mergeFirst pivotMatrix5 (0 : Fin 1))) = 0 at hc
  rw [hm0] at hc
  norm_num [value5, value0, Sparse.eval] at hc ⊢
  linarith

theorem sound11 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node11 = Sparse.eval value11 (momentVector H) := by
  have heq : pivotMatrix11 = (fun u v => node11 (pivotPermutation11 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node11 = injectiveMoment H pivotMatrix11 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix11 0 = Pi.single (0 : Fin 2) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix11 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (0 : Fin 2) = raw7718 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7718 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix11 (1 : Fin 2) = raw5210 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5210 hH).trans (sound4 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node11 + (injectiveMoment H (mergeFirst pivotMatrix11 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix11 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value11, value4, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound41 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node41 = Sparse.eval value41 (momentVector H) := by
  have hc : momentVector H 12 = injectiveMoment H node41 := rfl
  simp [value41, Sparse.eval, hc]

theorem sound44 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H node44 = Sparse.eval value44 (momentVector H) := by
  have hc : momentVector H 4 = injectiveMoment H node44 := rfl
  simp [value44, Sparse.eval, hc]

theorem sound61 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node61 = Sparse.eval value61 (momentVector H) := by
  have heq : pivotMatrix61 = (fun u v => node61 (pivotPermutation61 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node61 = injectiveMoment H pivotMatrix61 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix61 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix61 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (0 : Fin 2) = raw7462 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7462 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix61 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node61 + (injectiveMoment H (mergeFirst pivotMatrix61 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix61 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value61, value11, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound62 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node62 = Sparse.eval value62 (momentVector H) := by
  have heq : pivotMatrix62 = (fun u v => node62 (pivotPermutation62 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node62 = injectiveMoment H pivotMatrix62 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix62 0 = Pi.single (0 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix62 0 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (0 : Fin 2) = raw8215 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical8215 hH).trans (sound4 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix62 (1 : Fin 2) = raw6885 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical6885 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node62 + (injectiveMoment H (mergeFirst pivotMatrix62 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix62 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value62, value11, value4, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical129
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4131 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4131 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4131 = injectiveMoment H raw4131step0 := by
      have heq : raw4131step0 = (fun i j => raw4131 (permutation25 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4131 permutation25 permutation6
    _ = injectiveMoment H node294 := by rfl

theorem canonical4133 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4133 = injectiveMoment H node294 := by
  calc
    injectiveMoment H raw4133 = injectiveMoment H raw4133step0 := by
      have heq : raw4133step0 = (fun i j => raw4133 (permutation31 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4133 permutation31 permutation6
    _ = injectiveMoment H node294 := by rfl

theorem canonical4134 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4134 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4134 = injectiveMoment H raw4134step0 := by
      have heq : raw4134step0 = (fun i j => raw4134 (permutation7 i) (permutation6 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4134 permutation7 permutation6
    _ = injectiveMoment H node62 := by rfl

theorem canonical4140 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4140 = injectiveMoment H node207 := by
  calc
    injectiveMoment H raw4140 = injectiveMoment H raw4140step0 := by
      have heq : raw4140step0 = (fun i j => raw4140 (permutation18 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4140 permutation18 permutation7
    _ = injectiveMoment H node207 := by rfl

theorem canonical4141 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4141 = injectiveMoment H node41 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical246
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7878 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw7878 = injectiveMoment H node711 := by
  calc
    injectiveMoment H raw7878 = injectiveMoment H raw7878step0 := by
      have heq : raw7878step0 = -raw7878 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw7878).symm
    injectiveMoment H raw7878step0 = injectiveMoment H raw7878step1 := by
      have heq : raw7878step1 = (fun i j => raw7878step0 (permutation69 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7878step0 permutation69 permutation7
    _ = injectiveMoment H node711 := by rfl

theorem canonical7888 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7888 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7888 = injectiveMoment H raw7888step0 := by
      have heq : raw7888step0 = (fun i j => raw7888 (permutation146 i) (permutation8 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7888 permutation146 permutation8
    _ = injectiveMoment H node1294 := by rfl

theorem canonical7892 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7892 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7892 = injectiveMoment H raw7892step0 := by
      have heq : raw7892step0 = (fun i j => raw7892 (permutation39 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7892 permutation39 permutation4
    _ = injectiveMoment H node1294 := by rfl

theorem canonical7893 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7893 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw7893 = injectiveMoment H raw7893step0 := by
      have hz : ∀ j, raw7893 (permutation128 0) j = 0 := by decide +kernel
      have heq : raw7893step0 = (fun i j => raw7893 (permutation128 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw7893 permutation128 hz
    injectiveMoment H raw7893step0 = injectiveMoment H raw7893step1 := by
      have heq : raw7893step1 = (fun i j => raw7893step0 (permutation11 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7893step0 permutation11 permutation4
    _ = injectiveMoment H node293 := by rfl

theorem canonical7895 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7895 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw7895 = injectiveMoment H raw7895step0 := by
      have hz : ∀ i, raw7895 i (permutation7 0) = 0 := by decide +kernel
      have heq : raw7895step0 = (fun i j => raw7895 i (permutation7 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw7895 permutation7 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical10000 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw10000 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw10000 = injectiveMoment H raw10000step0 := by
      have hz : ∀ i, raw10000 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw10000step0 = (fun i j => raw10000 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw10000 permutation3 hz
    injectiveMoment H raw10000step0 = injectiveMoment H raw10000step1 := by
      have heq : raw10000step1 = (fun i j => raw10000step0 (permutation2 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw10000step0 permutation2 permutation1
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound1
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound64 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node64 = Sparse.eval value64 (momentVector H) := by
  have heq : pivotMatrix64 = (fun u v => node64 (pivotPermutation64 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node64 = injectiveMoment H pivotMatrix64 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix64 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 2 < 6) hH pivotMatrix64 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (0 : Fin 2) = raw7895 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7895 hH).trans (sound5 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix64 (1 : Fin 2) = raw10000 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical10000 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (4 : ℝ) * injectiveMoment H node64 + (injectiveMoment H (mergeFirst pivotMatrix64 (0 : Fin 2)) + (injectiveMoment H (mergeFirst pivotMatrix64 (1 : Fin 2)))) = 0 at hc
  rw [hm0, hm1] at hc
  norm_num [value64, value5, Sparse.eval] at hc ⊢
  linarith

theorem sound65 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node65 = Sparse.eval value65 (momentVector H) := by
  have heq : pivotMatrix65 = (fun u v => node65 (pivotPermutation65 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node65 = injectiveMoment H pivotMatrix65 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix65 0 = Pi.single (1 : Fin 2) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix65 1 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (0 : Fin 3) = raw5199 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical5199 hH).trans (sound11 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (1 : Fin 3) = raw7709 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7709 hH).trans (sound5 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix65 (2 : Fin 3) = raw7735 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical7735 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node65 + (injectiveMoment H (mergeFirst pivotMatrix65 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix65 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value65, value11, value5, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical130
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4160 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H raw4160 = injectiveMoment H node62 := by
  calc
    injectiveMoment H raw4160 = injectiveMoment H raw4160step0 := by
      have heq : raw4160step0 = -raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact (injectiveMoment_neg hH raw4160).symm
    injectiveMoment H raw4160step0 = injectiveMoment H raw4160step1 := by
      have heq : raw4160step1 = (fun i j => raw4160step0 (permutation7 i) (permutation5 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw4160step0 permutation7 permutation5
    _ = injectiveMoment H node62 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6858 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6858 = injectiveMoment H node61 := by
  rfl

theorem canonical6865 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6865 = injectiveMoment H node62 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound3
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound207 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node207 = Sparse.eval value207 (momentVector H) := by
  have heq : pivotMatrix207 = (fun u v => node207 (pivotPermutation207 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node207 = injectiveMoment H pivotMatrix207 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix207 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix207 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (0 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) =
      Sparse.eval value41 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (1 : Fin 3) = raw4141 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4141 hH).trans (sound41 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix207 (2 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node207 + (injectiveMoment H (mergeFirst pivotMatrix207 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix207 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value207, value41, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound227 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node227 = Sparse.eval value227 (momentVector H) := by
  have heq : pivotMatrix227 = (fun u v => node227 (pivotPermutation227 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node227 = injectiveMoment H pivotMatrix227 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix227 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix227 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (0 : Fin 3) = raw4134 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4134 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (1 : Fin 3) = raw4950 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4950 hH).trans (sound11 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix227 (2 : Fin 3) = raw4956 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4956 hH).trans (sound62 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node227 + (injectiveMoment H (mergeFirst pivotMatrix227 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix227 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value227, value11, value62, Sparse.eval] at hc ⊢
  linarith

theorem sound230 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node230 = Sparse.eval value230 (momentVector H) := by
  have heq : pivotMatrix230 = (fun u v => node230 (pivotPermutation230 u) v) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
  have hmoment : injectiveMoment H node230 = injectiveMoment H pivotMatrix230 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix230 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix230 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (0 : Fin 3) = raw4160 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4160 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) =
      Sparse.eval value44 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (1 : Fin 3) = raw4966 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4966 hH).trans (sound44 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix230 (2 : Fin 3) = raw4967 := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
    rw [heq]
    exact (canonical4967 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node230 + (injectiveMoment H (mergeFirst pivotMatrix230 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix230 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value230, value44, value61, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical6845 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw6845 = injectiveMoment H node287 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical232
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical7445 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7445 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7445 = injectiveMoment H raw7445step0 := by
      have heq : raw7445step0 = (fun i j => raw7445 (permutation65 i) (permutation7 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7445 permutation65 permutation7
    _ = injectiveMoment H node1294 := by rfl

theorem canonical7448 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7448 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7448 = injectiveMoment H raw7448step0 := by
      have heq : raw7448step0 = (fun i j => raw7448 (permutation45 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7448 permutation45 permutation3
    _ = injectiveMoment H node1294 := by rfl

theorem canonical7450 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7450 = injectiveMoment H node1294 := by
  calc
    injectiveMoment H raw7450 = injectiveMoment H raw7450step0 := by
      have heq : raw7450step0 = (fun i j => raw7450 (permutation51 i) (permutation3 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw7450 permutation51 permutation3
    _ = injectiveMoment H node1294 := by rfl

theorem canonical7453 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw7453 = injectiveMoment H node64 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical266
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8537 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8537 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw8537 = injectiveMoment H raw8537step0 := by
      have heq : raw8537step0 = (fun i j => raw8537 (permutation17 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8537 permutation17 permutation4
    _ = injectiveMoment H node293 := by rfl

theorem canonical8542 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8542 = injectiveMoment H node64 := by
  calc
    injectiveMoment H raw8542 = injectiveMoment H raw8542step0 := by
      have heq : raw8542step0 = (fun i j => raw8542 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8542 permutation5 permutation4
    _ = injectiveMoment H node64 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical267
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8545 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8545 = injectiveMoment H node61 := by
  calc
    injectiveMoment H raw8545 = injectiveMoment H raw8545step0 := by
      have heq : raw8545step0 = (fun i j => raw8545 (permutation5 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8545 permutation5 permutation4
    _ = injectiveMoment H node61 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical271
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8692 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8692 = injectiveMoment H node293 := by
  calc
    injectiveMoment H raw8692 = injectiveMoment H raw8692step0 := by
      have heq : raw8692step0 = (fun i j => raw8692 (permutation23 i) (permutation4 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8692 permutation23 permutation4
    _ = injectiveMoment H node293 := by rfl

theorem canonical8697 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8697 = injectiveMoment H node5 := by
  calc
    injectiveMoment H raw8697 = injectiveMoment H raw8697step0 := by
      have hz : ∀ j, raw8697 (permutation7 0) j = 0 := by decide +kernel
      have heq : raw8697step0 = (fun i j => raw8697 (permutation7 i.succ) j) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_row (by decide) H raw8697 permutation7 hz
    injectiveMoment H raw8697step0 = injectiveMoment H raw8697step1 := by
      have hz : ∀ i, raw8697step0 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8697step1 = (fun i j => raw8697step0 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8697step0 permutation3 hz
    _ = injectiveMoment H node5 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical274
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8778 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8778 = injectiveMoment H node11 := by
  calc
    injectiveMoment H raw8778 = injectiveMoment H raw8778step0 := by
      have hz : ∀ i, raw8778 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8778step0 = (fun i j => raw8778 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8778 permutation3 hz
    injectiveMoment H raw8778step0 = injectiveMoment H raw8778step1 := by
      have heq : raw8778step1 = (fun i j => raw8778step0 (permutation5 i) (permutation2 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8778step0 permutation5 permutation2
    _ = injectiveMoment H node11 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound4
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound287 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node287 = Sparse.eval value287 (momentVector H) := by
  have heq : pivotMatrix287 = (fun u v => node287 (pivotPermutation287 u) v) := by apply Matrix.ext; unfold pivotMatrix287 node287 pivotPermutation287; decide +kernel
  have hmoment : injectiveMoment H node287 = injectiveMoment H pivotMatrix287 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix287 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix287 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (0 : Fin 3) = raw7453 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw7453; decide +kernel
    rw [heq]
    exact (canonical7453 hH).trans (sound64 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (1 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix287 (2 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix287 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node287 + (injectiveMoment H (mergeFirst pivotMatrix287 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix287 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value287, value61, value62, value64, Sparse.eval] at hc ⊢
  linarith

theorem sound293 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node293 = Sparse.eval value293 (momentVector H) := by
  have heq : pivotMatrix293 = (fun u v => node293 (pivotPermutation293 u) v) := by apply Matrix.ext; unfold pivotMatrix293 node293 pivotPermutation293; decide +kernel
  have hmoment : injectiveMoment H node293 = injectiveMoment H pivotMatrix293 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix293 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix293 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix293 (0 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (0 : Fin 3) = raw6858 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw6858; decide +kernel
    rw [heq]
    exact (canonical6858 hH).trans (sound61 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix293 (1 : Fin 3)) =
      Sparse.eval value64 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (1 : Fin 3) = raw8542 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw8542; decide +kernel
    rw [heq]
    exact (canonical8542 hH).trans (sound64 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix293 (2 : Fin 3)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : mergeFirst pivotMatrix293 (2 : Fin 3) = raw8697 := by apply Matrix.ext; unfold mergeFirst pivotMatrix293 raw8697; decide +kernel
    rw [heq]
    exact (canonical8697 hH).trans (sound5 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node293 + (injectiveMoment H (mergeFirst pivotMatrix293 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix293 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix293 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value293, value5, value61, value64, Sparse.eval] at hc ⊢
  linarith

theorem sound294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node294 = Sparse.eval value294 (momentVector H) := by
  have heq : pivotMatrix294 = (fun u v => node294 (pivotPermutation294 u) v) := by apply Matrix.ext; unfold pivotMatrix294 node294 pivotPermutation294; decide +kernel
  have hmoment : injectiveMoment H node294 = injectiveMoment H pivotMatrix294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 3 < 6) hH pivotMatrix294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) =
      Sparse.eval value62 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (0 : Fin 3) = raw6865 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw6865; decide +kernel
    rw [heq]
    exact (canonical6865 hH).trans (sound62 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (1 : Fin 3) = raw8545 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8545; decide +kernel
    rw [heq]
    exact (canonical8545 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : mergeFirst pivotMatrix294 (2 : Fin 3) = raw8778 := by apply Matrix.ext; unfold mergeFirst pivotMatrix294 raw8778; decide +kernel
    rw [heq]
    exact (canonical8778 hH).trans (sound11 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (3 : ℝ) * injectiveMoment H node294 + (injectiveMoment H (mergeFirst pivotMatrix294 (0 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (1 : Fin 3)) + (injectiveMoment H (mergeFirst pivotMatrix294 (2 : Fin 3))))) = 0 at hc
  rw [hm0, hm1, hm2] at hc
  norm_num [value294, value11, value61, value62, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound11
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound711 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node711 = Sparse.eval value711 (momentVector H) := by
  have heq : pivotMatrix711 = (fun u v => node711 (pivotPermutation711 u) v) := by apply Matrix.ext; unfold pivotMatrix711 node711 pivotPermutation711; decide +kernel
  have hmoment : injectiveMoment H node711 = injectiveMoment H pivotMatrix711 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix711 0 = Pi.single (2 : Fin 3) 1 - Pi.single 1 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix711 2 1 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix711 (0 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (0 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix711 (1 : Fin 4)) =
      Sparse.eval value61 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (1 : Fin 4) = raw4949 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4949; decide +kernel
    rw [heq]
    exact (canonical4949 hH).trans (sound61 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix711 (2 : Fin 4)) =
      Sparse.eval value230 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (2 : Fin 4) = raw4954 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4954; decide +kernel
    rw [heq]
    exact (canonical4954 hH).trans (sound230 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix711 (3 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix711 (3 : Fin 4) = raw4955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix711 raw4955; decide +kernel
    rw [heq]
    exact (canonical4955 hH).trans (sound287 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node711 + (injectiveMoment H (mergeFirst pivotMatrix711 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix711 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix711 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix711 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value711, value230, value287, value294, value61, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical272
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical8711 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw8711 = injectiveMoment H node65 := by
  calc
    injectiveMoment H raw8711 = injectiveMoment H raw8711step0 := by
      have hz : ∀ i, raw8711 i (permutation3 0) = 0 := by decide +kernel
      have heq : raw8711step0 = (fun i j => raw8711 i (permutation3 j.succ)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_delete_zero_column (by decide) H raw8711 permutation3 hz
    injectiveMoment H raw8711step0 = injectiveMoment H raw8711step1 := by
      have heq : raw8711step1 = (fun i j => raw8711step0 (permutation13 i) (permutation1 j)) := by ext i j; fin_cases i <;> fin_cases j <;> decide +kernel
      rw [heq]
      exact moment_permute H raw8711step0 permutation13 permutation1
    _ = injectiveMoment H node65 := by rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound20
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound1294 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node1294 = Sparse.eval value1294 (momentVector H) := by
  have heq : pivotMatrix1294 = (fun u v => node1294 (pivotPermutation1294 u) v) := by apply Matrix.ext; unfold pivotMatrix1294 node1294 pivotPermutation1294; decide +kernel
  have hmoment : injectiveMoment H node1294 = injectiveMoment H pivotMatrix1294 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix1294 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix1294 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix1294 (0 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (0 : Fin 4) = raw6845 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw6845; decide +kernel
    rw [heq]
    exact (canonical6845 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix1294 (1 : Fin 4)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (1 : Fin 4) = raw8537 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw8537; decide +kernel
    rw [heq]
    exact (canonical8537 hH).trans (sound293 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix1294 (2 : Fin 4)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (2 : Fin 4) = raw8692 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw8692; decide +kernel
    rw [heq]
    exact (canonical8692 hH).trans (sound293 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix1294 (3 : Fin 4)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : mergeFirst pivotMatrix1294 (3 : Fin 4) = raw8711 := by apply Matrix.ext; unfold mergeFirst pivotMatrix1294 raw8711; decide +kernel
    rw [heq]
    exact (canonical8711 hH).trans (sound65 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node1294 + (injectiveMoment H (mergeFirst pivotMatrix1294 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1294 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1294 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix1294 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value1294, value287, value293, value65, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

theorem canonical4116 {H : CMatrix} (_hH : IsHadamard H) :
    injectiveMoment H raw4116 = injectiveMoment H node668 := by
  rfl

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound10
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound668 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node668 = Sparse.eval value668 (momentVector H) := by
  have heq : pivotMatrix668 = (fun u v => node668 (pivotPermutation668 u) v) := by apply Matrix.ext; unfold pivotMatrix668 node668 pivotPermutation668; decide +kernel
  have hmoment : injectiveMoment H node668 = injectiveMoment H pivotMatrix668 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix668 0 = Pi.single (1 : Fin 3) 1 - Pi.single 2 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 4 < 6) hH pivotMatrix668 1 2 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix668 (0 : Fin 4)) =
      Sparse.eval value287 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (0 : Fin 4) = raw4955 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4955; decide +kernel
    rw [heq]
    exact (canonical4955 hH).trans (sound287 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix668 (1 : Fin 4)) =
      Sparse.eval value207 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (1 : Fin 4) = raw4140 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4140; decide +kernel
    rw [heq]
    exact (canonical4140 hH).trans (sound207 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix668 (2 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (2 : Fin 4) = raw4133 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4133; decide +kernel
    rw [heq]
    exact (canonical4133 hH).trans (sound294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix668 (3 : Fin 4)) =
      Sparse.eval value294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix668 (3 : Fin 4) = raw4131 := by apply Matrix.ext; unfold mergeFirst pivotMatrix668 raw4131; decide +kernel
    rw [heq]
    exact (canonical4131 hH).trans (sound294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (2 : ℝ) * injectiveMoment H node668 + (injectiveMoment H (mergeFirst pivotMatrix668 (0 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix668 (1 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix668 (2 : Fin 4)) + (injectiveMoment H (mergeFirst pivotMatrix668 (3 : Fin 4)))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3] at hc
  norm_num [value668, value207, value287, value294, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_PairSemantics_Sound43
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSemantics

open scoped BigOperators

theorem sound2792 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2792 = Sparse.eval value2792 (momentVector H) := by
  have heq : pivotMatrix2792 = (fun u v => node2792 (pivotPermutation2792 u) v) := by apply Matrix.ext; unfold pivotMatrix2792 node2792 pivotPermutation2792; decide +kernel
  have hmoment : injectiveMoment H node2792 = injectiveMoment H pivotMatrix2792 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2792 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2792 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2792 (0 : Fin 5)) =
      Sparse.eval value668 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2792 (0 : Fin 5) = raw4116 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2792 raw4116; decide +kernel
    rw [heq]
    exact (canonical4116 hH).trans (sound668 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2792 (1 : Fin 5)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2792 (1 : Fin 5) = raw7396 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2792 raw7396; decide +kernel
    rw [heq]
    exact (canonical7396 hH).trans (sound1294 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2792 (2 : Fin 5)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2792 (2 : Fin 5) = raw7445 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2792 raw7445; decide +kernel
    rw [heq]
    exact (canonical7445 hH).trans (sound1294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2792 (3 : Fin 5)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2792 (3 : Fin 5) = raw7448 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2792 raw7448; decide +kernel
    rw [heq]
    exact (canonical7448 hH).trans (sound1294 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2792 (4 : Fin 5)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2792 (4 : Fin 5) = raw7450 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2792 raw7450; decide +kernel
    rw [heq]
    exact (canonical7450 hH).trans (sound1294 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2792 + (injectiveMoment H (mergeFirst pivotMatrix2792 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2792 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2792 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2792 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2792 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2792, value1294, value668, Sparse.eval] at hc ⊢
  linarith

theorem sound2796 {H : CMatrix} (hH : IsHadamard H) :
    injectiveMoment H node2796 = Sparse.eval value2796 (momentVector H) := by
  have heq : pivotMatrix2796 = (fun u v => node2796 (pivotPermutation2796 u) v) := by apply Matrix.ext; unfold pivotMatrix2796 node2796 pivotPermutation2796; decide +kernel
  have hmoment : injectiveMoment H node2796 = injectiveMoment H pivotMatrix2796 := by
    rw [heq]
    rw [injectiveMoment_row_permutation]
  have hshape : pivotMatrix2796 0 = Pi.single (2 : Fin 3) 1 - Pi.single 0 1 := by exact funext (by decide +kernel)
  have hc := injectiveMoment_first_row_contraction (by decide : 5 < 6) hH pivotMatrix2796 2 0 (by decide) hshape
  rw [← hmoment] at hc
  have hm0 : injectiveMoment H (mergeFirst pivotMatrix2796 (0 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2796 (0 : Fin 5) = raw4941 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2796 raw4941; decide +kernel
    rw [heq]
    exact (canonical4941 hH).trans (sound711 hH)
  have hm1 : injectiveMoment H (mergeFirst pivotMatrix2796 (1 : Fin 5)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2796 (1 : Fin 5) = raw7878 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2796 raw7878; decide +kernel
    rw [heq]
    exact (canonical7878 hH).trans (sound711 hH)
  have hm2 : injectiveMoment H (mergeFirst pivotMatrix2796 (2 : Fin 5)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2796 (2 : Fin 5) = raw7888 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2796 raw7888; decide +kernel
    rw [heq]
    exact (canonical7888 hH).trans (sound1294 hH)
  have hm3 : injectiveMoment H (mergeFirst pivotMatrix2796 (3 : Fin 5)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2796 (3 : Fin 5) = raw7892 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2796 raw7892; decide +kernel
    rw [heq]
    exact (canonical7892 hH).trans (sound1294 hH)
  have hm4 : injectiveMoment H (mergeFirst pivotMatrix2796 (4 : Fin 5)) =
      Sparse.eval value293 (momentVector H) := by
    have heq : mergeFirst pivotMatrix2796 (4 : Fin 5) = raw7893 := by apply Matrix.ext; unfold mergeFirst pivotMatrix2796 raw7893; decide +kernel
    rw [heq]
    exact (canonical7893 hH).trans (sound293 hH)
  norm_num only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  change (1 : ℝ) * injectiveMoment H node2796 + (injectiveMoment H (mergeFirst pivotMatrix2796 (0 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2796 (1 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2796 (2 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2796 (3 : Fin 5)) + (injectiveMoment H (mergeFirst pivotMatrix2796 (4 : Fin 5))))))) = 0 at hc
  rw [hm0, hm1, hm2, hm3, hm4] at hc
  norm_num [value2796, value1294, value293, value711, Sparse.eval] at hc ⊢
  linarith

end MUB6.Certificate.PairSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SingleGroup32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem singlePair526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node526 node526Labels = Sparse.eval singlePairValue526 (familyPairVector B) := by
  have hp := single_label_three B hB node526
  have hl : node526Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 0) = PairSemantics.raw7981 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node526 PairSemantics.raw7981; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7981 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 1) = PairSemantics.raw7677 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node526 PairSemantics.raw7677; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7677 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 2) = PairSemantics.raw7732 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node526 PairSemantics.raw7732; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7732 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 3) = PairSemantics.raw5167 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node526 PairSemantics.raw5167; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5167 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node526 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value711 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node526 (EqualityPatterns.family3.label 4) = PairSemantics.raw4941 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node526 PairSemantics.raw4941; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4941 hH).trans (PairSemantics.sound711 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue526, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value711, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node527 node527Labels = Sparse.eval singlePairValue527 (familyPairVector B) := by
  have hp := single_label_three B hB node527
  have hl : node527Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node527 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 1) = PairSemantics.raw7678 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node527 PairSemantics.raw7678; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7678 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 2) = PairSemantics.raw7731 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node527 PairSemantics.raw7731; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7731 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value4 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 3) = PairSemantics.raw5169 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node527 PairSemantics.raw5169; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5169 hH).trans (PairSemantics.sound4 hH)
  have hm4 : familyPairMoment B (groupedColumns node527 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value227 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node527 (EqualityPatterns.family3.label 4) = PairSemantics.raw4943 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node527 PairSemantics.raw4943; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4943 hH).trans (PairSemantics.sound227 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue527, PairSemantics.value0, PairSemantics.value4, PairSemantics.value65, PairSemantics.value227, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node528 node528Labels = Sparse.eval singlePairValue528 (familyPairVector B) := by
  have hp := single_label_three B hB node528
  have hl : node528Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 0) = PairSemantics.raw7980 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node528 PairSemantics.raw7980; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7980 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 1) = PairSemantics.raw7671 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node528 PairSemantics.raw7671; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7671 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 2) = PairSemantics.raw7738 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node528 PairSemantics.raw7738; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7738 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 3) = PairSemantics.raw5177 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node528 PairSemantics.raw5177; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5177 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node528 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value230 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node528 (EqualityPatterns.family3.label 4) = PairSemantics.raw4946 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node528 PairSemantics.raw4946; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4946 hH).trans (PairSemantics.sound230 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue528, PairSemantics.value0, PairSemantics.value11, PairSemantics.value65, PairSemantics.value230, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair530 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node530 node530Labels = Sparse.eval singlePairValue530 (familyPairVector B) := by
  have hp := single_label_three B hB node530
  have hl : node530Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 0) = PairSemantics.raw7979 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node530 PairSemantics.raw7979; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7979 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 1) = PairSemantics.raw7683 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node530 PairSemantics.raw7683; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7683 hH).trans (PairSemantics.sound11 hH)
  have hm2 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 2) = PairSemantics.raw7749 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node530 PairSemantics.raw7749; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7749 hH).trans (PairSemantics.sound11 hH)
  have hm3 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value11 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 3) = PairSemantics.raw5199 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node530 PairSemantics.raw5199; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical5199 hH).trans (PairSemantics.sound11 hH)
  have hm4 : familyPairMoment B (groupedColumns node530 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value44 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node530 (EqualityPatterns.family3.label 4) = PairSemantics.raw4966 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node530 PairSemantics.raw4966; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical4966 hH).trans (PairSemantics.sound44 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue530, PairSemantics.value0, PairSemantics.value11, PairSemantics.value44, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair531 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node531 node531Labels = Sparse.eval singlePairValue531 (familyPairVector B) := by
  have hp := single_label_three B hB node531
  have hl : node531Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node531 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 1) = PairSemantics.raw7680 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node531 PairSemantics.raw7680; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7680 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 2) = PairSemantics.raw9044 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node531 PairSemantics.raw9044; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9044 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 3) = PairSemantics.raw7668 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node531 PairSemantics.raw7668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7668 hH).trans (PairSemantics.sound65 hH)
  have hm4 : familyPairMoment B (groupedColumns node531 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2792 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node531 (EqualityPatterns.family3.label 4) = PairSemantics.raw7385 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node531 PairSemantics.raw7385; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7385 hH).trans (PairSemantics.sound2792 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue531, PairSemantics.value0, PairSemantics.value65, PairSemantics.value2792, Sparse.eval] at hp ⊢
  linarith only [hp]

theorem singlePair533 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    mixedMoment B node533 node533Labels = Sparse.eval singlePairValue533 (familyPairVector B) := by
  have hp := single_label_three B hB node533
  have hl : node533Labels = (fun _ => (0 : Fin 1)) := by decide +kernel
  rw [← hl] at hp
  have hm0 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 0)) =
      Sparse.eval PairSemantics.value0 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 0) = PairSemantics.raw7982 := by
      rw [groupedColumns_family3_0]
      apply Matrix.ext; unfold node533 PairSemantics.raw7982; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7982 hH).trans (PairSemantics.sound0 hH)
  have hm1 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 1)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 1) = PairSemantics.raw7702 := by
      rw [groupedColumns_family3_1]
      apply Matrix.ext; unfold node533 PairSemantics.raw7702; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7702 hH).trans (PairSemantics.sound65 hH)
  have hm2 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 2)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 2) = PairSemantics.raw9026 := by
      rw [groupedColumns_family3_2]
      apply Matrix.ext; unfold node533 PairSemantics.raw9026; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical9026 hH).trans (PairSemantics.sound65 hH)
  have hm3 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 3)) =
      Sparse.eval PairSemantics.value65 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 3) = PairSemantics.raw7668 := by
      rw [groupedColumns_family3_3]
      apply Matrix.ext; unfold node533 PairSemantics.raw7668; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7668 hH).trans (PairSemantics.sound65 hH)
  have hm4 : familyPairMoment B (groupedColumns node533 (EqualityPatterns.family3.label 4)) =
      Sparse.eval PairSemantics.value2796 (familyPairVector B) := by
    apply familyPairMoment_of_pointwise B hB
    intro H hH
    have heq : groupedColumns node533 (EqualityPatterns.family3.label 4) = PairSemantics.raw7392 := by
      rw [groupedColumns_family3_4]
      apply Matrix.ext; unfold node533 PairSemantics.raw7392; decide +kernel
    rw [heq]
    exact (PairSemantics.canonical7392 hH).trans (PairSemantics.sound2796 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [singlePairValue533, PairSemantics.value0, PairSemantics.value65, PairSemantics.value2796, Sparse.eval] at hp ⊢
  linarith only [hp]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero529 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node529 node529Labels = 0 := by
  exact mixedMoment_order_one B hB node529 node529Labels 1
    (by decide +kernel) (by decide +kernel)

theorem zero532 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node532 node532Labels = 0 := by
  exact mixedMoment_order_one B hB node532 node532Labels 1
    (by decide +kernel) (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node526 node526Labels = Sparse.eval nodeValue526 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue526 (familyPairVector B) := singlePair526 B _hB
    _ = _ := by norm_num [singlePairValue526, nodeValue526, Sparse.eval, mixedVector] <;> ring

theorem sound527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node527 node527Labels = Sparse.eval nodeValue527 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue527 (familyPairVector B) := singlePair527 B _hB
    _ = _ := by norm_num [singlePairValue527, nodeValue527, Sparse.eval, mixedVector]

theorem sound528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node528 node528Labels = Sparse.eval nodeValue528 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue528 (familyPairVector B) := singlePair528 B _hB
    _ = _ := by norm_num [singlePairValue528, nodeValue528, Sparse.eval, mixedVector] <;> ring

theorem sound529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node529 node529Labels = Sparse.eval nodeValue529 (mixedVector B) := by
  simpa only [nodeValue529, Sparse.eval_nil] using zero529 B _hB _hF

theorem sound530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node530 node530Labels = Sparse.eval nodeValue530 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue530 (familyPairVector B) := singlePair530 B _hB
    _ = _ := by norm_num [singlePairValue530, nodeValue530, Sparse.eval, mixedVector] <;> ring

theorem sound531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node531 node531Labels = Sparse.eval nodeValue531 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue531 (familyPairVector B) := singlePair531 B _hB
    _ = _ := by norm_num [singlePairValue531, nodeValue531, Sparse.eval, mixedVector] <;> ring

theorem sound532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node532 node532Labels = Sparse.eval nodeValue532 (mixedVector B) := by
  simpa only [nodeValue532, Sparse.eval_nil] using zero532 B _hB _hF

theorem sound533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node533 node533Labels = Sparse.eval nodeValue533 (mixedVector B) := by
  calc
    _ = Sparse.eval singlePairValue533 (familyPairVector B) := singlePair533 B _hB
    _ = _ := by norm_num [singlePairValue533, nodeValue533, Sparse.eval, mixedVector] <;> ring

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node577 node577Labels = Sparse.eval nodeValue577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 577) = mixedMoment B node577 node577Labels := rfl
  simpa [nodeValue577, Sparse.eval] using hc.symm

theorem sound578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node578 node578Labels = Sparse.eval nodeValue578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 578) = mixedMoment B node578 node578Labels := rfl
  simpa [nodeValue578, Sparse.eval] using hc.symm

theorem sound579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node579 node579Labels = Sparse.eval nodeValue579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 579) = mixedMoment B node579 node579Labels := rfl
  simpa [nodeValue579, Sparse.eval] using hc.symm

theorem sound580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node580 node580Labels = Sparse.eval nodeValue580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 580) = mixedMoment B node580 node580Labels := rfl
  simpa [nodeValue580, Sparse.eval] using hc.symm

theorem sound581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node581 node581Labels = Sparse.eval nodeValue581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 581) = mixedMoment B node581 node581Labels := rfl
  simpa [nodeValue581, Sparse.eval] using hc.symm

theorem sound582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node582 node582Labels = Sparse.eval nodeValue582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 582) = mixedMoment B node582 node582Labels := rfl
  simpa [nodeValue582, Sparse.eval] using hc.symm

theorem sound583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node583 node583Labels = Sparse.eval nodeValue583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 583) = mixedMoment B node583 node583Labels := rfl
  simpa [nodeValue583, Sparse.eval] using hc.symm

theorem sound584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node584 node584Labels = Sparse.eval nodeValue584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 584) = mixedMoment B node584 node584Labels := rfl
  simpa [nodeValue584, Sparse.eval] using hc.symm

theorem sound585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node585 node585Labels = Sparse.eval nodeValue585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 585) = mixedMoment B node585 node585Labels := rfl
  simpa [nodeValue585, Sparse.eval] using hc.symm

theorem sound586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node586 node586Labels = Sparse.eval nodeValue586 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 586) = mixedMoment B node586 node586Labels := rfl
  simpa [nodeValue586, Sparse.eval] using hc.symm

theorem sound587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node587 node587Labels = Sparse.eval nodeValue587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 587) = mixedMoment B node587 node587Labels := rfl
  simpa [nodeValue587, Sparse.eval] using hc.symm

theorem sound588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node588 node588Labels = Sparse.eval nodeValue588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 588) = mixedMoment B node588 node588Labels := rfl
  simpa [nodeValue588, Sparse.eval] using hc.symm

theorem sound589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node589 node589Labels = Sparse.eval nodeValue589 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 589) = mixedMoment B node589 node589Labels := rfl
  simpa [nodeValue589, Sparse.eval] using hc.symm

theorem sound590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node590 node590Labels = Sparse.eval nodeValue590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 590) = mixedMoment B node590 node590Labels := rfl
  simpa [nodeValue590, Sparse.eval] using hc.symm

theorem sound591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node591 node591Labels = Sparse.eval nodeValue591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 591) = mixedMoment B node591 node591Labels := rfl
  simpa [nodeValue591, Sparse.eval] using hc.symm

theorem sound597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node597 node597Labels = Sparse.eval nodeValue597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 597) = mixedMoment B node597 node597Labels := rfl
  simpa [nodeValue597, Sparse.eval] using hc.symm

theorem sound599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node599 node599Labels = Sparse.eval nodeValue599 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 599) = mixedMoment B node599 node599Labels := rfl
  simpa [nodeValue599, Sparse.eval] using hc.symm

theorem sound600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node600 node600Labels = Sparse.eval nodeValue600 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 600) = mixedMoment B node600 node600Labels := rfl
  simpa [nodeValue600, Sparse.eval] using hc.symm

theorem sound601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node601 node601Labels = Sparse.eval nodeValue601 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 601) = mixedMoment B node601 node601Labels := rfl
  simpa [nodeValue601, Sparse.eval] using hc.symm

theorem sound603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node603 node603Labels = Sparse.eval nodeValue603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 603) = mixedMoment B node603 node603Labels := rfl
  simpa [nodeValue603, Sparse.eval] using hc.symm

theorem sound604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node604 node604Labels = Sparse.eval nodeValue604 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 604) = mixedMoment B node604 node604Labels := rfl
  simpa [nodeValue604, Sparse.eval] using hc.symm

theorem sound605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node605 node605Labels = Sparse.eval nodeValue605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 605) = mixedMoment B node605 node605Labels := rfl
  simpa [nodeValue605, Sparse.eval] using hc.symm

theorem sound606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node606 node606Labels = Sparse.eval nodeValue606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 606) = mixedMoment B node606 node606Labels := rfl
  simpa [nodeValue606, Sparse.eval] using hc.symm

theorem sound607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node607 node607Labels = Sparse.eval nodeValue607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 607) = mixedMoment B node607 node607Labels := rfl
  simpa [nodeValue607, Sparse.eval] using hc.symm

theorem sound608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node608 node608Labels = Sparse.eval nodeValue608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 608) = mixedMoment B node608 node608Labels := rfl
  simpa [nodeValue608, Sparse.eval] using hc.symm

theorem sound610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node610 node610Labels = Sparse.eval nodeValue610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 610) = mixedMoment B node610 node610Labels := rfl
  simpa [nodeValue610, Sparse.eval] using hc.symm

theorem sound611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node611 node611Labels = Sparse.eval nodeValue611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 611) = mixedMoment B node611 node611Labels := rfl
  simpa [nodeValue611, Sparse.eval] using hc.symm

theorem sound612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node612 node612Labels = Sparse.eval nodeValue612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 612) = mixedMoment B node612 node612Labels := rfl
  simpa [nodeValue612, Sparse.eval] using hc.symm

theorem sound613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node613 node613Labels = Sparse.eval nodeValue613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 613) = mixedMoment B node613 node613Labels := rfl
  simpa [nodeValue613, Sparse.eval] using hc.symm

theorem sound614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node614 node614Labels = Sparse.eval nodeValue614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 614) = mixedMoment B node614 node614Labels := rfl
  simpa [nodeValue614, Sparse.eval] using hc.symm

theorem sound615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node615 node615Labels = Sparse.eval nodeValue615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 615) = mixedMoment B node615 node615Labels := rfl
  simpa [nodeValue615, Sparse.eval] using hc.symm

theorem sound616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node616 node616Labels = Sparse.eval nodeValue616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 616) = mixedMoment B node616 node616Labels := rfl
  simpa [nodeValue616, Sparse.eval] using hc.symm

theorem sound617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node617 node617Labels = Sparse.eval nodeValue617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 617) = mixedMoment B node617 node617Labels := rfl
  simpa [nodeValue617, Sparse.eval] using hc.symm

theorem sound618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node618 node618Labels = Sparse.eval nodeValue618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 618) = mixedMoment B node618 node618Labels := rfl
  simpa [nodeValue618, Sparse.eval] using hc.symm

theorem sound619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node619 node619Labels = Sparse.eval nodeValue619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 619) = mixedMoment B node619 node619Labels := rfl
  simpa [nodeValue619, Sparse.eval] using hc.symm

theorem sound620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node620 node620Labels = Sparse.eval nodeValue620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 620) = mixedMoment B node620 node620Labels := rfl
  simpa [nodeValue620, Sparse.eval] using hc.symm

theorem sound621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node621 node621Labels = Sparse.eval nodeValue621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 621) = mixedMoment B node621 node621Labels := rfl
  simpa [nodeValue621, Sparse.eval] using hc.symm

theorem sound622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node622 node622Labels = Sparse.eval nodeValue622 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 622) = mixedMoment B node622 node622Labels := rfl
  simpa [nodeValue622, Sparse.eval] using hc.symm

theorem sound623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node623 node623Labels = Sparse.eval nodeValue623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 623) = mixedMoment B node623 node623Labels := rfl
  simpa [nodeValue623, Sparse.eval] using hc.symm

theorem sound624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node624 node624Labels = Sparse.eval nodeValue624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 624) = mixedMoment B node624 node624Labels := rfl
  simpa [nodeValue624, Sparse.eval] using hc.symm

theorem sound626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node626 node626Labels = Sparse.eval nodeValue626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 626) = mixedMoment B node626 node626Labels := rfl
  simpa [nodeValue626, Sparse.eval] using hc.symm

theorem sound627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node627 node627Labels = Sparse.eval nodeValue627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 627) = mixedMoment B node627 node627Labels := rfl
  simpa [nodeValue627, Sparse.eval] using hc.symm

theorem sound628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node628 node628Labels = Sparse.eval nodeValue628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 628) = mixedMoment B node628 node628Labels := rfl
  simpa [nodeValue628, Sparse.eval] using hc.symm

theorem sound629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node629 node629Labels = Sparse.eval nodeValue629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 629) = mixedMoment B node629 node629Labels := rfl
  simpa [nodeValue629, Sparse.eval] using hc.symm

theorem sound630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node630 node630Labels = Sparse.eval nodeValue630 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 630) = mixedMoment B node630 node630Labels := rfl
  simpa [nodeValue630, Sparse.eval] using hc.symm

theorem sound631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node631 node631Labels = Sparse.eval nodeValue631 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 631) = mixedMoment B node631 node631Labels := rfl
  simpa [nodeValue631, Sparse.eval] using hc.symm

theorem sound633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node633 node633Labels = Sparse.eval nodeValue633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 633) = mixedMoment B node633 node633Labels := rfl
  simpa [nodeValue633, Sparse.eval] using hc.symm

theorem sound634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node634 node634Labels = Sparse.eval nodeValue634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 634) = mixedMoment B node634 node634Labels := rfl
  simpa [nodeValue634, Sparse.eval] using hc.symm

theorem sound635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node635 node635Labels = Sparse.eval nodeValue635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 635) = mixedMoment B node635 node635Labels := rfl
  simpa [nodeValue635, Sparse.eval] using hc.symm

theorem sound636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node636 node636Labels = Sparse.eval nodeValue636 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 636) = mixedMoment B node636 node636Labels := rfl
  simpa [nodeValue636, Sparse.eval] using hc.symm

theorem sound637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node637 node637Labels = Sparse.eval nodeValue637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 637) = mixedMoment B node637 node637Labels := rfl
  simpa [nodeValue637, Sparse.eval] using hc.symm

theorem sound638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node638 node638Labels = Sparse.eval nodeValue638 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 638) = mixedMoment B node638 node638Labels := rfl
  simpa [nodeValue638, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic419 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm419 x = (-6268329904672604160000 : ℝ) * Sparse.eval nodeValue526 x := by
  norm_num [reducedTerm419, nodeValue526, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic420 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm420 x = (3294283875393208320000 : ℝ) * Sparse.eval nodeValue527 x := by
  norm_num [reducedTerm420, nodeValue527, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic421 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm421 x = (43831740715499520000 : ℝ) * Sparse.eval nodeValue528 x := by
  norm_num [reducedTerm421, nodeValue528, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic422 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm422 x = (1001082421468200960000 : ℝ) * Sparse.eval nodeValue529 x := by
  norm_num [reducedTerm422, nodeValue529, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic423 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm423 x = (4050726198607872000000 : ℝ) * Sparse.eval nodeValue530 x := by
  norm_num [reducedTerm423, nodeValue530, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic424 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm424 x = (6584917799562117120000 : ℝ) * Sparse.eval nodeValue531 x := by
  norm_num [reducedTerm424, nodeValue531, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic425 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm425 x = (-12197954412781240320000 : ℝ) * Sparse.eval nodeValue532 x := by
  norm_num [reducedTerm425, nodeValue532, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic426 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm426 x = (-971881186342993920000 : ℝ) * Sparse.eval nodeValue533 x := by
  norm_num [reducedTerm426, nodeValue533, Integer.Sparse.eval, Sparse.eval]
  ring

theorem reducedTermArithmetic427 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm427 x = (-654308882759024640000 : ℝ) * Sparse.eval nodeValue577 x := by
  norm_num [reducedTerm427, nodeValue577, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic428 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm428 x = (-2282493232765992960000 : ℝ) * Sparse.eval nodeValue578 x := by
  norm_num [reducedTerm428, nodeValue578, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic429 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm429 x = (654308882759024640000 : ℝ) * Sparse.eval nodeValue579 x := by
  norm_num [reducedTerm429, nodeValue579, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic430 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm430 x = (877592856526848000000 : ℝ) * Sparse.eval nodeValue580 x := by
  norm_num [reducedTerm430, nodeValue580, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic431 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm431 x = (877447660307742720000 : ℝ) * Sparse.eval nodeValue581 x := by
  norm_num [reducedTerm431, nodeValue581, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic432 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm432 x = (607591276892651520000 : ℝ) * Sparse.eval nodeValue582 x := by
  norm_num [reducedTerm432, nodeValue582, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic433 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm433 x = (2282493232765992960000 : ℝ) * Sparse.eval nodeValue583 x := by
  norm_num [reducedTerm433, nodeValue583, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic434 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm434 x = (-113253321790586880000 : ℝ) * Sparse.eval nodeValue584 x := by
  norm_num [reducedTerm434, nodeValue584, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic435 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm435 x = (-2325444766551244800000 : ℝ) * Sparse.eval nodeValue585 x := by
  norm_num [reducedTerm435, nodeValue585, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic436 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm436 x = (-878028445184163840000 : ℝ) * Sparse.eval nodeValue586 x := by
  norm_num [reducedTerm436, nodeValue586, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic437 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm437 x = (4950070676784414720000 : ℝ) * Sparse.eval nodeValue587 x := by
  norm_num [reducedTerm437, nodeValue587, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic438 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm438 x = (-947351242264412160000 : ℝ) * Sparse.eval nodeValue588 x := by
  norm_num [reducedTerm438, nodeValue588, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic439 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm439 x = (-877883248965058560000 : ℝ) * Sparse.eval nodeValue589 x := by
  norm_num [reducedTerm439, nodeValue589, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic440 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm440 x = (-544816666760970240000 : ℝ) * Sparse.eval nodeValue590 x := by
  norm_num [reducedTerm440, nodeValue590, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic441 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm441 x = (2291676713032089600000 : ℝ) * Sparse.eval nodeValue591 x := by
  norm_num [reducedTerm441, nodeValue591, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic442 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm442 x = (-28541892592926720000 : ℝ) * Sparse.eval nodeValue597 x := by
  norm_num [reducedTerm442, nodeValue597, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic443 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm443 x = (-1211529171307069440000 : ℝ) * Sparse.eval nodeValue599 x := by
  norm_num [reducedTerm443, nodeValue599, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic444 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm444 x = (344588552322416640000 : ℝ) * Sparse.eval nodeValue600 x := by
  norm_num [reducedTerm444, nodeValue600, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic445 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm445 x = (28541892592926720000 : ℝ) * Sparse.eval nodeValue601 x := by
  norm_num [reducedTerm445, nodeValue601, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic446 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm446 x = (533546803510640640000 : ℝ) * Sparse.eval nodeValue603 x := by
  norm_num [reducedTerm446, nodeValue603, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic447 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm447 x = (6690208535414046720000 : ℝ) * Sparse.eval nodeValue604 x := by
  norm_num [reducedTerm447, nodeValue604, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermArithmetic448 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm448 x = (-2453660793490636800000 : ℝ) * Sparse.eval nodeValue605 x := by
  norm_num [reducedTerm448, nodeValue605, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic449 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm449 x = (1441480432653434880000 : ℝ) * Sparse.eval nodeValue606 x := by
  norm_num [reducedTerm449, nodeValue606, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic450 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm450 x = (2300979745408942080000 : ℝ) * Sparse.eval nodeValue607 x := by
  norm_num [reducedTerm450, nodeValue607, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic451 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm451 x = (-1054181617875025920000 : ℝ) * Sparse.eval nodeValue608 x := by
  norm_num [reducedTerm451, nodeValue608, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic452 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm452 x = (-9473152863350292480000 : ℝ) * Sparse.eval nodeValue610 x := by
  norm_num [reducedTerm452, nodeValue610, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic453 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm453 x = (18388973290326589440000 : ℝ) * Sparse.eval nodeValue611 x := by
  norm_num [reducedTerm453, nodeValue611, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic454 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm454 x = (-584459388199895040000 : ℝ) * Sparse.eval nodeValue612 x := by
  norm_num [reducedTerm454, nodeValue612, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic455 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm455 x = (-2602745435968634880000 : ℝ) * Sparse.eval nodeValue613 x := by
  norm_num [reducedTerm455, nodeValue613, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic456 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm456 x = (677982367796428800000 : ℝ) * Sparse.eval nodeValue614 x := by
  norm_num [reducedTerm456, nodeValue614, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic457 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm457 x = (1801435404238848000000 : ℝ) * Sparse.eval nodeValue615 x := by
  norm_num [reducedTerm457, nodeValue615, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic458 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm458 x = (-2365767237453742080000 : ℝ) * Sparse.eval nodeValue616 x := by
  norm_num [reducedTerm458, nodeValue616, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic459 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm459 x = (3002873618910412800000 : ℝ) * Sparse.eval nodeValue617 x := by
  norm_num [reducedTerm459, nodeValue617, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic460 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm460 x = (1287214867623444480000 : ℝ) * Sparse.eval nodeValue618 x := by
  norm_num [reducedTerm460, nodeValue618, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic461 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm461 x = (3163253859043246080000 : ℝ) * Sparse.eval nodeValue619 x := by
  norm_num [reducedTerm461, nodeValue619, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic462 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm462 x = (9267211259630714880000 : ℝ) * Sparse.eval nodeValue620 x := by
  norm_num [reducedTerm462, nodeValue620, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic463 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm463 x = (365728146625658880000 : ℝ) * Sparse.eval nodeValue621 x := by
  norm_num [reducedTerm463, nodeValue621, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic464 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm464 x = (-820112129438515200000 : ℝ) * Sparse.eval nodeValue622 x := by
  norm_num [reducedTerm464, nodeValue622, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic465 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm465 x = (-1258494730418257920000 : ℝ) * Sparse.eval nodeValue623 x := by
  norm_num [reducedTerm465, nodeValue623, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic466 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm466 x = (-363229471392399360000 : ℝ) * Sparse.eval nodeValue624 x := by
  norm_num [reducedTerm466, nodeValue624, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic467 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm467 x = (4002258833827430400000 : ℝ) * Sparse.eval nodeValue626 x := by
  norm_num [reducedTerm467, nodeValue626, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic468 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm468 x = (-860150167449108480000 : ℝ) * Sparse.eval nodeValue627 x := by
  norm_num [reducedTerm468, nodeValue627, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic469 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm469 x = (363229471392399360000 : ℝ) * Sparse.eval nodeValue628 x := by
  norm_num [reducedTerm469, nodeValue628, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic470 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm470 x = (1355923199361024000000 : ℝ) * Sparse.eval nodeValue629 x := by
  norm_num [reducedTerm470, nodeValue629, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic471 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm471 x = (-1355923199361024000000 : ℝ) * Sparse.eval nodeValue630 x := by
  norm_num [reducedTerm471, nodeValue630, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic472 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm472 x = (-3620046943302451200000 : ℝ) * Sparse.eval nodeValue631 x := by
  norm_num [reducedTerm472, nodeValue631, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic473 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm473 x = (4614435349529886720000 : ℝ) * Sparse.eval nodeValue633 x := by
  norm_num [reducedTerm473, nodeValue633, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic474 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm474 x = (-4581648092858941440000 : ℝ) * Sparse.eval nodeValue634 x := by
  norm_num [reducedTerm474, nodeValue634, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic475 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm475 x = (-1883613935960064000000 : ℝ) * Sparse.eval nodeValue635 x := by
  norm_num [reducedTerm475, nodeValue635, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic476 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm476 x = (-3999431119401123840000 : ℝ) * Sparse.eval nodeValue636 x := by
  norm_num [reducedTerm476, nodeValue636, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic477 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm477 x = (5023829814312960000000 : ℝ) * Sparse.eval nodeValue637 x := by
  norm_num [reducedTerm477, nodeValue637, Integer.Sparse.eval, Sparse.eval]

theorem reducedTermArithmetic478 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm478 x = (5237719375993896960000 : ℝ) * Sparse.eval nodeValue638 x := by
  norm_num [reducedTerm478, nodeValue638, Integer.Sparse.eval, Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge416Check : reducedMerge416 = Integer.Sparse.mergeBy masterLess reducedTerm420 reducedTerm421 := by decide +kernel

theorem reducedMerge417Check : reducedMerge417 = Integer.Sparse.mergeBy masterLess reducedTerm419 reducedMerge416 := by decide +kernel

theorem reducedMerge418Check : reducedMerge418 = Integer.Sparse.mergeBy masterLess reducedTerm422 reducedTerm423 := by decide +kernel

theorem reducedMerge419Check : reducedMerge419 = Integer.Sparse.mergeBy masterLess reducedTerm424 reducedTerm425 := by decide +kernel

theorem reducedMerge420Check : reducedMerge420 = Integer.Sparse.mergeBy masterLess reducedMerge418 reducedMerge419 := by decide +kernel

theorem reducedMerge421Check : reducedMerge421 = Integer.Sparse.mergeBy masterLess reducedMerge417 reducedMerge420 := by decide +kernel

theorem reducedMerge422Check : reducedMerge422 = Integer.Sparse.mergeBy masterLess reducedTerm426 reducedTerm427 := by decide +kernel

theorem reducedMerge423Check : reducedMerge423 = Integer.Sparse.mergeBy masterLess reducedTerm428 reducedTerm429 := by decide +kernel

theorem reducedMerge424Check : reducedMerge424 = Integer.Sparse.mergeBy masterLess reducedMerge422 reducedMerge423 := by decide +kernel

theorem reducedMerge425Check : reducedMerge425 = Integer.Sparse.mergeBy masterLess reducedTerm430 reducedTerm431 := by decide +kernel

theorem reducedMerge426Check : reducedMerge426 = Integer.Sparse.mergeBy masterLess reducedTerm432 reducedTerm433 := by decide +kernel

theorem reducedMerge427Check : reducedMerge427 = Integer.Sparse.mergeBy masterLess reducedMerge425 reducedMerge426 := by decide +kernel

theorem reducedMerge428Check : reducedMerge428 = Integer.Sparse.mergeBy masterLess reducedMerge424 reducedMerge427 := by decide +kernel

theorem reducedMerge429Check : reducedMerge429 = Integer.Sparse.mergeBy masterLess reducedMerge421 reducedMerge428 := by decide +kernel

theorem reducedMerge430Check : reducedMerge430 = Integer.Sparse.mergeBy masterLess reducedTerm435 reducedTerm436 := by decide +kernel

theorem reducedMerge431Check : reducedMerge431 = Integer.Sparse.mergeBy masterLess reducedTerm434 reducedMerge430 := by decide +kernel

theorem reducedMerge432Check : reducedMerge432 = Integer.Sparse.mergeBy masterLess reducedTerm437 reducedTerm438 := by decide +kernel

theorem reducedMerge433Check : reducedMerge433 = Integer.Sparse.mergeBy masterLess reducedTerm439 reducedTerm440 := by decide +kernel

theorem reducedMerge434Check : reducedMerge434 = Integer.Sparse.mergeBy masterLess reducedMerge432 reducedMerge433 := by decide +kernel

theorem reducedMerge435Check : reducedMerge435 = Integer.Sparse.mergeBy masterLess reducedMerge431 reducedMerge434 := by decide +kernel

theorem reducedMerge436Check : reducedMerge436 = Integer.Sparse.mergeBy masterLess reducedTerm441 reducedTerm442 := by decide +kernel

theorem reducedMerge437Check : reducedMerge437 = Integer.Sparse.mergeBy masterLess reducedTerm443 reducedTerm444 := by decide +kernel

theorem reducedMerge438Check : reducedMerge438 = Integer.Sparse.mergeBy masterLess reducedMerge436 reducedMerge437 := by decide +kernel

theorem reducedMerge439Check : reducedMerge439 = Integer.Sparse.mergeBy masterLess reducedTerm445 reducedTerm446 := by decide +kernel

theorem reducedMerge440Check : reducedMerge440 = Integer.Sparse.mergeBy masterLess reducedTerm447 reducedTerm448 := by decide +kernel

theorem reducedMerge441Check : reducedMerge441 = Integer.Sparse.mergeBy masterLess reducedMerge439 reducedMerge440 := by decide +kernel

theorem reducedMerge442Check : reducedMerge442 = Integer.Sparse.mergeBy masterLess reducedMerge438 reducedMerge441 := by decide +kernel

theorem reducedMerge443Check : reducedMerge443 = Integer.Sparse.mergeBy masterLess reducedMerge435 reducedMerge442 := by decide +kernel

theorem reducedMerge444Check : reducedMerge444 = Integer.Sparse.mergeBy masterLess reducedMerge429 reducedMerge443 := by decide +kernel

theorem reducedMerge445Check : reducedMerge445 = Integer.Sparse.mergeBy masterLess reducedTerm450 reducedTerm451 := by decide +kernel

theorem reducedMerge446Check : reducedMerge446 = Integer.Sparse.mergeBy masterLess reducedTerm449 reducedMerge445 := by decide +kernel

theorem reducedMerge447Check : reducedMerge447 = Integer.Sparse.mergeBy masterLess reducedTerm452 reducedTerm453 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMerge448Check : reducedMerge448 = Integer.Sparse.mergeBy masterLess reducedTerm454 reducedTerm455 := by decide +kernel

theorem reducedMerge449Check : reducedMerge449 = Integer.Sparse.mergeBy masterLess reducedMerge447 reducedMerge448 := by decide +kernel

theorem reducedMerge450Check : reducedMerge450 = Integer.Sparse.mergeBy masterLess reducedMerge446 reducedMerge449 := by decide +kernel

theorem reducedMerge451Check : reducedMerge451 = Integer.Sparse.mergeBy masterLess reducedTerm456 reducedTerm457 := by decide +kernel

theorem reducedMerge452Check : reducedMerge452 = Integer.Sparse.mergeBy masterLess reducedTerm458 reducedTerm459 := by decide +kernel

theorem reducedMerge453Check : reducedMerge453 = Integer.Sparse.mergeBy masterLess reducedMerge451 reducedMerge452 := by decide +kernel

theorem reducedMerge454Check : reducedMerge454 = Integer.Sparse.mergeBy masterLess reducedTerm460 reducedTerm461 := by decide +kernel

theorem reducedMerge455Check : reducedMerge455 = Integer.Sparse.mergeBy masterLess reducedTerm462 reducedTerm463 := by decide +kernel

theorem reducedMerge456Check : reducedMerge456 = Integer.Sparse.mergeBy masterLess reducedMerge454 reducedMerge455 := by decide +kernel

theorem reducedMerge457Check : reducedMerge457 = Integer.Sparse.mergeBy masterLess reducedMerge453 reducedMerge456 := by decide +kernel

theorem reducedMerge458Check : reducedMerge458 = Integer.Sparse.mergeBy masterLess reducedMerge450 reducedMerge457 := by decide +kernel

theorem reducedMerge459Check : reducedMerge459 = Integer.Sparse.mergeBy masterLess reducedTerm465 reducedTerm466 := by decide +kernel

theorem reducedMerge460Check : reducedMerge460 = Integer.Sparse.mergeBy masterLess reducedTerm464 reducedMerge459 := by decide +kernel

theorem reducedMerge461Check : reducedMerge461 = Integer.Sparse.mergeBy masterLess reducedTerm467 reducedTerm468 := by decide +kernel

theorem reducedMerge462Check : reducedMerge462 = Integer.Sparse.mergeBy masterLess reducedTerm469 reducedTerm470 := by decide +kernel

theorem reducedMerge463Check : reducedMerge463 = Integer.Sparse.mergeBy masterLess reducedMerge461 reducedMerge462 := by decide +kernel

theorem reducedMerge464Check : reducedMerge464 = Integer.Sparse.mergeBy masterLess reducedMerge460 reducedMerge463 := by decide +kernel

theorem reducedMerge465Check : reducedMerge465 = Integer.Sparse.mergeBy masterLess reducedTerm471 reducedTerm472 := by decide +kernel

theorem reducedMerge466Check : reducedMerge466 = Integer.Sparse.mergeBy masterLess reducedTerm473 reducedTerm474 := by decide +kernel

theorem reducedMerge467Check : reducedMerge467 = Integer.Sparse.mergeBy masterLess reducedMerge465 reducedMerge466 := by decide +kernel

theorem reducedMerge468Check : reducedMerge468 = Integer.Sparse.mergeBy masterLess reducedTerm475 reducedTerm476 := by decide +kernel

theorem reducedMerge469Check : reducedMerge469 = Integer.Sparse.mergeBy masterLess reducedTerm477 reducedTerm478 := by decide +kernel

theorem reducedMerge470Check : reducedMerge470 = Integer.Sparse.mergeBy masterLess reducedMerge468 reducedMerge469 := by decide +kernel

theorem reducedMerge471Check : reducedMerge471 = Integer.Sparse.mergeBy masterLess reducedMerge467 reducedMerge470 := by decide +kernel

theorem reducedMerge472Check : reducedMerge472 = Integer.Sparse.mergeBy masterLess reducedMerge464 reducedMerge471 := by decide +kernel

theorem reducedMerge473Check : reducedMerge473 = Integer.Sparse.mergeBy masterLess reducedMerge458 reducedMerge472 := by decide +kernel

theorem reducedMerge474Check : reducedMerge474 = Integer.Sparse.mergeBy masterLess reducedMerge444 reducedMerge473 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm419 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm419 (originalVector B) := by
  rw [reducedTermArithmetic419, ← sound526 B hB hF]
  change (-6268329904672604160000 : ℝ) * mixedMoment B node526 node526Labels =
    (37623398400 : ℝ) * (((-166607222400 : ℤ) : ℝ) * mixedMoment B node526 node526Labels + 0)
  ring

theorem reducedTermEval420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm420 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm420 (originalVector B) := by
  rw [reducedTermArithmetic420, ← sound527 B hB hF]
  change (3294283875393208320000 : ℝ) * mixedMoment B node527 node527Labels =
    (37623398400 : ℝ) * ((87559444800 : ℝ) * mixedMoment B node527 node527Labels + 0)
  ring

theorem reducedTermEval421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm421 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm421 (originalVector B) := by
  rw [reducedTermArithmetic421, ← sound528 B hB hF]
  change (43831740715499520000 : ℝ) * mixedMoment B node528 node528Labels =
    (37623398400 : ℝ) * ((1165012800 : ℝ) * mixedMoment B node528 node528Labels + 0)
  ring

theorem reducedTermEval422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm422 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm422 (originalVector B) := by
  rw [reducedTermArithmetic422, ← sound529 B hB hF]
  change (1001082421468200960000 : ℝ) * mixedMoment B node529 node529Labels =
    (37623398400 : ℝ) * ((26607974400 : ℝ) * mixedMoment B node529 node529Labels + 0)
  ring

theorem reducedTermEval423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm423 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm423 (originalVector B) := by
  rw [reducedTermArithmetic423, ← sound530 B hB hF]
  change (4050726198607872000000 : ℝ) * mixedMoment B node530 node530Labels =
    (37623398400 : ℝ) * ((107665080000 : ℝ) * mixedMoment B node530 node530Labels + 0)
  ring

theorem reducedTermEval424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm424 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm424 (originalVector B) := by
  rw [reducedTermArithmetic424, ← sound531 B hB hF]
  change (6584917799562117120000 : ℝ) * mixedMoment B node531 node531Labels =
    (37623398400 : ℝ) * ((175021876800 : ℝ) * mixedMoment B node531 node531Labels + 0)
  ring

theorem reducedTermEval425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm425 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm425 (originalVector B) := by
  rw [reducedTermArithmetic425, ← sound532 B hB hF]
  change (-12197954412781240320000 : ℝ) * mixedMoment B node532 node532Labels =
    (37623398400 : ℝ) * (((-324211924800 : ℤ) : ℝ) * mixedMoment B node532 node532Labels + 0)
  ring

theorem reducedTermEval426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm426 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm426 (originalVector B) := by
  rw [reducedTermArithmetic426, ← sound533 B hB hF]
  change (-971881186342993920000 : ℝ) * mixedMoment B node533 node533Labels =
    (37623398400 : ℝ) * (((-25831828800 : ℤ) : ℝ) * mixedMoment B node533 node533Labels + 0)
  ring

theorem reducedTermEval427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm427 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm427 (originalVector B) := by
  rw [reducedTermArithmetic427, ← sound577 B hB hF]
  change (-654308882759024640000 : ℝ) * mixedMoment B node577 node577Labels =
    (37623398400 : ℝ) * (((-17391009600 : ℤ) : ℝ) * mixedMoment B node577 node577Labels + 0)
  ring

theorem reducedTermEval428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm428 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm428 (originalVector B) := by
  rw [reducedTermArithmetic428, ← sound578 B hB hF]
  change (-2282493232765992960000 : ℝ) * mixedMoment B node578 node578Labels =
    (37623398400 : ℝ) * (((-60666854400 : ℤ) : ℝ) * mixedMoment B node578 node578Labels + 0)
  ring

theorem reducedTermEval429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm429 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm429 (originalVector B) := by
  rw [reducedTermArithmetic429, ← sound579 B hB hF]
  change (654308882759024640000 : ℝ) * mixedMoment B node579 node579Labels =
    (37623398400 : ℝ) * ((17391009600 : ℝ) * mixedMoment B node579 node579Labels + 0)
  ring

theorem reducedTermEval430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm430 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm430 (originalVector B) := by
  rw [reducedTermArithmetic430, ← sound580 B hB hF]
  change (877592856526848000000 : ℝ) * mixedMoment B node580 node580Labels =
    (37623398400 : ℝ) * ((23325720000 : ℝ) * mixedMoment B node580 node580Labels + 0)
  ring

theorem reducedTermEval431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm431 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm431 (originalVector B) := by
  rw [reducedTermArithmetic431, ← sound581 B hB hF]
  change (877447660307742720000 : ℝ) * mixedMoment B node581 node581Labels =
    (37623398400 : ℝ) * ((23321860800 : ℝ) * mixedMoment B node581 node581Labels + 0)
  ring

theorem reducedTermEval432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm432 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm432 (originalVector B) := by
  rw [reducedTermArithmetic432, ← sound582 B hB hF]
  change (607591276892651520000 : ℝ) * mixedMoment B node582 node582Labels =
    (37623398400 : ℝ) * ((16149292800 : ℝ) * mixedMoment B node582 node582Labels + 0)
  ring

theorem reducedTermEval433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm433 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm433 (originalVector B) := by
  rw [reducedTermArithmetic433, ← sound583 B hB hF]
  change (2282493232765992960000 : ℝ) * mixedMoment B node583 node583Labels =
    (37623398400 : ℝ) * ((60666854400 : ℝ) * mixedMoment B node583 node583Labels + 0)
  ring

theorem reducedTermEval434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm434 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm434 (originalVector B) := by
  rw [reducedTermArithmetic434, ← sound584 B hB hF]
  change (-113253321790586880000 : ℝ) * mixedMoment B node584 node584Labels =
    (37623398400 : ℝ) * (((-3010183200 : ℤ) : ℝ) * mixedMoment B node584 node584Labels + 0)
  ring

theorem reducedTermEval435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm435 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm435 (originalVector B) := by
  rw [reducedTermArithmetic435, ← sound585 B hB hF]
  change (-2325444766551244800000 : ℝ) * mixedMoment B node585 node585Labels =
    (37623398400 : ℝ) * (((-61808472000 : ℤ) : ℝ) * mixedMoment B node585 node585Labels + 0)
  ring

theorem reducedTermEval436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm436 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm436 (originalVector B) := by
  rw [reducedTermArithmetic436, ← sound586 B hB hF]
  change (-878028445184163840000 : ℝ) * mixedMoment B node586 node586Labels =
    (37623398400 : ℝ) * (((-23337297600 : ℤ) : ℝ) * mixedMoment B node586 node586Labels + 0)
  ring

theorem reducedTermEval437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm437 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm437 (originalVector B) := by
  rw [reducedTermArithmetic437, ← sound587 B hB hF]
  change (4950070676784414720000 : ℝ) * mixedMoment B node587 node587Labels =
    (37623398400 : ℝ) * ((131568940800 : ℝ) * mixedMoment B node587 node587Labels + 0)
  ring

theorem reducedTermEval438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm438 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm438 (originalVector B) := by
  rw [reducedTermArithmetic438, ← sound588 B hB hF]
  change (-947351242264412160000 : ℝ) * mixedMoment B node588 node588Labels =
    (37623398400 : ℝ) * (((-25179842400 : ℤ) : ℝ) * mixedMoment B node588 node588Labels + 0)
  ring

theorem reducedTermEval439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm439 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm439 (originalVector B) := by
  rw [reducedTermArithmetic439, ← sound589 B hB hF]
  change (-877883248965058560000 : ℝ) * mixedMoment B node589 node589Labels =
    (37623398400 : ℝ) * (((-23333438400 : ℤ) : ℝ) * mixedMoment B node589 node589Labels + 0)
  ring

theorem reducedTermEval440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm440 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm440 (originalVector B) := by
  rw [reducedTermArithmetic440, ← sound590 B hB hF]
  change (-544816666760970240000 : ℝ) * mixedMoment B node590 node590Labels =
    (37623398400 : ℝ) * (((-14480793600 : ℤ) : ℝ) * mixedMoment B node590 node590Labels + 0)
  ring

theorem reducedTermEval441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm441 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm441 (originalVector B) := by
  rw [reducedTermArithmetic441, ← sound591 B hB hF]
  change (2291676713032089600000 : ℝ) * mixedMoment B node591 node591Labels =
    (37623398400 : ℝ) * ((60910944000 : ℝ) * mixedMoment B node591 node591Labels + 0)
  ring

theorem reducedTermEval442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm442 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm442 (originalVector B) := by
  rw [reducedTermArithmetic442, ← sound597 B hB hF]
  change (-28541892592926720000 : ℝ) * mixedMoment B node597 node597Labels =
    (37623398400 : ℝ) * (((-758620800 : ℤ) : ℝ) * mixedMoment B node597 node597Labels + 0)
  ring

theorem reducedTermEval443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm443 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm443 (originalVector B) := by
  rw [reducedTermArithmetic443, ← sound599 B hB hF]
  change (-1211529171307069440000 : ℝ) * mixedMoment B node599 node599Labels =
    (37623398400 : ℝ) * (((-32201481600 : ℤ) : ℝ) * mixedMoment B node599 node599Labels + 0)
  ring

theorem reducedTermEval444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm444 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm444 (originalVector B) := by
  rw [reducedTermArithmetic444, ← sound600 B hB hF]
  change (344588552322416640000 : ℝ) * mixedMoment B node600 node600Labels =
    (37623398400 : ℝ) * ((9158889600 : ℝ) * mixedMoment B node600 node600Labels + 0)
  ring

theorem reducedTermEval445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm445 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm445 (originalVector B) := by
  rw [reducedTermArithmetic445, ← sound601 B hB hF]
  change (28541892592926720000 : ℝ) * mixedMoment B node601 node601Labels =
    (37623398400 : ℝ) * ((758620800 : ℝ) * mixedMoment B node601 node601Labels + 0)
  ring

theorem reducedTermEval446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm446 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm446 (originalVector B) := by
  rw [reducedTermArithmetic446, ← sound603 B hB hF]
  change (533546803510640640000 : ℝ) * mixedMoment B node603 node603Labels =
    (37623398400 : ℝ) * ((14181249600 : ℝ) * mixedMoment B node603 node603Labels + 0)
  ring

theorem reducedTermEval447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm447 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm447 (originalVector B) := by
  rw [reducedTermArithmetic447, ← sound604 B hB hF]
  change (6690208535414046720000 : ℝ) * mixedMoment B node604 node604Labels =
    (37623398400 : ℝ) * ((177820420800 : ℝ) * mixedMoment B node604 node604Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionSound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedTermEval448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm448 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm448 (originalVector B) := by
  rw [reducedTermArithmetic448, ← sound605 B hB hF]
  change (-2453660793490636800000 : ℝ) * mixedMoment B node605 node605Labels =
    (37623398400 : ℝ) * (((-65216352000 : ℤ) : ℝ) * mixedMoment B node605 node605Labels + 0)
  ring

theorem reducedTermEval449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm449 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm449 (originalVector B) := by
  rw [reducedTermArithmetic449, ← sound606 B hB hF]
  change (1441480432653434880000 : ℝ) * mixedMoment B node606 node606Labels =
    (37623398400 : ℝ) * ((38313403200 : ℝ) * mixedMoment B node606 node606Labels + 0)
  ring

theorem reducedTermEval450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm450 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm450 (originalVector B) := by
  rw [reducedTermArithmetic450, ← sound607 B hB hF]
  change (2300979745408942080000 : ℝ) * mixedMoment B node607 node607Labels =
    (37623398400 : ℝ) * ((61158211200 : ℝ) * mixedMoment B node607 node607Labels + 0)
  ring

theorem reducedTermEval451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm451 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm451 (originalVector B) := by
  rw [reducedTermArithmetic451, ← sound608 B hB hF]
  change (-1054181617875025920000 : ℝ) * mixedMoment B node608 node608Labels =
    (37623398400 : ℝ) * (((-28019308800 : ℤ) : ℝ) * mixedMoment B node608 node608Labels + 0)
  ring

theorem reducedTermEval452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm452 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm452 (originalVector B) := by
  rw [reducedTermArithmetic452, ← sound610 B hB hF]
  change (-9473152863350292480000 : ℝ) * mixedMoment B node610 node610Labels =
    (37623398400 : ℝ) * (((-251788867200 : ℤ) : ℝ) * mixedMoment B node610 node610Labels + 0)
  ring

theorem reducedTermEval453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm453 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm453 (originalVector B) := by
  rw [reducedTermArithmetic453, ← sound611 B hB hF]
  change (18388973290326589440000 : ℝ) * mixedMoment B node611 node611Labels =
    (37623398400 : ℝ) * ((488764281600 : ℝ) * mixedMoment B node611 node611Labels + 0)
  ring

theorem reducedTermEval454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm454 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm454 (originalVector B) := by
  rw [reducedTermArithmetic454, ← sound612 B hB hF]
  change (-584459388199895040000 : ℝ) * mixedMoment B node612 node612Labels =
    (37623398400 : ℝ) * (((-15534465600 : ℤ) : ℝ) * mixedMoment B node612 node612Labels + 0)
  ring

theorem reducedTermEval455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm455 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm455 (originalVector B) := by
  rw [reducedTermArithmetic455, ← sound613 B hB hF]
  change (-2602745435968634880000 : ℝ) * mixedMoment B node613 node613Labels =
    (37623398400 : ℝ) * (((-69178903200 : ℤ) : ℝ) * mixedMoment B node613 node613Labels + 0)
  ring

theorem reducedTermEval456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm456 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm456 (originalVector B) := by
  rw [reducedTermArithmetic456, ← sound614 B hB hF]
  change (677982367796428800000 : ℝ) * mixedMoment B node614 node614Labels =
    (37623398400 : ℝ) * ((18020232000 : ℝ) * mixedMoment B node614 node614Labels + 0)
  ring

theorem reducedTermEval457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm457 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm457 (originalVector B) := by
  rw [reducedTermArithmetic457, ← sound615 B hB hF]
  change (1801435404238848000000 : ℝ) * mixedMoment B node615 node615Labels =
    (37623398400 : ℝ) * ((47880720000 : ℝ) * mixedMoment B node615 node615Labels + 0)
  ring

theorem reducedTermEval458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm458 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm458 (originalVector B) := by
  rw [reducedTermArithmetic458, ← sound616 B hB hF]
  change (-2365767237453742080000 : ℝ) * mixedMoment B node616 node616Labels =
    (37623398400 : ℝ) * (((-62880211200 : ℤ) : ℝ) * mixedMoment B node616 node616Labels + 0)
  ring

theorem reducedTermEval459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm459 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm459 (originalVector B) := by
  rw [reducedTermArithmetic459, ← sound617 B hB hF]
  change (3002873618910412800000 : ℝ) * mixedMoment B node617 node617Labels =
    (37623398400 : ℝ) * ((79813992000 : ℝ) * mixedMoment B node617 node617Labels + 0)
  ring

theorem reducedTermEval460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm460 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm460 (originalVector B) := by
  rw [reducedTermArithmetic460, ← sound618 B hB hF]
  change (1287214867623444480000 : ℝ) * mixedMoment B node618 node618Labels =
    (37623398400 : ℝ) * ((34213147200 : ℝ) * mixedMoment B node618 node618Labels + 0)
  ring

theorem reducedTermEval461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm461 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm461 (originalVector B) := by
  rw [reducedTermArithmetic461, ← sound619 B hB hF]
  change (3163253859043246080000 : ℝ) * mixedMoment B node619 node619Labels =
    (37623398400 : ℝ) * ((84076771200 : ℝ) * mixedMoment B node619 node619Labels + 0)
  ring

theorem reducedTermEval462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm462 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm462 (originalVector B) := by
  rw [reducedTermArithmetic462, ← sound620 B hB hF]
  change (9267211259630714880000 : ℝ) * mixedMoment B node620 node620Labels =
    (37623398400 : ℝ) * ((246315103200 : ℝ) * mixedMoment B node620 node620Labels + 0)
  ring

theorem reducedTermEval463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm463 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm463 (originalVector B) := by
  rw [reducedTermArithmetic463, ← sound621 B hB hF]
  change (365728146625658880000 : ℝ) * mixedMoment B node621 node621Labels =
    (37623398400 : ℝ) * ((9720763200 : ℝ) * mixedMoment B node621 node621Labels + 0)
  ring

theorem reducedTermEval464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm464 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm464 (originalVector B) := by
  rw [reducedTermArithmetic464, ← sound622 B hB hF]
  change (-820112129438515200000 : ℝ) * mixedMoment B node622 node622Labels =
    (37623398400 : ℝ) * (((-21797928000 : ℤ) : ℝ) * mixedMoment B node622 node622Labels + 0)
  ring

theorem reducedTermEval465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm465 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm465 (originalVector B) := by
  rw [reducedTermArithmetic465, ← sound623 B hB hF]
  change (-1258494730418257920000 : ℝ) * mixedMoment B node623 node623Labels =
    (37623398400 : ℝ) * (((-33449788800 : ℤ) : ℝ) * mixedMoment B node623 node623Labels + 0)
  ring

theorem reducedTermEval466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm466 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm466 (originalVector B) := by
  rw [reducedTermArithmetic466, ← sound624 B hB hF]
  change (-363229471392399360000 : ℝ) * mixedMoment B node624 node624Labels =
    (37623398400 : ℝ) * (((-9654350400 : ℤ) : ℝ) * mixedMoment B node624 node624Labels + 0)
  ring

theorem reducedTermEval467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm467 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm467 (originalVector B) := by
  rw [reducedTermArithmetic467, ← sound626 B hB hF]
  change (4002258833827430400000 : ℝ) * mixedMoment B node626 node626Labels =
    (37623398400 : ℝ) * ((106376856000 : ℝ) * mixedMoment B node626 node626Labels + 0)
  ring

theorem reducedTermEval468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm468 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm468 (originalVector B) := by
  rw [reducedTermArithmetic468, ← sound627 B hB hF]
  change (-860150167449108480000 : ℝ) * mixedMoment B node627 node627Labels =
    (37623398400 : ℝ) * (((-22862107200 : ℤ) : ℝ) * mixedMoment B node627 node627Labels + 0)
  ring

theorem reducedTermEval469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm469 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm469 (originalVector B) := by
  rw [reducedTermArithmetic469, ← sound628 B hB hF]
  change (363229471392399360000 : ℝ) * mixedMoment B node628 node628Labels =
    (37623398400 : ℝ) * ((9654350400 : ℝ) * mixedMoment B node628 node628Labels + 0)
  ring

theorem reducedTermEval470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm470 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm470 (originalVector B) := by
  rw [reducedTermArithmetic470, ← sound629 B hB hF]
  change (1355923199361024000000 : ℝ) * mixedMoment B node629 node629Labels =
    (37623398400 : ℝ) * ((36039360000 : ℝ) * mixedMoment B node629 node629Labels + 0)
  ring

theorem reducedTermEval471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm471 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm471 (originalVector B) := by
  rw [reducedTermArithmetic471, ← sound630 B hB hF]
  change (-1355923199361024000000 : ℝ) * mixedMoment B node630 node630Labels =
    (37623398400 : ℝ) * (((-36039360000 : ℤ) : ℝ) * mixedMoment B node630 node630Labels + 0)
  ring

theorem reducedTermEval472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm472 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm472 (originalVector B) := by
  rw [reducedTermArithmetic472, ← sound631 B hB hF]
  change (-3620046943302451200000 : ℝ) * mixedMoment B node631 node631Labels =
    (37623398400 : ℝ) * (((-96217968000 : ℤ) : ℝ) * mixedMoment B node631 node631Labels + 0)
  ring

theorem reducedTermEval473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm473 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm473 (originalVector B) := by
  rw [reducedTermArithmetic473, ← sound633 B hB hF]
  change (4614435349529886720000 : ℝ) * mixedMoment B node633 node633Labels =
    (37623398400 : ℝ) * ((122648020800 : ℝ) * mixedMoment B node633 node633Labels + 0)
  ring

theorem reducedTermEval474 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm474 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm474 (originalVector B) := by
  rw [reducedTermArithmetic474, ← sound634 B hB hF]
  change (-4581648092858941440000 : ℝ) * mixedMoment B node634 node634Labels =
    (37623398400 : ℝ) * (((-121776561600 : ℤ) : ℝ) * mixedMoment B node634 node634Labels + 0)
  ring

theorem reducedTermEval475 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm475 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm475 (originalVector B) := by
  rw [reducedTermArithmetic475, ← sound635 B hB hF]
  change (-1883613935960064000000 : ℝ) * mixedMoment B node635 node635Labels =
    (37623398400 : ℝ) * (((-50064960000 : ℤ) : ℝ) * mixedMoment B node635 node635Labels + 0)
  ring

theorem reducedTermEval476 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm476 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm476 (originalVector B) := by
  rw [reducedTermArithmetic476, ← sound636 B hB hF]
  change (-3999431119401123840000 : ℝ) * mixedMoment B node636 node636Labels =
    (37623398400 : ℝ) * (((-106301697600 : ℤ) : ℝ) * mixedMoment B node636 node636Labels + 0)
  ring

theorem reducedTermEval477 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm477 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm477 (originalVector B) := by
  rw [reducedTermArithmetic477, ← sound637 B hB hF]
  change (5023829814312960000000 : ℝ) * mixedMoment B node637 node637Labels =
    (37623398400 : ℝ) * ((133529400000 : ℝ) * mixedMoment B node637 node637Labels + 0)
  ring

theorem reducedTermEval478 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedTerm478 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalTerm478 (originalVector B) := by
  rw [reducedTermArithmetic478, ← sound638 B hB hF]
  change (5237719375993896960000 : ℝ) * mixedMoment B node638 node638Labels =
    (37623398400 : ℝ) * ((139214414400 : ℝ) * mixedMoment B node638 node638Labels + 0)
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval416 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge416 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge416 (originalVector B) := by
  rw [reducedMerge416Check, Integer.Sparse.eval_mergeBy, reducedTermEval420 B hB hF, reducedTermEval421 B hB hF]
  rw [originalMerge416, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval417 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge417 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge417 (originalVector B) := by
  rw [reducedMerge417Check, Integer.Sparse.eval_mergeBy, reducedTermEval419 B hB hF, reducedMergeEval416 B hB hF]
  rw [originalMerge417, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval418 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge418 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge418 (originalVector B) := by
  rw [reducedMerge418Check, Integer.Sparse.eval_mergeBy, reducedTermEval422 B hB hF, reducedTermEval423 B hB hF]
  rw [originalMerge418, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval419 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge419 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge419 (originalVector B) := by
  rw [reducedMerge419Check, Integer.Sparse.eval_mergeBy, reducedTermEval424 B hB hF, reducedTermEval425 B hB hF]
  rw [originalMerge419, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval420 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge420 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge420 (originalVector B) := by
  rw [reducedMerge420Check, Integer.Sparse.eval_mergeBy, reducedMergeEval418 B hB hF, reducedMergeEval419 B hB hF]
  rw [originalMerge420, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval421 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge421 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge421 (originalVector B) := by
  rw [reducedMerge421Check, Integer.Sparse.eval_mergeBy, reducedMergeEval417 B hB hF, reducedMergeEval420 B hB hF]
  rw [originalMerge421, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval422 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge422 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge422 (originalVector B) := by
  rw [reducedMerge422Check, Integer.Sparse.eval_mergeBy, reducedTermEval426 B hB hF, reducedTermEval427 B hB hF]
  rw [originalMerge422, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval423 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge423 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge423 (originalVector B) := by
  rw [reducedMerge423Check, Integer.Sparse.eval_mergeBy, reducedTermEval428 B hB hF, reducedTermEval429 B hB hF]
  rw [originalMerge423, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval424 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge424 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge424 (originalVector B) := by
  rw [reducedMerge424Check, Integer.Sparse.eval_mergeBy, reducedMergeEval422 B hB hF, reducedMergeEval423 B hB hF]
  rw [originalMerge424, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval425 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge425 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge425 (originalVector B) := by
  rw [reducedMerge425Check, Integer.Sparse.eval_mergeBy, reducedTermEval430 B hB hF, reducedTermEval431 B hB hF]
  rw [originalMerge425, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval426 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge426 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge426 (originalVector B) := by
  rw [reducedMerge426Check, Integer.Sparse.eval_mergeBy, reducedTermEval432 B hB hF, reducedTermEval433 B hB hF]
  rw [originalMerge426, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval427 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge427 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge427 (originalVector B) := by
  rw [reducedMerge427Check, Integer.Sparse.eval_mergeBy, reducedMergeEval425 B hB hF, reducedMergeEval426 B hB hF]
  rw [originalMerge427, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval428 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge428 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge428 (originalVector B) := by
  rw [reducedMerge428Check, Integer.Sparse.eval_mergeBy, reducedMergeEval424 B hB hF, reducedMergeEval427 B hB hF]
  rw [originalMerge428, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval429 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge429 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge429 (originalVector B) := by
  rw [reducedMerge429Check, Integer.Sparse.eval_mergeBy, reducedMergeEval421 B hB hF, reducedMergeEval428 B hB hF]
  rw [originalMerge429, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval430 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge430 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge430 (originalVector B) := by
  rw [reducedMerge430Check, Integer.Sparse.eval_mergeBy, reducedTermEval435 B hB hF, reducedTermEval436 B hB hF]
  rw [originalMerge430, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval431 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge431 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge431 (originalVector B) := by
  rw [reducedMerge431Check, Integer.Sparse.eval_mergeBy, reducedTermEval434 B hB hF, reducedMergeEval430 B hB hF]
  rw [originalMerge431, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge432 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge432 (originalVector B) := by
  rw [reducedMerge432Check, Integer.Sparse.eval_mergeBy, reducedTermEval437 B hB hF, reducedTermEval438 B hB hF]
  rw [originalMerge432, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge433 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge433 (originalVector B) := by
  rw [reducedMerge433Check, Integer.Sparse.eval_mergeBy, reducedTermEval439 B hB hF, reducedTermEval440 B hB hF]
  rw [originalMerge433, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge434 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge434 (originalVector B) := by
  rw [reducedMerge434Check, Integer.Sparse.eval_mergeBy, reducedMergeEval432 B hB hF, reducedMergeEval433 B hB hF]
  rw [originalMerge434, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge435 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge435 (originalVector B) := by
  rw [reducedMerge435Check, Integer.Sparse.eval_mergeBy, reducedMergeEval431 B hB hF, reducedMergeEval434 B hB hF]
  rw [originalMerge435, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge436 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge436 (originalVector B) := by
  rw [reducedMerge436Check, Integer.Sparse.eval_mergeBy, reducedTermEval441 B hB hF, reducedTermEval442 B hB hF]
  rw [originalMerge436, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge437 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge437 (originalVector B) := by
  rw [reducedMerge437Check, Integer.Sparse.eval_mergeBy, reducedTermEval443 B hB hF, reducedTermEval444 B hB hF]
  rw [originalMerge437, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval438 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge438 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge438 (originalVector B) := by
  rw [reducedMerge438Check, Integer.Sparse.eval_mergeBy, reducedMergeEval436 B hB hF, reducedMergeEval437 B hB hF]
  rw [originalMerge438, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge439 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge439 (originalVector B) := by
  rw [reducedMerge439Check, Integer.Sparse.eval_mergeBy, reducedTermEval445 B hB hF, reducedTermEval446 B hB hF]
  rw [originalMerge439, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge440 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge440 (originalVector B) := by
  rw [reducedMerge440Check, Integer.Sparse.eval_mergeBy, reducedTermEval447 B hB hF, reducedTermEval448 B hB hF]
  rw [originalMerge440, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge441 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge441 (originalVector B) := by
  rw [reducedMerge441Check, Integer.Sparse.eval_mergeBy, reducedMergeEval439 B hB hF, reducedMergeEval440 B hB hF]
  rw [originalMerge441, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge442 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge442 (originalVector B) := by
  rw [reducedMerge442Check, Integer.Sparse.eval_mergeBy, reducedMergeEval438 B hB hF, reducedMergeEval441 B hB hF]
  rw [originalMerge442, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge443 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge443 (originalVector B) := by
  rw [reducedMerge443Check, Integer.Sparse.eval_mergeBy, reducedMergeEval435 B hB hF, reducedMergeEval442 B hB hF]
  rw [originalMerge443, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval444 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge444 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge444 (originalVector B) := by
  rw [reducedMerge444Check, Integer.Sparse.eval_mergeBy, reducedMergeEval429 B hB hF, reducedMergeEval443 B hB hF]
  rw [originalMerge444, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval445 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge445 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge445 (originalVector B) := by
  rw [reducedMerge445Check, Integer.Sparse.eval_mergeBy, reducedTermEval450 B hB hF, reducedTermEval451 B hB hF]
  rw [originalMerge445, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval446 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge446 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge446 (originalVector B) := by
  rw [reducedMerge446Check, Integer.Sparse.eval_mergeBy, reducedTermEval449 B hB hF, reducedMergeEval445 B hB hF]
  rw [originalMerge446, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval447 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge447 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge447 (originalVector B) := by
  rw [reducedMerge447Check, Integer.Sparse.eval_mergeBy, reducedTermEval452 B hB hF, reducedTermEval453 B hB hF]
  rw [originalMerge447, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_ReductionMergeSound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval448 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge448 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge448 (originalVector B) := by
  rw [reducedMerge448Check, Integer.Sparse.eval_mergeBy, reducedTermEval454 B hB hF, reducedTermEval455 B hB hF]
  rw [originalMerge448, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval449 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge449 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge449 (originalVector B) := by
  rw [reducedMerge449Check, Integer.Sparse.eval_mergeBy, reducedMergeEval447 B hB hF, reducedMergeEval448 B hB hF]
  rw [originalMerge449, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval450 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge450 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge450 (originalVector B) := by
  rw [reducedMerge450Check, Integer.Sparse.eval_mergeBy, reducedMergeEval446 B hB hF, reducedMergeEval449 B hB hF]
  rw [originalMerge450, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval451 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge451 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge451 (originalVector B) := by
  rw [reducedMerge451Check, Integer.Sparse.eval_mergeBy, reducedTermEval456 B hB hF, reducedTermEval457 B hB hF]
  rw [originalMerge451, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval452 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge452 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge452 (originalVector B) := by
  rw [reducedMerge452Check, Integer.Sparse.eval_mergeBy, reducedTermEval458 B hB hF, reducedTermEval459 B hB hF]
  rw [originalMerge452, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval453 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge453 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge453 (originalVector B) := by
  rw [reducedMerge453Check, Integer.Sparse.eval_mergeBy, reducedMergeEval451 B hB hF, reducedMergeEval452 B hB hF]
  rw [originalMerge453, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval454 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge454 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge454 (originalVector B) := by
  rw [reducedMerge454Check, Integer.Sparse.eval_mergeBy, reducedTermEval460 B hB hF, reducedTermEval461 B hB hF]
  rw [originalMerge454, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval455 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge455 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge455 (originalVector B) := by
  rw [reducedMerge455Check, Integer.Sparse.eval_mergeBy, reducedTermEval462 B hB hF, reducedTermEval463 B hB hF]
  rw [originalMerge455, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval456 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge456 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge456 (originalVector B) := by
  rw [reducedMerge456Check, Integer.Sparse.eval_mergeBy, reducedMergeEval454 B hB hF, reducedMergeEval455 B hB hF]
  rw [originalMerge456, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval457 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge457 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge457 (originalVector B) := by
  rw [reducedMerge457Check, Integer.Sparse.eval_mergeBy, reducedMergeEval453 B hB hF, reducedMergeEval456 B hB hF]
  rw [originalMerge457, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval458 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge458 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge458 (originalVector B) := by
  rw [reducedMerge458Check, Integer.Sparse.eval_mergeBy, reducedMergeEval450 B hB hF, reducedMergeEval457 B hB hF]
  rw [originalMerge458, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval459 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge459 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge459 (originalVector B) := by
  rw [reducedMerge459Check, Integer.Sparse.eval_mergeBy, reducedTermEval465 B hB hF, reducedTermEval466 B hB hF]
  rw [originalMerge459, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval460 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge460 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge460 (originalVector B) := by
  rw [reducedMerge460Check, Integer.Sparse.eval_mergeBy, reducedTermEval464 B hB hF, reducedMergeEval459 B hB hF]
  rw [originalMerge460, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval461 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge461 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge461 (originalVector B) := by
  rw [reducedMerge461Check, Integer.Sparse.eval_mergeBy, reducedTermEval467 B hB hF, reducedTermEval468 B hB hF]
  rw [originalMerge461, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval462 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge462 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge462 (originalVector B) := by
  rw [reducedMerge462Check, Integer.Sparse.eval_mergeBy, reducedTermEval469 B hB hF, reducedTermEval470 B hB hF]
  rw [originalMerge462, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval463 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge463 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge463 (originalVector B) := by
  rw [reducedMerge463Check, Integer.Sparse.eval_mergeBy, reducedMergeEval461 B hB hF, reducedMergeEval462 B hB hF]
  rw [originalMerge463, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval464 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge464 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge464 (originalVector B) := by
  rw [reducedMerge464Check, Integer.Sparse.eval_mergeBy, reducedMergeEval460 B hB hF, reducedMergeEval463 B hB hF]
  rw [originalMerge464, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval465 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge465 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge465 (originalVector B) := by
  rw [reducedMerge465Check, Integer.Sparse.eval_mergeBy, reducedTermEval471 B hB hF, reducedTermEval472 B hB hF]
  rw [originalMerge465, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval466 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge466 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge466 (originalVector B) := by
  rw [reducedMerge466Check, Integer.Sparse.eval_mergeBy, reducedTermEval473 B hB hF, reducedTermEval474 B hB hF]
  rw [originalMerge466, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval467 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge467 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge467 (originalVector B) := by
  rw [reducedMerge467Check, Integer.Sparse.eval_mergeBy, reducedMergeEval465 B hB hF, reducedMergeEval466 B hB hF]
  rw [originalMerge467, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval468 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge468 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge468 (originalVector B) := by
  rw [reducedMerge468Check, Integer.Sparse.eval_mergeBy, reducedTermEval475 B hB hF, reducedTermEval476 B hB hF]
  rw [originalMerge468, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval469 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge469 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge469 (originalVector B) := by
  rw [reducedMerge469Check, Integer.Sparse.eval_mergeBy, reducedTermEval477 B hB hF, reducedTermEval478 B hB hF]
  rw [originalMerge469, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval470 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge470 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge470 (originalVector B) := by
  rw [reducedMerge470Check, Integer.Sparse.eval_mergeBy, reducedMergeEval468 B hB hF, reducedMergeEval469 B hB hF]
  rw [originalMerge470, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval471 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge471 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge471 (originalVector B) := by
  rw [reducedMerge471Check, Integer.Sparse.eval_mergeBy, reducedMergeEval467 B hB hF, reducedMergeEval470 B hB hF]
  rw [originalMerge471, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval472 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge472 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge472 (originalVector B) := by
  rw [reducedMerge472Check, Integer.Sparse.eval_mergeBy, reducedMergeEval464 B hB hF, reducedMergeEval471 B hB hF]
  rw [originalMerge472, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval473 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge473 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge473 (originalVector B) := by
  rw [reducedMerge473Check, Integer.Sparse.eval_mergeBy, reducedMergeEval458 B hB hF, reducedMergeEval472 B hB hF]
  rw [originalMerge473, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval474_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge474 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge474 (originalVector B) := by
  rw [reducedMerge474Check, Integer.Sparse.eval_mergeBy, reducedMergeEval444 B hB hF, reducedMergeEval473 B hB hF]
  rw [originalMerge474, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.reducedMergeEval474_e_oai
