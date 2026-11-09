-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:22:14.923015+00:00
-- url     : https://prove2.me/submissions/82079e59-8519-421c-bee8-f9b5f5d9ed7e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E105
import Definitions.Def_OAIQ106E106
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170

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

theorem g_neg {H : CMatrix} (hH : IsHadamard H) (a : Charge) :
    g H (-a) = conj (g H a) := by
  simp only [g, character_neg _ (fun i => hH.1 i _) a, map_mul, map_sum,
    map_inv₀, map_ofNat]

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

theorem IsHadamard.column_orthogonal {H : CMatrix} (hH : IsHadamard H)
    (i j : Coord) :
    ∑ k, conj (H k i) * H k j = if i = j then 6 else 0 := by
  have h := congrArg (fun M : CMatrix => M i j) hH.2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h

theorem character_single (x : Coord → ℂ) (i : Coord) (n : ℤ) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  simp [character, Pi.single_apply]

theorem character_difference (x : Coord → ℂ) (hx : ∀ k, Complex.normSq (x k) = 1)
    (i j : Coord) : character x (difference i j) = x i * conj (x j) := by
  rw [difference, sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)),
    character_neg x hx, character_single, character_single]
  simp

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_Equivalence
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem IsHadamard.permutations {H : CMatrix} (hH : IsHadamard H)
    (r c : Equiv.Perm Coord) : IsHadamard (fun i j => H (r i) (c j)) := by
  refine ⟨fun i j => hH.1 _ _, ?_⟩
  ext i j
  change (∑ k, conj (H (r k) (c i)) * H (r k) (c j)) =
    (6 : ℂ) * (if i = j then 1 else 0)
  rw [Equiv.sum_comp r (fun k => conj (H k (c i)) * H k (c j)), hH.column_orthogonal]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> norm_num

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

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

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

theorem sum_injective_extension {p : ℕ} (f : (Fin p ↪ B) → B → V) :
    (∑ e : Fin (p + 1) ↪ B, f (dropFirst e) (e 0)) =
      ∑ e : Fin p ↪ B, ∑ b : {b // b ∉ Set.range e}, f e b := by
  classical
  have h := (Equiv.embeddingFinSucc p B).sum_comp
    (fun x : Σ e : Fin p ↪ B, {b // b ∉ Set.range e} => f x.1 x.2)
  simpa [dropFirst, Fintype.sum_sigma] using h

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

end MUB6.Sampling

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_EmbeddedCharge
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
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

theorem embedCharge_neg {p : ℕ} (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    embedCharge ρ (-a) = -embedCharge ρ a := by
  funext i
  by_cases hi : i ∈ Set.range ρ
  · obtain ⟨j, rfl⟩ := hi
    simp
  · simp [Pi.neg_apply, embedCharge_outside ρ _ i hi]

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

theorem rowFourier_neg {p : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (ρ : Fin p ↪ Coord) (a : Fin p → ℤ) :
    rowFourier H ρ (-a) = conj (rowFourier H ρ a) := by
  rw [rowFourier_eq_g, embedCharge_neg, g_neg hH, rowFourier_eq_g]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedMoment_neg {p n l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B (-A) label = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  have h : mixedIntegrand B (-A) label r ρ τ = conj (mixedIntegrand B A label r ρ τ) := by
    unfold mixedIntegrand
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_neg (relativeMatrix_isHadamard B hB r _) ρ _
  rw [h, Complex.conj_re]

theorem mixedMoment_factor_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B (fun i j => A i (σ j)) (label ∘ σ) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  exact congrArg Complex.re (Equiv.prod_comp σ
    (fun j => rowFourier (relativeMatrix B r (τ (label j))) ρ (fun i => A i j)))

theorem rowFourier_row_permutation {p : ℕ} (H : CMatrix) (a : Fin p → ℤ)
    (σ : Equiv.Perm (Fin p)) (ρ : Fin p ↪ Coord) :
    rowFourier H ρ (a ∘ σ) =
      rowFourier H (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) a := by
  unfold rowFourier
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Equiv.embeddingCongr_apply, Function.Embedding.congr_apply,
    Function.comp_apply, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.refl_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => H (ρ (σ.symm i)) k ^ a i)

theorem mixedMoment_row_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin p)) :
    mixedMoment B (fun i j => A (σ i) j) label = mixedMoment B A label := by
  apply average_congr
  intro r
  have h (ρ : Fin p ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B (fun i j => A (σ i) j) label r ρ τ =
        mixedIntegrand B A label r (Equiv.embeddingCongr σ (Equiv.refl Coord) ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_row_permutation _ (fun i => A i j) σ ρ
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ (Equiv.refl Coord))
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B A label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedAlpha
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6

theorem rowFourier_alpha_zero {H : CMatrix} (hH : FourierZero H)
    (ρ : Coord ↪ Coord) (σ : Equiv.Perm Coord) :
    rowFourier H ρ (permuteCharge σ alpha) = 0 := by
  rw [permuteCharge, rowFourier_row_permutation]
  let e : Coord ↪ Coord := Equiv.embeddingCongr σ (Equiv.refl Coord) ρ
  let π : Equiv.Perm Coord := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  exact hH π

theorem mixedMoment_alpha {n l : ℕ} (B : Fin 7 → Basis) (hB : AllTransitionsFourierZero B)
    (A : Matrix Coord (Fin n) ℤ) (label : Fin n → Fin l) (j : Fin n)
    (σ : Equiv.Perm Coord) (hA : (fun i => A i j) = permuteCharge σ alpha) :
    mixedMoment B A label = 0 := by
  have h (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [hA]
    exact rowFourier_alpha_zero (hB r _) ρ σ
  simp [mixedMoment, h]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem rowFourier_zero_first {p : ℕ} (H : CMatrix) (a : Fin (p + 1) → ℤ)
    (ha : a 0 = 0) (ρ : Fin (p + 1) ↪ Coord) :
    rowFourier H ρ a = rowFourier H (Sampling.dropFirst ρ) (fun i => a i.succ) := by
  simp only [rowFourier, Fin.prod_univ_succ, ha, zpow_zero, one_mul]
  rfl

theorem mixedMoment_zero_first_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (hA : ∀ j, A 0 j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i.succ j) label := by
  apply average_congr
  intro r
  have h (ρ : Fin (p + 1) ↪ Coord) (τ : Fin l ↪ Coord) :
      mixedIntegrand B A label r ρ τ =
        mixedIntegrand B (fun i j => A i.succ j) label r (Sampling.dropFirst ρ) τ := by
    apply Finset.prod_congr rfl
    intro j _
    exact rowFourier_zero_first _ (fun i => A i j) (hA j) ρ
  simp_rw [h]
  exact Sampling.average_dropFirst hp
    (fun ρ : Fin p ↪ Coord => average (fun τ : Fin l ↪ Coord =>
      (mixedIntegrand B (fun i j => A i.succ j) label r ρ τ).re))

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_Orthogonality
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

/-- The finite orthogonality contraction underlying equation (same-matrix). -/
theorem weighted_contraction {H : CMatrix} (hH : IsHadamard H)
    (u v : Coord → ℂ) (i : Coord) :
    (∑ j, (∑ k, u k * H i k * conj (H j k)) *
      (∑ l, v l * conj (H i l) * H j l)) =
      6 * ∑ k, u k * v k := by
  have hexpand :
      (∑ j, (∑ k, u k * H i k * conj (H j k)) *
        (∑ l, v l * conj (H i l) * H j l)) =
      ∑ l, ∑ k, (u k * v l * H i k * conj (H i l)) *
        (∑ j, conj (H j k) * H j l) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonal]
  have hunit (k : Coord) : H i k * conj (H i k) = 1 := by
    rw [Complex.mul_conj, hH.1]
    norm_num
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    u k * v k * H i k * conj (H i k) * 6 =
      6 * (u k * v k) * (H i k * conj (H i k)) := by ring
    _ = _ := by rw [hunit, mul_one]

theorem g_add_difference {H : CMatrix} (hH : IsHadamard H)
    (a : Charge) (i j : Coord) :
    g H (a + difference i j) = (6 : ℂ)⁻¹ *
      ∑ k, character (fun r => H r k) a * H i k * conj (H j k) := by
  simp only [g]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [character_add _ (fun r => unit_ne_zero (hH.1 r k)),
    character_difference _ (fun r => hH.1 r k)]
  ring

/-- Source Lemma (basic), equation (same-matrix), for arbitrary integral charges. -/
theorem same_matrix_identity {H : CMatrix} (hH : IsHadamard H)
    (a b : Charge) (i : Coord) :
    ∑ j, g H (a + difference i j) * g H (b + difference j i) = g H (a + b) := by
  simp_rw [g_add_difference hH]
  have hexpand :
      (∑ j, ((6 : ℂ)⁻¹ * ∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
        ((6 : ℂ)⁻¹ * ∑ l, character (fun r => H r l) b * H j l * conj (H i l))) =
      (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
        (∑ j, (∑ k, character (fun r => H r k) a * H i k * conj (H j k)) *
          (∑ l, character (fun r => H r l) b * conj (H i l) * H j l)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have he : (∑ l, character (fun r => H r l) b * H j l * conj (H i l)) =
        ∑ l, character (fun r => H r l) b * conj (H i l) * H j l := by
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hexpand, weighted_contraction hH]
  unfold g
  have hs : (∑ k, character (fun r => H r k) a * character (fun r => H r k) b) =
      ∑ k, character (fun r => H r k) (a + b) := by
    apply Finset.sum_congr rfl
    intro k _
    exact (character_add _ (fun r => unit_ne_zero (hH.1 r k)) a b).symm
  rw [hs]
  ring

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem sampledMatrix_isHadamard (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s : Coord) : IsHadamard (sampledMatrix B r ρ s) := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  exact (relativeMatrix_isHadamard B hB r s).permutations e (Equiv.refl Coord)

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem mixedIntegrand_two {l : ℕ} (B : Fin 7 → Basis) (a b : Charge)
    (s t : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (doubleCharges a b) ![s, t] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b := by
  simp [mixedIntegrand, doubleCharges, Fin.prod_univ_succ, rowFourier, g, character, sampledMatrix]

theorem mixedMoment_same {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  rw [same_matrix_identity (sampledMatrix_isHadamard B hB r ρ _) a b i]

theorem mixedMoment_same_reversed {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s u : Fin l) (i : Coord) :
    (∑ j, mixedMoment B (tripleCharges (a + difference j i) (b + difference i j) c) ![s, s, u]) =
      mixedMoment B (doubleCharges (a + b) c) ![s, u] := by
  simp only [mixedMoment, ← average_sum]
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  simp only [mixedIntegrand_three, mixedIntegrand_two, ← Complex.re_sum, ← Finset.sum_mul]
  have h := same_matrix_identity (sampledMatrix_isHadamard B hB r ρ (τ s)) b a i
  simpa only [mul_comm, add_comm] using congrArg
    (fun z => (z * g (sampledMatrix B r ρ (τ u)) c).re) h

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Rules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Sound rules for mixed certificate normalization

Generated witnesses may only permute rows or factors, negate all charges,
remove zero rows or factors, and injectively rename labels. The equalities
here justify those operations for the actual finite mixed moments.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem permute {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin p)) (σ : Equiv.Perm (Fin n)) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i) (σ j)) (label ∘ σ) := by
  rw [mixedMoment_factor_permutation B (fun i j => A (ρ i) j) label σ,
    mixedMoment_row_permutation]

theorem delete_zero_row {p n l : ℕ} (hp : p < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin (p + 1)) (Fin n) ℤ) (label : Fin n → Fin l)
    (ρ : Equiv.Perm (Fin (p + 1))) (hz : ∀ j, A (ρ 0) j = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A (ρ i.succ) j) label := by
  rw [← mixedMoment_row_permutation B A label ρ]
  exact mixedMoment_zero_first_row hp B _ label hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13064 raw13064Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13064 raw13064Labels = mixedMoment B raw13064step0 raw13064step0Labels := by
      have hz : ∀ j, raw13064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13064step0 = (fun i j => raw13064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13064step0 raw13064; decide +kernel
      have hl : raw13064step0Labels = raw13064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13064 raw13064Labels permutation265 hz
    mixedMoment B raw13064step0 raw13064step0Labels = mixedMoment B raw13064step1 raw13064step1Labels := by
      have ha : raw13064step1 = (fun i j => raw13064step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13064step1 raw13064step0; decide +kernel
      have hl : raw13064step1Labels = raw13064step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13064step0 raw13064step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13068 raw13068Labels = mixedMoment B node2976 node2976Labels := by
  calc
    _ = mixedMoment B node2976 node2976Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14556 raw14556Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14556 raw14556Labels = mixedMoment B raw14556step0 raw14556step0Labels := by
      have hz : ∀ j, raw14556 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14556step0 = (fun i j => raw14556 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14556step0 raw14556; decide +kernel
      have hl : raw14556step0Labels = raw14556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14556 raw14556Labels permutation590 hz
    mixedMoment B raw14556step0 raw14556step0Labels = mixedMoment B raw14556step1 raw14556step1Labels := by
      have hz : ∀ j, raw14556step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14556step1 = (fun i j => raw14556step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14556step1 raw14556step0; decide +kernel
      have hl : raw14556step1Labels = raw14556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14556step0 raw14556step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical14566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14566 raw14566Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14566 raw14566Labels = mixedMoment B raw14566step0 raw14566step0Labels := by
      have ha : raw14566step0 = (fun i j => raw14566 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14566step0 raw14566; decide +kernel
      have hl : raw14566step0Labels = raw14566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14566 raw14566Labels permutation176 permutation2
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical14569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14569 raw14569Labels = mixedMoment B node2557 node2557Labels := by
  calc
    _ = mixedMoment B node2557 node2557Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17313 raw17313Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17313 raw17313Labels = mixedMoment B raw17313step0 raw17313step0Labels := by
      have hz : ∀ j, raw17313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17313step0 = (fun i j => raw17313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17313step0 raw17313; decide +kernel
      have hl : raw17313step0Labels = raw17313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17313 raw17313Labels permutation434 hz
    mixedMoment B raw17313step0 raw17313step0Labels = mixedMoment B raw17313step1 raw17313step1Labels := by
      have ha : raw17313step1 = (fun i j => raw17313step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17313step1 raw17313step0; decide +kernel
      have hl : raw17313step1Labels = raw17313step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17313step0 raw17313step0Labels permutation140 permutation0
    mixedMoment B raw17313step1 raw17313step1Labels = mixedMoment B raw17313step2 raw17313step2Labels := by
      have ha : raw17313step2 = -raw17313step1 := by apply Matrix.ext; change ∀ i j, raw17313step2 i j = -(raw17313step1 i j); unfold raw17313step2 raw17313step1; decide +kernel
      have hl : raw17313step2Labels = raw17313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23811 raw23811Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw23811 raw23811Labels = mixedMoment B raw23811step0 raw23811step0Labels := by
      have hz : ∀ j, raw23811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23811step0 = (fun i j => raw23811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23811step0 raw23811; decide +kernel
      have hl : raw23811step0Labels = raw23811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23811 raw23811Labels permutation265 hz
    mixedMoment B raw23811step0 raw23811step0Labels = mixedMoment B raw23811step1 raw23811step1Labels := by
      have ha : raw23811step1 = (fun i j => raw23811step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23811step1 raw23811step0; decide +kernel
      have hl : raw23811step1Labels = raw23811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23811step0 raw23811step0Labels permutation34 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical23817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23817 raw23817Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw23817 raw23817Labels = mixedMoment B raw23817step0 raw23817step0Labels := by
      have hz : ∀ j, raw23817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23817step0 = (fun i j => raw23817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23817step0 raw23817; decide +kernel
      have hl : raw23817step0Labels = raw23817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23817 raw23817Labels permutation265 hz
    mixedMoment B raw23817step0 raw23817step0Labels = mixedMoment B raw23817step1 raw23817step1Labels := by
      have ha : raw23817step1 = (fun i j => raw23817step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23817step1 raw23817step0; decide +kernel
      have hl : raw23817step1Labels = raw23817step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23817step0 raw23817step0Labels permutation140 permutation0
    mixedMoment B raw23817step1 raw23817step1Labels = mixedMoment B raw23817step2 raw23817step2Labels := by
      have ha : raw23817step2 = -raw23817step1 := by apply Matrix.ext; change ∀ i j, raw23817step2 i j = -(raw23817step1 i j); unfold raw23817step2 raw23817step1; decide +kernel
      have hl : raw23817step2Labels = raw23817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical23839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23839 raw23839Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw23839 raw23839Labels = mixedMoment B raw23839step0 raw23839step0Labels := by
      have hz : ∀ j, raw23839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23839step0 = (fun i j => raw23839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23839step0 raw23839; decide +kernel
      have hl : raw23839step0Labels = raw23839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23839 raw23839Labels permutation265 hz
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical23860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23860 raw23860Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw23860 raw23860Labels = mixedMoment B raw23860step0 raw23860step0Labels := by
      have hz : ∀ j, raw23860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23860step0 = (fun i j => raw23860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23860step0 raw23860; decide +kernel
      have hl : raw23860step0Labels = raw23860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23860 raw23860Labels permutation265 hz
    mixedMoment B raw23860step0 raw23860step0Labels = mixedMoment B raw23860step1 raw23860step1Labels := by
      have ha : raw23860step1 = (fun i j => raw23860step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23860step1 raw23860step0; decide +kernel
      have hl : raw23860step1Labels = raw23860step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23860step0 raw23860step0Labels permutation34 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical23866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23866 raw23866Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw23866 raw23866Labels = mixedMoment B raw23866step0 raw23866step0Labels := by
      have hz : ∀ j, raw23866 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23866step0 = (fun i j => raw23866 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23866step0 raw23866; decide +kernel
      have hl : raw23866step0Labels = raw23866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23866 raw23866Labels permutation520 hz
    mixedMoment B raw23866step0 raw23866step0Labels = mixedMoment B raw23866step1 raw23866step1Labels := by
      have hz : ∀ j, raw23866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23866step1 = (fun i j => raw23866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23866step1 raw23866step0; decide +kernel
      have hl : raw23866step1Labels = raw23866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23866step0 raw23866step0Labels permutation56 hz
    mixedMoment B raw23866step1 raw23866step1Labels = mixedMoment B raw23866step2 raw23866step2Labels := by
      have ha : raw23866step2 = (fun i j => raw23866step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23866step2 raw23866step1; decide +kernel
      have hl : raw23866step2Labels = raw23866step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23866step1 raw23866step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical214
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27463 raw27463Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw27463 raw27463Labels = mixedMoment B raw27463step0 raw27463step0Labels := by
      have ha : raw27463step0 = (fun i j => raw27463 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27463step0 raw27463; decide +kernel
      have hl : raw27463step0Labels = raw27463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27463 raw27463Labels permutation176 permutation2
    _ = mixedMoment B node2426 node2426Labels := by rfl

theorem canonical27466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27466 raw27466Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27466 raw27466Labels = mixedMoment B raw27466step0 raw27466step0Labels := by
      have hz : ∀ j, raw27466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27466step0 = (fun i j => raw27466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27466step0 raw27466; decide +kernel
      have hl : raw27466step0Labels = raw27466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27466 raw27466Labels permutation434 hz
    mixedMoment B raw27466step0 raw27466step0Labels = mixedMoment B raw27466step1 raw27466step1Labels := by
      have hz : ∀ j, raw27466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27466step1 = (fun i j => raw27466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27466step1 raw27466step0; decide +kernel
      have hl : raw27466step1Labels = raw27466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27466step0 raw27466step0Labels permutation56 hz
    mixedMoment B raw27466step1 raw27466step1Labels = mixedMoment B raw27466step2 raw27466step2Labels := by
      have ha : raw27466step2 = (fun i j => raw27466step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27466step2 raw27466step1; decide +kernel
      have hl : raw27466step2Labels = raw27466step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27466step1 raw27466step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical27476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27476 raw27476Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw27476 raw27476Labels = mixedMoment B raw27476step0 raw27476step0Labels := by
      have hz : ∀ j, raw27476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27476step0 = (fun i j => raw27476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27476step0 raw27476; decide +kernel
      have hl : raw27476step0Labels = raw27476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27476 raw27476Labels permutation434 hz
    mixedMoment B raw27476step0 raw27476step0Labels = mixedMoment B raw27476step1 raw27476step1Labels := by
      have ha : raw27476step1 = (fun i j => raw27476step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27476step1 raw27476step0; decide +kernel
      have hl : raw27476step1Labels = raw27476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27476step0 raw27476step0Labels permutation34 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical229
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29434 raw29434Labels = mixedMoment B node2427 node2427Labels := by
  calc
    mixedMoment B raw29434 raw29434Labels = mixedMoment B raw29434step0 raw29434step0Labels := by
      have ha : raw29434step0 = (fun i j => raw29434 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29434step0 raw29434; decide +kernel
      have hl : raw29434step0Labels = raw29434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29434 raw29434Labels permutation176 permutation2
    _ = mixedMoment B node2427 node2427Labels := by rfl

theorem canonical29437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29437 raw29437Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29437 raw29437Labels = mixedMoment B raw29437step0 raw29437step0Labels := by
      have hz : ∀ j, raw29437 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29437step0 = (fun i j => raw29437 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29437step0 raw29437; decide +kernel
      have hl : raw29437step0Labels = raw29437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29437 raw29437Labels permutation520 hz
    mixedMoment B raw29437step0 raw29437step0Labels = mixedMoment B raw29437step1 raw29437step1Labels := by
      have hz : ∀ j, raw29437step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29437step1 = (fun i j => raw29437step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29437step1 raw29437step0; decide +kernel
      have hl : raw29437step1Labels = raw29437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29437step0 raw29437step0Labels permutation104 hz
    mixedMoment B raw29437step1 raw29437step1Labels = mixedMoment B raw29437step2 raw29437step2Labels := by
      have hz : ∀ j, raw29437step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw29437step2 = (fun i j => raw29437step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw29437step2 raw29437step1; decide +kernel
      have hl : raw29437step2Labels = raw29437step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29437step1 raw29437step1Labels permutation14 hz
    mixedMoment B raw29437step2 raw29437step2Labels = mixedMoment B raw29437step3 raw29437step3Labels := by
      have ha : raw29437step3 = (fun i j => raw29437step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29437step3 raw29437step2; decide +kernel
      have hl : raw29437step3Labels = raw29437step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29437step2 raw29437step2Labels permutation7 permutation0
    mixedMoment B raw29437step3 raw29437step3Labels = mixedMoment B raw29437step4 raw29437step4Labels := by
      have ha : raw29437step4 = -raw29437step3 := by apply Matrix.ext; change ∀ i j, raw29437step4 i j = -(raw29437step3 i j); unfold raw29437step4 raw29437step3; decide +kernel
      have hl : raw29437step4Labels = raw29437step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical236
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical30305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30305 raw30305Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30305 raw30305Labels = mixedMoment B raw30305step0 raw30305step0Labels := by
      have hz : ∀ j, raw30305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw30305step0 = (fun i j => raw30305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw30305step0 raw30305; decide +kernel
      have hl : raw30305step0Labels = raw30305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30305 raw30305Labels permutation590 hz
    mixedMoment B raw30305step0 raw30305step0Labels = mixedMoment B raw30305step1 raw30305step1Labels := by
      have hz : ∀ j, raw30305step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw30305step1 = (fun i j => raw30305step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw30305step1 raw30305step0; decide +kernel
      have hl : raw30305step1Labels = raw30305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30305step0 raw30305step0Labels permutation104 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical249
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical31928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31928 raw31928Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw31928 raw31928Labels = mixedMoment B raw31928step0 raw31928step0Labels := by
      have hz : ∀ j, raw31928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31928step0 = (fun i j => raw31928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31928step0 raw31928; decide +kernel
      have hl : raw31928step0Labels = raw31928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31928 raw31928Labels permutation346 hz
    mixedMoment B raw31928step0 raw31928step0Labels = mixedMoment B raw31928step1 raw31928step1Labels := by
      have ha : raw31928step1 = (fun i j => raw31928step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31928step1 raw31928step0; decide +kernel
      have hl : raw31928step1Labels = raw31928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31928step0 raw31928step0Labels permutation58 permutation2
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical31929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31929 raw31929Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw31929 raw31929Labels = mixedMoment B raw31929step0 raw31929step0Labels := by
      have hz : ∀ j, raw31929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31929step0 = (fun i j => raw31929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31929step0 raw31929; decide +kernel
      have hl : raw31929step0Labels = raw31929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31929 raw31929Labels permutation346 hz
    mixedMoment B raw31929step0 raw31929step0Labels = mixedMoment B raw31929step1 raw31929step1Labels := by
      have ha : raw31929step1 = (fun i j => raw31929step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31929step1 raw31929step0; decide +kernel
      have hl : raw31929step1Labels = raw31929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31929step0 raw31929step0Labels permutation34 permutation2
    _ = mixedMoment B node3180 node3180Labels := by rfl

theorem canonical31930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31930 raw31930Labels = mixedMoment B node3136 node3136Labels := by
  calc
    mixedMoment B raw31930 raw31930Labels = mixedMoment B raw31930step0 raw31930step0Labels := by
      have ha : raw31930step0 = (fun i j => raw31930 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31930step0 raw31930; decide +kernel
      have hl : raw31930step0Labels = raw31930Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31930 raw31930Labels permutation164 permutation2
    _ = mixedMoment B node3136 node3136Labels := by rfl

theorem canonical31931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31931 raw31931Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw31931 raw31931Labels = mixedMoment B raw31931step0 raw31931step0Labels := by
      have hz : ∀ j, raw31931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31931step0 = (fun i j => raw31931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31931step0 raw31931; decide +kernel
      have hl : raw31931step0Labels = raw31931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31931 raw31931Labels permutation346 hz
    mixedMoment B raw31931step0 raw31931step0Labels = mixedMoment B raw31931step1 raw31931step1Labels := by
      have ha : raw31931step1 = (fun i j => raw31931step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31931step1 raw31931step0; decide +kernel
      have hl : raw31931step1Labels = raw31931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31931step0 raw31931step0Labels permutation34 permutation2
    _ = mixedMoment B node3138 node3138Labels := by rfl

theorem canonical31932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31932 raw31932Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw31932 raw31932Labels = mixedMoment B raw31932step0 raw31932step0Labels := by
      have hz : ∀ j, raw31932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31932step0 = (fun i j => raw31932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31932step0 raw31932; decide +kernel
      have hl : raw31932step0Labels = raw31932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31932 raw31932Labels permutation346 hz
    mixedMoment B raw31932step0 raw31932step0Labels = mixedMoment B raw31932step1 raw31932step1Labels := by
      have ha : raw31932step1 = (fun i j => raw31932step0 (permutation113 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31932step1 raw31932step0; decide +kernel
      have hl : raw31932step1Labels = raw31932step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31932step0 raw31932step0Labels permutation113 permutation4
    _ = mixedMoment B node3033 node3033Labels := by rfl

theorem canonical31933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31933 raw31933Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw31933 raw31933Labels = mixedMoment B raw31933step0 raw31933step0Labels := by
      have hz : ∀ j, raw31933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31933step0 = (fun i j => raw31933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31933step0 raw31933; decide +kernel
      have hl : raw31933step0Labels = raw31933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31933 raw31933Labels permutation346 hz
    mixedMoment B raw31933step0 raw31933step0Labels = mixedMoment B raw31933step1 raw31933step1Labels := by
      have ha : raw31933step1 = (fun i j => raw31933step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31933step1 raw31933step0; decide +kernel
      have hl : raw31933step1Labels = raw31933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31933step0 raw31933step0Labels permutation145 permutation2
    mixedMoment B raw31933step1 raw31933step1Labels = mixedMoment B raw31933step2 raw31933step2Labels := by
      have ha : raw31933step2 = -raw31933step1 := by apply Matrix.ext; change ∀ i j, raw31933step2 i j = -(raw31933step1 i j); unfold raw31933step2 raw31933step1; decide +kernel
      have hl : raw31933step2Labels = raw31933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2443 node2443Labels := by rfl

theorem canonical31934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31934 raw31934Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw31934 raw31934Labels = mixedMoment B raw31934step0 raw31934step0Labels := by
      have hz : ∀ j, raw31934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31934step0 = (fun i j => raw31934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31934step0 raw31934; decide +kernel
      have hl : raw31934step0Labels = raw31934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31934 raw31934Labels permutation346 hz
    mixedMoment B raw31934step0 raw31934step0Labels = mixedMoment B raw31934step1 raw31934step1Labels := by
      have hz : ∀ j, raw31934step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31934step1 = (fun i j => raw31934step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31934step1 raw31934step0; decide +kernel
      have hl : raw31934step1Labels = raw31934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31934step0 raw31934step0Labels permutation32 hz
    mixedMoment B raw31934step1 raw31934step1Labels = mixedMoment B raw31934step2 raw31934step2Labels := by
      have ha : raw31934step2 = (fun i j => raw31934step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw31934step2 raw31934step1; decide +kernel
      have hl : raw31934step2Labels = raw31934step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31934step1 raw31934step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical31935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31935 raw31935Labels = mixedMoment B node942 node942Labels := by
  calc
    mixedMoment B raw31935 raw31935Labels = mixedMoment B raw31935step0 raw31935step0Labels := by
      have ha : raw31935step0 = (fun i j => raw31935 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31935step0 raw31935; decide +kernel
      have hl : raw31935step0Labels = raw31935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31935 raw31935Labels permutation160 permutation2
    _ = mixedMoment B node942 node942Labels := by rfl

theorem canonical31936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31936 raw31936Labels = mixedMoment B node1822 node1822Labels := by
  calc
    mixedMoment B raw31936 raw31936Labels = mixedMoment B raw31936step0 raw31936step0Labels := by
      have ha : raw31936step0 = (fun i j => raw31936 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31936step0 raw31936; decide +kernel
      have hl : raw31936step0Labels = raw31936Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31936 raw31936Labels permutation160 permutation2
    _ = mixedMoment B node1822 node1822Labels := by rfl

theorem canonical31937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31937 raw31937Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw31937 raw31937Labels = mixedMoment B raw31937step0 raw31937step0Labels := by
      have hz : ∀ j, raw31937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31937step0 = (fun i j => raw31937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31937step0 raw31937; decide +kernel
      have hl : raw31937step0Labels = raw31937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31937 raw31937Labels permutation520 hz
    mixedMoment B raw31937step0 raw31937step0Labels = mixedMoment B raw31937step1 raw31937step1Labels := by
      have ha : raw31937step1 = (fun i j => raw31937step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31937step1 raw31937step0; decide +kernel
      have hl : raw31937step1Labels = raw31937step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31937step0 raw31937step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical31938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31938 raw31938Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw31938 raw31938Labels = mixedMoment B raw31938step0 raw31938step0Labels := by
      have ha : raw31938step0 = (fun i j => raw31938 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31938step0 raw31938; decide +kernel
      have hl : raw31938step0Labels = raw31938Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31938 raw31938Labels permutation160 permutation2
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical31939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31939 raw31939Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw31939 raw31939Labels = mixedMoment B raw31939step0 raw31939step0Labels := by
      have ha : raw31939step0 = (fun i j => raw31939 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31939step0 raw31939; decide +kernel
      have hl : raw31939step0Labels = raw31939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31939 raw31939Labels permutation265 permutation2
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical31940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31940 raw31940Labels = mixedMoment B node3172 node3172Labels := by
  calc
    _ = mixedMoment B node3172 node3172Labels := by rfl

theorem canonical31941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31941 raw31941Labels = mixedMoment B node3137 node3137Labels := by
  calc
    _ = mixedMoment B node3137 node3137Labels := by rfl

theorem canonical31942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31942 raw31942Labels = mixedMoment B node3135 node3135Labels := by
  calc
    mixedMoment B raw31942 raw31942Labels = mixedMoment B raw31942step0 raw31942step0Labels := by
      have ha : raw31942step0 = (fun i j => raw31942 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31942step0 raw31942; decide +kernel
      have hl : raw31942step0Labels = raw31942Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31942 raw31942Labels permutation154 permutation2
    _ = mixedMoment B node3135 node3135Labels := by rfl

theorem canonical31943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31943 raw31943Labels = mixedMoment B node3135 node3135Labels := by
  calc
    _ = mixedMoment B node3135 node3135Labels := by rfl

theorem canonical31944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31944 raw31944Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw31944 raw31944Labels = mixedMoment B raw31944step0 raw31944step0Labels := by
      have ha : raw31944step0 = (fun i j => raw31944 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31944step0 raw31944; decide +kernel
      have hl : raw31944step0Labels = raw31944Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31944 raw31944Labels permutation664 permutation2
    mixedMoment B raw31944step0 raw31944step0Labels = mixedMoment B raw31944step1 raw31944step1Labels := by
      have ha : raw31944step1 = -raw31944step0 := by apply Matrix.ext; change ∀ i j, raw31944step1 i j = -(raw31944step0 i j); unfold raw31944step1 raw31944step0; decide +kernel
      have hl : raw31944step1Labels = raw31944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2890 node2890Labels := by rfl

theorem canonical31945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31945 raw31945Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw31945 raw31945Labels = mixedMoment B raw31945step0 raw31945step0Labels := by
      have hz : ∀ j, raw31945 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw31945step0 = (fun i j => raw31945 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw31945step0 raw31945; decide +kernel
      have hl : raw31945step0Labels = raw31945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31945 raw31945Labels permutation152 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical31946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31946 raw31946Labels = mixedMoment B node944 node944Labels := by
  calc
    mixedMoment B raw31946 raw31946Labels = mixedMoment B raw31946step0 raw31946step0Labels := by
      have ha : raw31946step0 = (fun i j => raw31946 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31946step0 raw31946; decide +kernel
      have hl : raw31946step0Labels = raw31946Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31946 raw31946Labels permutation158 permutation2
    _ = mixedMoment B node944 node944Labels := by rfl

theorem canonical31947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31947 raw31947Labels = mixedMoment B node1824 node1824Labels := by
  calc
    mixedMoment B raw31947 raw31947Labels = mixedMoment B raw31947step0 raw31947step0Labels := by
      have ha : raw31947step0 = (fun i j => raw31947 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31947step0 raw31947; decide +kernel
      have hl : raw31947step0Labels = raw31947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31947 raw31947Labels permutation158 permutation2
    _ = mixedMoment B node1824 node1824Labels := by rfl

theorem canonical31948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31948 raw31948Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw31948 raw31948Labels = mixedMoment B raw31948step0 raw31948step0Labels := by
      have ha : raw31948step0 = (fun i j => raw31948 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31948step0 raw31948; decide +kernel
      have hl : raw31948step0Labels = raw31948Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31948 raw31948Labels permutation166 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

theorem canonical31949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31949 raw31949Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw31949 raw31949Labels = mixedMoment B raw31949step0 raw31949step0Labels := by
      have ha : raw31949step0 = (fun i j => raw31949 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31949step0 raw31949; decide +kernel
      have hl : raw31949step0Labels = raw31949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31949 raw31949Labels permutation162 permutation2
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical31950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31950 raw31950Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw31950 raw31950Labels = mixedMoment B raw31950step0 raw31950step0Labels := by
      have ha : raw31950step0 = (fun i j => raw31950 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31950step0 raw31950; decide +kernel
      have hl : raw31950step0Labels = raw31950Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31950 raw31950Labels permutation267 permutation2
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical31951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31951 raw31951Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw31951 raw31951Labels = mixedMoment B raw31951step0 raw31951step0Labels := by
      have ha : raw31951step0 = (fun i j => raw31951 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31951step0 raw31951; decide +kernel
      have hl : raw31951step0Labels = raw31951Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31951 raw31951Labels permutation154 permutation2
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical31952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31952 raw31952Labels = mixedMoment B node3136 node3136Labels := by
  calc
    mixedMoment B raw31952 raw31952Labels = mixedMoment B raw31952step0 raw31952step0Labels := by
      have ha : raw31952step0 = (fun i j => raw31952 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31952step0 raw31952; decide +kernel
      have hl : raw31952step0Labels = raw31952Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31952 raw31952Labels permutation154 permutation2
    _ = mixedMoment B node3136 node3136Labels := by rfl

theorem canonical31953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31953 raw31953Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw31953 raw31953Labels = mixedMoment B raw31953step0 raw31953step0Labels := by
      have ha : raw31953step0 = (fun i j => raw31953 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31953step0 raw31953; decide +kernel
      have hl : raw31953step0Labels = raw31953Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31953 raw31953Labels permutation154 permutation2
    _ = mixedMoment B node3133 node3133Labels := by rfl

theorem canonical31954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31954 raw31954Labels = mixedMoment B node3134 node3134Labels := by
  calc
    _ = mixedMoment B node3134 node3134Labels := by rfl

theorem canonical31955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31955 raw31955Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw31955 raw31955Labels = mixedMoment B raw31955step0 raw31955step0Labels := by
      have ha : raw31955step0 = (fun i j => raw31955 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31955step0 raw31955; decide +kernel
      have hl : raw31955step0Labels = raw31955Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31955 raw31955Labels permutation664 permutation2
    mixedMoment B raw31955step0 raw31955step0Labels = mixedMoment B raw31955step1 raw31955step1Labels := by
      have ha : raw31955step1 = -raw31955step0 := by apply Matrix.ext; change ∀ i j, raw31955step1 i j = -(raw31955step0 i j); unfold raw31955step1 raw31955step0; decide +kernel
      have hl : raw31955step1Labels = raw31955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2423 node2423Labels := by rfl

theorem canonical31956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31956 raw31956Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw31956 raw31956Labels = mixedMoment B raw31956step0 raw31956step0Labels := by
      have hz : ∀ j, raw31956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31956step0 = (fun i j => raw31956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31956step0 raw31956; decide +kernel
      have hl : raw31956step0Labels = raw31956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31956 raw31956Labels permutation520 hz
    mixedMoment B raw31956step0 raw31956step0Labels = mixedMoment B raw31956step1 raw31956step1Labels := by
      have hz : ∀ j, raw31956step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31956step1 = (fun i j => raw31956step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31956step1 raw31956step0; decide +kernel
      have hl : raw31956step1Labels = raw31956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31956step0 raw31956step0Labels permutation32 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical31964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31964 raw31964Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw31964 raw31964Labels = mixedMoment B raw31964step0 raw31964step0Labels := by
      have hz : ∀ j, raw31964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31964step0 = (fun i j => raw31964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31964step0 raw31964; decide +kernel
      have hl : raw31964step0Labels = raw31964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31964 raw31964Labels permutation346 hz
    mixedMoment B raw31964step0 raw31964step0Labels = mixedMoment B raw31964step1 raw31964step1Labels := by
      have ha : raw31964step1 = (fun i j => raw31964step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31964step1 raw31964step0; decide +kernel
      have hl : raw31964step1Labels = raw31964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31964step0 raw31964step0Labels permutation56 permutation2
    _ = mixedMoment B node3394 node3394Labels := by rfl

theorem canonical31965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31965 raw31965Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw31965 raw31965Labels = mixedMoment B raw31965step0 raw31965step0Labels := by
      have hz : ∀ j, raw31965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31965step0 = (fun i j => raw31965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31965step0 raw31965; decide +kernel
      have hl : raw31965step0Labels = raw31965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31965 raw31965Labels permutation346 hz
    _ = mixedMoment B node3158 node3158Labels := by rfl

theorem canonical31966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31966 raw31966Labels = mixedMoment B node3128 node3128Labels := by
  calc
    _ = mixedMoment B node3128 node3128Labels := by rfl

theorem canonical31967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31967 raw31967Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw31967 raw31967Labels = mixedMoment B raw31967step0 raw31967step0Labels := by
      have hz : ∀ j, raw31967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31967step0 = (fun i j => raw31967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31967step0 raw31967; decide +kernel
      have hl : raw31967step0Labels = raw31967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31967 raw31967Labels permutation346 hz
    mixedMoment B raw31967step0 raw31967step0Labels = mixedMoment B raw31967step1 raw31967step1Labels := by
      have ha : raw31967step1 = (fun i j => raw31967step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31967step1 raw31967step0; decide +kernel
      have hl : raw31967step1Labels = raw31967step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31967step0 raw31967step0Labels permutation34 permutation2
    _ = mixedMoment B node3132 node3132Labels := by rfl

theorem canonical31968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31968 raw31968Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw31968 raw31968Labels = mixedMoment B raw31968step0 raw31968step0Labels := by
      have hz : ∀ j, raw31968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31968step0 = (fun i j => raw31968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31968step0 raw31968; decide +kernel
      have hl : raw31968step0Labels = raw31968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31968 raw31968Labels permutation346 hz
    _ = mixedMoment B node3132 node3132Labels := by rfl

theorem canonical31969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31969 raw31969Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw31969 raw31969Labels = mixedMoment B raw31969step0 raw31969step0Labels := by
      have hz : ∀ j, raw31969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31969step0 = (fun i j => raw31969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31969step0 raw31969; decide +kernel
      have hl : raw31969step0Labels = raw31969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31969 raw31969Labels permutation346 hz
    mixedMoment B raw31969step0 raw31969step0Labels = mixedMoment B raw31969step1 raw31969step1Labels := by
      have ha : raw31969step1 = (fun i j => raw31969step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31969step1 raw31969step0; decide +kernel
      have hl : raw31969step1Labels = raw31969step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31969step0 raw31969step0Labels permutation145 permutation2
    mixedMoment B raw31969step1 raw31969step1Labels = mixedMoment B raw31969step2 raw31969step2Labels := by
      have ha : raw31969step2 = -raw31969step1 := by apply Matrix.ext; change ∀ i j, raw31969step2 i j = -(raw31969step1 i j); unfold raw31969step2 raw31969step1; decide +kernel
      have hl : raw31969step2Labels = raw31969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2899 node2899Labels := by rfl

theorem canonical31970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31970 raw31970Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw31970 raw31970Labels = mixedMoment B raw31970step0 raw31970step0Labels := by
      have hz : ∀ j, raw31970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31970step0 = (fun i j => raw31970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31970step0 raw31970; decide +kernel
      have hl : raw31970step0Labels = raw31970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31970 raw31970Labels permutation346 hz
    mixedMoment B raw31970step0 raw31970step0Labels = mixedMoment B raw31970step1 raw31970step1Labels := by
      have hz : ∀ j, raw31970step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw31970step1 = (fun i j => raw31970step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw31970step1 raw31970step0; decide +kernel
      have hl : raw31970step1Labels = raw31970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31970step0 raw31970step0Labels permutation32 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical31971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31971 raw31971Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw31971 raw31971Labels = mixedMoment B raw31971step0 raw31971step0Labels := by
      have hz : ∀ j, raw31971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31971step0 = (fun i j => raw31971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31971step0 raw31971; decide +kernel
      have hl : raw31971step0Labels = raw31971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31971 raw31971Labels permutation346 hz
    mixedMoment B raw31971step0 raw31971step0Labels = mixedMoment B raw31971step1 raw31971step1Labels := by
      have ha : raw31971step1 = (fun i j => raw31971step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31971step1 raw31971step0; decide +kernel
      have hl : raw31971step1Labels = raw31971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31971step0 raw31971step0Labels permutation58 permutation2
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical31972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31972 raw31972Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw31972 raw31972Labels = mixedMoment B raw31972step0 raw31972step0Labels := by
      have hz : ∀ j, raw31972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31972step0 = (fun i j => raw31972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31972step0 raw31972; decide +kernel
      have hl : raw31972step0Labels = raw31972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31972 raw31972Labels permutation346 hz
    mixedMoment B raw31972step0 raw31972step0Labels = mixedMoment B raw31972step1 raw31972step1Labels := by
      have ha : raw31972step1 = (fun i j => raw31972step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31972step1 raw31972step0; decide +kernel
      have hl : raw31972step1Labels = raw31972step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31972step0 raw31972step0Labels permutation34 permutation2
    _ = mixedMoment B node3156 node3156Labels := by rfl

theorem canonical31973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31973 raw31973Labels = mixedMoment B node3127 node3127Labels := by
  calc
    mixedMoment B raw31973 raw31973Labels = mixedMoment B raw31973step0 raw31973step0Labels := by
      have ha : raw31973step0 = (fun i j => raw31973 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31973step0 raw31973; decide +kernel
      have hl : raw31973step0Labels = raw31973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31973 raw31973Labels permutation154 permutation2
    _ = mixedMoment B node3127 node3127Labels := by rfl

theorem canonical31974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31974 raw31974Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw31974 raw31974Labels = mixedMoment B raw31974step0 raw31974step0Labels := by
      have hz : ∀ j, raw31974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31974step0 = (fun i j => raw31974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31974step0 raw31974; decide +kernel
      have hl : raw31974step0Labels = raw31974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31974 raw31974Labels permutation346 hz
    mixedMoment B raw31974step0 raw31974step0Labels = mixedMoment B raw31974step1 raw31974step1Labels := by
      have ha : raw31974step1 = (fun i j => raw31974step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31974step1 raw31974step0; decide +kernel
      have hl : raw31974step1Labels = raw31974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31974step0 raw31974step0Labels permutation34 permutation2
    _ = mixedMoment B node3129 node3129Labels := by rfl

theorem canonical31975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31975 raw31975Labels = mixedMoment B node3131 node3131Labels := by
  calc
    mixedMoment B raw31975 raw31975Labels = mixedMoment B raw31975step0 raw31975step0Labels := by
      have hz : ∀ j, raw31975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31975step0 = (fun i j => raw31975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31975step0 raw31975; decide +kernel
      have hl : raw31975step0Labels = raw31975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31975 raw31975Labels permutation346 hz
    _ = mixedMoment B node3131 node3131Labels := by rfl

theorem canonical31976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31976 raw31976Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw31976 raw31976Labels = mixedMoment B raw31976step0 raw31976step0Labels := by
      have hz : ∀ j, raw31976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31976step0 = (fun i j => raw31976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31976step0 raw31976; decide +kernel
      have hl : raw31976step0Labels = raw31976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31976 raw31976Labels permutation346 hz
    mixedMoment B raw31976step0 raw31976step0Labels = mixedMoment B raw31976step1 raw31976step1Labels := by
      have ha : raw31976step1 = (fun i j => raw31976step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31976step1 raw31976step0; decide +kernel
      have hl : raw31976step1Labels = raw31976step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31976step0 raw31976step0Labels permutation145 permutation2
    mixedMoment B raw31976step1 raw31976step1Labels = mixedMoment B raw31976step2 raw31976step2Labels := by
      have ha : raw31976step2 = -raw31976step1 := by apply Matrix.ext; change ∀ i j, raw31976step2 i j = -(raw31976step1 i j); unfold raw31976step2 raw31976step1; decide +kernel
      have hl : raw31976step2Labels = raw31976step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2435 node2435Labels := by rfl

theorem canonical31977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31977 raw31977Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw31977 raw31977Labels = mixedMoment B raw31977step0 raw31977step0Labels := by
      have hz : ∀ j, raw31977 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31977step0 = (fun i j => raw31977 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31977step0 raw31977; decide +kernel
      have hl : raw31977step0Labels = raw31977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31977 raw31977Labels permutation520 hz
    mixedMoment B raw31977step0 raw31977step0Labels = mixedMoment B raw31977step1 raw31977step1Labels := by
      have hz : ∀ j, raw31977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31977step1 = (fun i j => raw31977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31977step1 raw31977step0; decide +kernel
      have hl : raw31977step1Labels = raw31977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31977step0 raw31977step0Labels permutation80 hz
    mixedMoment B raw31977step1 raw31977step1Labels = mixedMoment B raw31977step2 raw31977step2Labels := by
      have hz : ∀ j, raw31977step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw31977step2 = (fun i j => raw31977step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw31977step2 raw31977step1; decide +kernel
      have hl : raw31977step2Labels = raw31977step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31977step1 raw31977step1Labels permutation8 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical31978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31978 raw31978Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw31978 raw31978Labels = mixedMoment B raw31978step0 raw31978step0Labels := by
      have ha : raw31978step0 = (fun i j => raw31978 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31978step0 raw31978; decide +kernel
      have hl : raw31978step0Labels = raw31978Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31978 raw31978Labels permutation158 permutation2
    _ = mixedMoment B node1130 node1130Labels := by rfl

theorem canonical31979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31979 raw31979Labels = mixedMoment B node2333 node2333Labels := by
  calc
    mixedMoment B raw31979 raw31979Labels = mixedMoment B raw31979step0 raw31979step0Labels := by
      have ha : raw31979step0 = (fun i j => raw31979 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31979step0 raw31979; decide +kernel
      have hl : raw31979step0Labels = raw31979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31979 raw31979Labels permutation158 permutation2
    _ = mixedMoment B node2333 node2333Labels := by rfl

theorem canonical31980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31980 raw31980Labels = mixedMoment B node2481 node2481Labels := by
  calc
    _ = mixedMoment B node2481 node2481Labels := by rfl

theorem canonical31981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31981 raw31981Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw31981 raw31981Labels = mixedMoment B raw31981step0 raw31981step0Labels := by
      have hz : ∀ j, raw31981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31981step0 = (fun i j => raw31981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31981step0 raw31981; decide +kernel
      have hl : raw31981step0Labels = raw31981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31981 raw31981Labels permutation434 hz
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical31982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31982 raw31982Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw31982 raw31982Labels = mixedMoment B raw31982step0 raw31982step0Labels := by
      have ha : raw31982step0 = (fun i j => raw31982 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31982step0 raw31982; decide +kernel
      have hl : raw31982step0Labels = raw31982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31982 raw31982Labels permutation166 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical31983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31983 raw31983Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw31983 raw31983Labels = mixedMoment B raw31983step0 raw31983step0Labels := by
      have ha : raw31983step0 = (fun i j => raw31983 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31983step0 raw31983; decide +kernel
      have hl : raw31983step0Labels = raw31983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31983 raw31983Labels permutation162 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical31984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31984 raw31984Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw31984 raw31984Labels = mixedMoment B raw31984step0 raw31984step0Labels := by
      have ha : raw31984step0 = (fun i j => raw31984 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31984step0 raw31984; decide +kernel
      have hl : raw31984step0Labels = raw31984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31984 raw31984Labels permutation662 permutation2
    mixedMoment B raw31984step0 raw31984step0Labels = mixedMoment B raw31984step1 raw31984step1Labels := by
      have ha : raw31984step1 = -raw31984step0 := by apply Matrix.ext; change ∀ i j, raw31984step1 i j = -(raw31984step0 i j); unfold raw31984step1 raw31984step0; decide +kernel
      have hl : raw31984step1Labels = raw31984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical31985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31985 raw31985Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw31985 raw31985Labels = mixedMoment B raw31985step0 raw31985step0Labels := by
      have ha : raw31985step0 = (fun i j => raw31985 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31985step0 raw31985; decide +kernel
      have hl : raw31985step0Labels = raw31985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31985 raw31985Labels permutation154 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical31986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31986 raw31986Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw31986 raw31986Labels = mixedMoment B raw31986step0 raw31986step0Labels := by
      have ha : raw31986step0 = (fun i j => raw31986 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31986step0 raw31986; decide +kernel
      have hl : raw31986step0Labels = raw31986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31986 raw31986Labels permutation178 permutation2
    _ = mixedMoment B node2900 node2900Labels := by rfl

theorem canonical31987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31987 raw31987Labels = mixedMoment B node2902 node2902Labels := by
  calc
    mixedMoment B raw31987 raw31987Labels = mixedMoment B raw31987step0 raw31987step0Labels := by
      have ha : raw31987step0 = (fun i j => raw31987 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31987step0 raw31987; decide +kernel
      have hl : raw31987step0Labels = raw31987Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31987 raw31987Labels permutation176 permutation2
    _ = mixedMoment B node2902 node2902Labels := by rfl

theorem canonical31988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31988 raw31988Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw31988 raw31988Labels = mixedMoment B raw31988step0 raw31988step0Labels := by
      have ha : raw31988step0 = (fun i j => raw31988 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31988step0 raw31988; decide +kernel
      have hl : raw31988step0Labels = raw31988Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31988 raw31988Labels permutation662 permutation2
    mixedMoment B raw31988step0 raw31988step0Labels = mixedMoment B raw31988step1 raw31988step1Labels := by
      have ha : raw31988step1 = -raw31988step0 := by apply Matrix.ext; change ∀ i j, raw31988step1 i j = -(raw31988step0 i j); unfold raw31988step1 raw31988step0; decide +kernel
      have hl : raw31988step1Labels = raw31988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2437 node2437Labels := by rfl

theorem canonical31994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31994 raw31994Labels = mixedMoment B node1127 node1127Labels := by
  calc
    mixedMoment B raw31994 raw31994Labels = mixedMoment B raw31994step0 raw31994step0Labels := by
      have ha : raw31994step0 = (fun i j => raw31994 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31994step0 raw31994; decide +kernel
      have hl : raw31994step0Labels = raw31994Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31994 raw31994Labels permutation160 permutation2
    _ = mixedMoment B node1127 node1127Labels := by rfl

theorem canonical31995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31995 raw31995Labels = mixedMoment B node2331 node2331Labels := by
  calc
    mixedMoment B raw31995 raw31995Labels = mixedMoment B raw31995step0 raw31995step0Labels := by
      have ha : raw31995step0 = (fun i j => raw31995 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31995step0 raw31995; decide +kernel
      have hl : raw31995step0Labels = raw31995Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31995 raw31995Labels permutation160 permutation2
    _ = mixedMoment B node2331 node2331Labels := by rfl

theorem canonical31996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31996 raw31996Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw31996 raw31996Labels = mixedMoment B raw31996step0 raw31996step0Labels := by
      have hz : ∀ j, raw31996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31996step0 = (fun i j => raw31996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31996step0 raw31996; decide +kernel
      have hl : raw31996step0Labels = raw31996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31996 raw31996Labels permutation434 hz
    mixedMoment B raw31996step0 raw31996step0Labels = mixedMoment B raw31996step1 raw31996step1Labels := by
      have ha : raw31996step1 = (fun i j => raw31996step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31996step1 raw31996step0; decide +kernel
      have hl : raw31996step1Labels = raw31996step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31996step0 raw31996step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical31997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31997 raw31997Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw31997 raw31997Labels = mixedMoment B raw31997step0 raw31997step0Labels := by
      have hz : ∀ j, raw31997 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw31997step0 = (fun i j => raw31997 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw31997step0 raw31997; decide +kernel
      have hl : raw31997step0Labels = raw31997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31997 raw31997Labels permutation520 hz
    mixedMoment B raw31997step0 raw31997step0Labels = mixedMoment B raw31997step1 raw31997step1Labels := by
      have ha : raw31997step1 = (fun i j => raw31997step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31997step1 raw31997step0; decide +kernel
      have hl : raw31997step1Labels = raw31997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31997step0 raw31997step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical31998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31998 raw31998Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw31998 raw31998Labels = mixedMoment B raw31998step0 raw31998step0Labels := by
      have ha : raw31998step0 = (fun i j => raw31998 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31998step0 raw31998; decide +kernel
      have hl : raw31998step0Labels = raw31998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31998 raw31998Labels permutation176 permutation2
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical31999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31999 raw31999Labels = mixedMoment B node2849 node2849Labels := by
  calc
    mixedMoment B raw31999 raw31999Labels = mixedMoment B raw31999step0 raw31999step0Labels := by
      have ha : raw31999step0 = (fun i j => raw31999 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31999step0 raw31999; decide +kernel
      have hl : raw31999step0Labels = raw31999Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31999 raw31999Labels permutation178 permutation2
    _ = mixedMoment B node2849 node2849Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical250
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical32000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32000 raw32000Labels = mixedMoment B node2849 node2849Labels := by
  calc
    mixedMoment B raw32000 raw32000Labels = mixedMoment B raw32000step0 raw32000step0Labels := by
      have ha : raw32000step0 = (fun i j => raw32000 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32000step0 raw32000; decide +kernel
      have hl : raw32000step0Labels = raw32000Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32000 raw32000Labels permutation176 permutation2
    _ = mixedMoment B node2849 node2849Labels := by rfl

theorem canonical32001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32001 raw32001Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw32001 raw32001Labels = mixedMoment B raw32001step0 raw32001step0Labels := by
      have ha : raw32001step0 = (fun i j => raw32001 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32001step0 raw32001; decide +kernel
      have hl : raw32001step0Labels = raw32001Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32001 raw32001Labels permutation176 permutation2
    _ = mixedMoment B node2847 node2847Labels := by rfl

theorem canonical32007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32007 raw32007Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw32007 raw32007Labels = mixedMoment B raw32007step0 raw32007step0Labels := by
      have ha : raw32007step0 = (fun i j => raw32007 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32007step0 raw32007; decide +kernel
      have hl : raw32007step0Labels = raw32007Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32007 raw32007Labels permutation662 permutation2
    mixedMoment B raw32007step0 raw32007step0Labels = mixedMoment B raw32007step1 raw32007step1Labels := by
      have ha : raw32007step1 = -raw32007step0 := by apply Matrix.ext; change ∀ i j, raw32007step1 i j = -(raw32007step0 i j); unfold raw32007step1 raw32007step0; decide +kernel
      have hl : raw32007step1Labels = raw32007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical32008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32008 raw32008Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw32008 raw32008Labels = mixedMoment B raw32008step0 raw32008step0Labels := by
      have ha : raw32008step0 = (fun i j => raw32008 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32008step0 raw32008; decide +kernel
      have hl : raw32008step0Labels = raw32008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32008 raw32008Labels permutation154 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical32009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32009 raw32009Labels = mixedMoment B node2846 node2846Labels := by
  calc
    mixedMoment B raw32009 raw32009Labels = mixedMoment B raw32009step0 raw32009step0Labels := by
      have ha : raw32009step0 = (fun i j => raw32009 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32009step0 raw32009; decide +kernel
      have hl : raw32009step0Labels = raw32009Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32009 raw32009Labels permutation178 permutation2
    _ = mixedMoment B node2846 node2846Labels := by rfl

theorem canonical32010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32010 raw32010Labels = mixedMoment B node2848 node2848Labels := by
  calc
    mixedMoment B raw32010 raw32010Labels = mixedMoment B raw32010step0 raw32010step0Labels := by
      have ha : raw32010step0 = (fun i j => raw32010 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32010step0 raw32010; decide +kernel
      have hl : raw32010step0Labels = raw32010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32010 raw32010Labels permutation176 permutation2
    _ = mixedMoment B node2848 node2848Labels := by rfl

theorem canonical32011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32011 raw32011Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw32011 raw32011Labels = mixedMoment B raw32011step0 raw32011step0Labels := by
      have ha : raw32011step0 = (fun i j => raw32011 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32011step0 raw32011; decide +kernel
      have hl : raw32011step0Labels = raw32011Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32011 raw32011Labels permutation662 permutation2
    mixedMoment B raw32011step0 raw32011step0Labels = mixedMoment B raw32011step1 raw32011step1Labels := by
      have ha : raw32011step1 = -raw32011step0 := by apply Matrix.ext; change ∀ i j, raw32011step1 i j = -(raw32011step0 i j); unfold raw32011step1 raw32011step0; decide +kernel
      have hl : raw32011step1Labels = raw32011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2426 node2426Labels := by rfl

theorem canonical32012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32012 raw32012Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw32012 raw32012Labels = mixedMoment B raw32012step0 raw32012step0Labels := by
      have ha : raw32012step0 = (fun i j => raw32012 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32012step0 raw32012; decide +kernel
      have hl : raw32012step0Labels = raw32012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32012 raw32012Labels permutation662 permutation2
    mixedMoment B raw32012step0 raw32012step0Labels = mixedMoment B raw32012step1 raw32012step1Labels := by
      have ha : raw32012step1 = -raw32012step0 := by apply Matrix.ext; change ∀ i j, raw32012step1 i j = -(raw32012step0 i j); unfold raw32012step1 raw32012step0; decide +kernel
      have hl : raw32012step1Labels = raw32012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3493 node3493Labels := by rfl

theorem canonical32013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32013 raw32013Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw32013 raw32013Labels = mixedMoment B raw32013step0 raw32013step0Labels := by
      have hz : ∀ j, raw32013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32013step0 = (fun i j => raw32013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32013step0 raw32013; decide +kernel
      have hl : raw32013step0Labels = raw32013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32013 raw32013Labels permutation265 hz
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical32014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32014 raw32014Labels = mixedMoment B node2552 node2552Labels := by
  calc
    _ = mixedMoment B node2552 node2552Labels := by rfl

theorem canonical32015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32015 raw32015Labels = mixedMoment B node2427 node2427Labels := by
  calc
    mixedMoment B raw32015 raw32015Labels = mixedMoment B raw32015step0 raw32015step0Labels := by
      have ha : raw32015step0 = (fun i j => raw32015 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32015step0 raw32015; decide +kernel
      have hl : raw32015step0Labels = raw32015Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32015 raw32015Labels permutation178 permutation2
    _ = mixedMoment B node2427 node2427Labels := by rfl

theorem canonical32016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32016 raw32016Labels = mixedMoment B node1960 node1960Labels := by
  calc
    mixedMoment B raw32016 raw32016Labels = mixedMoment B raw32016step0 raw32016step0Labels := by
      have ha : raw32016step0 = (fun i j => raw32016 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32016step0 raw32016; decide +kernel
      have hl : raw32016step0Labels = raw32016Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32016 raw32016Labels permutation662 permutation2
    mixedMoment B raw32016step0 raw32016step0Labels = mixedMoment B raw32016step1 raw32016step1Labels := by
      have ha : raw32016step1 = -raw32016step0 := by apply Matrix.ext; change ∀ i j, raw32016step1 i j = -(raw32016step0 i j); unfold raw32016step1 raw32016step0; decide +kernel
      have hl : raw32016step1Labels = raw32016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1960 node1960Labels := by rfl

theorem canonical32017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32017 raw32017Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw32017 raw32017Labels = mixedMoment B raw32017step0 raw32017step0Labels := by
      have ha : raw32017step0 = (fun i j => raw32017 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32017step0 raw32017; decide +kernel
      have hl : raw32017step0Labels = raw32017Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32017 raw32017Labels permutation176 permutation2
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical32018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32018 raw32018Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw32018 raw32018Labels = mixedMoment B raw32018step0 raw32018step0Labels := by
      have hz : ∀ j, raw32018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32018step0 = (fun i j => raw32018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32018step0 raw32018; decide +kernel
      have hl : raw32018step0Labels = raw32018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32018 raw32018Labels permutation265 hz
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical32019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32019 raw32019Labels = mixedMoment B node2554 node2554Labels := by
  calc
    _ = mixedMoment B node2554 node2554Labels := by rfl

theorem canonical32020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32020 raw32020Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw32020 raw32020Labels = mixedMoment B raw32020step0 raw32020step0Labels := by
      have ha : raw32020step0 = (fun i j => raw32020 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32020step0 raw32020; decide +kernel
      have hl : raw32020step0Labels = raw32020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32020 raw32020Labels permutation178 permutation2
    _ = mixedMoment B node2433 node2433Labels := by rfl

theorem canonical32021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32021 raw32021Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw32021 raw32021Labels = mixedMoment B raw32021step0 raw32021step0Labels := by
      have ha : raw32021step0 = (fun i j => raw32021 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32021step0 raw32021; decide +kernel
      have hl : raw32021step0Labels = raw32021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32021 raw32021Labels permutation177 permutation2
    _ = mixedMoment B node2428 node2428Labels := by rfl

theorem canonical32022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32022 raw32022Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw32022 raw32022Labels = mixedMoment B raw32022step0 raw32022step0Labels := by
      have hz : ∀ j, raw32022 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32022step0 = (fun i j => raw32022 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32022step0 raw32022; decide +kernel
      have hl : raw32022step0Labels = raw32022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32022 raw32022Labels permutation265 hz
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical32023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32023 raw32023Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw32023 raw32023Labels = mixedMoment B raw32023step0 raw32023step0Labels := by
      have ha : raw32023step0 = (fun i j => raw32023 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32023step0 raw32023; decide +kernel
      have hl : raw32023step0Labels = raw32023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32023 raw32023Labels permutation179 permutation2
    _ = mixedMoment B node2433 node2433Labels := by rfl

theorem canonical32024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32024 raw32024Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw32024 raw32024Labels = mixedMoment B raw32024step0 raw32024step0Labels := by
      have ha : raw32024step0 = (fun i j => raw32024 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32024step0 raw32024; decide +kernel
      have hl : raw32024step0Labels = raw32024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32024 raw32024Labels permutation177 permutation2
    _ = mixedMoment B node2431 node2431Labels := by rfl

theorem canonical32025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32025 raw32025Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw32025 raw32025Labels = mixedMoment B raw32025step0 raw32025step0Labels := by
      have ha : raw32025step0 = (fun i j => raw32025 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32025step0 raw32025; decide +kernel
      have hl : raw32025step0Labels = raw32025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32025 raw32025Labels permutation176 permutation2
    _ = mixedMoment B node2430 node2430Labels := by rfl

theorem canonical32026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32026 raw32026Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw32026 raw32026Labels = mixedMoment B raw32026step0 raw32026step0Labels := by
      have ha : raw32026step0 = (fun i j => raw32026 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32026step0 raw32026; decide +kernel
      have hl : raw32026step0Labels = raw32026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32026 raw32026Labels permutation166 permutation2
    _ = mixedMoment B node1335 node1335Labels := by rfl

theorem canonical32027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32027 raw32027Labels = mixedMoment B node2826 node2826Labels := by
  calc
    mixedMoment B raw32027 raw32027Labels = mixedMoment B raw32027step0 raw32027step0Labels := by
      have ha : raw32027step0 = (fun i j => raw32027 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32027step0 raw32027; decide +kernel
      have hl : raw32027step0Labels = raw32027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32027 raw32027Labels permutation166 permutation2
    _ = mixedMoment B node2826 node2826Labels := by rfl

theorem canonical32028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32028 raw32028Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw32028 raw32028Labels = mixedMoment B raw32028step0 raw32028step0Labels := by
      have ha : raw32028step0 = (fun i j => raw32028 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32028step0 raw32028; decide +kernel
      have hl : raw32028step0Labels = raw32028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32028 raw32028Labels permutation154 permutation2
    _ = mixedMoment B node2933 node2933Labels := by rfl

theorem canonical32029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32029 raw32029Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw32029 raw32029Labels = mixedMoment B raw32029step0 raw32029step0Labels := by
      have ha : raw32029step0 = (fun i j => raw32029 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32029step0 raw32029; decide +kernel
      have hl : raw32029step0Labels = raw32029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32029 raw32029Labels permutation166 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical32030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32030 raw32030Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw32030 raw32030Labels = mixedMoment B raw32030step0 raw32030step0Labels := by
      have ha : raw32030step0 = (fun i j => raw32030 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32030step0 raw32030; decide +kernel
      have hl : raw32030step0Labels = raw32030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32030 raw32030Labels permutation166 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11086 raw11086Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11086 raw11086Labels = mixedMoment B raw11086step0 raw11086step0Labels := by
      have hz : ∀ j, raw11086 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11086step0 = (fun i j => raw11086 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11086step0 raw11086; decide +kernel
      have hl : raw11086step0Labels = raw11086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086 raw11086Labels permutation590 hz
    mixedMoment B raw11086step0 raw11086step0Labels = mixedMoment B raw11086step1 raw11086step1Labels := by
      have hz : ∀ j, raw11086step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11086step1 = (fun i j => raw11086step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11086step1 raw11086step0; decide +kernel
      have hl : raw11086step1Labels = raw11086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086step0 raw11086step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11092 raw11092Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw11092 raw11092Labels = mixedMoment B raw11092step0 raw11092step0Labels := by
      have hz : ∀ j, raw11092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11092step0 = (fun i j => raw11092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11092step0 raw11092; decide +kernel
      have hl : raw11092step0Labels = raw11092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11092 raw11092Labels permutation434 hz
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical11093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11093 raw11093Labels = mixedMoment B node2089 node2089Labels := by
  calc
    _ = mixedMoment B node2089 node2089Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11298 raw11298Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11298 raw11298Labels = mixedMoment B raw11298step0 raw11298step0Labels := by
      have hz : ∀ j, raw11298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11298step0 = (fun i j => raw11298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11298step0 raw11298; decide +kernel
      have hl : raw11298step0Labels = raw11298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298 raw11298Labels permutation520 hz
    mixedMoment B raw11298step0 raw11298step0Labels = mixedMoment B raw11298step1 raw11298step1Labels := by
      have hz : ∀ j, raw11298step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11298step1 = (fun i j => raw11298step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11298step1 raw11298step0; decide +kernel
      have hl : raw11298step1Labels = raw11298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298step0 raw11298step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11308 raw11308Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw11308 raw11308Labels = mixedMoment B raw11308step0 raw11308step0Labels := by
      have hz : ∀ j, raw11308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11308step0 = (fun i j => raw11308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11308step0 raw11308; decide +kernel
      have hl : raw11308step0Labels = raw11308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11308 raw11308Labels permutation434 hz
    mixedMoment B raw11308step0 raw11308step0Labels = mixedMoment B raw11308step1 raw11308step1Labels := by
      have ha : raw11308step1 = (fun i j => raw11308step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11308step1 raw11308step0; decide +kernel
      have hl : raw11308step1Labels = raw11308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11308step0 raw11308step0Labels permutation34 permutation2
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical11309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11309 raw11309Labels = mixedMoment B node2088 node2088Labels := by
  calc
    _ = mixedMoment B node2088 node2088Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical92
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11868 raw11868Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw11868 raw11868Labels = mixedMoment B raw11868step0 raw11868step0Labels := by
      have hz : ∀ j, raw11868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11868step0 = (fun i j => raw11868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11868step0 raw11868; decide +kernel
      have hl : raw11868step0Labels = raw11868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11868 raw11868Labels permutation520 hz
    mixedMoment B raw11868step0 raw11868step0Labels = mixedMoment B raw11868step1 raw11868step1Labels := by
      have hz : ∀ j, raw11868step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11868step1 = (fun i j => raw11868step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11868step1 raw11868step0; decide +kernel
      have hl : raw11868step1Labels = raw11868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11868step0 raw11868step0Labels permutation104 hz
    mixedMoment B raw11868step1 raw11868step1Labels = mixedMoment B raw11868step2 raw11868step2Labels := by
      have ha : raw11868step2 = (fun i j => raw11868step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11868step2 raw11868step1; decide +kernel
      have hl : raw11868step2Labels = raw11868step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11868step1 raw11868step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical11878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11878 raw11878Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw11878 raw11878Labels = mixedMoment B raw11878step0 raw11878step0Labels := by
      have ha : raw11878step0 = (fun i j => raw11878 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11878step0 raw11878; decide +kernel
      have hl : raw11878step0Labels = raw11878Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11878 raw11878Labels permutation161 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical11881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11881 raw11881Labels = mixedMoment B node2493 node2493Labels := by
  calc
    _ = mixedMoment B node2493 node2493Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem sum_fin_six {R : Type*} [AddCommMonoid R] (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ac_rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_NumericVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6.Certificate.MixedSemantics

theorem integer_eval_numericVector (B : Fin 7 → Basis) (v : Integer.Sparse (Fin 3237)) :
    Integer.Sparse.eval v (numericVector B) =
      Integer.Sparse.eval (Integer.Sparse.reindex keyMap v) (mixedVector B) := by
  rw [Integer.Sparse.eval_reindex]
  rfl

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node942 node942Labels = Sparse.eval nodeValue942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 942) = mixedMoment B node942 node942Labels := rfl
  simpa [nodeValue942, Sparse.eval] using hc.symm

theorem sound944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node944 node944Labels = Sparse.eval nodeValue944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 944) = mixedMoment B node944 node944Labels := rfl
  simpa [nodeValue944, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1127 node1127Labels = Sparse.eval nodeValue1127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1127) = mixedMoment B node1127 node1127Labels := rfl
  simpa [nodeValue1127, Sparse.eval] using hc.symm

theorem sound1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1130 node1130Labels = Sparse.eval nodeValue1130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1130) = mixedMoment B node1130 node1130Labels := rfl
  simpa [nodeValue1130, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1335 node1335Labels = Sparse.eval nodeValue1335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1335) = mixedMoment B node1335 node1335Labels := rfl
  simpa [nodeValue1335, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1822 node1822Labels = Sparse.eval nodeValue1822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1822) = mixedMoment B node1822 node1822Labels := rfl
  simpa [nodeValue1822, Sparse.eval] using hc.symm

theorem sound1824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1824 node1824Labels = Sparse.eval nodeValue1824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1824) = mixedMoment B node1824 node1824Labels := rfl
  simpa [nodeValue1824, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1960 node1960Labels = Sparse.eval nodeValue1960 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1960) = mixedMoment B node1960 node1960Labels := rfl
  simpa [nodeValue1960, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2088 node2088Labels = Sparse.eval nodeValue2088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2088) = mixedMoment B node2088 node2088Labels := rfl
  simpa [nodeValue2088, Sparse.eval] using hc.symm

theorem sound2089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2089 node2089Labels = Sparse.eval nodeValue2089 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2089) = mixedMoment B node2089 node2089Labels := rfl
  simpa [nodeValue2089, Sparse.eval] using hc.symm

theorem sound2105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2105 node2105Labels = Sparse.eval nodeValue2105 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2105) = mixedMoment B node2105 node2105Labels := rfl
  simpa [nodeValue2105, Sparse.eval] using hc.symm

theorem sound2107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2107 node2107Labels = Sparse.eval nodeValue2107 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2107) = mixedMoment B node2107 node2107Labels := rfl
  simpa [nodeValue2107, Sparse.eval] using hc.symm

theorem sound2110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2110 node2110Labels = Sparse.eval nodeValue2110 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2110) = mixedMoment B node2110 node2110Labels := rfl
  simpa [nodeValue2110, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2331 node2331Labels = 0 := by
  exact mixedMoment_alpha B hF node2331 node2331Labels 1 permutation160
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound36
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2331 node2331Labels = Sparse.eval nodeValue2331 (mixedVector B) := by
  simpa only [nodeValue2331, Sparse.eval_nil] using zero2331 B _hB _hF

theorem sound2333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2333 node2333Labels = Sparse.eval nodeValue2333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2333) = mixedMoment B node2333 node2333Labels := rfl
  simpa [nodeValue2333, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2423 node2423Labels = Sparse.eval nodeValue2423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2423) = mixedMoment B node2423 node2423Labels := rfl
  simpa [nodeValue2423, Sparse.eval] using hc.symm

theorem sound2426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2426 node2426Labels = Sparse.eval nodeValue2426 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2426) = mixedMoment B node2426 node2426Labels := rfl
  simpa [nodeValue2426, Sparse.eval] using hc.symm

theorem sound2427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2427 node2427Labels = Sparse.eval nodeValue2427 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2427) = mixedMoment B node2427 node2427Labels := rfl
  simpa [nodeValue2427, Sparse.eval] using hc.symm

theorem sound2428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2428 node2428Labels = Sparse.eval nodeValue2428 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2428) = mixedMoment B node2428 node2428Labels := rfl
  simpa [nodeValue2428, Sparse.eval] using hc.symm

theorem sound2430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2430 node2430Labels = Sparse.eval nodeValue2430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2430) = mixedMoment B node2430 node2430Labels := rfl
  simpa [nodeValue2430, Sparse.eval] using hc.symm

theorem sound2431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2431 node2431Labels = Sparse.eval nodeValue2431 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2431) = mixedMoment B node2431 node2431Labels := rfl
  simpa [nodeValue2431, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2433 node2433Labels = Sparse.eval nodeValue2433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2433) = mixedMoment B node2433 node2433Labels := rfl
  simpa [nodeValue2433, Sparse.eval] using hc.symm

theorem sound2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2435 node2435Labels = Sparse.eval nodeValue2435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2435) = mixedMoment B node2435 node2435Labels := rfl
  simpa [nodeValue2435, Sparse.eval] using hc.symm

theorem sound2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2437 node2437Labels = Sparse.eval nodeValue2437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2437) = mixedMoment B node2437 node2437Labels := rfl
  simpa [nodeValue2437, Sparse.eval] using hc.symm

theorem sound2443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2443 node2443Labels = Sparse.eval nodeValue2443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2443) = mixedMoment B node2443 node2443Labels := rfl
  simpa [nodeValue2443, Sparse.eval] using hc.symm

theorem sound2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2481 node2481Labels = Sparse.eval nodeValue2481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2481) = mixedMoment B node2481 node2481Labels := rfl
  simpa [nodeValue2481, Sparse.eval] using hc.symm

theorem sound2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2493 node2493Labels = Sparse.eval nodeValue2493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2493) = mixedMoment B node2493 node2493Labels := rfl
  simpa [nodeValue2493, Sparse.eval] using hc.symm

theorem sound2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2494 node2494Labels = Sparse.eval nodeValue2494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2494) = mixedMoment B node2494 node2494Labels := rfl
  simpa [nodeValue2494, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = 0 := by
  exact mixedMoment_alpha B hF node2552 node2552Labels 1 permutation161
    (by decide +kernel)

theorem zero2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = 0 := by
  exact mixedMoment_alpha B hF node2554 node2554Labels 1 permutation160
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2508 node2508Labels = Sparse.eval nodeValue2508 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2508) = mixedMoment B node2508 node2508Labels := rfl
  simpa [nodeValue2508, Sparse.eval] using hc.symm

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

theorem sound2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2552 node2552Labels = Sparse.eval nodeValue2552 (mixedVector B) := by
  simpa only [nodeValue2552, Sparse.eval_nil] using zero2552 B _hB _hF

theorem sound2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = Sparse.eval nodeValue2554 (mixedVector B) := by
  simpa only [nodeValue2554, Sparse.eval_nil] using zero2554 B _hB _hF

theorem sound2557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2557 node2557Labels = Sparse.eval nodeValue2557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2557) = mixedMoment B node2557 node2557Labels := rfl
  simpa [nodeValue2557, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2826 node2826Labels = Sparse.eval nodeValue2826 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2826) = mixedMoment B node2826 node2826Labels := rfl
  simpa [nodeValue2826, Sparse.eval] using hc.symm

theorem sound2846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2846 node2846Labels = Sparse.eval nodeValue2846 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2846) = mixedMoment B node2846 node2846Labels := rfl
  simpa [nodeValue2846, Sparse.eval] using hc.symm

theorem sound2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2847 node2847Labels = Sparse.eval nodeValue2847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2847) = mixedMoment B node2847 node2847Labels := rfl
  simpa [nodeValue2847, Sparse.eval] using hc.symm

theorem sound2848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2848 node2848Labels = Sparse.eval nodeValue2848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2848) = mixedMoment B node2848 node2848Labels := rfl
  simpa [nodeValue2848, Sparse.eval] using hc.symm

theorem sound2849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2849 node2849Labels = Sparse.eval nodeValue2849 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2849) = mixedMoment B node2849 node2849Labels := rfl
  simpa [nodeValue2849, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2881 node2881Labels = Sparse.eval nodeValue2881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2881) = mixedMoment B node2881 node2881Labels := rfl
  simpa [nodeValue2881, Sparse.eval] using hc.symm

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

theorem sound2890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2890 node2890Labels = Sparse.eval nodeValue2890 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2890) = mixedMoment B node2890 node2890Labels := rfl
  simpa [nodeValue2890, Sparse.eval] using hc.symm

theorem sound2899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2899 node2899Labels = Sparse.eval nodeValue2899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2899) = mixedMoment B node2899 node2899Labels := rfl
  simpa [nodeValue2899, Sparse.eval] using hc.symm

theorem sound2900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2900 node2900Labels = Sparse.eval nodeValue2900 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2900) = mixedMoment B node2900 node2900Labels := rfl
  simpa [nodeValue2900, Sparse.eval] using hc.symm

theorem sound2902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2902 node2902Labels = Sparse.eval nodeValue2902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2902) = mixedMoment B node2902 node2902Labels := rfl
  simpa [nodeValue2902, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2933 node2933Labels = Sparse.eval nodeValue2933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2933) = mixedMoment B node2933 node2933Labels := rfl
  simpa [nodeValue2933, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2951 node2951Labels = Sparse.eval nodeValue2951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2951) = mixedMoment B node2951 node2951Labels := rfl
  simpa [nodeValue2951, Sparse.eval] using hc.symm

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

theorem sound2976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2976 node2976Labels = Sparse.eval nodeValue2976 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2976) = mixedMoment B node2976 node2976Labels := rfl
  simpa [nodeValue2976, Sparse.eval] using hc.symm

theorem sound2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2984 node2984Labels = Sparse.eval nodeValue2984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2984) = mixedMoment B node2984 node2984Labels := rfl
  simpa [nodeValue2984, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3033 node3033Labels = Sparse.eval nodeValue3033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3033) = mixedMoment B node3033 node3033Labels := rfl
  simpa [nodeValue3033, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3127 node3127Labels = Sparse.eval nodeValue3127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3127) = mixedMoment B node3127 node3127Labels := rfl
  simpa [nodeValue3127, Sparse.eval] using hc.symm

theorem sound3128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3128 node3128Labels = Sparse.eval nodeValue3128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3128) = mixedMoment B node3128 node3128Labels := rfl
  simpa [nodeValue3128, Sparse.eval] using hc.symm

theorem sound3129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3129 node3129Labels = Sparse.eval nodeValue3129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3129) = mixedMoment B node3129 node3129Labels := rfl
  simpa [nodeValue3129, Sparse.eval] using hc.symm

theorem sound3131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3131 node3131Labels = Sparse.eval nodeValue3131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3131) = mixedMoment B node3131 node3131Labels := rfl
  simpa [nodeValue3131, Sparse.eval] using hc.symm

theorem sound3132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3132 node3132Labels = Sparse.eval nodeValue3132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3132) = mixedMoment B node3132 node3132Labels := rfl
  simpa [nodeValue3132, Sparse.eval] using hc.symm

theorem sound3133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3133 node3133Labels = Sparse.eval nodeValue3133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3133) = mixedMoment B node3133 node3133Labels := rfl
  simpa [nodeValue3133, Sparse.eval] using hc.symm

theorem sound3134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3134 node3134Labels = Sparse.eval nodeValue3134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3134) = mixedMoment B node3134 node3134Labels := rfl
  simpa [nodeValue3134, Sparse.eval] using hc.symm

theorem sound3135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3135 node3135Labels = Sparse.eval nodeValue3135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3135) = mixedMoment B node3135 node3135Labels := rfl
  simpa [nodeValue3135, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3136 node3136Labels = Sparse.eval nodeValue3136 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3136) = mixedMoment B node3136 node3136Labels := rfl
  simpa [nodeValue3136, Sparse.eval] using hc.symm

theorem sound3137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3137 node3137Labels = Sparse.eval nodeValue3137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3137) = mixedMoment B node3137 node3137Labels := rfl
  simpa [nodeValue3137, Sparse.eval] using hc.symm

theorem sound3138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3138 node3138Labels = Sparse.eval nodeValue3138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3138) = mixedMoment B node3138 node3138Labels := rfl
  simpa [nodeValue3138, Sparse.eval] using hc.symm

theorem sound3156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3156 node3156Labels = Sparse.eval nodeValue3156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3156) = mixedMoment B node3156 node3156Labels := rfl
  simpa [nodeValue3156, Sparse.eval] using hc.symm

theorem sound3158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3158 node3158Labels = Sparse.eval nodeValue3158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3158) = mixedMoment B node3158 node3158Labels := rfl
  simpa [nodeValue3158, Sparse.eval] using hc.symm

theorem sound3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3170 node3170Labels = Sparse.eval nodeValue3170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3170) = mixedMoment B node3170 node3170Labels := rfl
  simpa [nodeValue3170, Sparse.eval] using hc.symm

theorem sound3172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3172 node3172Labels = Sparse.eval nodeValue3172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3172) = mixedMoment B node3172 node3172Labels := rfl
  simpa [nodeValue3172, Sparse.eval] using hc.symm

theorem sound3180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3180 node3180Labels = Sparse.eval nodeValue3180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3180) = mixedMoment B node3180 node3180Labels := rfl
  simpa [nodeValue3180, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3391 node3391Labels = Sparse.eval nodeValue3391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3391) = mixedMoment B node3391 node3391Labels := rfl
  simpa [nodeValue3391, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3394 node3394Labels = Sparse.eval nodeValue3394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3394) = mixedMoment B node3394 node3394Labels := rfl
  simpa [nodeValue3394, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3493 node3493Labels = Sparse.eval nodeValue3493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3493) = mixedMoment B node3493 node3493Labels := rfl
  simpa [nodeValue3493, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3719 node3719Labels = Sparse.eval nodeValue3719 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3719) = mixedMoment B node3719 node3719Labels := rfl
  simpa [nodeValue3719, Sparse.eval] using hc.symm

theorem sound3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3721 node3721Labels = Sparse.eval nodeValue3721 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3721) = mixedMoment B node3721 node3721Labels := rfl
  simpa [nodeValue3721, Sparse.eval] using hc.symm

theorem sound3732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3732 node3732Labels = Sparse.eval nodeValue3732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3732) = mixedMoment B node3732 node3732Labels := rfl
  simpa [nodeValue3732, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3782 node3782Labels = Sparse.eval nodeValue3782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3782) = mixedMoment B node3782 node3782Labels := rfl
  simpa [nodeValue3782, Sparse.eval] using hc.symm

theorem sound3787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3787 node3787Labels = Sparse.eval nodeValue3787 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3787) = mixedMoment B node3787 node3787Labels := rfl
  simpa [nodeValue3787, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3945 node3945Labels = Sparse.eval nodeValue3945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3945) = mixedMoment B node3945 node3945Labels := rfl
  simpa [nodeValue3945, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4091 node4091Labels = Sparse.eval nodeValue4091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4091) = mixedMoment B node4091 node4091Labels := rfl
  simpa [nodeValue4091, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources72
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2319 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2319 + difference 0 1) (sourceB2319 + difference 1 0) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3732) := by
    have ha : (tripleCharges (sourceA2319 + difference 0 1) (sourceB2319 + difference 1 0) sourceC2319) = raw31928 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31928; decide +kernel
    rw [ha]
    exact (canonical31928 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2319 + difference 1 1) (sourceB2319 + difference 1 1) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3180) := by
    have ha : (tripleCharges (sourceA2319 + difference 1 1) (sourceB2319 + difference 1 1) sourceC2319) = raw31929 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31929; decide +kernel
    rw [ha]
    exact (canonical31929 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2319 + difference 2 1) (sourceB2319 + difference 1 2) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3136) := by
    have ha : (tripleCharges (sourceA2319 + difference 2 1) (sourceB2319 + difference 1 2) sourceC2319) = raw31930 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31930; decide +kernel
    rw [ha]
    exact (canonical31930 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2319 + difference 3 1) (sourceB2319 + difference 1 3) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3138) := by
    have ha : (tripleCharges (sourceA2319 + difference 3 1) (sourceB2319 + difference 1 3) sourceC2319) = raw31931 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31931; decide +kernel
    rw [ha]
    exact (canonical31931 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2319 + difference 4 1) (sourceB2319 + difference 1 4) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3033) := by
    have ha : (tripleCharges (sourceA2319 + difference 4 1) (sourceB2319 + difference 1 4) sourceC2319) = raw31932 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31932; decide +kernel
    rw [ha]
    exact (canonical31932 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2319 + difference 5 1) (sourceB2319 + difference 1 5) sourceC2319) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2443) := by
    have ha : (tripleCharges (sourceA2319 + difference 5 1) (sourceB2319 + difference 1 5) sourceC2319) = raw31933 := by
      apply Matrix.ext; unfold tripleCharges sourceA2319 sourceB2319 sourceC2319 difference raw31933; decide +kernel
    rw [ha]
    exact (canonical31933 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2319 + sourceB2319) sourceC2319) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2319 + sourceB2319) sourceC2319) = raw31934 := by
      apply Matrix.ext; unfold doubleCharges sourceA2319 sourceB2319 sourceC2319 raw31934; decide +kernel
    rw [ha]
    exact (canonical31934 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2319 sourceB2319 sourceC2319
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2319, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2320 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 0) (sourceB2320 + difference 0 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 942) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 0) (sourceB2320 + difference 0 2) sourceC2320) = raw31935 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31935; decide +kernel
    rw [ha]
    exact (canonical31935 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 1) (sourceB2320 + difference 1 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1822) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 1) (sourceB2320 + difference 1 2) sourceC2320) = raw31936 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31936; decide +kernel
    rw [ha]
    exact (canonical31936 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 2) (sourceB2320 + difference 2 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2088) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 2) (sourceB2320 + difference 2 2) sourceC2320) = raw11309 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw11309; decide +kernel
    rw [ha]
    exact (canonical11309 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 3) (sourceB2320 + difference 3 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 3) (sourceB2320 + difference 3 2) sourceC2320) = raw11308 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw11308; decide +kernel
    rw [ha]
    exact (canonical11308 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 4) (sourceB2320 + difference 4 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2107) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 4) (sourceB2320 + difference 4 2) sourceC2320) = raw31937 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31937; decide +kernel
    rw [ha]
    exact (canonical31937 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2320 + difference 2 5) (sourceB2320 + difference 5 2) sourceC2320) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA2320 + difference 2 5) (sourceB2320 + difference 5 2) sourceC2320) = raw31938 := by
      apply Matrix.ext; unfold tripleCharges sourceA2320 sourceB2320 sourceC2320 difference raw31938; decide +kernel
    rw [ha]
    exact (canonical31938 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2320 + sourceB2320) sourceC2320) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2320 + sourceB2320) sourceC2320) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA2320 sourceB2320 sourceC2320 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2320 sourceB2320 sourceC2320
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2320, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2321 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2321 + difference 0 1) (sourceB2321 + difference 1 0) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2321 + difference 0 1) (sourceB2321 + difference 1 0) sourceC2321) = raw31939 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31939; decide +kernel
    rw [ha]
    exact (canonical31939 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2321 + difference 1 1) (sourceB2321 + difference 1 1) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA2321 + difference 1 1) (sourceB2321 + difference 1 1) sourceC2321) = raw31940 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31940; decide +kernel
    rw [ha]
    exact (canonical31940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2321 + difference 2 1) (sourceB2321 + difference 1 2) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3137) := by
    have ha : (tripleCharges (sourceA2321 + difference 2 1) (sourceB2321 + difference 1 2) sourceC2321) = raw31941 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31941; decide +kernel
    rw [ha]
    exact (canonical31941 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2321 + difference 3 1) (sourceB2321 + difference 1 3) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2321 + difference 3 1) (sourceB2321 + difference 1 3) sourceC2321) = raw31942 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31942; decide +kernel
    rw [ha]
    exact (canonical31942 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2321 + difference 4 1) (sourceB2321 + difference 1 4) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3135) := by
    have ha : (tripleCharges (sourceA2321 + difference 4 1) (sourceB2321 + difference 1 4) sourceC2321) = raw31943 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31943; decide +kernel
    rw [ha]
    exact (canonical31943 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2321 + difference 5 1) (sourceB2321 + difference 1 5) sourceC2321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2321 + difference 5 1) (sourceB2321 + difference 1 5) sourceC2321) = raw31944 := by
      apply Matrix.ext; unfold tripleCharges sourceA2321 sourceB2321 sourceC2321 difference raw31944; decide +kernel
    rw [ha]
    exact (canonical31944 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2321 + sourceB2321) sourceC2321) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2321 + sourceB2321) sourceC2321) = raw31945 := by
      apply Matrix.ext; unfold doubleCharges sourceA2321 sourceB2321 sourceC2321 raw31945; decide +kernel
    rw [ha]
    exact (canonical31945 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2321 sourceB2321 sourceC2321
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2321, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2322 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 0) (sourceB2322 + difference 0 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 944) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 0) (sourceB2322 + difference 0 2) sourceC2322) = raw31946 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31946; decide +kernel
    rw [ha]
    exact (canonical31946 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 1) (sourceB2322 + difference 1 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1824) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 1) (sourceB2322 + difference 1 2) sourceC2322) = raw31947 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31947; decide +kernel
    rw [ha]
    exact (canonical31947 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 2) (sourceB2322 + difference 2 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 2) (sourceB2322 + difference 2 2) sourceC2322) = raw11093 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw11093; decide +kernel
    rw [ha]
    exact (canonical11093 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 3) (sourceB2322 + difference 3 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2110) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 3) (sourceB2322 + difference 3 2) sourceC2322) = raw11092 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw11092; decide +kernel
    rw [ha]
    exact (canonical11092 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 4) (sourceB2322 + difference 4 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2089) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 4) (sourceB2322 + difference 4 2) sourceC2322) = raw31948 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31948; decide +kernel
    rw [ha]
    exact (canonical31948 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2322 + difference 2 5) (sourceB2322 + difference 5 2) sourceC2322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2105) := by
    have ha : (tripleCharges (sourceA2322 + difference 2 5) (sourceB2322 + difference 5 2) sourceC2322) = raw31949 := by
      apply Matrix.ext; unfold tripleCharges sourceA2322 sourceB2322 sourceC2322 difference raw31949; decide +kernel
    rw [ha]
    exact (canonical31949 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2322 + sourceB2322) sourceC2322) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2322 + sourceB2322) sourceC2322) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA2322 sourceB2322 sourceC2322 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2322 sourceB2322 sourceC2322
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2322, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2323 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2323 + difference 0 1) (sourceB2323 + difference 1 0) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2323 + difference 0 1) (sourceB2323 + difference 1 0) sourceC2323) = raw31950 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31950; decide +kernel
    rw [ha]
    exact (canonical31950 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2323 + difference 1 1) (sourceB2323 + difference 1 1) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA2323 + difference 1 1) (sourceB2323 + difference 1 1) sourceC2323) = raw31951 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31951; decide +kernel
    rw [ha]
    exact (canonical31951 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2323 + difference 2 1) (sourceB2323 + difference 1 2) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3136) := by
    have ha : (tripleCharges (sourceA2323 + difference 2 1) (sourceB2323 + difference 1 2) sourceC2323) = raw31952 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31952; decide +kernel
    rw [ha]
    exact (canonical31952 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2323 + difference 3 1) (sourceB2323 + difference 1 3) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3133) := by
    have ha : (tripleCharges (sourceA2323 + difference 3 1) (sourceB2323 + difference 1 3) sourceC2323) = raw31953 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31953; decide +kernel
    rw [ha]
    exact (canonical31953 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2323 + difference 4 1) (sourceB2323 + difference 1 4) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3134) := by
    have ha : (tripleCharges (sourceA2323 + difference 4 1) (sourceB2323 + difference 1 4) sourceC2323) = raw31954 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31954; decide +kernel
    rw [ha]
    exact (canonical31954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2323 + difference 5 1) (sourceB2323 + difference 1 5) sourceC2323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA2323 + difference 5 1) (sourceB2323 + difference 1 5) sourceC2323) = raw31955 := by
      apply Matrix.ext; unfold tripleCharges sourceA2323 sourceB2323 sourceC2323 difference raw31955; decide +kernel
    rw [ha]
    exact (canonical31955 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2323 + sourceB2323) sourceC2323) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2323 + sourceB2323) sourceC2323) = raw31956 := by
      apply Matrix.ext; unfold doubleCharges sourceA2323 sourceB2323 sourceC2323 raw31956; decide +kernel
    rw [ha]
    exact (canonical31956 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2323 sourceB2323 sourceC2323
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2323, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2325 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2325 + difference 0 1) (sourceB2325 + difference 1 0) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3394) := by
    have ha : (tripleCharges (sourceA2325 + difference 0 1) (sourceB2325 + difference 1 0) sourceC2325) = raw31964 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31964; decide +kernel
    rw [ha]
    exact (canonical31964 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2325 + difference 1 1) (sourceB2325 + difference 1 1) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3158) := by
    have ha : (tripleCharges (sourceA2325 + difference 1 1) (sourceB2325 + difference 1 1) sourceC2325) = raw31965 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31965; decide +kernel
    rw [ha]
    exact (canonical31965 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2325 + difference 2 1) (sourceB2325 + difference 1 2) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3128) := by
    have ha : (tripleCharges (sourceA2325 + difference 2 1) (sourceB2325 + difference 1 2) sourceC2325) = raw31966 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31966; decide +kernel
    rw [ha]
    exact (canonical31966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2325 + difference 3 1) (sourceB2325 + difference 1 3) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3132) := by
    have ha : (tripleCharges (sourceA2325 + difference 3 1) (sourceB2325 + difference 1 3) sourceC2325) = raw31967 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31967; decide +kernel
    rw [ha]
    exact (canonical31967 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2325 + difference 4 1) (sourceB2325 + difference 1 4) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3132) := by
    have ha : (tripleCharges (sourceA2325 + difference 4 1) (sourceB2325 + difference 1 4) sourceC2325) = raw31968 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31968; decide +kernel
    rw [ha]
    exact (canonical31968 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2325 + difference 5 1) (sourceB2325 + difference 1 5) sourceC2325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2899) := by
    have ha : (tripleCharges (sourceA2325 + difference 5 1) (sourceB2325 + difference 1 5) sourceC2325) = raw31969 := by
      apply Matrix.ext; unfold tripleCharges sourceA2325 sourceB2325 sourceC2325 difference raw31969; decide +kernel
    rw [ha]
    exact (canonical31969 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2325 + sourceB2325) sourceC2325) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA2325 + sourceB2325) sourceC2325) = raw31970 := by
      apply Matrix.ext; unfold doubleCharges sourceA2325 sourceB2325 sourceC2325 raw31970; decide +kernel
    rw [ha]
    exact (canonical31970 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2325 sourceB2325 sourceC2325
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2325, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2326 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2326 + difference 0 1) (sourceB2326 + difference 1 0) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2326 + difference 0 1) (sourceB2326 + difference 1 0) sourceC2326) = raw31971 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31971; decide +kernel
    rw [ha]
    exact (canonical31971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2326 + difference 1 1) (sourceB2326 + difference 1 1) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA2326 + difference 1 1) (sourceB2326 + difference 1 1) sourceC2326) = raw31972 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31972; decide +kernel
    rw [ha]
    exact (canonical31972 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2326 + difference 2 1) (sourceB2326 + difference 1 2) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3127) := by
    have ha : (tripleCharges (sourceA2326 + difference 2 1) (sourceB2326 + difference 1 2) sourceC2326) = raw31973 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31973; decide +kernel
    rw [ha]
    exact (canonical31973 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2326 + difference 3 1) (sourceB2326 + difference 1 3) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3129) := by
    have ha : (tripleCharges (sourceA2326 + difference 3 1) (sourceB2326 + difference 1 3) sourceC2326) = raw31974 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31974; decide +kernel
    rw [ha]
    exact (canonical31974 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2326 + difference 4 1) (sourceB2326 + difference 1 4) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3131) := by
    have ha : (tripleCharges (sourceA2326 + difference 4 1) (sourceB2326 + difference 1 4) sourceC2326) = raw31975 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31975; decide +kernel
    rw [ha]
    exact (canonical31975 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2326 + difference 5 1) (sourceB2326 + difference 1 5) sourceC2326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA2326 + difference 5 1) (sourceB2326 + difference 1 5) sourceC2326) = raw31976 := by
      apply Matrix.ext; unfold tripleCharges sourceA2326 sourceB2326 sourceC2326 difference raw31976; decide +kernel
    rw [ha]
    exact (canonical31976 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2326 + sourceB2326) sourceC2326) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2326 + sourceB2326) sourceC2326) = raw31977 := by
      apply Matrix.ext; unfold doubleCharges sourceA2326 sourceB2326 sourceC2326 raw31977; decide +kernel
    rw [ha]
    exact (canonical31977 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2326 sourceB2326 sourceC2326
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2326, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2327 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 0) (sourceB2327 + difference 0 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 0) (sourceB2327 + difference 0 2) sourceC2327) = raw31978 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31978; decide +kernel
    rw [ha]
    exact (canonical31978 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 1) (sourceB2327 + difference 1 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2333) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 1) (sourceB2327 + difference 1 2) sourceC2327) = raw31979 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31979; decide +kernel
    rw [ha]
    exact (canonical31979 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 2) (sourceB2327 + difference 2 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 2) (sourceB2327 + difference 2 2) sourceC2327) = raw31980 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31980; decide +kernel
    rw [ha]
    exact (canonical31980 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 3) (sourceB2327 + difference 3 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 3) (sourceB2327 + difference 3 2) sourceC2327) = raw31981 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31981; decide +kernel
    rw [ha]
    exact (canonical31981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 4) (sourceB2327 + difference 4 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 4) (sourceB2327 + difference 4 2) sourceC2327) = raw31982 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31982; decide +kernel
    rw [ha]
    exact (canonical31982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2327 + difference 2 5) (sourceB2327 + difference 5 2) sourceC2327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2327 + difference 2 5) (sourceB2327 + difference 5 2) sourceC2327) = raw31983 := by
      apply Matrix.ext; unfold tripleCharges sourceA2327 sourceB2327 sourceC2327 difference raw31983; decide +kernel
    rw [ha]
    exact (canonical31983 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2327 + sourceB2327) sourceC2327) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2327 + sourceB2327) sourceC2327) = raw30305 := by
      apply Matrix.ext; unfold doubleCharges sourceA2327 sourceB2327 sourceC2327 raw30305; decide +kernel
    rw [ha]
    exact (canonical30305 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2327 sourceB2327 sourceC2327
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2327, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2328 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2328 + difference 0 2) (sourceB2328 + difference 2 0) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3787) := by
    have ha : (tripleCharges (sourceA2328 + difference 0 2) (sourceB2328 + difference 2 0) sourceC2328) = raw31984 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31984; decide +kernel
    rw [ha]
    exact (canonical31984 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2328 + difference 1 2) (sourceB2328 + difference 2 1) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2328 + difference 1 2) (sourceB2328 + difference 2 1) sourceC2328) = raw23811 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw23811; decide +kernel
    rw [ha]
    exact (canonical23811 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2328 + difference 2 2) (sourceB2328 + difference 2 2) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA2328 + difference 2 2) (sourceB2328 + difference 2 2) sourceC2328) = raw31985 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31985; decide +kernel
    rw [ha]
    exact (canonical31985 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2328 + difference 3 2) (sourceB2328 + difference 2 3) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2900) := by
    have ha : (tripleCharges (sourceA2328 + difference 3 2) (sourceB2328 + difference 2 3) sourceC2328) = raw31986 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31986; decide +kernel
    rw [ha]
    exact (canonical31986 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2328 + difference 4 2) (sourceB2328 + difference 2 4) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2902) := by
    have ha : (tripleCharges (sourceA2328 + difference 4 2) (sourceB2328 + difference 2 4) sourceC2328) = raw31987 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31987; decide +kernel
    rw [ha]
    exact (canonical31987 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2328 + difference 5 2) (sourceB2328 + difference 2 5) sourceC2328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2437) := by
    have ha : (tripleCharges (sourceA2328 + difference 5 2) (sourceB2328 + difference 2 5) sourceC2328) = raw31988 := by
      apply Matrix.ext; unfold tripleCharges sourceA2328 sourceB2328 sourceC2328 difference raw31988; decide +kernel
    rw [ha]
    exact (canonical31988 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2328 + sourceB2328) sourceC2328) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2328 + sourceB2328) sourceC2328) = raw23817 := by
      apply Matrix.ext; unfold doubleCharges sourceA2328 sourceB2328 sourceC2328 raw23817; decide +kernel
    rw [ha]
    exact (canonical23817 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2328 sourceB2328 sourceC2328
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2328, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2330 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 0) (sourceB2330 + difference 0 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 0) (sourceB2330 + difference 0 2) sourceC2330) = raw31994 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31994; decide +kernel
    rw [ha]
    exact (canonical31994 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 1) (sourceB2330 + difference 1 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2331) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 1) (sourceB2330 + difference 1 2) sourceC2330) = raw31995 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31995; decide +kernel
    rw [ha]
    exact (canonical31995 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 2) (sourceB2330 + difference 2 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 2) (sourceB2330 + difference 2 2) sourceC2330) = raw11881 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw11881; decide +kernel
    rw [ha]
    exact (canonical11881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 3) (sourceB2330 + difference 3 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 3) (sourceB2330 + difference 3 2) sourceC2330) = raw31996 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31996; decide +kernel
    rw [ha]
    exact (canonical31996 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 4) (sourceB2330 + difference 4 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 4) (sourceB2330 + difference 4 2) sourceC2330) = raw31997 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw31997; decide +kernel
    rw [ha]
    exact (canonical31997 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2330 + difference 2 5) (sourceB2330 + difference 5 2) sourceC2330) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2508) := by
    have ha : (tripleCharges (sourceA2330 + difference 2 5) (sourceB2330 + difference 5 2) sourceC2330) = raw11878 := by
      apply Matrix.ext; unfold tripleCharges sourceA2330 sourceB2330 sourceC2330 difference raw11878; decide +kernel
    rw [ha]
    exact (canonical11878 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2330 + sourceB2330) sourceC2330) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2330 + sourceB2330) sourceC2330) = raw11868 := by
      apply Matrix.ext; unfold doubleCharges sourceA2330 sourceB2330 sourceC2330 raw11868; decide +kernel
    rw [ha]
    exact (canonical11868 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2330 sourceB2330 sourceC2330
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2330, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2331 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2331 + difference 0 2) (sourceB2331 + difference 2 0) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3945) := by
    have ha : (tripleCharges (sourceA2331 + difference 0 2) (sourceB2331 + difference 2 0) sourceC2331) = raw31998 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw31998; decide +kernel
    rw [ha]
    exact (canonical31998 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2331 + difference 1 2) (sourceB2331 + difference 2 1) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA2331 + difference 1 2) (sourceB2331 + difference 2 1) sourceC2331) = raw23839 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw23839; decide +kernel
    rw [ha]
    exact (canonical23839 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2331 + difference 2 2) (sourceB2331 + difference 2 2) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2976) := by
    have ha : (tripleCharges (sourceA2331 + difference 2 2) (sourceB2331 + difference 2 2) sourceC2331) = raw13068 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw13068; decide +kernel
    rw [ha]
    exact (canonical13068 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2331 + difference 3 2) (sourceB2331 + difference 2 3) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2849) := by
    have ha : (tripleCharges (sourceA2331 + difference 3 2) (sourceB2331 + difference 2 3) sourceC2331) = raw31999 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw31999; decide +kernel
    rw [ha]
    exact (canonical31999 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2331 + difference 4 2) (sourceB2331 + difference 2 4) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2849) := by
    have ha : (tripleCharges (sourceA2331 + difference 4 2) (sourceB2331 + difference 2 4) sourceC2331) = raw32000 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw32000; decide +kernel
    rw [ha]
    exact (canonical32000 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2331 + difference 5 2) (sourceB2331 + difference 2 5) sourceC2331) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2847) := by
    have ha : (tripleCharges (sourceA2331 + difference 5 2) (sourceB2331 + difference 2 5) sourceC2331) = raw32001 := by
      apply Matrix.ext; unfold tripleCharges sourceA2331 sourceB2331 sourceC2331 difference raw32001; decide +kernel
    rw [ha]
    exact (canonical32001 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2331 + sourceB2331) sourceC2331) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2331 + sourceB2331) sourceC2331) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA2331 sourceB2331 sourceC2331 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2331 sourceB2331 sourceC2331
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2331, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2333 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2333 + difference 0 2) (sourceB2333 + difference 2 0) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA2333 + difference 0 2) (sourceB2333 + difference 2 0) sourceC2333) = raw32007 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32007; decide +kernel
    rw [ha]
    exact (canonical32007 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2333 + difference 1 2) (sourceB2333 + difference 2 1) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA2333 + difference 1 2) (sourceB2333 + difference 2 1) sourceC2333) = raw23860 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw23860; decide +kernel
    rw [ha]
    exact (canonical23860 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2333 + difference 2 2) (sourceB2333 + difference 2 2) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA2333 + difference 2 2) (sourceB2333 + difference 2 2) sourceC2333) = raw32008 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32008; decide +kernel
    rw [ha]
    exact (canonical32008 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2333 + difference 3 2) (sourceB2333 + difference 2 3) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2846) := by
    have ha : (tripleCharges (sourceA2333 + difference 3 2) (sourceB2333 + difference 2 3) sourceC2333) = raw32009 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32009; decide +kernel
    rw [ha]
    exact (canonical32009 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2333 + difference 4 2) (sourceB2333 + difference 2 4) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2848) := by
    have ha : (tripleCharges (sourceA2333 + difference 4 2) (sourceB2333 + difference 2 4) sourceC2333) = raw32010 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32010; decide +kernel
    rw [ha]
    exact (canonical32010 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2333 + difference 5 2) (sourceB2333 + difference 2 5) sourceC2333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA2333 + difference 5 2) (sourceB2333 + difference 2 5) sourceC2333) = raw32011 := by
      apply Matrix.ext; unfold tripleCharges sourceA2333 sourceB2333 sourceC2333 difference raw32011; decide +kernel
    rw [ha]
    exact (canonical32011 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2333 + sourceB2333) sourceC2333) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2333 + sourceB2333) sourceC2333) = raw23866 := by
      apply Matrix.ext; unfold doubleCharges sourceA2333 sourceB2333 sourceC2333 raw23866; decide +kernel
    rw [ha]
    exact (canonical23866 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2333 sourceB2333 sourceC2333
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2333, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2334 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2334 + difference 0 2) (sourceB2334 + difference 2 0) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3493) := by
    have ha : (tripleCharges (sourceA2334 + difference 0 2) (sourceB2334 + difference 2 0) sourceC2334) = raw32012 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32012; decide +kernel
    rw [ha]
    exact (canonical32012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2334 + difference 1 2) (sourceB2334 + difference 2 1) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA2334 + difference 1 2) (sourceB2334 + difference 2 1) sourceC2334) = raw32013 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32013; decide +kernel
    rw [ha]
    exact (canonical32013 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2334 + difference 2 2) (sourceB2334 + difference 2 2) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2552) := by
    have ha : (tripleCharges (sourceA2334 + difference 2 2) (sourceB2334 + difference 2 2) sourceC2334) = raw32014 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32014; decide +kernel
    rw [ha]
    exact (canonical32014 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2334 + difference 3 2) (sourceB2334 + difference 2 3) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2427) := by
    have ha : (tripleCharges (sourceA2334 + difference 3 2) (sourceB2334 + difference 2 3) sourceC2334) = raw32015 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32015; decide +kernel
    rw [ha]
    exact (canonical32015 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2334 + difference 4 2) (sourceB2334 + difference 2 4) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2427) := by
    have ha : (tripleCharges (sourceA2334 + difference 4 2) (sourceB2334 + difference 2 4) sourceC2334) = raw29434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw29434; decide +kernel
    rw [ha]
    exact (canonical29434 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2334 + difference 5 2) (sourceB2334 + difference 2 5) sourceC2334) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1960) := by
    have ha : (tripleCharges (sourceA2334 + difference 5 2) (sourceB2334 + difference 2 5) sourceC2334) = raw32016 := by
      apply Matrix.ext; unfold tripleCharges sourceA2334 sourceB2334 sourceC2334 difference raw32016; decide +kernel
    rw [ha]
    exact (canonical32016 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2334 + sourceB2334) sourceC2334) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2334 + sourceB2334) sourceC2334) = raw29437 := by
      apply Matrix.ext; unfold doubleCharges sourceA2334 sourceB2334 sourceC2334 raw29437; decide +kernel
    rw [ha]
    exact (canonical29437 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2334 sourceB2334 sourceC2334
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2334, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2335 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2335 + difference 0 2) (sourceB2335 + difference 2 0) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA2335 + difference 0 2) (sourceB2335 + difference 2 0) sourceC2335) = raw32017 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32017; decide +kernel
    rw [ha]
    exact (canonical32017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2335 + difference 1 2) (sourceB2335 + difference 2 1) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA2335 + difference 1 2) (sourceB2335 + difference 2 1) sourceC2335) = raw32018 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32018; decide +kernel
    rw [ha]
    exact (canonical32018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2335 + difference 2 2) (sourceB2335 + difference 2 2) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA2335 + difference 2 2) (sourceB2335 + difference 2 2) sourceC2335) = raw32019 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32019; decide +kernel
    rw [ha]
    exact (canonical32019 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2335 + difference 3 2) (sourceB2335 + difference 2 3) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2335 + difference 3 2) (sourceB2335 + difference 2 3) sourceC2335) = raw32020 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32020; decide +kernel
    rw [ha]
    exact (canonical32020 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2335 + difference 4 2) (sourceB2335 + difference 2 4) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2428) := by
    have ha : (tripleCharges (sourceA2335 + difference 4 2) (sourceB2335 + difference 2 4) sourceC2335) = raw32021 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw32021; decide +kernel
    rw [ha]
    exact (canonical32021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2335 + difference 5 2) (sourceB2335 + difference 2 5) sourceC2335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2426) := by
    have ha : (tripleCharges (sourceA2335 + difference 5 2) (sourceB2335 + difference 2 5) sourceC2335) = raw27463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2335 sourceB2335 sourceC2335 difference raw27463; decide +kernel
    rw [ha]
    exact (canonical27463 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2335 + sourceB2335) sourceC2335) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2335 + sourceB2335) sourceC2335) = raw27466 := by
      apply Matrix.ext; unfold doubleCharges sourceA2335 sourceB2335 sourceC2335 raw27466; decide +kernel
    rw [ha]
    exact (canonical27466 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2335 sourceB2335 sourceC2335
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2335, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources73
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2336 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2336 + difference 0 2) (sourceB2336 + difference 2 0) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3782) := by
    have ha : (tripleCharges (sourceA2336 + difference 0 2) (sourceB2336 + difference 2 0) sourceC2336) = raw14566 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw14566; decide +kernel
    rw [ha]
    exact (canonical14566 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2336 + difference 1 2) (sourceB2336 + difference 2 1) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA2336 + difference 1 2) (sourceB2336 + difference 2 1) sourceC2336) = raw32022 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32022; decide +kernel
    rw [ha]
    exact (canonical32022 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2336 + difference 2 2) (sourceB2336 + difference 2 2) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA2336 + difference 2 2) (sourceB2336 + difference 2 2) sourceC2336) = raw14569 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw14569; decide +kernel
    rw [ha]
    exact (canonical14569 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2336 + difference 3 2) (sourceB2336 + difference 2 3) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2433) := by
    have ha : (tripleCharges (sourceA2336 + difference 3 2) (sourceB2336 + difference 2 3) sourceC2336) = raw32023 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32023; decide +kernel
    rw [ha]
    exact (canonical32023 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2336 + difference 4 2) (sourceB2336 + difference 2 4) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2336 + difference 4 2) (sourceB2336 + difference 2 4) sourceC2336) = raw32024 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32024; decide +kernel
    rw [ha]
    exact (canonical32024 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2336 + difference 5 2) (sourceB2336 + difference 2 5) sourceC2336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2430) := by
    have ha : (tripleCharges (sourceA2336 + difference 5 2) (sourceB2336 + difference 2 5) sourceC2336) = raw32025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2336 sourceB2336 sourceC2336 difference raw32025; decide +kernel
    rw [ha]
    exact (canonical32025 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2336 + sourceB2336) sourceC2336) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2336 + sourceB2336) sourceC2336) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA2336 sourceB2336 sourceC2336 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2336 sourceB2336 sourceC2336
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2336, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2337 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 0) (sourceB2337 + difference 0 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1335) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 0) (sourceB2337 + difference 0 2) sourceC2337) = raw32026 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32026; decide +kernel
    rw [ha]
    exact (canonical32026 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 1) (sourceB2337 + difference 1 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2826) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 1) (sourceB2337 + difference 1 2) sourceC2337) = raw32027 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32027; decide +kernel
    rw [ha]
    exact (canonical32027 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 2) (sourceB2337 + difference 2 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 2) (sourceB2337 + difference 2 2) sourceC2337) = raw32028 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32028; decide +kernel
    rw [ha]
    exact (canonical32028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 3) (sourceB2337 + difference 3 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 3) (sourceB2337 + difference 3 2) sourceC2337) = raw27476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw27476; decide +kernel
    rw [ha]
    exact (canonical27476 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 4) (sourceB2337 + difference 4 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 4) (sourceB2337 + difference 4 2) sourceC2337) = raw32029 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32029; decide +kernel
    rw [ha]
    exact (canonical32029 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2337 + difference 2 5) (sourceB2337 + difference 5 2) sourceC2337) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2951) := by
    have ha : (tripleCharges (sourceA2337 + difference 2 5) (sourceB2337 + difference 5 2) sourceC2337) = raw32030 := by
      apply Matrix.ext; unfold tripleCharges sourceA2337 sourceB2337 sourceC2337 difference raw32030; decide +kernel
    rw [ha]
    exact (canonical32030 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2337 + sourceB2337) sourceC2337) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2337 + sourceB2337) sourceC2337) = raw17313 := by
      apply Matrix.ext; unfold doubleCharges sourceA2337 sourceB2337 sourceC2337 raw17313; decide +kernel
    rw [ha]
    exact (canonical17313 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2337 sourceB2337 sourceC2337
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2337, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1888 : Integer.Sparse.reindex keyMap MixedData.row1888 = numericRow1888 := by decide +kernel

theorem numericCheck1888 (x : Master → ℝ) : Integer.Sparse.eval numericRow1888 x =
    (1 : ℝ) * reducedSource1888 x := by
  norm_num [numericRow1888, reducedSource1888, Integer.Sparse.eval, Sparse.eval, nodeValue2443, nodeValue3033, nodeValue3136, nodeValue3138, nodeValue3180, nodeValue3732, nodeValue4092]

theorem reindexCheck1889 : Integer.Sparse.reindex keyMap MixedData.row1889 = numericRow1889 := by decide +kernel

theorem numericCheck1889 (x : Master → ℝ) : Integer.Sparse.eval numericRow1889 x =
    (1 : ℝ) * reducedSource1889 x := by
  norm_num [numericRow1889, reducedSource1889, Integer.Sparse.eval, Sparse.eval, nodeValue942, nodeValue1822, nodeValue2088, nodeValue2105, nodeValue2107, nodeValue4083]

theorem reindexCheck1890 : Integer.Sparse.reindex keyMap MixedData.row1890 = numericRow1890 := by decide +kernel

theorem numericCheck1890 (x : Master → ℝ) : Integer.Sparse.eval numericRow1890 x =
    (1 : ℝ) * reducedSource1890 x := by
  norm_num [numericRow1890, reducedSource1890, Integer.Sparse.eval, Sparse.eval, nodeValue2890, nodeValue3135, nodeValue3137, nodeValue3172, nodeValue3721, nodeValue4091]

theorem reindexCheck1891 : Integer.Sparse.reindex keyMap MixedData.row1891 = numericRow1891 := by decide +kernel

theorem numericCheck1891 (x : Master → ℝ) : Integer.Sparse.eval numericRow1891 x =
    (1 : ℝ) * reducedSource1891 x := by
  norm_num [numericRow1891, reducedSource1891, Integer.Sparse.eval, Sparse.eval, nodeValue944, nodeValue1824, nodeValue2089, nodeValue2105, nodeValue2110, nodeValue4083]

theorem reindexCheck1892 : Integer.Sparse.reindex keyMap MixedData.row1892 = numericRow1892 := by decide +kernel

theorem numericCheck1892 (x : Master → ℝ) : Integer.Sparse.eval numericRow1892 x =
    (1 : ℝ) * reducedSource1892 x := by
  norm_num [numericRow1892, reducedSource1892, Integer.Sparse.eval, Sparse.eval, nodeValue2423, nodeValue3133, nodeValue3134, nodeValue3136, nodeValue3170, nodeValue3719, nodeValue4092]

theorem reindexCheck1893 : Integer.Sparse.reindex keyMap MixedData.row1893 = numericRow1893 := by decide +kernel

theorem numericCheck1893 (x : Master → ℝ) : Integer.Sparse.eval numericRow1893 x =
    (1 : ℝ) * reducedSource1893 x := by
  norm_num [numericRow1893, reducedSource1893, Integer.Sparse.eval, Sparse.eval, nodeValue2899, nodeValue3128, nodeValue3132, nodeValue3158, nodeValue3394, nodeValue4083]

theorem reindexCheck1894 : Integer.Sparse.reindex keyMap MixedData.row1894 = numericRow1894 := by decide +kernel

theorem numericCheck1894 (x : Master → ℝ) : Integer.Sparse.eval numericRow1894 x =
    (1 : ℝ) * reducedSource1894 x := by
  norm_num [numericRow1894, reducedSource1894, Integer.Sparse.eval, Sparse.eval, nodeValue2435, nodeValue3127, nodeValue3129, nodeValue3131, nodeValue3156, nodeValue3391, nodeValue4084]

theorem reindexCheck1895 : Integer.Sparse.reindex keyMap MixedData.row1895 = numericRow1895 := by decide +kernel

theorem numericCheck1895 (x : Master → ℝ) : Integer.Sparse.eval numericRow1895 x =
    (1 : ℝ) * reducedSource1895 x := by
  norm_num [numericRow1895, reducedSource1895, Integer.Sparse.eval, Sparse.eval, nodeValue1130, nodeValue2333, nodeValue2481, nodeValue2494, nodeValue2508, nodeValue2515, nodeValue4092]

theorem reindexCheck1896 : Integer.Sparse.reindex keyMap MixedData.row1896 = numericRow1896 := by decide +kernel

theorem numericCheck1896 (x : Master → ℝ) : Integer.Sparse.eval numericRow1896 x =
    (1 : ℝ) * reducedSource1896 x := by
  norm_num [numericRow1896, reducedSource1896, Integer.Sparse.eval, Sparse.eval, nodeValue2437, nodeValue2900, nodeValue2902, nodeValue2954, nodeValue2984, nodeValue3787, nodeValue4091]

theorem reindexCheck1897 : Integer.Sparse.reindex keyMap MixedData.row1897 = numericRow1897 := by decide +kernel

theorem numericCheck1897 (x : Master → ℝ) : Integer.Sparse.eval numericRow1897 x =
    (1 : ℝ) * reducedSource1897 x := by
  norm_num [numericRow1897, reducedSource1897, Integer.Sparse.eval, Sparse.eval, nodeValue1127, nodeValue2331, nodeValue2493, nodeValue2508, nodeValue2512, nodeValue4092]

theorem reindexCheck1898 : Integer.Sparse.reindex keyMap MixedData.row1898 = numericRow1898 := by decide +kernel

theorem numericCheck1898 (x : Master → ℝ) : Integer.Sparse.eval numericRow1898 x =
    (1 : ℝ) * reducedSource1898 x := by
  norm_num [numericRow1898, reducedSource1898, Integer.Sparse.eval, Sparse.eval, nodeValue2847, nodeValue2849, nodeValue2884, nodeValue2976, nodeValue3945, nodeValue4091]

theorem reindexCheck1899 : Integer.Sparse.reindex keyMap MixedData.row1899 = numericRow1899 := by decide +kernel

theorem numericCheck1899 (x : Master → ℝ) : Integer.Sparse.eval numericRow1899 x =
    (1 : ℝ) * reducedSource1899 x := by
  norm_num [numericRow1899, reducedSource1899, Integer.Sparse.eval, Sparse.eval, nodeValue2426, nodeValue2846, nodeValue2848, nodeValue2881, nodeValue2974, nodeValue3781, nodeValue4092]

theorem reindexCheck1900 : Integer.Sparse.reindex keyMap MixedData.row1900 = numericRow1900 := by decide +kernel

theorem numericCheck1900 (x : Master → ℝ) : Integer.Sparse.eval numericRow1900 x =
    (1 : ℝ) * reducedSource1900 x := by
  norm_num [numericRow1900, reducedSource1900, Integer.Sparse.eval, Sparse.eval, nodeValue1960, nodeValue2427, nodeValue2509, nodeValue2552, nodeValue3493, nodeValue4084]

theorem reindexCheck1901 : Integer.Sparse.reindex keyMap MixedData.row1901 = numericRow1901 := by decide +kernel

theorem numericCheck1901 (x : Master → ℝ) : Integer.Sparse.eval numericRow1901 x =
    (1 : ℝ) * reducedSource1901 x := by
  norm_num [numericRow1901, reducedSource1901, Integer.Sparse.eval, Sparse.eval, nodeValue2426, nodeValue2428, nodeValue2433, nodeValue2512, nodeValue2554, nodeValue3781, nodeValue4092]

theorem reindexCheck1902 : Integer.Sparse.reindex keyMap MixedData.row1902 = numericRow1902 := by decide +kernel

theorem numericCheck1902 (x : Master → ℝ) : Integer.Sparse.eval numericRow1902 x =
    (1 : ℝ) * reducedSource1902 x := by
  norm_num [numericRow1902, reducedSource1902, Integer.Sparse.eval, Sparse.eval, nodeValue2430, nodeValue2431, nodeValue2433, nodeValue2515, nodeValue2557, nodeValue3782, nodeValue4092]

theorem reindexCheck1903 : Integer.Sparse.reindex keyMap MixedData.row1903 = numericRow1903 := by decide +kernel

theorem numericCheck1903 (x : Master → ℝ) : Integer.Sparse.eval numericRow1903 x =
    (1 : ℝ) * reducedSource1903 x := by
  norm_num [numericRow1903, reducedSource1903, Integer.Sparse.eval, Sparse.eval, nodeValue1335, nodeValue2826, nodeValue2924, nodeValue2933, nodeValue2951, nodeValue2954, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1888 (mixedVector B) = 0 := by
  have h2443 : mixedVector B (Sum.inr 2443) = Sparse.eval nodeValue2443 (mixedVector B) := by
    change mixedMoment B node2443 node2443Labels = _
    exact sound2443 B hB hF
  have h3033 : mixedVector B (Sum.inr 3033) = Sparse.eval nodeValue3033 (mixedVector B) := by
    change mixedMoment B node3033 node3033Labels = _
    exact sound3033 B hB hF
  have h3136 : mixedVector B (Sum.inr 3136) = Sparse.eval nodeValue3136 (mixedVector B) := by
    change mixedMoment B node3136 node3136Labels = _
    exact sound3136 B hB hF
  have h3138 : mixedVector B (Sum.inr 3138) = Sparse.eval nodeValue3138 (mixedVector B) := by
    change mixedMoment B node3138 node3138Labels = _
    exact sound3138 B hB hF
  have h3180 : mixedVector B (Sum.inr 3180) = Sparse.eval nodeValue3180 (mixedVector B) := by
    change mixedMoment B node3180 node3180Labels = _
    exact sound3180 B hB hF
  have h3732 : mixedVector B (Sum.inr 3732) = Sparse.eval nodeValue3732 (mixedVector B) := by
    change mixedMoment B node3732 node3732Labels = _
    exact sound3732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2319, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2443, h3033, h3136, h3138, h3180, h3732, h4092, reducedSource1888] using sourceEq2319 B hB

theorem rowSound1888 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1888 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1888, numericCheck1888, reducedZero1888 B hB hF, mul_zero]

theorem reducedZero1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1889 (mixedVector B) = 0 := by
  have h942 : mixedVector B (Sum.inr 942) = Sparse.eval nodeValue942 (mixedVector B) := by
    change mixedMoment B node942 node942Labels = _
    exact sound942 B hB hF
  have h1822 : mixedVector B (Sum.inr 1822) = Sparse.eval nodeValue1822 (mixedVector B) := by
    change mixedMoment B node1822 node1822Labels = _
    exact sound1822 B hB hF
  have h2088 : mixedVector B (Sum.inr 2088) = Sparse.eval nodeValue2088 (mixedVector B) := by
    change mixedMoment B node2088 node2088Labels = _
    exact sound2088 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2107 : mixedVector B (Sum.inr 2107) = Sparse.eval nodeValue2107 (mixedVector B) := by
    change mixedMoment B node2107 node2107Labels = _
    exact sound2107 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2320, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h942, h1822, h2088, h2105, h2107, h4083, reducedSource1889] using sourceEq2320 B hB

theorem rowSound1889 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1889 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1889, numericCheck1889, reducedZero1889 B hB hF, mul_zero]

theorem reducedZero1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1890 (mixedVector B) = 0 := by
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h3135 : mixedVector B (Sum.inr 3135) = Sparse.eval nodeValue3135 (mixedVector B) := by
    change mixedMoment B node3135 node3135Labels = _
    exact sound3135 B hB hF
  have h3137 : mixedVector B (Sum.inr 3137) = Sparse.eval nodeValue3137 (mixedVector B) := by
    change mixedMoment B node3137 node3137Labels = _
    exact sound3137 B hB hF
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2321, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2890, h3135, h3137, h3172, h3721, h4091, reducedSource1890] using sourceEq2321 B hB

theorem rowSound1890 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1890 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1890, numericCheck1890, reducedZero1890 B hB hF, mul_zero]

theorem reducedZero1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1891 (mixedVector B) = 0 := by
  have h944 : mixedVector B (Sum.inr 944) = Sparse.eval nodeValue944 (mixedVector B) := by
    change mixedMoment B node944 node944Labels = _
    exact sound944 B hB hF
  have h1824 : mixedVector B (Sum.inr 1824) = Sparse.eval nodeValue1824 (mixedVector B) := by
    change mixedMoment B node1824 node1824Labels = _
    exact sound1824 B hB hF
  have h2089 : mixedVector B (Sum.inr 2089) = Sparse.eval nodeValue2089 (mixedVector B) := by
    change mixedMoment B node2089 node2089Labels = _
    exact sound2089 B hB hF
  have h2105 : mixedVector B (Sum.inr 2105) = Sparse.eval nodeValue2105 (mixedVector B) := by
    change mixedMoment B node2105 node2105Labels = _
    exact sound2105 B hB hF
  have h2110 : mixedVector B (Sum.inr 2110) = Sparse.eval nodeValue2110 (mixedVector B) := by
    change mixedMoment B node2110 node2110Labels = _
    exact sound2110 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2322, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h944, h1824, h2089, h2105, h2110, h4083, reducedSource1891] using sourceEq2322 B hB

theorem rowSound1891 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1891 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1891, numericCheck1891, reducedZero1891 B hB hF, mul_zero]

theorem reducedZero1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1892 (mixedVector B) = 0 := by
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h3133 : mixedVector B (Sum.inr 3133) = Sparse.eval nodeValue3133 (mixedVector B) := by
    change mixedMoment B node3133 node3133Labels = _
    exact sound3133 B hB hF
  have h3134 : mixedVector B (Sum.inr 3134) = Sparse.eval nodeValue3134 (mixedVector B) := by
    change mixedMoment B node3134 node3134Labels = _
    exact sound3134 B hB hF
  have h3136 : mixedVector B (Sum.inr 3136) = Sparse.eval nodeValue3136 (mixedVector B) := by
    change mixedMoment B node3136 node3136Labels = _
    exact sound3136 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2323, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2423, h3133, h3134, h3136, h3170, h3719, h4092, reducedSource1892] using sourceEq2323 B hB

theorem rowSound1892 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1892 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1892, numericCheck1892, reducedZero1892 B hB hF, mul_zero]

theorem reducedZero1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1893 (mixedVector B) = 0 := by
  have h2899 : mixedVector B (Sum.inr 2899) = Sparse.eval nodeValue2899 (mixedVector B) := by
    change mixedMoment B node2899 node2899Labels = _
    exact sound2899 B hB hF
  have h3128 : mixedVector B (Sum.inr 3128) = Sparse.eval nodeValue3128 (mixedVector B) := by
    change mixedMoment B node3128 node3128Labels = _
    exact sound3128 B hB hF
  have h3132 : mixedVector B (Sum.inr 3132) = Sparse.eval nodeValue3132 (mixedVector B) := by
    change mixedMoment B node3132 node3132Labels = _
    exact sound3132 B hB hF
  have h3158 : mixedVector B (Sum.inr 3158) = Sparse.eval nodeValue3158 (mixedVector B) := by
    change mixedMoment B node3158 node3158Labels = _
    exact sound3158 B hB hF
  have h3394 : mixedVector B (Sum.inr 3394) = Sparse.eval nodeValue3394 (mixedVector B) := by
    change mixedMoment B node3394 node3394Labels = _
    exact sound3394 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm2325, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2899, h3128, h3132, h3158, h3394, h4083, reducedSource1893] using sourceEq2325 B hB

theorem rowSound1893 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1893 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1893, numericCheck1893, reducedZero1893 B hB hF, mul_zero]

theorem reducedZero1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1894 (mixedVector B) = 0 := by
  have h2435 : mixedVector B (Sum.inr 2435) = Sparse.eval nodeValue2435 (mixedVector B) := by
    change mixedMoment B node2435 node2435Labels = _
    exact sound2435 B hB hF
  have h3127 : mixedVector B (Sum.inr 3127) = Sparse.eval nodeValue3127 (mixedVector B) := by
    change mixedMoment B node3127 node3127Labels = _
    exact sound3127 B hB hF
  have h3129 : mixedVector B (Sum.inr 3129) = Sparse.eval nodeValue3129 (mixedVector B) := by
    change mixedMoment B node3129 node3129Labels = _
    exact sound3129 B hB hF
  have h3131 : mixedVector B (Sum.inr 3131) = Sparse.eval nodeValue3131 (mixedVector B) := by
    change mixedMoment B node3131 node3131Labels = _
    exact sound3131 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2326, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2435, h3127, h3129, h3131, h3156, h3391, h4084, reducedSource1894] using sourceEq2326 B hB

theorem rowSound1894 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1894 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1894, numericCheck1894, reducedZero1894 B hB hF, mul_zero]

theorem reducedZero1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1895 (mixedVector B) = 0 := by
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h2333 : mixedVector B (Sum.inr 2333) = Sparse.eval nodeValue2333 (mixedVector B) := by
    change mixedMoment B node2333 node2333Labels = _
    exact sound2333 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2327, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1130, h2333, h2481, h2494, h2508, h2515, h4092, reducedSource1895] using sourceEq2327 B hB

theorem rowSound1895 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1895 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1895, numericCheck1895, reducedZero1895 B hB hF, mul_zero]

theorem reducedZero1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1896 (mixedVector B) = 0 := by
  have h2437 : mixedVector B (Sum.inr 2437) = Sparse.eval nodeValue2437 (mixedVector B) := by
    change mixedMoment B node2437 node2437Labels = _
    exact sound2437 B hB hF
  have h2900 : mixedVector B (Sum.inr 2900) = Sparse.eval nodeValue2900 (mixedVector B) := by
    change mixedMoment B node2900 node2900Labels = _
    exact sound2900 B hB hF
  have h2902 : mixedVector B (Sum.inr 2902) = Sparse.eval nodeValue2902 (mixedVector B) := by
    change mixedMoment B node2902 node2902Labels = _
    exact sound2902 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3787 : mixedVector B (Sum.inr 3787) = Sparse.eval nodeValue3787 (mixedVector B) := by
    change mixedMoment B node3787 node3787Labels = _
    exact sound3787 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2328, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2437, h2900, h2902, h2954, h2984, h3787, h4091, reducedSource1896] using sourceEq2328 B hB

theorem rowSound1896 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1896 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1896, numericCheck1896, reducedZero1896 B hB hF, mul_zero]

theorem reducedZero1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1897 (mixedVector B) = 0 := by
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h2331 : mixedVector B (Sum.inr 2331) = Sparse.eval nodeValue2331 (mixedVector B) := by
    change mixedMoment B node2331 node2331Labels = _
    exact sound2331 B hB hF
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2508 : mixedVector B (Sum.inr 2508) = Sparse.eval nodeValue2508 (mixedVector B) := by
    change mixedMoment B node2508 node2508Labels = _
    exact sound2508 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2330, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1127, h2331, h2493, h2508, h2512, h4092, reducedSource1897] using sourceEq2330 B hB

theorem rowSound1897 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1897 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1897, numericCheck1897, reducedZero1897 B hB hF, mul_zero]

theorem reducedZero1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1898 (mixedVector B) = 0 := by
  have h2847 : mixedVector B (Sum.inr 2847) = Sparse.eval nodeValue2847 (mixedVector B) := by
    change mixedMoment B node2847 node2847Labels = _
    exact sound2847 B hB hF
  have h2849 : mixedVector B (Sum.inr 2849) = Sparse.eval nodeValue2849 (mixedVector B) := by
    change mixedMoment B node2849 node2849Labels = _
    exact sound2849 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h2976 : mixedVector B (Sum.inr 2976) = Sparse.eval nodeValue2976 (mixedVector B) := by
    change mixedMoment B node2976 node2976Labels = _
    exact sound2976 B hB hF
  have h3945 : mixedVector B (Sum.inr 3945) = Sparse.eval nodeValue3945 (mixedVector B) := by
    change mixedMoment B node3945 node3945Labels = _
    exact sound3945 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2331, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2847, h2849, h2884, h2976, h3945, h4091, reducedSource1898] using sourceEq2331 B hB

theorem rowSound1898 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1898 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1898, numericCheck1898, reducedZero1898 B hB hF, mul_zero]

theorem reducedZero1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1899 (mixedVector B) = 0 := by
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2846 : mixedVector B (Sum.inr 2846) = Sparse.eval nodeValue2846 (mixedVector B) := by
    change mixedMoment B node2846 node2846Labels = _
    exact sound2846 B hB hF
  have h2848 : mixedVector B (Sum.inr 2848) = Sparse.eval nodeValue2848 (mixedVector B) := by
    change mixedMoment B node2848 node2848Labels = _
    exact sound2848 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2333, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2426, h2846, h2848, h2881, h2974, h3781, h4092, reducedSource1899] using sourceEq2333 B hB

theorem rowSound1899 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1899 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1899, numericCheck1899, reducedZero1899 B hB hF, mul_zero]

theorem reducedZero1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1900 (mixedVector B) = 0 := by
  have h1960 : mixedVector B (Sum.inr 1960) = Sparse.eval nodeValue1960 (mixedVector B) := by
    change mixedMoment B node1960 node1960Labels = _
    exact sound1960 B hB hF
  have h2427 : mixedVector B (Sum.inr 2427) = Sparse.eval nodeValue2427 (mixedVector B) := by
    change mixedMoment B node2427 node2427Labels = _
    exact sound2427 B hB hF
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h2552 : mixedVector B (Sum.inr 2552) = Sparse.eval nodeValue2552 (mixedVector B) := by
    change mixedMoment B node2552 node2552Labels = _
    exact sound2552 B hB hF
  have h3493 : mixedVector B (Sum.inr 3493) = Sparse.eval nodeValue3493 (mixedVector B) := by
    change mixedMoment B node3493 node3493Labels = _
    exact sound3493 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2334, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1960, h2427, h2509, h2552, h3493, h4084, reducedSource1900] using sourceEq2334 B hB

theorem rowSound1900 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1900 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1900, numericCheck1900, reducedZero1900 B hB hF, mul_zero]

theorem reducedZero1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1901 (mixedVector B) = 0 := by
  have h2426 : mixedVector B (Sum.inr 2426) = Sparse.eval nodeValue2426 (mixedVector B) := by
    change mixedMoment B node2426 node2426Labels = _
    exact sound2426 B hB hF
  have h2428 : mixedVector B (Sum.inr 2428) = Sparse.eval nodeValue2428 (mixedVector B) := by
    change mixedMoment B node2428 node2428Labels = _
    exact sound2428 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2335, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2426, h2428, h2433, h2512, h2554, h3781, h4092, reducedSource1901] using sourceEq2335 B hB

theorem rowSound1901 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1901 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1901, numericCheck1901, reducedZero1901 B hB hF, mul_zero]

theorem reducedZero1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1902 (mixedVector B) = 0 := by
  have h2430 : mixedVector B (Sum.inr 2430) = Sparse.eval nodeValue2430 (mixedVector B) := by
    change mixedMoment B node2430 node2430Labels = _
    exact sound2430 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2433 : mixedVector B (Sum.inr 2433) = Sparse.eval nodeValue2433 (mixedVector B) := by
    change mixedMoment B node2433 node2433Labels = _
    exact sound2433 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h3782 : mixedVector B (Sum.inr 3782) = Sparse.eval nodeValue3782 (mixedVector B) := by
    change mixedMoment B node3782 node3782Labels = _
    exact sound3782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2336, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2430, h2431, h2433, h2515, h2557, h3782, h4092, reducedSource1902] using sourceEq2336 B hB

theorem rowSound1902 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1902 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1902, numericCheck1902, reducedZero1902 B hB hF, mul_zero]

theorem reducedZero1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1903 (mixedVector B) = 0 := by
  have h1335 : mixedVector B (Sum.inr 1335) = Sparse.eval nodeValue1335 (mixedVector B) := by
    change mixedMoment B node1335 node1335Labels = _
    exact sound1335 B hB hF
  have h2826 : mixedVector B (Sum.inr 2826) = Sparse.eval nodeValue2826 (mixedVector B) := by
    change mixedMoment B node2826 node2826Labels = _
    exact sound2826 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h2951 : mixedVector B (Sum.inr 2951) = Sparse.eval nodeValue2951 (mixedVector B) := by
    change mixedMoment B node2951 node2951Labels = _
    exact sound2951 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2337, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1335, h2826, h2924, h2933, h2951, h2954, h4091, reducedSource1903] using sourceEq2337 B hB

theorem rowSound1903 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1903 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1903, numericCheck1903, reducedZero1903 B hB hF, mul_zero]

theorem sourceRowsAt1888 : MixedData.sourceRows (1888 : Fin 2425) =
    MixedData.row1888 := by decide +kernel

theorem sourceRowsAt1889 : MixedData.sourceRows (1889 : Fin 2425) =
    MixedData.row1889 := by decide +kernel

theorem sourceRowsAt1890 : MixedData.sourceRows (1890 : Fin 2425) =
    MixedData.row1890 := by decide +kernel

theorem sourceRowsAt1891 : MixedData.sourceRows (1891 : Fin 2425) =
    MixedData.row1891 := by decide +kernel

theorem sourceRowsAt1892 : MixedData.sourceRows (1892 : Fin 2425) =
    MixedData.row1892 := by decide +kernel

theorem sourceRowsAt1893 : MixedData.sourceRows (1893 : Fin 2425) =
    MixedData.row1893 := by decide +kernel

theorem sourceRowsAt1894 : MixedData.sourceRows (1894 : Fin 2425) =
    MixedData.row1894 := by decide +kernel

theorem sourceRowsAt1895 : MixedData.sourceRows (1895 : Fin 2425) =
    MixedData.row1895 := by decide +kernel

theorem sourceRowsAt1896 : MixedData.sourceRows (1896 : Fin 2425) =
    MixedData.row1896 := by decide +kernel

theorem sourceRowsAt1897 : MixedData.sourceRows (1897 : Fin 2425) =
    MixedData.row1897 := by decide +kernel

theorem sourceRowsAt1898 : MixedData.sourceRows (1898 : Fin 2425) =
    MixedData.row1898 := by decide +kernel

theorem sourceRowsAt1899 : MixedData.sourceRows (1899 : Fin 2425) =
    MixedData.row1899 := by decide +kernel

theorem sourceRowsAt1900 : MixedData.sourceRows (1900 : Fin 2425) =
    MixedData.row1900 := by decide +kernel

theorem sourceRowsAt1901 : MixedData.sourceRows (1901 : Fin 2425) =
    MixedData.row1901 := by decide +kernel

theorem sourceRowsAt1902 : MixedData.sourceRows (1902 : Fin 2425) =
    MixedData.row1902 := by decide +kernel

theorem sourceRowsAt1903 : MixedData.sourceRows (1903 : Fin 2425) =
    MixedData.row1903 := by decide +kernel

theorem chunkSound118_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 118) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1888 ∨ k.val = 1889 ∨ k.val = 1890 ∨ k.val = 1891 ∨ k.val = 1892 ∨ k.val = 1893 ∨ k.val = 1894 ∨ k.val = 1895 ∨ k.val = 1896 ∨ k.val = 1897 ∨ k.val = 1898 ∨ k.val = 1899 ∨ k.val = 1900 ∨ k.val = 1901 ∨ k.val = 1902 ∨ k.val = 1903 := by omega
  rcases heq with h1888 | h1889 | h1890 | h1891 | h1892 | h1893 | h1894 | h1895 | h1896 | h1897 | h1898 | h1899 | h1900 | h1901 | h1902 | h1903
  · have he : k = (1888 : Fin 2425) := Fin.ext h1888
    subst k
    rw [sourceRowsAt1888]
    exact rowSound1888 B hB hF
  · have he : k = (1889 : Fin 2425) := Fin.ext h1889
    subst k
    rw [sourceRowsAt1889]
    exact rowSound1889 B hB hF
  · have he : k = (1890 : Fin 2425) := Fin.ext h1890
    subst k
    rw [sourceRowsAt1890]
    exact rowSound1890 B hB hF
  · have he : k = (1891 : Fin 2425) := Fin.ext h1891
    subst k
    rw [sourceRowsAt1891]
    exact rowSound1891 B hB hF
  · have he : k = (1892 : Fin 2425) := Fin.ext h1892
    subst k
    rw [sourceRowsAt1892]
    exact rowSound1892 B hB hF
  · have he : k = (1893 : Fin 2425) := Fin.ext h1893
    subst k
    rw [sourceRowsAt1893]
    exact rowSound1893 B hB hF
  · have he : k = (1894 : Fin 2425) := Fin.ext h1894
    subst k
    rw [sourceRowsAt1894]
    exact rowSound1894 B hB hF
  · have he : k = (1895 : Fin 2425) := Fin.ext h1895
    subst k
    rw [sourceRowsAt1895]
    exact rowSound1895 B hB hF
  · have he : k = (1896 : Fin 2425) := Fin.ext h1896
    subst k
    rw [sourceRowsAt1896]
    exact rowSound1896 B hB hF
  · have he : k = (1897 : Fin 2425) := Fin.ext h1897
    subst k
    rw [sourceRowsAt1897]
    exact rowSound1897 B hB hF
  · have he : k = (1898 : Fin 2425) := Fin.ext h1898
    subst k
    rw [sourceRowsAt1898]
    exact rowSound1898 B hB hF
  · have he : k = (1899 : Fin 2425) := Fin.ext h1899
    subst k
    rw [sourceRowsAt1899]
    exact rowSound1899 B hB hF
  · have he : k = (1900 : Fin 2425) := Fin.ext h1900
    subst k
    rw [sourceRowsAt1900]
    exact rowSound1900 B hB hF
  · have he : k = (1901 : Fin 2425) := Fin.ext h1901
    subst k
    rw [sourceRowsAt1901]
    exact rowSound1901 B hB hF
  · have he : k = (1902 : Fin 2425) := Fin.ext h1902
    subst k
    rw [sourceRowsAt1902]
    exact rowSound1902 B hB hF
  · have he : k = (1903 : Fin 2425) := Fin.ext h1903
    subst k
    rw [sourceRowsAt1903]
    exact rowSound1903 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound118_e_oai
