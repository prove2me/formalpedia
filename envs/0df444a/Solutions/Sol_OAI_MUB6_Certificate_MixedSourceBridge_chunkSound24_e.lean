-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:30:16.29+00:00
-- url     : https://prove2.me/submissions/4e9e630a-3380-481c-810e-31a7412ace5d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E117
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound388_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound391_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound392_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound395_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound396_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4744 raw4744Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw4744 raw4744Labels = mixedMoment B raw4744step0 raw4744step0Labels := by
      have hz : ∀ j, raw4744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4744step0 = (fun i j => raw4744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4744step0 raw4744; decide +kernel
      have hl : raw4744step0Labels = raw4744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744 raw4744Labels permutation346 hz
    mixedMoment B raw4744step0 raw4744step0Labels = mixedMoment B raw4744step1 raw4744step1Labels := by
      have hz : ∀ j, raw4744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4744step1 = (fun i j => raw4744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4744step1 raw4744step0; decide +kernel
      have hl : raw4744step1Labels = raw4744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744step0 raw4744step0Labels permutation56 hz
    mixedMoment B raw4744step1 raw4744step1Labels = mixedMoment B raw4744step2 raw4744step2Labels := by
      have ha : raw4744step2 = (fun i j => raw4744step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4744step2 raw4744step1; decide +kernel
      have hl : raw4744step2Labels = raw4744step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4744step1 raw4744step1Labels permutation26 permutation0
    mixedMoment B raw4744step2 raw4744step2Labels = mixedMoment B raw4744step3 raw4744step3Labels := by
      have ha : raw4744step3 = -raw4744step2 := by apply Matrix.ext; change ∀ i j, raw4744step3 i j = -(raw4744step2 i j); unfold raw4744step3 raw4744step2; decide +kernel
      have hl : raw4744step3Labels = raw4744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical4756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4756 raw4756Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw4756 raw4756Labels = mixedMoment B raw4756step0 raw4756step0Labels := by
      have hz : ∀ j, raw4756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4756step0 = (fun i j => raw4756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4756step0 raw4756; decide +kernel
      have hl : raw4756step0Labels = raw4756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4756 raw4756Labels permutation346 hz
    mixedMoment B raw4756step0 raw4756step0Labels = mixedMoment B raw4756step1 raw4756step1Labels := by
      have ha : raw4756step1 = (fun i j => raw4756step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4756step1 raw4756step0; decide +kernel
      have hl : raw4756step1Labels = raw4756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4756step0 raw4756step0Labels permutation151 permutation2
    mixedMoment B raw4756step1 raw4756step1Labels = mixedMoment B raw4756step2 raw4756step2Labels := by
      have ha : raw4756step2 = -raw4756step1 := by apply Matrix.ext; change ∀ i j, raw4756step2 i j = -(raw4756step1 i j); unfold raw4756step2 raw4756step1; decide +kernel
      have hl : raw4756step2Labels = raw4756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

theorem canonical4760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4760 raw4760Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw4760 raw4760Labels = mixedMoment B raw4760step0 raw4760step0Labels := by
      have hz : ∀ j, raw4760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4760step0 = (fun i j => raw4760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4760step0 raw4760; decide +kernel
      have hl : raw4760step0Labels = raw4760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4760 raw4760Labels permutation346 hz
    mixedMoment B raw4760step0 raw4760step0Labels = mixedMoment B raw4760step1 raw4760step1Labels := by
      have hz : ∀ j, raw4760step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4760step1 = (fun i j => raw4760step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4760step1 raw4760step0; decide +kernel
      have hl : raw4760step1Labels = raw4760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4760step0 raw4760step0Labels permutation56 hz
    mixedMoment B raw4760step1 raw4760step1Labels = mixedMoment B raw4760step2 raw4760step2Labels := by
      have ha : raw4760step2 = (fun i j => raw4760step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4760step2 raw4760step1; decide +kernel
      have hl : raw4760step2Labels = raw4760step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4760step1 raw4760step1Labels permutation10 permutation2
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical4762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4762 raw4762Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4762 raw4762Labels = mixedMoment B raw4762step0 raw4762step0Labels := by
      have hz : ∀ j, raw4762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4762step0 = (fun i j => raw4762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4762step0 raw4762; decide +kernel
      have hl : raw4762step0Labels = raw4762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762 raw4762Labels permutation346 hz
    mixedMoment B raw4762step0 raw4762step0Labels = mixedMoment B raw4762step1 raw4762step1Labels := by
      have hz : ∀ j, raw4762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4762step1 = (fun i j => raw4762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4762step1 raw4762step0; decide +kernel
      have hl : raw4762step1Labels = raw4762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762step0 raw4762step0Labels permutation56 hz
    mixedMoment B raw4762step1 raw4762step1Labels = mixedMoment B raw4762step2 raw4762step2Labels := by
      have ha : raw4762step2 = (fun i j => raw4762step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4762step2 raw4762step1; decide +kernel
      have hl : raw4762step2Labels = raw4762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4762step1 raw4762step1Labels permutation31 permutation2
    mixedMoment B raw4762step2 raw4762step2Labels = mixedMoment B raw4762step3 raw4762step3Labels := by
      have ha : raw4762step3 = -raw4762step2 := by apply Matrix.ext; change ∀ i j, raw4762step3 i j = -(raw4762step2 i j); unfold raw4762step3 raw4762step2; decide +kernel
      have hl : raw4762step3Labels = raw4762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5754 raw5754Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5754 raw5754Labels = mixedMoment B raw5754step0 raw5754step0Labels := by
      have hz : ∀ j, raw5754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5754step0 = (fun i j => raw5754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5754step0 raw5754; decide +kernel
      have hl : raw5754step0Labels = raw5754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754 raw5754Labels permutation434 hz
    mixedMoment B raw5754step0 raw5754step0Labels = mixedMoment B raw5754step1 raw5754step1Labels := by
      have hz : ∀ j, raw5754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5754step1 = (fun i j => raw5754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5754step1 raw5754step0; decide +kernel
      have hl : raw5754step1Labels = raw5754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step0 raw5754step0Labels permutation80 hz
    mixedMoment B raw5754step1 raw5754step1Labels = mixedMoment B raw5754step2 raw5754step2Labels := by
      have hz : ∀ j, raw5754step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5754step2 = (fun i j => raw5754step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5754step2 raw5754step1; decide +kernel
      have hl : raw5754step2Labels = raw5754step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5754step1 raw5754step1Labels permutation14 hz
    mixedMoment B raw5754step2 raw5754step2Labels = mixedMoment B raw5754step3 raw5754step3Labels := by
      have ha : raw5754step3 = -raw5754step2 := by apply Matrix.ext; change ∀ i j, raw5754step3 i j = -(raw5754step2 i j); unfold raw5754step3 raw5754step2; decide +kernel
      have hl : raw5754step3Labels = raw5754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6438 raw6438Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw6438 raw6438Labels = mixedMoment B raw6438step0 raw6438step0Labels := by
      have hz : ∀ j, raw6438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6438step0 = (fun i j => raw6438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6438step0 raw6438; decide +kernel
      have hl : raw6438step0Labels = raw6438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6438 raw6438Labels permutation346 hz
    mixedMoment B raw6438step0 raw6438step0Labels = mixedMoment B raw6438step1 raw6438step1Labels := by
      have ha : raw6438step1 = (fun i j => raw6438step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6438step1 raw6438step0; decide +kernel
      have hl : raw6438step1Labels = raw6438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6438step0 raw6438step0Labels permutation139 permutation2
    _ = mixedMoment B node2588 node2588Labels := by rfl

theorem canonical6439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6439 raw6439Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw6439 raw6439Labels = mixedMoment B raw6439step0 raw6439step0Labels := by
      have hz : ∀ j, raw6439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6439step0 = (fun i j => raw6439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6439step0 raw6439; decide +kernel
      have hl : raw6439step0Labels = raw6439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6439 raw6439Labels permutation346 hz
    mixedMoment B raw6439step0 raw6439step0Labels = mixedMoment B raw6439step1 raw6439step1Labels := by
      have hz : ∀ j, raw6439step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6439step1 = (fun i j => raw6439step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6439step1 raw6439step0; decide +kernel
      have hl : raw6439step1Labels = raw6439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6439step0 raw6439step0Labels permutation56 hz
    mixedMoment B raw6439step1 raw6439step1Labels = mixedMoment B raw6439step2 raw6439step2Labels := by
      have ha : raw6439step2 = (fun i j => raw6439step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6439step2 raw6439step1; decide +kernel
      have hl : raw6439step2Labels = raw6439step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6439step1 raw6439step1Labels permutation12 permutation4
    mixedMoment B raw6439step2 raw6439step2Labels = mixedMoment B raw6439step3 raw6439step3Labels := by
      have ha : raw6439step3 = -raw6439step2 := by apply Matrix.ext; change ∀ i j, raw6439step3 i j = -(raw6439step2 i j); unfold raw6439step3 raw6439step2; decide +kernel
      have hl : raw6439step3Labels = raw6439step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical6446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6446 raw6446Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw6446 raw6446Labels = mixedMoment B raw6446step0 raw6446step0Labels := by
      have hz : ∀ j, raw6446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6446step0 = (fun i j => raw6446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6446step0 raw6446; decide +kernel
      have hl : raw6446step0Labels = raw6446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6446 raw6446Labels permutation346 hz
    mixedMoment B raw6446step0 raw6446step0Labels = mixedMoment B raw6446step1 raw6446step1Labels := by
      have hz : ∀ j, raw6446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6446step1 = (fun i j => raw6446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6446step1 raw6446step0; decide +kernel
      have hl : raw6446step1Labels = raw6446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6446step0 raw6446step0Labels permutation56 hz
    mixedMoment B raw6446step1 raw6446step1Labels = mixedMoment B raw6446step2 raw6446step2Labels := by
      have ha : raw6446step2 = (fun i j => raw6446step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6446step2 raw6446step1; decide +kernel
      have hl : raw6446step2Labels = raw6446step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6446step1 raw6446step1Labels permutation31 permutation2
    _ = mixedMoment B node2781 node2781Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7695 raw7695Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw7695 raw7695Labels = mixedMoment B raw7695step0 raw7695step0Labels := by
      have hz : ∀ j, raw7695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7695step0 = (fun i j => raw7695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7695step0 raw7695; decide +kernel
      have hl : raw7695step0Labels = raw7695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695 raw7695Labels permutation434 hz
    mixedMoment B raw7695step0 raw7695step0Labels = mixedMoment B raw7695step1 raw7695step1Labels := by
      have hz : ∀ j, raw7695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7695step1 = (fun i j => raw7695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7695step1 raw7695step0; decide +kernel
      have hl : raw7695step1Labels = raw7695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695step0 raw7695step0Labels permutation80 hz
    mixedMoment B raw7695step1 raw7695step1Labels = mixedMoment B raw7695step2 raw7695step2Labels := by
      have hz : ∀ j, raw7695step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw7695step2 = (fun i j => raw7695step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw7695step2 raw7695step1; decide +kernel
      have hl : raw7695step2Labels = raw7695step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7695step1 raw7695step1Labels permutation14 hz
    mixedMoment B raw7695step2 raw7695step2Labels = mixedMoment B raw7695step3 raw7695step3Labels := by
      have ha : raw7695step3 = (fun i j => raw7695step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7695step3 raw7695step2; decide +kernel
      have hl : raw7695step3Labels = raw7695step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7695step2 raw7695step2Labels permutation7 permutation2
    _ = mixedMoment B node2783 node2783Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8253 raw8253Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw8253 raw8253Labels = mixedMoment B raw8253step0 raw8253step0Labels := by
      have hz : ∀ j, raw8253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8253step0 = (fun i j => raw8253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8253step0 raw8253; decide +kernel
      have hl : raw8253step0Labels = raw8253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8253 raw8253Labels permutation346 hz
    mixedMoment B raw8253step0 raw8253step0Labels = mixedMoment B raw8253step1 raw8253step1Labels := by
      have hz : ∀ j, raw8253step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8253step1 = (fun i j => raw8253step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8253step1 raw8253step0; decide +kernel
      have hl : raw8253step1Labels = raw8253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8253step0 raw8253step0Labels permutation56 hz
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical8254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8254 raw8254Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8254 raw8254Labels = mixedMoment B raw8254step0 raw8254step0Labels := by
      have hz : ∀ j, raw8254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8254step0 = (fun i j => raw8254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8254step0 raw8254; decide +kernel
      have hl : raw8254step0Labels = raw8254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8254 raw8254Labels permutation346 hz
    mixedMoment B raw8254step0 raw8254step0Labels = mixedMoment B raw8254step1 raw8254step1Labels := by
      have ha : raw8254step1 = (fun i j => raw8254step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8254step1 raw8254step0; decide +kernel
      have hl : raw8254step1Labels = raw8254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8254step0 raw8254step0Labels permutation151 permutation2
    mixedMoment B raw8254step1 raw8254step1Labels = mixedMoment B raw8254step2 raw8254step2Labels := by
      have ha : raw8254step2 = -raw8254step1 := by apply Matrix.ext; change ∀ i j, raw8254step2 i j = -(raw8254step1 i j); unfold raw8254step2 raw8254step1; decide +kernel
      have hl : raw8254step2Labels = raw8254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

theorem canonical8256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8256 raw8256Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8256 raw8256Labels = mixedMoment B raw8256step0 raw8256step0Labels := by
      have hz : ∀ j, raw8256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8256step0 = (fun i j => raw8256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8256step0 raw8256; decide +kernel
      have hl : raw8256step0Labels = raw8256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8256 raw8256Labels permutation346 hz
    mixedMoment B raw8256step0 raw8256step0Labels = mixedMoment B raw8256step1 raw8256step1Labels := by
      have hz : ∀ j, raw8256step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8256step1 = (fun i j => raw8256step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8256step1 raw8256step0; decide +kernel
      have hl : raw8256step1Labels = raw8256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8256step0 raw8256step0Labels permutation56 hz
    mixedMoment B raw8256step1 raw8256step1Labels = mixedMoment B raw8256step2 raw8256step2Labels := by
      have ha : raw8256step2 = (fun i j => raw8256step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8256step2 raw8256step1; decide +kernel
      have hl : raw8256step2Labels = raw8256step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8256step1 raw8256step1Labels permutation31 permutation2
    mixedMoment B raw8256step2 raw8256step2Labels = mixedMoment B raw8256step3 raw8256step3Labels := by
      have ha : raw8256step3 = -raw8256step2 := by apply Matrix.ext; change ∀ i j, raw8256step3 i j = -(raw8256step2 i j); unfold raw8256step3 raw8256step2; decide +kernel
      have hl : raw8256step3Labels = raw8256step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

theorem canonical8260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8260 raw8260Labels = mixedMoment B node1440 node1440Labels := by
  calc
    mixedMoment B raw8260 raw8260Labels = mixedMoment B raw8260step0 raw8260step0Labels := by
      have hz : ∀ j, raw8260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8260step0 = (fun i j => raw8260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8260step0 raw8260; decide +kernel
      have hl : raw8260step0Labels = raw8260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8260 raw8260Labels permutation346 hz
    mixedMoment B raw8260step0 raw8260step0Labels = mixedMoment B raw8260step1 raw8260step1Labels := by
      have hz : ∀ j, raw8260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8260step1 = (fun i j => raw8260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8260step1 raw8260step0; decide +kernel
      have hl : raw8260step1Labels = raw8260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8260step0 raw8260step0Labels permutation56 hz
    _ = mixedMoment B node1440 node1440Labels := by rfl

theorem canonical8261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8261 raw8261Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw8261 raw8261Labels = mixedMoment B raw8261step0 raw8261step0Labels := by
      have hz : ∀ j, raw8261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8261step0 = (fun i j => raw8261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8261step0 raw8261; decide +kernel
      have hl : raw8261step0Labels = raw8261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8261 raw8261Labels permutation346 hz
    mixedMoment B raw8261step0 raw8261step0Labels = mixedMoment B raw8261step1 raw8261step1Labels := by
      have hz : ∀ j, raw8261step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8261step1 = (fun i j => raw8261step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8261step1 raw8261step0; decide +kernel
      have hl : raw8261step1Labels = raw8261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8261step0 raw8261step0Labels permutation56 hz
    _ = mixedMoment B node1418 node1418Labels := by rfl

theorem canonical8263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8263 raw8263Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8263 raw8263Labels = mixedMoment B raw8263step0 raw8263step0Labels := by
      have hz : ∀ j, raw8263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8263step0 = (fun i j => raw8263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8263step0 raw8263; decide +kernel
      have hl : raw8263step0Labels = raw8263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8263 raw8263Labels permutation346 hz
    mixedMoment B raw8263step0 raw8263step0Labels = mixedMoment B raw8263step1 raw8263step1Labels := by
      have ha : raw8263step1 = (fun i j => raw8263step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8263step1 raw8263step0; decide +kernel
      have hl : raw8263step1Labels = raw8263step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8263step0 raw8263step0Labels permutation40 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

theorem canonical8265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8265 raw8265Labels = mixedMoment B node2983 node2983Labels := by
  calc
    mixedMoment B raw8265 raw8265Labels = mixedMoment B raw8265step0 raw8265step0Labels := by
      have ha : raw8265step0 = (fun i j => raw8265 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8265step0 raw8265; decide +kernel
      have hl : raw8265step0Labels = raw8265Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8265 raw8265Labels permutation160 permutation2
    _ = mixedMoment B node2983 node2983Labels := by rfl

theorem canonical8266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8266 raw8266Labels = mixedMoment B node2995 node2995Labels := by
  calc
    mixedMoment B raw8266 raw8266Labels = mixedMoment B raw8266step0 raw8266step0Labels := by
      have hz : ∀ j, raw8266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8266step0 = (fun i j => raw8266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8266step0 raw8266; decide +kernel
      have hl : raw8266step0Labels = raw8266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8266 raw8266Labels permutation346 hz
    _ = mixedMoment B node2995 node2995Labels := by rfl

theorem canonical8267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8267 raw8267Labels = mixedMoment B node2962 node2962Labels := by
  calc
    mixedMoment B raw8267 raw8267Labels = mixedMoment B raw8267step0 raw8267step0Labels := by
      have hz : ∀ j, raw8267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8267step0 = (fun i j => raw8267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8267step0 raw8267; decide +kernel
      have hl : raw8267step0Labels = raw8267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8267 raw8267Labels permutation346 hz
    mixedMoment B raw8267step0 raw8267step0Labels = mixedMoment B raw8267step1 raw8267step1Labels := by
      have ha : raw8267step1 = (fun i j => raw8267step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8267step1 raw8267step0; decide +kernel
      have hl : raw8267step1Labels = raw8267step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8267step0 raw8267step0Labels permutation119 permutation4
    _ = mixedMoment B node2962 node2962Labels := by rfl

theorem canonical8268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8268 raw8268Labels = mixedMoment B node2995 node2995Labels := by
  calc
    mixedMoment B raw8268 raw8268Labels = mixedMoment B raw8268step0 raw8268step0Labels := by
      have hz : ∀ j, raw8268 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8268step0 = (fun i j => raw8268 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8268step0 raw8268; decide +kernel
      have hl : raw8268step0Labels = raw8268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8268 raw8268Labels permutation265 hz
    _ = mixedMoment B node2995 node2995Labels := by rfl

theorem canonical8269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8269 raw8269Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw8269 raw8269Labels = mixedMoment B raw8269step0 raw8269step0Labels := by
      have hz : ∀ j, raw8269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8269step0 = (fun i j => raw8269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8269step0 raw8269; decide +kernel
      have hl : raw8269step0Labels = raw8269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8269 raw8269Labels permutation346 hz
    mixedMoment B raw8269step0 raw8269step0Labels = mixedMoment B raw8269step1 raw8269step1Labels := by
      have hz : ∀ j, raw8269step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8269step1 = (fun i j => raw8269step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8269step1 raw8269step0; decide +kernel
      have hl : raw8269step1Labels = raw8269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8269step0 raw8269step0Labels permutation56 hz
    _ = mixedMoment B node3118 node3118Labels := by rfl

theorem canonical8270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8270 raw8270Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8270 raw8270Labels = mixedMoment B raw8270step0 raw8270step0Labels := by
      have hz : ∀ j, raw8270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8270step0 = (fun i j => raw8270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8270step0 raw8270; decide +kernel
      have hl : raw8270step0Labels = raw8270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8270 raw8270Labels permutation265 hz
    mixedMoment B raw8270step0 raw8270step0Labels = mixedMoment B raw8270step1 raw8270step1Labels := by
      have ha : raw8270step1 = (fun i j => raw8270step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8270step1 raw8270step0; decide +kernel
      have hl : raw8270step1Labels = raw8270step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8270step0 raw8270step0Labels permutation40 permutation2
    _ = mixedMoment B node2952 node2952Labels := by rfl

theorem canonical8271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8271 raw8271Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw8271 raw8271Labels = mixedMoment B raw8271step0 raw8271step0Labels := by
      have hz : ∀ j, raw8271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8271step0 = (fun i j => raw8271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8271step0 raw8271; decide +kernel
      have hl : raw8271step0Labels = raw8271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8271 raw8271Labels permutation346 hz
    mixedMoment B raw8271step0 raw8271step0Labels = mixedMoment B raw8271step1 raw8271step1Labels := by
      have hz : ∀ j, raw8271step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8271step1 = (fun i j => raw8271step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8271step1 raw8271step0; decide +kernel
      have hl : raw8271step1Labels = raw8271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8271step0 raw8271step0Labels permutation56 hz
    _ = mixedMoment B node2967 node2967Labels := by rfl

theorem canonical8272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8272 raw8272Labels = mixedMoment B node2962 node2962Labels := by
  calc
    mixedMoment B raw8272 raw8272Labels = mixedMoment B raw8272step0 raw8272step0Labels := by
      have hz : ∀ j, raw8272 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8272step0 = (fun i j => raw8272 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8272step0 raw8272; decide +kernel
      have hl : raw8272step0Labels = raw8272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8272 raw8272Labels permutation265 hz
    mixedMoment B raw8272step0 raw8272step0Labels = mixedMoment B raw8272step1 raw8272step1Labels := by
      have ha : raw8272step1 = (fun i j => raw8272step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8272step1 raw8272step0; decide +kernel
      have hl : raw8272step1Labels = raw8272step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8272step0 raw8272step0Labels permutation119 permutation4
    _ = mixedMoment B node2962 node2962Labels := by rfl

theorem canonical8273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8273 raw8273Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw8273 raw8273Labels = mixedMoment B raw8273step0 raw8273step0Labels := by
      have hz : ∀ j, raw8273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8273step0 = (fun i j => raw8273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8273step0 raw8273; decide +kernel
      have hl : raw8273step0Labels = raw8273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8273 raw8273Labels permutation346 hz
    mixedMoment B raw8273step0 raw8273step0Labels = mixedMoment B raw8273step1 raw8273step1Labels := by
      have hz : ∀ j, raw8273step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8273step1 = (fun i j => raw8273step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8273step1 raw8273step0; decide +kernel
      have hl : raw8273step1Labels = raw8273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8273step0 raw8273step0Labels permutation56 hz
    mixedMoment B raw8273step1 raw8273step1Labels = mixedMoment B raw8273step2 raw8273step2Labels := by
      have ha : raw8273step2 = (fun i j => raw8273step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8273step2 raw8273step1; decide +kernel
      have hl : raw8273step2Labels = raw8273step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8273step1 raw8273step1Labels permutation22 permutation4
    _ = mixedMoment B node2967 node2967Labels := by rfl

theorem canonical8315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8315 raw8315Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw8315 raw8315Labels = mixedMoment B raw8315step0 raw8315step0Labels := by
      have hz : ∀ j, raw8315 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8315step0 = (fun i j => raw8315 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8315step0 raw8315; decide +kernel
      have hl : raw8315step0Labels = raw8315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8315 raw8315Labels permutation265 hz
    mixedMoment B raw8315step0 raw8315step0Labels = mixedMoment B raw8315step1 raw8315step1Labels := by
      have ha : raw8315step1 = (fun i j => raw8315step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8315step1 raw8315step0; decide +kernel
      have hl : raw8315step1Labels = raw8315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8315step0 raw8315step0Labels permutation139 permutation2
    _ = mixedMoment B node2588 node2588Labels := by rfl

theorem canonical8316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8316 raw8316Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw8316 raw8316Labels = mixedMoment B raw8316step0 raw8316step0Labels := by
      have hz : ∀ j, raw8316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8316step0 = (fun i j => raw8316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8316step0 raw8316; decide +kernel
      have hl : raw8316step0Labels = raw8316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8316 raw8316Labels permutation346 hz
    mixedMoment B raw8316step0 raw8316step0Labels = mixedMoment B raw8316step1 raw8316step1Labels := by
      have hz : ∀ j, raw8316step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8316step1 = (fun i j => raw8316step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8316step1 raw8316step0; decide +kernel
      have hl : raw8316step1Labels = raw8316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8316step0 raw8316step0Labels permutation56 hz
    mixedMoment B raw8316step1 raw8316step1Labels = mixedMoment B raw8316step2 raw8316step2Labels := by
      have ha : raw8316step2 = (fun i j => raw8316step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8316step2 raw8316step1; decide +kernel
      have hl : raw8316step2Labels = raw8316step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8316step1 raw8316step1Labels permutation31 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical8317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8317 raw8317Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw8317 raw8317Labels = mixedMoment B raw8317step0 raw8317step0Labels := by
      have hz : ∀ j, raw8317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8317step0 = (fun i j => raw8317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8317step0 raw8317; decide +kernel
      have hl : raw8317step0Labels = raw8317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8317 raw8317Labels permutation346 hz
    mixedMoment B raw8317step0 raw8317step0Labels = mixedMoment B raw8317step1 raw8317step1Labels := by
      have hz : ∀ j, raw8317step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8317step1 = (fun i j => raw8317step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8317step1 raw8317step0; decide +kernel
      have hl : raw8317step1Labels = raw8317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8317step0 raw8317step0Labels permutation56 hz
    mixedMoment B raw8317step1 raw8317step1Labels = mixedMoment B raw8317step2 raw8317step2Labels := by
      have ha : raw8317step2 = (fun i j => raw8317step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8317step2 raw8317step1; decide +kernel
      have hl : raw8317step2Labels = raw8317step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8317step1 raw8317step1Labels permutation31 permutation2
    _ = mixedMoment B node1292 node1292Labels := by rfl

theorem canonical8318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8318 raw8318Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw8318 raw8318Labels = mixedMoment B raw8318step0 raw8318step0Labels := by
      have hz : ∀ j, raw8318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8318step0 = (fun i j => raw8318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8318step0 raw8318; decide +kernel
      have hl : raw8318step0Labels = raw8318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8318 raw8318Labels permutation346 hz
    mixedMoment B raw8318step0 raw8318step0Labels = mixedMoment B raw8318step1 raw8318step1Labels := by
      have ha : raw8318step1 = (fun i j => raw8318step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8318step1 raw8318step0; decide +kernel
      have hl : raw8318step1Labels = raw8318step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8318step0 raw8318step0Labels permutation50 permutation4
    mixedMoment B raw8318step1 raw8318step1Labels = mixedMoment B raw8318step2 raw8318step2Labels := by
      have ha : raw8318step2 = -raw8318step1 := by apply Matrix.ext; change ∀ i j, raw8318step2 i j = -(raw8318step1 i j); unfold raw8318step2 raw8318step1; decide +kernel
      have hl : raw8318step2Labels = raw8318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2132 node2132Labels := by rfl

theorem canonical8319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8319 raw8319Labels = mixedMoment B node2132 node2132Labels := by
  calc
    mixedMoment B raw8319 raw8319Labels = mixedMoment B raw8319step0 raw8319step0Labels := by
      have hz : ∀ j, raw8319 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8319step0 = (fun i j => raw8319 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8319step0 raw8319; decide +kernel
      have hl : raw8319step0Labels = raw8319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8319 raw8319Labels permutation265 hz
    mixedMoment B raw8319step0 raw8319step0Labels = mixedMoment B raw8319step1 raw8319step1Labels := by
      have ha : raw8319step1 = (fun i j => raw8319step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8319step1 raw8319step0; decide +kernel
      have hl : raw8319step1Labels = raw8319step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8319step0 raw8319step0Labels permutation50 permutation4
    mixedMoment B raw8319step1 raw8319step1Labels = mixedMoment B raw8319step2 raw8319step2Labels := by
      have ha : raw8319step2 = -raw8319step1 := by apply Matrix.ext; change ∀ i j, raw8319step2 i j = -(raw8319step1 i j); unfold raw8319step2 raw8319step1; decide +kernel
      have hl : raw8319step2Labels = raw8319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2132 node2132Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8320 raw8320Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw8320 raw8320Labels = mixedMoment B raw8320step0 raw8320step0Labels := by
      have hz : ∀ j, raw8320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8320step0 = (fun i j => raw8320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8320step0 raw8320; decide +kernel
      have hl : raw8320step0Labels = raw8320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8320 raw8320Labels permutation346 hz
    mixedMoment B raw8320step0 raw8320step0Labels = mixedMoment B raw8320step1 raw8320step1Labels := by
      have hz : ∀ j, raw8320step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8320step1 = (fun i j => raw8320step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8320step1 raw8320step0; decide +kernel
      have hl : raw8320step1Labels = raw8320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8320step0 raw8320step0Labels permutation56 hz
    mixedMoment B raw8320step1 raw8320step1Labels = mixedMoment B raw8320step2 raw8320step2Labels := by
      have ha : raw8320step2 = (fun i j => raw8320step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8320step2 raw8320step1; decide +kernel
      have hl : raw8320step2Labels = raw8320step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8320step1 raw8320step1Labels permutation12 permutation4
    mixedMoment B raw8320step2 raw8320step2Labels = mixedMoment B raw8320step3 raw8320step3Labels := by
      have ha : raw8320step3 = -raw8320step2 := by apply Matrix.ext; change ∀ i j, raw8320step3 i j = -(raw8320step2 i j); unfold raw8320step3 raw8320step2; decide +kernel
      have hl : raw8320step3Labels = raw8320step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2138 node2138Labels := by rfl

theorem canonical8321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8321 raw8321Labels = mixedMoment B node2134 node2134Labels := by
  calc
    mixedMoment B raw8321 raw8321Labels = mixedMoment B raw8321step0 raw8321step0Labels := by
      have hz : ∀ j, raw8321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8321step0 = (fun i j => raw8321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8321step0 raw8321; decide +kernel
      have hl : raw8321step0Labels = raw8321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8321 raw8321Labels permutation346 hz
    mixedMoment B raw8321step0 raw8321step0Labels = mixedMoment B raw8321step1 raw8321step1Labels := by
      have hz : ∀ j, raw8321step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8321step1 = (fun i j => raw8321step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8321step1 raw8321step0; decide +kernel
      have hl : raw8321step1Labels = raw8321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8321step0 raw8321step0Labels permutation56 hz
    mixedMoment B raw8321step1 raw8321step1Labels = mixedMoment B raw8321step2 raw8321step2Labels := by
      have ha : raw8321step2 = (fun i j => raw8321step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8321step2 raw8321step1; decide +kernel
      have hl : raw8321step2Labels = raw8321step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8321step1 raw8321step1Labels permutation12 permutation4
    mixedMoment B raw8321step2 raw8321step2Labels = mixedMoment B raw8321step3 raw8321step3Labels := by
      have ha : raw8321step3 = -raw8321step2 := by apply Matrix.ext; change ∀ i j, raw8321step3 i j = -(raw8321step2 i j); unfold raw8321step3 raw8321step2; decide +kernel
      have hl : raw8321step3Labels = raw8321step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2134 node2134Labels := by rfl

theorem canonical8416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8416 raw8416Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8416 raw8416Labels = mixedMoment B raw8416step0 raw8416step0Labels := by
      have hz : ∀ j, raw8416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8416step0 = (fun i j => raw8416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8416step0 raw8416; decide +kernel
      have hl : raw8416step0Labels = raw8416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8416 raw8416Labels permutation346 hz
    mixedMoment B raw8416step0 raw8416step0Labels = mixedMoment B raw8416step1 raw8416step1Labels := by
      have hz : ∀ j, raw8416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8416step1 = (fun i j => raw8416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8416step1 raw8416step0; decide +kernel
      have hl : raw8416step1Labels = raw8416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8416step0 raw8416step0Labels permutation56 hz
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical8417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8417 raw8417Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw8417 raw8417Labels = mixedMoment B raw8417step0 raw8417step0Labels := by
      have hz : ∀ j, raw8417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8417step0 = (fun i j => raw8417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8417step0 raw8417; decide +kernel
      have hl : raw8417step0Labels = raw8417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8417 raw8417Labels permutation346 hz
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical8418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8418 raw8418Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw8418 raw8418Labels = mixedMoment B raw8418step0 raw8418step0Labels := by
      have hz : ∀ j, raw8418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8418step0 = (fun i j => raw8418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8418step0 raw8418; decide +kernel
      have hl : raw8418step0Labels = raw8418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8418 raw8418Labels permutation265 hz
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical8419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8419 raw8419Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8419 raw8419Labels = mixedMoment B raw8419step0 raw8419step0Labels := by
      have hz : ∀ j, raw8419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8419step0 = (fun i j => raw8419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8419step0 raw8419; decide +kernel
      have hl : raw8419step0Labels = raw8419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8419 raw8419Labels permutation346 hz
    mixedMoment B raw8419step0 raw8419step0Labels = mixedMoment B raw8419step1 raw8419step1Labels := by
      have hz : ∀ j, raw8419step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8419step1 = (fun i j => raw8419step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8419step1 raw8419step0; decide +kernel
      have hl : raw8419step1Labels = raw8419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8419step0 raw8419step0Labels permutation56 hz
    mixedMoment B raw8419step1 raw8419step1Labels = mixedMoment B raw8419step2 raw8419step2Labels := by
      have ha : raw8419step2 = (fun i j => raw8419step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8419step2 raw8419step1; decide +kernel
      have hl : raw8419step2Labels = raw8419step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8419step1 raw8419step1Labels permutation15 permutation4
    mixedMoment B raw8419step2 raw8419step2Labels = mixedMoment B raw8419step3 raw8419step3Labels := by
      have ha : raw8419step3 = -raw8419step2 := by apply Matrix.ext; change ∀ i j, raw8419step3 i j = -(raw8419step2 i j); unfold raw8419step3 raw8419step2; decide +kernel
      have hl : raw8419step3Labels = raw8419step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical8420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8420 raw8420Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw8420 raw8420Labels = mixedMoment B raw8420step0 raw8420step0Labels := by
      have hz : ∀ j, raw8420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8420step0 = (fun i j => raw8420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8420step0 raw8420; decide +kernel
      have hl : raw8420step0Labels = raw8420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8420 raw8420Labels permutation346 hz
    mixedMoment B raw8420step0 raw8420step0Labels = mixedMoment B raw8420step1 raw8420step1Labels := by
      have hz : ∀ j, raw8420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8420step1 = (fun i j => raw8420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8420step1 raw8420step0; decide +kernel
      have hl : raw8420step1Labels = raw8420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8420step0 raw8420step0Labels permutation56 hz
    mixedMoment B raw8420step1 raw8420step1Labels = mixedMoment B raw8420step2 raw8420step2Labels := by
      have ha : raw8420step2 = (fun i j => raw8420step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8420step2 raw8420step1; decide +kernel
      have hl : raw8420step2Labels = raw8420step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8420step1 raw8420step1Labels permutation10 permutation2
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical8421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8421 raw8421Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw8421 raw8421Labels = mixedMoment B raw8421step0 raw8421step0Labels := by
      have hz : ∀ j, raw8421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8421step0 = (fun i j => raw8421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8421step0 raw8421; decide +kernel
      have hl : raw8421step0Labels = raw8421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8421 raw8421Labels permutation346 hz
    mixedMoment B raw8421step0 raw8421step0Labels = mixedMoment B raw8421step1 raw8421step1Labels := by
      have hz : ∀ j, raw8421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8421step1 = (fun i j => raw8421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8421step1 raw8421step0; decide +kernel
      have hl : raw8421step1Labels = raw8421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8421step0 raw8421step0Labels permutation56 hz
    mixedMoment B raw8421step1 raw8421step1Labels = mixedMoment B raw8421step2 raw8421step2Labels := by
      have ha : raw8421step2 = (fun i j => raw8421step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8421step2 raw8421step1; decide +kernel
      have hl : raw8421step2Labels = raw8421step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8421step1 raw8421step1Labels permutation18 permutation4
    mixedMoment B raw8421step2 raw8421step2Labels = mixedMoment B raw8421step3 raw8421step3Labels := by
      have ha : raw8421step3 = -raw8421step2 := by apply Matrix.ext; change ∀ i j, raw8421step3 i j = -(raw8421step2 i j); unfold raw8421step3 raw8421step2; decide +kernel
      have hl : raw8421step3Labels = raw8421step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical8422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8422 raw8422Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8422 raw8422Labels = mixedMoment B raw8422step0 raw8422step0Labels := by
      have hz : ∀ j, raw8422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8422step0 = (fun i j => raw8422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8422step0 raw8422; decide +kernel
      have hl : raw8422step0Labels = raw8422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8422 raw8422Labels permutation346 hz
    mixedMoment B raw8422step0 raw8422step0Labels = mixedMoment B raw8422step1 raw8422step1Labels := by
      have hz : ∀ j, raw8422step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8422step1 = (fun i j => raw8422step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8422step1 raw8422step0; decide +kernel
      have hl : raw8422step1Labels = raw8422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8422step0 raw8422step0Labels permutation56 hz
    mixedMoment B raw8422step1 raw8422step1Labels = mixedMoment B raw8422step2 raw8422step2Labels := by
      have ha : raw8422step2 = (fun i j => raw8422step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8422step2 raw8422step1; decide +kernel
      have hl : raw8422step2Labels = raw8422step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8422step1 raw8422step1Labels permutation11 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8425 raw8425Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw8425 raw8425Labels = mixedMoment B raw8425step0 raw8425step0Labels := by
      have hz : ∀ j, raw8425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8425step0 = (fun i j => raw8425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8425step0 raw8425; decide +kernel
      have hl : raw8425step0Labels = raw8425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8425 raw8425Labels permutation346 hz
    mixedMoment B raw8425step0 raw8425step0Labels = mixedMoment B raw8425step1 raw8425step1Labels := by
      have hz : ∀ j, raw8425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8425step1 = (fun i j => raw8425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8425step1 raw8425step0; decide +kernel
      have hl : raw8425step1Labels = raw8425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8425step0 raw8425step0Labels permutation56 hz
    mixedMoment B raw8425step1 raw8425step1Labels = mixedMoment B raw8425step2 raw8425step2Labels := by
      have ha : raw8425step2 = (fun i j => raw8425step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8425step2 raw8425step1; decide +kernel
      have hl : raw8425step2Labels = raw8425step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8425step1 raw8425step1Labels permutation10 permutation2
    _ = mixedMoment B node1295 node1295Labels := by rfl

theorem canonical8429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8429 raw8429Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw8429 raw8429Labels = mixedMoment B raw8429step0 raw8429step0Labels := by
      have hz : ∀ j, raw8429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8429step0 = (fun i j => raw8429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8429step0 raw8429; decide +kernel
      have hl : raw8429step0Labels = raw8429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8429 raw8429Labels permutation346 hz
    mixedMoment B raw8429step0 raw8429step0Labels = mixedMoment B raw8429step1 raw8429step1Labels := by
      have ha : raw8429step1 = (fun i j => raw8429step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8429step1 raw8429step0; decide +kernel
      have hl : raw8429step1Labels = raw8429step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8429step0 raw8429step0Labels permutation34 permutation2
    _ = mixedMoment B node2591 node2591Labels := by rfl

theorem canonical8432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8432 raw8432Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw8432 raw8432Labels = mixedMoment B raw8432step0 raw8432step0Labels := by
      have hz : ∀ j, raw8432 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8432step0 = (fun i j => raw8432 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8432step0 raw8432; decide +kernel
      have hl : raw8432step0Labels = raw8432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8432 raw8432Labels permutation265 hz
    mixedMoment B raw8432step0 raw8432step0Labels = mixedMoment B raw8432step1 raw8432step1Labels := by
      have ha : raw8432step1 = (fun i j => raw8432step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8432step1 raw8432step0; decide +kernel
      have hl : raw8432step1Labels = raw8432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8432step0 raw8432step0Labels permutation34 permutation2
    _ = mixedMoment B node2591 node2591Labels := by rfl

theorem canonical8433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8433 raw8433Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw8433 raw8433Labels = mixedMoment B raw8433step0 raw8433step0Labels := by
      have hz : ∀ j, raw8433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8433step0 = (fun i j => raw8433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8433step0 raw8433; decide +kernel
      have hl : raw8433step0Labels = raw8433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8433 raw8433Labels permutation346 hz
    mixedMoment B raw8433step0 raw8433step0Labels = mixedMoment B raw8433step1 raw8433step1Labels := by
      have hz : ∀ j, raw8433step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8433step1 = (fun i j => raw8433step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8433step1 raw8433step0; decide +kernel
      have hl : raw8433step1Labels = raw8433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8433step0 raw8433step0Labels permutation56 hz
    mixedMoment B raw8433step1 raw8433step1Labels = mixedMoment B raw8433step2 raw8433step2Labels := by
      have ha : raw8433step2 = (fun i j => raw8433step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8433step2 raw8433step1; decide +kernel
      have hl : raw8433step2Labels = raw8433step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8433step1 raw8433step1Labels permutation10 permutation2
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical8434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8434 raw8434Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw8434 raw8434Labels = mixedMoment B raw8434step0 raw8434step0Labels := by
      have hz : ∀ j, raw8434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8434step0 = (fun i j => raw8434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8434step0 raw8434; decide +kernel
      have hl : raw8434step0Labels = raw8434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8434 raw8434Labels permutation346 hz
    mixedMoment B raw8434step0 raw8434step0Labels = mixedMoment B raw8434step1 raw8434step1Labels := by
      have hz : ∀ j, raw8434step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8434step1 = (fun i j => raw8434step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8434step1 raw8434step0; decide +kernel
      have hl : raw8434step1Labels = raw8434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8434step0 raw8434step0Labels permutation56 hz
    mixedMoment B raw8434step1 raw8434step1Labels = mixedMoment B raw8434step2 raw8434step2Labels := by
      have ha : raw8434step2 = (fun i j => raw8434step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8434step2 raw8434step1; decide +kernel
      have hl : raw8434step2Labels = raw8434step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8434step1 raw8434step1Labels permutation11 permutation2
    _ = mixedMoment B node2782 node2782Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8525 raw8525Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw8525 raw8525Labels = mixedMoment B raw8525step0 raw8525step0Labels := by
      have hz : ∀ j, raw8525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8525step0 = (fun i j => raw8525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8525step0 raw8525; decide +kernel
      have hl : raw8525step0Labels = raw8525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8525 raw8525Labels permutation346 hz
    mixedMoment B raw8525step0 raw8525step0Labels = mixedMoment B raw8525step1 raw8525step1Labels := by
      have hz : ∀ j, raw8525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8525step1 = (fun i j => raw8525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8525step1 raw8525step0; decide +kernel
      have hl : raw8525step1Labels = raw8525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8525step0 raw8525step0Labels permutation56 hz
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical8526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8526 raw8526Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8526 raw8526Labels = mixedMoment B raw8526step0 raw8526step0Labels := by
      have hz : ∀ j, raw8526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8526step0 = (fun i j => raw8526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8526step0 raw8526; decide +kernel
      have hl : raw8526step0Labels = raw8526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8526 raw8526Labels permutation346 hz
    mixedMoment B raw8526step0 raw8526step0Labels = mixedMoment B raw8526step1 raw8526step1Labels := by
      have ha : raw8526step1 = (fun i j => raw8526step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8526step1 raw8526step0; decide +kernel
      have hl : raw8526step1Labels = raw8526step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8526step0 raw8526step0Labels permutation98 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical8527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8527 raw8527Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw8527 raw8527Labels = mixedMoment B raw8527step0 raw8527step0Labels := by
      have hz : ∀ j, raw8527 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8527step0 = (fun i j => raw8527 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8527step0 raw8527; decide +kernel
      have hl : raw8527step0Labels = raw8527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8527 raw8527Labels permutation265 hz
    mixedMoment B raw8527step0 raw8527step0Labels = mixedMoment B raw8527step1 raw8527step1Labels := by
      have ha : raw8527step1 = (fun i j => raw8527step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8527step1 raw8527step0; decide +kernel
      have hl : raw8527step1Labels = raw8527step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8527step0 raw8527step0Labels permutation98 permutation4
    _ = mixedMoment B node3884 node3884Labels := by rfl

theorem canonical8528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8528 raw8528Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw8528 raw8528Labels = mixedMoment B raw8528step0 raw8528step0Labels := by
      have hz : ∀ j, raw8528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8528step0 = (fun i j => raw8528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8528step0 raw8528; decide +kernel
      have hl : raw8528step0Labels = raw8528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8528 raw8528Labels permutation346 hz
    mixedMoment B raw8528step0 raw8528step0Labels = mixedMoment B raw8528step1 raw8528step1Labels := by
      have hz : ∀ j, raw8528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8528step1 = (fun i j => raw8528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8528step1 raw8528step0; decide +kernel
      have hl : raw8528step1Labels = raw8528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8528step0 raw8528step0Labels permutation56 hz
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical8529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8529 raw8529Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw8529 raw8529Labels = mixedMoment B raw8529step0 raw8529step0Labels := by
      have hz : ∀ j, raw8529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8529step0 = (fun i j => raw8529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8529step0 raw8529; decide +kernel
      have hl : raw8529step0Labels = raw8529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8529 raw8529Labels permutation346 hz
    mixedMoment B raw8529step0 raw8529step0Labels = mixedMoment B raw8529step1 raw8529step1Labels := by
      have hz : ∀ j, raw8529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8529step1 = (fun i j => raw8529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8529step1 raw8529step0; decide +kernel
      have hl : raw8529step1Labels = raw8529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8529step0 raw8529step0Labels permutation56 hz
    mixedMoment B raw8529step1 raw8529step1Labels = mixedMoment B raw8529step2 raw8529step2Labels := by
      have ha : raw8529step2 = (fun i j => raw8529step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8529step2 raw8529step1; decide +kernel
      have hl : raw8529step2Labels = raw8529step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8529step1 raw8529step1Labels permutation18 permutation4
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical8530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8530 raw8530Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw8530 raw8530Labels = mixedMoment B raw8530step0 raw8530step0Labels := by
      have hz : ∀ j, raw8530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8530step0 = (fun i j => raw8530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8530step0 raw8530; decide +kernel
      have hl : raw8530step0Labels = raw8530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8530 raw8530Labels permutation346 hz
    mixedMoment B raw8530step0 raw8530step0Labels = mixedMoment B raw8530step1 raw8530step1Labels := by
      have hz : ∀ j, raw8530step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8530step1 = (fun i j => raw8530step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8530step1 raw8530step0; decide +kernel
      have hl : raw8530step1Labels = raw8530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8530step0 raw8530step0Labels permutation56 hz
    mixedMoment B raw8530step1 raw8530step1Labels = mixedMoment B raw8530step2 raw8530step2Labels := by
      have ha : raw8530step2 = (fun i j => raw8530step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8530step2 raw8530step1; decide +kernel
      have hl : raw8530step2Labels = raw8530step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8530step1 raw8530step1Labels permutation18 permutation4
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical8531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8531 raw8531Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8531 raw8531Labels = mixedMoment B raw8531step0 raw8531step0Labels := by
      have hz : ∀ j, raw8531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8531step0 = (fun i j => raw8531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8531step0 raw8531; decide +kernel
      have hl : raw8531step0Labels = raw8531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531 raw8531Labels permutation346 hz
    mixedMoment B raw8531step0 raw8531step0Labels = mixedMoment B raw8531step1 raw8531step1Labels := by
      have hz : ∀ j, raw8531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8531step1 = (fun i j => raw8531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8531step1 raw8531step0; decide +kernel
      have hl : raw8531step1Labels = raw8531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8531step0 raw8531step0Labels permutation56 hz
    mixedMoment B raw8531step1 raw8531step1Labels = mixedMoment B raw8531step2 raw8531step2Labels := by
      have ha : raw8531step2 = (fun i j => raw8531step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8531step2 raw8531step1; decide +kernel
      have hl : raw8531step2Labels = raw8531step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8531step1 raw8531step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8532 raw8532Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw8532 raw8532Labels = mixedMoment B raw8532step0 raw8532step0Labels := by
      have hz : ∀ j, raw8532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8532step0 = (fun i j => raw8532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8532step0 raw8532; decide +kernel
      have hl : raw8532step0Labels = raw8532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8532 raw8532Labels permutation346 hz
    mixedMoment B raw8532step0 raw8532step0Labels = mixedMoment B raw8532step1 raw8532step1Labels := by
      have ha : raw8532step1 = (fun i j => raw8532step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8532step1 raw8532step0; decide +kernel
      have hl : raw8532step1Labels = raw8532step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8532step0 raw8532step0Labels permutation38 permutation2
    _ = mixedMoment B node1368 node1368Labels := by rfl

theorem canonical8533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8533 raw8533Labels = mixedMoment B node1368 node1368Labels := by
  calc
    mixedMoment B raw8533 raw8533Labels = mixedMoment B raw8533step0 raw8533step0Labels := by
      have hz : ∀ j, raw8533 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8533step0 = (fun i j => raw8533 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8533step0 raw8533; decide +kernel
      have hl : raw8533step0Labels = raw8533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8533 raw8533Labels permutation265 hz
    mixedMoment B raw8533step0 raw8533step0Labels = mixedMoment B raw8533step1 raw8533step1Labels := by
      have ha : raw8533step1 = (fun i j => raw8533step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8533step1 raw8533step0; decide +kernel
      have hl : raw8533step1Labels = raw8533step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8533step0 raw8533step0Labels permutation38 permutation2
    _ = mixedMoment B node1368 node1368Labels := by rfl

theorem canonical8534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8534 raw8534Labels = mixedMoment B node1437 node1437Labels := by
  calc
    mixedMoment B raw8534 raw8534Labels = mixedMoment B raw8534step0 raw8534step0Labels := by
      have hz : ∀ j, raw8534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8534step0 = (fun i j => raw8534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8534step0 raw8534; decide +kernel
      have hl : raw8534step0Labels = raw8534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8534 raw8534Labels permutation346 hz
    mixedMoment B raw8534step0 raw8534step0Labels = mixedMoment B raw8534step1 raw8534step1Labels := by
      have hz : ∀ j, raw8534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8534step1 = (fun i j => raw8534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8534step1 raw8534step0; decide +kernel
      have hl : raw8534step1Labels = raw8534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8534step0 raw8534step0Labels permutation56 hz
    _ = mixedMoment B node1437 node1437Labels := by rfl

theorem canonical8535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8535 raw8535Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw8535 raw8535Labels = mixedMoment B raw8535step0 raw8535step0Labels := by
      have hz : ∀ j, raw8535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8535step0 = (fun i j => raw8535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8535step0 raw8535; decide +kernel
      have hl : raw8535step0Labels = raw8535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535 raw8535Labels permutation346 hz
    mixedMoment B raw8535step0 raw8535step0Labels = mixedMoment B raw8535step1 raw8535step1Labels := by
      have hz : ∀ j, raw8535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8535step1 = (fun i j => raw8535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8535step1 raw8535step0; decide +kernel
      have hl : raw8535step1Labels = raw8535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8535step0 raw8535step0Labels permutation56 hz
    mixedMoment B raw8535step1 raw8535step1Labels = mixedMoment B raw8535step2 raw8535step2Labels := by
      have ha : raw8535step2 = (fun i j => raw8535step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8535step2 raw8535step1; decide +kernel
      have hl : raw8535step2Labels = raw8535step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8535step1 raw8535step1Labels permutation9 permutation2
    _ = mixedMoment B node1375 node1375Labels := by rfl

theorem canonical8536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8536 raw8536Labels = mixedMoment B node1373 node1373Labels := by
  calc
    mixedMoment B raw8536 raw8536Labels = mixedMoment B raw8536step0 raw8536step0Labels := by
      have hz : ∀ j, raw8536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8536step0 = (fun i j => raw8536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8536step0 raw8536; decide +kernel
      have hl : raw8536step0Labels = raw8536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8536 raw8536Labels permutation346 hz
    mixedMoment B raw8536step0 raw8536step0Labels = mixedMoment B raw8536step1 raw8536step1Labels := by
      have hz : ∀ j, raw8536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8536step1 = (fun i j => raw8536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8536step1 raw8536step0; decide +kernel
      have hl : raw8536step1Labels = raw8536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8536step0 raw8536step0Labels permutation56 hz
    _ = mixedMoment B node1373 node1373Labels := by rfl

theorem canonical8537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8537 raw8537Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw8537 raw8537Labels = mixedMoment B raw8537step0 raw8537step0Labels := by
      have ha : raw8537step0 = (fun i j => raw8537 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8537step0 raw8537; decide +kernel
      have hl : raw8537step0Labels = raw8537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8537 raw8537Labels permutation182 permutation2
    _ = mixedMoment B node2975 node2975Labels := by rfl

theorem canonical8538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8538 raw8538Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw8538 raw8538Labels = mixedMoment B raw8538step0 raw8538step0Labels := by
      have hz : ∀ j, raw8538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8538step0 = (fun i j => raw8538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8538step0 raw8538; decide +kernel
      have hl : raw8538step0Labels = raw8538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8538 raw8538Labels permutation346 hz
    mixedMoment B raw8538step0 raw8538step0Labels = mixedMoment B raw8538step1 raw8538step1Labels := by
      have ha : raw8538step1 = (fun i j => raw8538step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8538step1 raw8538step0; decide +kernel
      have hl : raw8538step1Labels = raw8538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8538step0 raw8538step0Labels permutation38 permutation2
    _ = mixedMoment B node2882 node2882Labels := by rfl

theorem canonical8539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8539 raw8539Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw8539 raw8539Labels = mixedMoment B raw8539step0 raw8539step0Labels := by
      have hz : ∀ j, raw8539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8539step0 = (fun i j => raw8539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8539step0 raw8539; decide +kernel
      have hl : raw8539step0Labels = raw8539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8539 raw8539Labels permutation346 hz
    mixedMoment B raw8539step0 raw8539step0Labels = mixedMoment B raw8539step1 raw8539step1Labels := by
      have ha : raw8539step1 = (fun i j => raw8539step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8539step1 raw8539step0; decide +kernel
      have hl : raw8539step1Labels = raw8539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8539step0 raw8539step0Labels permutation40 permutation2
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical8540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8540 raw8540Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8540 raw8540Labels = mixedMoment B raw8540step0 raw8540step0Labels := by
      have hz : ∀ j, raw8540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8540step0 = (fun i j => raw8540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8540step0 raw8540; decide +kernel
      have hl : raw8540step0Labels = raw8540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8540 raw8540Labels permutation346 hz
    mixedMoment B raw8540step0 raw8540step0Labels = mixedMoment B raw8540step1 raw8540step1Labels := by
      have ha : raw8540step1 = (fun i j => raw8540step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8540step1 raw8540step0; decide +kernel
      have hl : raw8540step1Labels = raw8540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8540step0 raw8540step0Labels permutation39 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SoundPriority
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

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

theorem sound1292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1292 node1292Labels = Sparse.eval nodeValue1292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1292) = mixedMoment B node1292 node1292Labels := rfl
  simpa [nodeValue1292, Sparse.eval] using hc.symm

theorem sound1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1295 node1295Labels = Sparse.eval nodeValue1295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1295) = mixedMoment B node1295 node1295Labels := rfl
  simpa [nodeValue1295, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1368 node1368Labels = Sparse.eval nodeValue1368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1368) = mixedMoment B node1368 node1368Labels := rfl
  simpa [nodeValue1368, Sparse.eval] using hc.symm

theorem sound1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1373 node1373Labels = Sparse.eval nodeValue1373 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1373) = mixedMoment B node1373 node1373Labels := rfl
  simpa [nodeValue1373, Sparse.eval] using hc.symm

theorem sound1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1375 node1375Labels = Sparse.eval nodeValue1375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1375) = mixedMoment B node1375 node1375Labels := rfl
  simpa [nodeValue1375, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1418 node1418Labels = Sparse.eval nodeValue1418 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1418) = mixedMoment B node1418 node1418Labels := rfl
  simpa [nodeValue1418, Sparse.eval] using hc.symm

theorem sound1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1437 node1437Labels = Sparse.eval nodeValue1437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1437) = mixedMoment B node1437 node1437Labels := rfl
  simpa [nodeValue1437, Sparse.eval] using hc.symm

theorem sound1440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1440 node1440Labels = Sparse.eval nodeValue1440 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1440) = mixedMoment B node1440 node1440Labels := rfl
  simpa [nodeValue1440, Sparse.eval] using hc.symm

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

theorem sound2090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2090 node2090Labels = Sparse.eval nodeValue2090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2090) = mixedMoment B node2090 node2090Labels := rfl
  simpa [nodeValue2090, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

theorem sound2132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2132 node2132Labels = Sparse.eval nodeValue2132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2132) = mixedMoment B node2132 node2132Labels := rfl
  simpa [nodeValue2132, Sparse.eval] using hc.symm

theorem sound2134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2134 node2134Labels = Sparse.eval nodeValue2134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2134) = mixedMoment B node2134 node2134Labels := rfl
  simpa [nodeValue2134, Sparse.eval] using hc.symm

theorem sound2138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2138 node2138Labels = Sparse.eval nodeValue2138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2138) = mixedMoment B node2138 node2138Labels := rfl
  simpa [nodeValue2138, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2278 node2278Labels = Sparse.eval nodeValue2278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2278) = mixedMoment B node2278 node2278Labels := rfl
  simpa [nodeValue2278, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2588 node2588Labels = Sparse.eval nodeValue2588 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2588) = mixedMoment B node2588 node2588Labels := rfl
  simpa [nodeValue2588, Sparse.eval] using hc.symm

theorem sound2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2591 node2591Labels = Sparse.eval nodeValue2591 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2591) = mixedMoment B node2591 node2591Labels := rfl
  simpa [nodeValue2591, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2740 node2740Labels = Sparse.eval nodeValue2740 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2740) = mixedMoment B node2740 node2740Labels := rfl
  simpa [nodeValue2740, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

theorem sound2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2782 node2782Labels = Sparse.eval nodeValue2782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2782) = mixedMoment B node2782 node2782Labels := rfl
  simpa [nodeValue2782, Sparse.eval] using hc.symm

theorem sound2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2783 node2783Labels = Sparse.eval nodeValue2783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2783) = mixedMoment B node2783 node2783Labels := rfl
  simpa [nodeValue2783, Sparse.eval] using hc.symm

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

theorem sound2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2882 node2882Labels = Sparse.eval nodeValue2882 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2882) = mixedMoment B node2882 node2882Labels := rfl
  simpa [nodeValue2882, Sparse.eval] using hc.symm

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

theorem sound2952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2952 node2952Labels = Sparse.eval nodeValue2952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2952) = mixedMoment B node2952 node2952Labels := rfl
  simpa [nodeValue2952, Sparse.eval] using hc.symm

theorem sound2962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2962 node2962Labels = Sparse.eval nodeValue2962 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2962) = mixedMoment B node2962 node2962Labels := rfl
  simpa [nodeValue2962, Sparse.eval] using hc.symm

theorem sound2967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2967 node2967Labels = Sparse.eval nodeValue2967 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2967) = mixedMoment B node2967 node2967Labels := rfl
  simpa [nodeValue2967, Sparse.eval] using hc.symm

theorem sound2975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2975 node2975Labels = Sparse.eval nodeValue2975 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2975) = mixedMoment B node2975 node2975Labels := rfl
  simpa [nodeValue2975, Sparse.eval] using hc.symm

theorem sound2983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2983 node2983Labels = Sparse.eval nodeValue2983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2983) = mixedMoment B node2983 node2983Labels := rfl
  simpa [nodeValue2983, Sparse.eval] using hc.symm

theorem sound2995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2995 node2995Labels = Sparse.eval nodeValue2995 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2995) = mixedMoment B node2995 node2995Labels := rfl
  simpa [nodeValue2995, Sparse.eval] using hc.symm

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

theorem sound3044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3044 node3044Labels = Sparse.eval nodeValue3044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3044) = mixedMoment B node3044 node3044Labels := rfl
  simpa [nodeValue3044, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

theorem sound3055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3055 node3055Labels = Sparse.eval nodeValue3055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3055) = mixedMoment B node3055 node3055Labels := rfl
  simpa [nodeValue3055, Sparse.eval] using hc.symm

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

theorem sound3098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3098 node3098Labels = Sparse.eval nodeValue3098 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3098) = mixedMoment B node3098 node3098Labels := rfl
  simpa [nodeValue3098, Sparse.eval] using hc.symm

theorem sound3118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3118 node3118Labels = Sparse.eval nodeValue3118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3118) = mixedMoment B node3118 node3118Labels := rfl
  simpa [nodeValue3118, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3572 node3572Labels = Sparse.eval nodeValue3572 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3572) = mixedMoment B node3572 node3572Labels := rfl
  simpa [nodeValue3572, Sparse.eval] using hc.symm

theorem sound3583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3583 node3583Labels = Sparse.eval nodeValue3583 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3583) = mixedMoment B node3583 node3583Labels := rfl
  simpa [nodeValue3583, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3884 node3884Labels = Sparse.eval nodeValue3884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3884) = mixedMoment B node3884 node3884Labels := rfl
  simpa [nodeValue3884, Sparse.eval] using hc.symm

theorem sound3886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3886 node3886Labels = Sparse.eval nodeValue3886 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3886) = mixedMoment B node3886 node3886Labels := rfl
  simpa [nodeValue3886, Sparse.eval] using hc.symm

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

theorem sound3913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3913 node3913Labels = Sparse.eval nodeValue3913 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3913) = mixedMoment B node3913 node3913Labels := rfl
  simpa [nodeValue3913, Sparse.eval] using hc.symm

theorem sound3963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3963 node3963Labels = Sparse.eval nodeValue3963 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3963) = mixedMoment B node3963 node3963Labels := rfl
  simpa [nodeValue3963, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources14
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm455 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA455 + difference 0 1) (sourceB455 + difference 1 0) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3572) := by
    have ha : (tripleCharges (sourceA455 + difference 0 1) (sourceB455 + difference 1 0) sourceC455) = raw8254 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8254; decide +kernel
    rw [ha]
    exact (canonical8254 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA455 + difference 1 1) (sourceB455 + difference 1 1) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA455 + difference 1 1) (sourceB455 + difference 1 1) sourceC455) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA455 + difference 2 1) (sourceB455 + difference 1 2) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2983) := by
    have ha : (tripleCharges (sourceA455 + difference 2 1) (sourceB455 + difference 1 2) sourceC455) = raw8265 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8265; decide +kernel
    rw [ha]
    exact (canonical8265 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA455 + difference 3 1) (sourceB455 + difference 1 3) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA455 + difference 3 1) (sourceB455 + difference 1 3) sourceC455) = raw8266 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8266; decide +kernel
    rw [ha]
    exact (canonical8266 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA455 + difference 4 1) (sourceB455 + difference 1 4) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA455 + difference 4 1) (sourceB455 + difference 1 4) sourceC455) = raw8267 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw8267; decide +kernel
    rw [ha]
    exact (canonical8267 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA455 + difference 5 1) (sourceB455 + difference 1 5) sourceC455) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2090) := by
    have ha : (tripleCharges (sourceA455 + difference 5 1) (sourceB455 + difference 1 5) sourceC455) = raw4756 := by
      apply Matrix.ext; unfold tripleCharges sourceA455 sourceB455 sourceC455 difference raw4756; decide +kernel
    rw [ha]
    exact (canonical4756 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA455 + sourceB455) sourceC455) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA455 + sourceB455) sourceC455) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA455 sourceB455 sourceC455 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA455 sourceB455 sourceC455
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm455, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm456 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA456 + difference 3 0) (sourceB456 + difference 0 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1440) := by
    have ha : (tripleCharges (sourceA456 + difference 3 0) (sourceB456 + difference 0 3) sourceC456) = raw8260 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8260; decide +kernel
    rw [ha]
    exact (canonical8260 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA456 + difference 3 1) (sourceB456 + difference 1 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA456 + difference 3 1) (sourceB456 + difference 1 3) sourceC456) = raw8266 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8266; decide +kernel
    rw [ha]
    exact (canonical8266 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA456 + difference 3 2) (sourceB456 + difference 2 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2995) := by
    have ha : (tripleCharges (sourceA456 + difference 3 2) (sourceB456 + difference 2 3) sourceC456) = raw8268 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8268; decide +kernel
    rw [ha]
    exact (canonical8268 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA456 + difference 3 3) (sourceB456 + difference 3 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA456 + difference 3 3) (sourceB456 + difference 3 3) sourceC456) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA456 + difference 3 4) (sourceB456 + difference 4 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA456 + difference 3 4) (sourceB456 + difference 4 3) sourceC456) = raw4760 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw4760; decide +kernel
    rw [ha]
    exact (canonical4760 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA456 + difference 3 5) (sourceB456 + difference 5 3) sourceC456) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3118) := by
    have ha : (tripleCharges (sourceA456 + difference 3 5) (sourceB456 + difference 5 3) sourceC456) = raw8269 := by
      apply Matrix.ext; unfold tripleCharges sourceA456 sourceB456 sourceC456 difference raw8269; decide +kernel
    rw [ha]
    exact (canonical8269 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA456 + sourceB456) sourceC456) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA456 + sourceB456) sourceC456) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA456 sourceB456 sourceC456 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA456 sourceB456 sourceC456
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm456, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm457 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA457 + difference 0 3) (sourceB457 + difference 3 0) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3583) := by
    have ha : (tripleCharges (sourceA457 + difference 0 3) (sourceB457 + difference 3 0) sourceC457) = raw8256 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8256; decide +kernel
    rw [ha]
    exact (canonical8256 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA457 + difference 1 3) (sourceB457 + difference 3 1) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA457 + difference 1 3) (sourceB457 + difference 3 1) sourceC457) = raw8263 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8263; decide +kernel
    rw [ha]
    exact (canonical8263 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA457 + difference 2 3) (sourceB457 + difference 3 2) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2952) := by
    have ha : (tripleCharges (sourceA457 + difference 2 3) (sourceB457 + difference 3 2) sourceC457) = raw8270 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8270; decide +kernel
    rw [ha]
    exact (canonical8270 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA457 + difference 3 3) (sourceB457 + difference 3 3) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA457 + difference 3 3) (sourceB457 + difference 3 3) sourceC457) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA457 + difference 4 3) (sourceB457 + difference 3 4) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA457 + difference 4 3) (sourceB457 + difference 3 4) sourceC457) = raw8271 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw8271; decide +kernel
    rw [ha]
    exact (canonical8271 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA457 + difference 5 3) (sourceB457 + difference 3 5) sourceC457) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA457 + difference 5 3) (sourceB457 + difference 3 5) sourceC457) = raw4762 := by
      apply Matrix.ext; unfold tripleCharges sourceA457 sourceB457 sourceC457 difference raw4762; decide +kernel
    rw [ha]
    exact (canonical4762 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA457 + sourceB457) sourceC457) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA457 + sourceB457) sourceC457) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA457 sourceB457 sourceC457 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA457 sourceB457 sourceC457
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm457, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm458 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA458 + difference 4 0) (sourceB458 + difference 0 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1418) := by
    have ha : (tripleCharges (sourceA458 + difference 4 0) (sourceB458 + difference 0 4) sourceC458) = raw8261 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8261; decide +kernel
    rw [ha]
    exact (canonical8261 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA458 + difference 4 1) (sourceB458 + difference 1 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA458 + difference 4 1) (sourceB458 + difference 1 4) sourceC458) = raw8267 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8267; decide +kernel
    rw [ha]
    exact (canonical8267 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA458 + difference 4 2) (sourceB458 + difference 2 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2962) := by
    have ha : (tripleCharges (sourceA458 + difference 4 2) (sourceB458 + difference 2 4) sourceC458) = raw8272 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8272; decide +kernel
    rw [ha]
    exact (canonical8272 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA458 + difference 4 3) (sourceB458 + difference 3 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA458 + difference 4 3) (sourceB458 + difference 3 4) sourceC458) = raw8271 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8271; decide +kernel
    rw [ha]
    exact (canonical8271 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA458 + difference 4 4) (sourceB458 + difference 4 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3098) := by
    have ha : (tripleCharges (sourceA458 + difference 4 4) (sourceB458 + difference 4 4) sourceC458) = raw8253 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8253; decide +kernel
    rw [ha]
    exact (canonical8253 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA458 + difference 4 5) (sourceB458 + difference 5 4) sourceC458) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2967) := by
    have ha : (tripleCharges (sourceA458 + difference 4 5) (sourceB458 + difference 5 4) sourceC458) = raw8273 := by
      apply Matrix.ext; unfold tripleCharges sourceA458 sourceB458 sourceC458 difference raw8273; decide +kernel
    rw [ha]
    exact (canonical8273 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA458 + sourceB458) sourceC458) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA458 + sourceB458) sourceC458) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA458 sourceB458 sourceC458 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA458 sourceB458 sourceC458
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm458, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm462 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA462 + difference 0 0) (sourceB462 + difference 0 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA462 + difference 0 0) (sourceB462 + difference 0 0) sourceC462) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA462 + difference 0 1) (sourceB462 + difference 1 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA462 + difference 0 1) (sourceB462 + difference 1 0) sourceC462) = raw6438 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw6438; decide +kernel
    rw [ha]
    exact (canonical6438 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA462 + difference 0 2) (sourceB462 + difference 2 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA462 + difference 0 2) (sourceB462 + difference 2 0) sourceC462) = raw8315 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw8315; decide +kernel
    rw [ha]
    exact (canonical8315 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA462 + difference 0 3) (sourceB462 + difference 3 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2783) := by
    have ha : (tripleCharges (sourceA462 + difference 0 3) (sourceB462 + difference 3 0) sourceC462) = raw7695 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw7695; decide +kernel
    rw [ha]
    exact (canonical7695 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA462 + difference 0 4) (sourceB462 + difference 4 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2740) := by
    have ha : (tripleCharges (sourceA462 + difference 0 4) (sourceB462 + difference 4 0) sourceC462) = raw8316 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw8316; decide +kernel
    rw [ha]
    exact (canonical8316 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA462 + difference 0 5) (sourceB462 + difference 5 0) sourceC462) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1292) := by
    have ha : (tripleCharges (sourceA462 + difference 0 5) (sourceB462 + difference 5 0) sourceC462) = raw8317 := by
      apply Matrix.ext; unfold tripleCharges sourceA462 sourceB462 sourceC462 difference raw8317; decide +kernel
    rw [ha]
    exact (canonical8317 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA462 + sourceB462) sourceC462) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA462 + sourceB462) sourceC462) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA462 sourceB462 sourceC462 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA462 sourceB462 sourceC462
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm462, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm463 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA463 + difference 0 0) (sourceB463 + difference 0 0) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA463 + difference 0 0) (sourceB463 + difference 0 0) sourceC463) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA463 + difference 1 0) (sourceB463 + difference 0 1) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA463 + difference 1 0) (sourceB463 + difference 0 1) sourceC463) = raw8318 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8318; decide +kernel
    rw [ha]
    exact (canonical8318 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA463 + difference 2 0) (sourceB463 + difference 0 2) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2132) := by
    have ha : (tripleCharges (sourceA463 + difference 2 0) (sourceB463 + difference 0 2) sourceC463) = raw8319 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8319; decide +kernel
    rw [ha]
    exact (canonical8319 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA463 + difference 3 0) (sourceB463 + difference 0 3) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA463 + difference 3 0) (sourceB463 + difference 0 3) sourceC463) = raw8320 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8320; decide +kernel
    rw [ha]
    exact (canonical8320 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA463 + difference 4 0) (sourceB463 + difference 0 4) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2134) := by
    have ha : (tripleCharges (sourceA463 + difference 4 0) (sourceB463 + difference 0 4) sourceC463) = raw8321 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw8321; decide +kernel
    rw [ha]
    exact (canonical8321 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA463 + difference 5 0) (sourceB463 + difference 0 5) sourceC463) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA463 + difference 5 0) (sourceB463 + difference 0 5) sourceC463) = raw6439 := by
      apply Matrix.ext; unfold tripleCharges sourceA463 sourceB463 sourceC463 difference raw6439; decide +kernel
    rw [ha]
    exact (canonical6439 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA463 + sourceB463) sourceC463) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA463 + sourceB463) sourceC463) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA463 sourceB463 sourceC463 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA463 sourceB463 sourceC463
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm463, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm468 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA468 + difference 0 0) (sourceB468 + difference 0 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA468 + difference 0 0) (sourceB468 + difference 0 0) sourceC468) = raw8416 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8416; decide +kernel
    rw [ha]
    exact (canonical8416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA468 + difference 0 1) (sourceB468 + difference 1 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA468 + difference 0 1) (sourceB468 + difference 1 0) sourceC468) = raw8417 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8417; decide +kernel
    rw [ha]
    exact (canonical8417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA468 + difference 0 2) (sourceB468 + difference 2 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA468 + difference 0 2) (sourceB468 + difference 2 0) sourceC468) = raw8418 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8418; decide +kernel
    rw [ha]
    exact (canonical8418 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA468 + difference 0 3) (sourceB468 + difference 3 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA468 + difference 0 3) (sourceB468 + difference 3 0) sourceC468) = raw8419 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8419; decide +kernel
    rw [ha]
    exact (canonical8419 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA468 + difference 0 4) (sourceB468 + difference 4 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA468 + difference 0 4) (sourceB468 + difference 4 0) sourceC468) = raw8420 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8420; decide +kernel
    rw [ha]
    exact (canonical8420 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA468 + difference 0 5) (sourceB468 + difference 5 0) sourceC468) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA468 + difference 0 5) (sourceB468 + difference 5 0) sourceC468) = raw8421 := by
      apply Matrix.ext; unfold tripleCharges sourceA468 sourceB468 sourceC468 difference raw8421; decide +kernel
    rw [ha]
    exact (canonical8421 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA468 + sourceB468) sourceC468) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA468 + sourceB468) sourceC468) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA468 sourceB468 sourceC468 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA468 sourceB468 sourceC468
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm468, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm471 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA471 + difference 3 0) (sourceB471 + difference 0 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1295) := by
    have ha : (tripleCharges (sourceA471 + difference 3 0) (sourceB471 + difference 0 3) sourceC471) = raw8425 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8425; decide +kernel
    rw [ha]
    exact (canonical8425 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA471 + difference 3 1) (sourceB471 + difference 1 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA471 + difference 3 1) (sourceB471 + difference 1 3) sourceC471) = raw8429 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8429; decide +kernel
    rw [ha]
    exact (canonical8429 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA471 + difference 3 2) (sourceB471 + difference 2 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2591) := by
    have ha : (tripleCharges (sourceA471 + difference 3 2) (sourceB471 + difference 2 3) sourceC471) = raw8432 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8432; decide +kernel
    rw [ha]
    exact (canonical8432 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA471 + difference 3 3) (sourceB471 + difference 3 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA471 + difference 3 3) (sourceB471 + difference 3 3) sourceC471) = raw8416 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8416; decide +kernel
    rw [ha]
    exact (canonical8416 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA471 + difference 3 4) (sourceB471 + difference 4 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA471 + difference 3 4) (sourceB471 + difference 4 3) sourceC471) = raw8433 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8433; decide +kernel
    rw [ha]
    exact (canonical8433 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA471 + difference 3 5) (sourceB471 + difference 5 3) sourceC471) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2782) := by
    have ha : (tripleCharges (sourceA471 + difference 3 5) (sourceB471 + difference 5 3) sourceC471) = raw8434 := by
      apply Matrix.ext; unfold tripleCharges sourceA471 sourceB471 sourceC471 difference raw8434; decide +kernel
    rw [ha]
    exact (canonical8434 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA471 + sourceB471) sourceC471) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA471 + sourceB471) sourceC471) = raw8422 := by
      apply Matrix.ext; unfold doubleCharges sourceA471 sourceB471 sourceC471 raw8422; decide +kernel
    rw [ha]
    exact (canonical8422 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA471 sourceB471 sourceC471
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm471, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm475 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA475 + difference 0 0) (sourceB475 + difference 0 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA475 + difference 0 0) (sourceB475 + difference 0 0) sourceC475) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA475 + difference 0 1) (sourceB475 + difference 1 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA475 + difference 0 1) (sourceB475 + difference 1 0) sourceC475) = raw8526 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8526; decide +kernel
    rw [ha]
    exact (canonical8526 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA475 + difference 0 2) (sourceB475 + difference 2 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3884) := by
    have ha : (tripleCharges (sourceA475 + difference 0 2) (sourceB475 + difference 2 0) sourceC475) = raw8527 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8527; decide +kernel
    rw [ha]
    exact (canonical8527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA475 + difference 0 3) (sourceB475 + difference 3 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3963) := by
    have ha : (tripleCharges (sourceA475 + difference 0 3) (sourceB475 + difference 3 0) sourceC475) = raw8528 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8528; decide +kernel
    rw [ha]
    exact (canonical8528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA475 + difference 0 4) (sourceB475 + difference 4 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3886) := by
    have ha : (tripleCharges (sourceA475 + difference 0 4) (sourceB475 + difference 4 0) sourceC475) = raw8529 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8529; decide +kernel
    rw [ha]
    exact (canonical8529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA475 + difference 0 5) (sourceB475 + difference 5 0) sourceC475) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3913) := by
    have ha : (tripleCharges (sourceA475 + difference 0 5) (sourceB475 + difference 5 0) sourceC475) = raw8530 := by
      apply Matrix.ext; unfold tripleCharges sourceA475 sourceB475 sourceC475 difference raw8530; decide +kernel
    rw [ha]
    exact (canonical8530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA475 + sourceB475) sourceC475) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA475 + sourceB475) sourceC475) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA475 sourceB475 sourceC475 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA475 sourceB475 sourceC475
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm475, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm476 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA476 + difference 0 0) (sourceB476 + difference 0 0) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA476 + difference 0 0) (sourceB476 + difference 0 0) sourceC476) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA476 + difference 1 0) (sourceB476 + difference 0 1) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA476 + difference 1 0) (sourceB476 + difference 0 1) sourceC476) = raw8532 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8532; decide +kernel
    rw [ha]
    exact (canonical8532 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA476 + difference 2 0) (sourceB476 + difference 0 2) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA476 + difference 2 0) (sourceB476 + difference 0 2) sourceC476) = raw8533 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8533; decide +kernel
    rw [ha]
    exact (canonical8533 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA476 + difference 3 0) (sourceB476 + difference 0 3) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1437) := by
    have ha : (tripleCharges (sourceA476 + difference 3 0) (sourceB476 + difference 0 3) sourceC476) = raw8534 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8534; decide +kernel
    rw [ha]
    exact (canonical8534 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA476 + difference 4 0) (sourceB476 + difference 0 4) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1375) := by
    have ha : (tripleCharges (sourceA476 + difference 4 0) (sourceB476 + difference 0 4) sourceC476) = raw8535 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8535; decide +kernel
    rw [ha]
    exact (canonical8535 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA476 + difference 5 0) (sourceB476 + difference 0 5) sourceC476) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1373) := by
    have ha : (tripleCharges (sourceA476 + difference 5 0) (sourceB476 + difference 0 5) sourceC476) = raw8536 := by
      apply Matrix.ext; unfold tripleCharges sourceA476 sourceB476 sourceC476 difference raw8536; decide +kernel
    rw [ha]
    exact (canonical8536 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA476 + sourceB476) sourceC476) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA476 + sourceB476) sourceC476) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA476 sourceB476 sourceC476 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA476 sourceB476 sourceC476
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm476, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm477 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA477 + difference 1 0) (sourceB477 + difference 0 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1368) := by
    have ha : (tripleCharges (sourceA477 + difference 1 0) (sourceB477 + difference 0 1) sourceC477) = raw8532 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8532; decide +kernel
    rw [ha]
    exact (canonical8532 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA477 + difference 1 1) (sourceB477 + difference 1 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3055) := by
    have ha : (tripleCharges (sourceA477 + difference 1 1) (sourceB477 + difference 1 1) sourceC477) = raw8525 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8525; decide +kernel
    rw [ha]
    exact (canonical8525 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA477 + difference 1 2) (sourceB477 + difference 2 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2975) := by
    have ha : (tripleCharges (sourceA477 + difference 1 2) (sourceB477 + difference 2 1) sourceC477) = raw8537 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8537; decide +kernel
    rw [ha]
    exact (canonical8537 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA477 + difference 1 3) (sourceB477 + difference 3 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2882) := by
    have ha : (tripleCharges (sourceA477 + difference 1 3) (sourceB477 + difference 3 1) sourceC477) = raw8538 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8538; decide +kernel
    rw [ha]
    exact (canonical8538 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA477 + difference 1 4) (sourceB477 + difference 4 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3044) := by
    have ha : (tripleCharges (sourceA477 + difference 1 4) (sourceB477 + difference 4 1) sourceC477) = raw8539 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8539; decide +kernel
    rw [ha]
    exact (canonical8539 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA477 + difference 1 5) (sourceB477 + difference 5 1) sourceC477) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA477 + difference 1 5) (sourceB477 + difference 5 1) sourceC477) = raw8540 := by
      apply Matrix.ext; unfold tripleCharges sourceA477 sourceB477 sourceC477 difference raw8540; decide +kernel
    rw [ha]
    exact (canonical8540 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA477 + sourceB477) sourceC477) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA477 + sourceB477) sourceC477) = raw8531 := by
      apply Matrix.ext; unfold doubleCharges sourceA477 sourceB477 sourceC477 raw8531; decide +kernel
    rw [ha]
    exact (canonical8531 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA477 sourceB477 sourceC477
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm477, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck384 : Integer.Sparse.reindex keyMap MixedData.row384 = numericRow384 := by decide +kernel

theorem numericCheck384 (x : Master → ℝ) : Integer.Sparse.eval numericRow384 x =
    (1 : ℝ) * reducedSource384 x := by
  norm_num [numericRow384, reducedSource384, Integer.Sparse.eval, Sparse.eval, nodeValue2090, nodeValue2962, nodeValue2983, nodeValue2995, nodeValue3098, nodeValue3572, nodeValue4083]

theorem reindexCheck385 : Integer.Sparse.reindex keyMap MixedData.row385 = numericRow385 := by decide +kernel

theorem numericCheck385 (x : Master → ℝ) : Integer.Sparse.eval numericRow385 x =
    (1 : ℝ) * reducedSource385 x := by
  norm_num [numericRow385, reducedSource385, Integer.Sparse.eval, Sparse.eval, nodeValue1440, nodeValue2995, nodeValue3098, nodeValue3118, nodeValue4083]

theorem reindexCheck386 : Integer.Sparse.reindex keyMap MixedData.row386 = numericRow386 := by decide +kernel

theorem numericCheck386 (x : Master → ℝ) : Integer.Sparse.eval numericRow386 x =
    (1 : ℝ) * reducedSource386 x := by
  norm_num [numericRow386, reducedSource386, Integer.Sparse.eval, Sparse.eval, nodeValue2112, nodeValue2952, nodeValue2967, nodeValue3098, nodeValue3583, nodeValue4083]

theorem reindexCheck387 : Integer.Sparse.reindex keyMap MixedData.row387 = numericRow387 := by decide +kernel

theorem numericCheck387 (x : Master → ℝ) : Integer.Sparse.eval numericRow387 x =
    (1 : ℝ) * reducedSource387 x := by
  norm_num [numericRow387, reducedSource387, Integer.Sparse.eval, Sparse.eval, nodeValue1418, nodeValue2962, nodeValue2967, nodeValue3098, nodeValue4083]

theorem reindexCheck389 : Integer.Sparse.reindex keyMap MixedData.row389 = numericRow389 := by decide +kernel

theorem numericCheck389 (x : Master → ℝ) : Integer.Sparse.eval numericRow389 x =
    (1 : ℝ) * reducedSource389 x := by
  norm_num [numericRow389, reducedSource389, Integer.Sparse.eval, Sparse.eval, nodeValue1292, nodeValue2588, nodeValue2740, nodeValue2781, nodeValue2783, nodeValue4084]

theorem reindexCheck390 : Integer.Sparse.reindex keyMap MixedData.row390 = numericRow390 := by decide +kernel

theorem numericCheck390 (x : Master → ℝ) : Integer.Sparse.eval numericRow390 x =
    (1 : ℝ) * reducedSource390 x := by
  norm_num [numericRow390, reducedSource390, Integer.Sparse.eval, Sparse.eval, nodeValue2132, nodeValue2134, nodeValue2138, nodeValue2278, nodeValue2781, nodeValue4084]

theorem reindexCheck393 : Integer.Sparse.reindex keyMap MixedData.row393 = numericRow393 := by decide +kernel

theorem numericCheck393 (x : Master → ℝ) : Integer.Sparse.eval numericRow393 x =
    (1 : ℝ) * reducedSource393 x := by
  norm_num [numericRow393, reducedSource393, Integer.Sparse.eval, Sparse.eval, nodeValue2774, nodeValue3854, nodeValue3907, nodeValue4092]

theorem reindexCheck394 : Integer.Sparse.reindex keyMap MixedData.row394 = numericRow394 := by decide +kernel

theorem numericCheck394 (x : Master → ℝ) : Integer.Sparse.eval numericRow394 x =
    (1 : ℝ) * reducedSource394 x := by
  norm_num [numericRow394, reducedSource394, Integer.Sparse.eval, Sparse.eval, nodeValue1295, nodeValue2591, nodeValue2743, nodeValue2774, nodeValue2782, nodeValue4092]

theorem reindexCheck397 : Integer.Sparse.reindex keyMap MixedData.row397 = numericRow397 := by decide +kernel

theorem numericCheck397 (x : Master → ℝ) : Integer.Sparse.eval numericRow397 x =
    (1 : ℝ) * reducedSource397 x := by
  norm_num [numericRow397, reducedSource397, Integer.Sparse.eval, Sparse.eval, nodeValue3055, nodeValue3884, nodeValue3886, nodeValue3913, nodeValue3963, nodeValue4092]

theorem reindexCheck398 : Integer.Sparse.reindex keyMap MixedData.row398 = numericRow398 := by decide +kernel

theorem numericCheck398 (x : Master → ℝ) : Integer.Sparse.eval numericRow398 x =
    (1 : ℝ) * reducedSource398 x := by
  norm_num [numericRow398, reducedSource398, Integer.Sparse.eval, Sparse.eval, nodeValue1368, nodeValue1373, nodeValue1375, nodeValue1437, nodeValue3055, nodeValue4092]

theorem reindexCheck399 : Integer.Sparse.reindex keyMap MixedData.row399 = numericRow399 := by decide +kernel

theorem numericCheck399 (x : Master → ℝ) : Integer.Sparse.eval numericRow399 x =
    (1 : ℝ) * reducedSource399 x := by
  norm_num [numericRow399, reducedSource399, Integer.Sparse.eval, Sparse.eval, nodeValue1368, nodeValue2882, nodeValue2975, nodeValue3044, nodeValue3051, nodeValue3055, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource384 (mixedVector B) = 0 := by
  have h2090 : mixedVector B (Sum.inr 2090) = Sparse.eval nodeValue2090 (mixedVector B) := by
    change mixedMoment B node2090 node2090Labels = _
    exact sound2090 B hB hF
  have h2962 : mixedVector B (Sum.inr 2962) = Sparse.eval nodeValue2962 (mixedVector B) := by
    change mixedMoment B node2962 node2962Labels = _
    exact sound2962 B hB hF
  have h2983 : mixedVector B (Sum.inr 2983) = Sparse.eval nodeValue2983 (mixedVector B) := by
    change mixedMoment B node2983 node2983Labels = _
    exact sound2983 B hB hF
  have h2995 : mixedVector B (Sum.inr 2995) = Sparse.eval nodeValue2995 (mixedVector B) := by
    change mixedMoment B node2995 node2995Labels = _
    exact sound2995 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3572 : mixedVector B (Sum.inr 3572) = Sparse.eval nodeValue3572 (mixedVector B) := by
    change mixedMoment B node3572 node3572Labels = _
    exact sound3572 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm455, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2090, h2962, h2983, h2995, h3098, h3572, h4083, reducedSource384] using sourceEq455 B hB

theorem rowSound384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row384 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck384, numericCheck384, reducedZero384 B hB hF, mul_zero]

theorem reducedZero385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource385 (mixedVector B) = 0 := by
  have h1440 : mixedVector B (Sum.inr 1440) = Sparse.eval nodeValue1440 (mixedVector B) := by
    change mixedMoment B node1440 node1440Labels = _
    exact sound1440 B hB hF
  have h2995 : mixedVector B (Sum.inr 2995) = Sparse.eval nodeValue2995 (mixedVector B) := by
    change mixedMoment B node2995 node2995Labels = _
    exact sound2995 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3118 : mixedVector B (Sum.inr 3118) = Sparse.eval nodeValue3118 (mixedVector B) := by
    change mixedMoment B node3118 node3118Labels = _
    exact sound3118 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm456, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1440, h2995, h3098, h3118, h4083, reducedSource385] using sourceEq456 B hB

theorem rowSound385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row385 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck385, numericCheck385, reducedZero385 B hB hF, mul_zero]

theorem reducedZero386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource386 (mixedVector B) = 0 := by
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h2952 : mixedVector B (Sum.inr 2952) = Sparse.eval nodeValue2952 (mixedVector B) := by
    change mixedMoment B node2952 node2952Labels = _
    exact sound2952 B hB hF
  have h2967 : mixedVector B (Sum.inr 2967) = Sparse.eval nodeValue2967 (mixedVector B) := by
    change mixedMoment B node2967 node2967Labels = _
    exact sound2967 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h3583 : mixedVector B (Sum.inr 3583) = Sparse.eval nodeValue3583 (mixedVector B) := by
    change mixedMoment B node3583 node3583Labels = _
    exact sound3583 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm457, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2112, h2952, h2967, h3098, h3583, h4083, reducedSource386] using sourceEq457 B hB

theorem rowSound386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row386 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck386, numericCheck386, reducedZero386 B hB hF, mul_zero]

theorem reducedZero387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource387 (mixedVector B) = 0 := by
  have h1418 : mixedVector B (Sum.inr 1418) = Sparse.eval nodeValue1418 (mixedVector B) := by
    change mixedMoment B node1418 node1418Labels = _
    exact sound1418 B hB hF
  have h2962 : mixedVector B (Sum.inr 2962) = Sparse.eval nodeValue2962 (mixedVector B) := by
    change mixedMoment B node2962 node2962Labels = _
    exact sound2962 B hB hF
  have h2967 : mixedVector B (Sum.inr 2967) = Sparse.eval nodeValue2967 (mixedVector B) := by
    change mixedMoment B node2967 node2967Labels = _
    exact sound2967 B hB hF
  have h3098 : mixedVector B (Sum.inr 3098) = Sparse.eval nodeValue3098 (mixedVector B) := by
    change mixedMoment B node3098 node3098Labels = _
    exact sound3098 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm458, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1418, h2962, h2967, h3098, h4083, reducedSource387] using sourceEq458 B hB

theorem rowSound387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row387 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck387, numericCheck387, reducedZero387 B hB hF, mul_zero]

theorem reducedZero389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource389 (mixedVector B) = 0 := by
  have h1292 : mixedVector B (Sum.inr 1292) = Sparse.eval nodeValue1292 (mixedVector B) := by
    change mixedMoment B node1292 node1292Labels = _
    exact sound1292 B hB hF
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h2740 : mixedVector B (Sum.inr 2740) = Sparse.eval nodeValue2740 (mixedVector B) := by
    change mixedMoment B node2740 node2740Labels = _
    exact sound2740 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h2783 : mixedVector B (Sum.inr 2783) = Sparse.eval nodeValue2783 (mixedVector B) := by
    change mixedMoment B node2783 node2783Labels = _
    exact sound2783 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm462, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1292, h2588, h2740, h2781, h2783, h4084, reducedSource389] using sourceEq462 B hB

theorem rowSound389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row389 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck389, numericCheck389, reducedZero389 B hB hF, mul_zero]

theorem reducedZero390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource390 (mixedVector B) = 0 := by
  have h2132 : mixedVector B (Sum.inr 2132) = Sparse.eval nodeValue2132 (mixedVector B) := by
    change mixedMoment B node2132 node2132Labels = _
    exact sound2132 B hB hF
  have h2134 : mixedVector B (Sum.inr 2134) = Sparse.eval nodeValue2134 (mixedVector B) := by
    change mixedMoment B node2134 node2134Labels = _
    exact sound2134 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm463, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2132, h2134, h2138, h2278, h2781, h4084, reducedSource390] using sourceEq463 B hB

theorem rowSound390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row390 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck390, numericCheck390, reducedZero390 B hB hF, mul_zero]

theorem reducedZero393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource393 (mixedVector B) = 0 := by
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm468, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2774, h3854, h3907, h4092, reducedSource393] using sourceEq468 B hB

theorem rowSound393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row393 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck393, numericCheck393, reducedZero393 B hB hF, mul_zero]

theorem reducedZero394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource394 (mixedVector B) = 0 := by
  have h1295 : mixedVector B (Sum.inr 1295) = Sparse.eval nodeValue1295 (mixedVector B) := by
    change mixedMoment B node1295 node1295Labels = _
    exact sound1295 B hB hF
  have h2591 : mixedVector B (Sum.inr 2591) = Sparse.eval nodeValue2591 (mixedVector B) := by
    change mixedMoment B node2591 node2591Labels = _
    exact sound2591 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h2782 : mixedVector B (Sum.inr 2782) = Sparse.eval nodeValue2782 (mixedVector B) := by
    change mixedMoment B node2782 node2782Labels = _
    exact sound2782 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm471, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1295, h2591, h2743, h2774, h2782, h4092, reducedSource394] using sourceEq471 B hB

theorem rowSound394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row394 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck394, numericCheck394, reducedZero394 B hB hF, mul_zero]

theorem reducedZero397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource397 (mixedVector B) = 0 := by
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h3884 : mixedVector B (Sum.inr 3884) = Sparse.eval nodeValue3884 (mixedVector B) := by
    change mixedMoment B node3884 node3884Labels = _
    exact sound3884 B hB hF
  have h3886 : mixedVector B (Sum.inr 3886) = Sparse.eval nodeValue3886 (mixedVector B) := by
    change mixedMoment B node3886 node3886Labels = _
    exact sound3886 B hB hF
  have h3913 : mixedVector B (Sum.inr 3913) = Sparse.eval nodeValue3913 (mixedVector B) := by
    change mixedMoment B node3913 node3913Labels = _
    exact sound3913 B hB hF
  have h3963 : mixedVector B (Sum.inr 3963) = Sparse.eval nodeValue3963 (mixedVector B) := by
    change mixedMoment B node3963 node3963Labels = _
    exact sound3963 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm475, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3055, h3884, h3886, h3913, h3963, h4092, reducedSource397] using sourceEq475 B hB

theorem rowSound397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row397 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck397, numericCheck397, reducedZero397 B hB hF, mul_zero]

theorem reducedZero398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource398 (mixedVector B) = 0 := by
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h1373 : mixedVector B (Sum.inr 1373) = Sparse.eval nodeValue1373 (mixedVector B) := by
    change mixedMoment B node1373 node1373Labels = _
    exact sound1373 B hB hF
  have h1375 : mixedVector B (Sum.inr 1375) = Sparse.eval nodeValue1375 (mixedVector B) := by
    change mixedMoment B node1375 node1375Labels = _
    exact sound1375 B hB hF
  have h1437 : mixedVector B (Sum.inr 1437) = Sparse.eval nodeValue1437 (mixedVector B) := by
    change mixedMoment B node1437 node1437Labels = _
    exact sound1437 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm476, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1368, h1373, h1375, h1437, h3055, h4092, reducedSource398] using sourceEq476 B hB

theorem rowSound398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row398 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck398, numericCheck398, reducedZero398 B hB hF, mul_zero]

theorem reducedZero399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource399 (mixedVector B) = 0 := by
  have h1368 : mixedVector B (Sum.inr 1368) = Sparse.eval nodeValue1368 (mixedVector B) := by
    change mixedMoment B node1368 node1368Labels = _
    exact sound1368 B hB hF
  have h2882 : mixedVector B (Sum.inr 2882) = Sparse.eval nodeValue2882 (mixedVector B) := by
    change mixedMoment B node2882 node2882Labels = _
    exact sound2882 B hB hF
  have h2975 : mixedVector B (Sum.inr 2975) = Sparse.eval nodeValue2975 (mixedVector B) := by
    change mixedMoment B node2975 node2975Labels = _
    exact sound2975 B hB hF
  have h3044 : mixedVector B (Sum.inr 3044) = Sparse.eval nodeValue3044 (mixedVector B) := by
    change mixedMoment B node3044 node3044Labels = _
    exact sound3044 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3055 : mixedVector B (Sum.inr 3055) = Sparse.eval nodeValue3055 (mixedVector B) := by
    change mixedMoment B node3055 node3055Labels = _
    exact sound3055 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm477, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1368, h2882, h2975, h3044, h3051, h3055, h4092, reducedSource399] using sourceEq477 B hB

theorem rowSound399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row399 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck399, numericCheck399, reducedZero399 B hB hF, mul_zero]

theorem sourceRowsAt384 : MixedData.sourceRows (384 : Fin 2425) =
    MixedData.row384 := by decide +kernel

theorem sourceRowsAt385 : MixedData.sourceRows (385 : Fin 2425) =
    MixedData.row385 := by decide +kernel

theorem sourceRowsAt386 : MixedData.sourceRows (386 : Fin 2425) =
    MixedData.row386 := by decide +kernel

theorem sourceRowsAt387 : MixedData.sourceRows (387 : Fin 2425) =
    MixedData.row387 := by decide +kernel

theorem sourceRowsAt388 : MixedData.sourceRows (388 : Fin 2425) =
    MixedData.row388 := by decide +kernel

theorem sourceRowsAt389 : MixedData.sourceRows (389 : Fin 2425) =
    MixedData.row389 := by decide +kernel

theorem sourceRowsAt390 : MixedData.sourceRows (390 : Fin 2425) =
    MixedData.row390 := by decide +kernel

theorem sourceRowsAt391 : MixedData.sourceRows (391 : Fin 2425) =
    MixedData.row391 := by decide +kernel

theorem sourceRowsAt392 : MixedData.sourceRows (392 : Fin 2425) =
    MixedData.row392 := by decide +kernel

theorem sourceRowsAt393 : MixedData.sourceRows (393 : Fin 2425) =
    MixedData.row393 := by decide +kernel

theorem sourceRowsAt394 : MixedData.sourceRows (394 : Fin 2425) =
    MixedData.row394 := by decide +kernel

theorem sourceRowsAt395 : MixedData.sourceRows (395 : Fin 2425) =
    MixedData.row395 := by decide +kernel

theorem sourceRowsAt396 : MixedData.sourceRows (396 : Fin 2425) =
    MixedData.row396 := by decide +kernel

theorem sourceRowsAt397 : MixedData.sourceRows (397 : Fin 2425) =
    MixedData.row397 := by decide +kernel

theorem sourceRowsAt398 : MixedData.sourceRows (398 : Fin 2425) =
    MixedData.row398 := by decide +kernel

theorem sourceRowsAt399 : MixedData.sourceRows (399 : Fin 2425) =
    MixedData.row399 := by decide +kernel

theorem chunkSound24_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 24) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 384 ∨ k.val = 385 ∨ k.val = 386 ∨ k.val = 387 ∨ k.val = 388 ∨ k.val = 389 ∨ k.val = 390 ∨ k.val = 391 ∨ k.val = 392 ∨ k.val = 393 ∨ k.val = 394 ∨ k.val = 395 ∨ k.val = 396 ∨ k.val = 397 ∨ k.val = 398 ∨ k.val = 399 := by omega
  rcases heq with h384 | h385 | h386 | h387 | h388 | h389 | h390 | h391 | h392 | h393 | h394 | h395 | h396 | h397 | h398 | h399
  · have he : k = (384 : Fin 2425) := Fin.ext h384
    subst k
    rw [sourceRowsAt384]
    exact rowSound384 B hB hF
  · have he : k = (385 : Fin 2425) := Fin.ext h385
    subst k
    rw [sourceRowsAt385]
    exact rowSound385 B hB hF
  · have he : k = (386 : Fin 2425) := Fin.ext h386
    subst k
    rw [sourceRowsAt386]
    exact rowSound386 B hB hF
  · have he : k = (387 : Fin 2425) := Fin.ext h387
    subst k
    rw [sourceRowsAt387]
    exact rowSound387 B hB hF
  · have he : k = (388 : Fin 2425) := Fin.ext h388
    subst k
    rw [sourceRowsAt388]
    exact rowSound388_e B hB hF
  · have he : k = (389 : Fin 2425) := Fin.ext h389
    subst k
    rw [sourceRowsAt389]
    exact rowSound389 B hB hF
  · have he : k = (390 : Fin 2425) := Fin.ext h390
    subst k
    rw [sourceRowsAt390]
    exact rowSound390 B hB hF
  · have he : k = (391 : Fin 2425) := Fin.ext h391
    subst k
    rw [sourceRowsAt391]
    exact rowSound391_e B hB hF
  · have he : k = (392 : Fin 2425) := Fin.ext h392
    subst k
    rw [sourceRowsAt392]
    exact rowSound392_e B hB hF
  · have he : k = (393 : Fin 2425) := Fin.ext h393
    subst k
    rw [sourceRowsAt393]
    exact rowSound393 B hB hF
  · have he : k = (394 : Fin 2425) := Fin.ext h394
    subst k
    rw [sourceRowsAt394]
    exact rowSound394 B hB hF
  · have he : k = (395 : Fin 2425) := Fin.ext h395
    subst k
    rw [sourceRowsAt395]
    exact rowSound395_e B hB hF
  · have he : k = (396 : Fin 2425) := Fin.ext h396
    subst k
    rw [sourceRowsAt396]
    exact rowSound396_e B hB hF
  · have he : k = (397 : Fin 2425) := Fin.ext h397
    subst k
    rw [sourceRowsAt397]
    exact rowSound397 B hB hF
  · have he : k = (398 : Fin 2425) := Fin.ext h398
    subst k
    rw [sourceRowsAt398]
    exact rowSound398 B hB hF
  · have he : k = (399 : Fin 2425) := Fin.ext h399
    subst k
    rw [sourceRowsAt399]
    exact rowSound399 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound24_e_oai
