-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:53:10.873621+00:00
-- url     : https://prove2.me/submissions/10c080c2-4dd3-4514-8731-f95b86bfda13

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound226_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound236_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6104 raw6104Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw6104 raw6104Labels = mixedMoment B raw6104step0 raw6104step0Labels := by
      have hz : ∀ j, raw6104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6104step0 = (fun i j => raw6104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6104step0 raw6104; decide +kernel
      have hl : raw6104step0Labels = raw6104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6104 raw6104Labels permutation434 hz
    mixedMoment B raw6104step0 raw6104step0Labels = mixedMoment B raw6104step1 raw6104step1Labels := by
      have hz : ∀ j, raw6104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6104step1 = (fun i j => raw6104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6104step1 raw6104step0; decide +kernel
      have hl : raw6104step1Labels = raw6104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6104step0 raw6104step0Labels permutation80 hz
    mixedMoment B raw6104step1 raw6104step1Labels = mixedMoment B raw6104step2 raw6104step2Labels := by
      have ha : raw6104step2 = (fun i j => raw6104step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6104step2 raw6104step1; decide +kernel
      have hl : raw6104step2Labels = raw6104step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6104step1 raw6104step1Labels permutation10 permutation2
    mixedMoment B raw6104step2 raw6104step2Labels = mixedMoment B raw6104step3 raw6104step3Labels := by
      have ha : raw6104step3 = -raw6104step2 := by apply Matrix.ext; change ∀ i j, raw6104step3 i j = -(raw6104step2 i j); unfold raw6104step3 raw6104step2; decide +kernel
      have hl : raw6104step3Labels = raw6104step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical6121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6121 raw6121Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw6121 raw6121Labels = mixedMoment B raw6121step0 raw6121step0Labels := by
      have hz : ∀ j, raw6121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6121step0 = (fun i j => raw6121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6121step0 raw6121; decide +kernel
      have hl : raw6121step0Labels = raw6121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121 raw6121Labels permutation434 hz
    mixedMoment B raw6121step0 raw6121step0Labels = mixedMoment B raw6121step1 raw6121step1Labels := by
      have hz : ∀ j, raw6121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6121step1 = (fun i j => raw6121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6121step1 raw6121step0; decide +kernel
      have hl : raw6121step1Labels = raw6121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121step0 raw6121step0Labels permutation80 hz
    mixedMoment B raw6121step1 raw6121step1Labels = mixedMoment B raw6121step2 raw6121step2Labels := by
      have hz : ∀ j, raw6121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6121step2 = (fun i j => raw6121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6121step2 raw6121step1; decide +kernel
      have hl : raw6121step2Labels = raw6121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121step1 raw6121step1Labels permutation14 hz
    mixedMoment B raw6121step2 raw6121step2Labels = mixedMoment B raw6121step3 raw6121step3Labels := by
      have ha : raw6121step3 = (fun i j => raw6121step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6121step3 raw6121step2; decide +kernel
      have hl : raw6121step3Labels = raw6121step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6121step2 raw6121step2Labels permutation3 permutation4
    mixedMoment B raw6121step3 raw6121step3Labels = mixedMoment B raw6121step4 raw6121step4Labels := by
      have ha : raw6121step4 = -raw6121step3 := by apply Matrix.ext; change ∀ i j, raw6121step4 i j = -(raw6121step3 i j); unfold raw6121step4 raw6121step3; decide +kernel
      have hl : raw6121step4Labels = raw6121step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

theorem canonical6122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6122 raw6122Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6122 raw6122Labels = mixedMoment B raw6122step0 raw6122step0Labels := by
      have hz : ∀ j, raw6122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6122step0 = (fun i j => raw6122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6122step0 raw6122; decide +kernel
      have hl : raw6122step0Labels = raw6122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6122 raw6122Labels permutation346 hz
    mixedMoment B raw6122step0 raw6122step0Labels = mixedMoment B raw6122step1 raw6122step1Labels := by
      have ha : raw6122step1 = (fun i j => raw6122step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6122step1 raw6122step0; decide +kernel
      have hl : raw6122step1Labels = raw6122step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6122step0 raw6122step0Labels permutation36 permutation4
    mixedMoment B raw6122step1 raw6122step1Labels = mixedMoment B raw6122step2 raw6122step2Labels := by
      have ha : raw6122step2 = -raw6122step1 := by apply Matrix.ext; change ∀ i j, raw6122step2 i j = -(raw6122step1 i j); unfold raw6122step2 raw6122step1; decide +kernel
      have hl : raw6122step2Labels = raw6122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6216 raw6216Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw6216 raw6216Labels = mixedMoment B raw6216step0 raw6216step0Labels := by
      have hz : ∀ j, raw6216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6216step0 = (fun i j => raw6216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6216step0 raw6216; decide +kernel
      have hl : raw6216step0Labels = raw6216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6216 raw6216Labels permutation346 hz
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical6220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6220 raw6220Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6220 raw6220Labels = mixedMoment B raw6220step0 raw6220step0Labels := by
      have hz : ∀ j, raw6220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6220step0 = (fun i j => raw6220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6220step0 raw6220; decide +kernel
      have hl : raw6220step0Labels = raw6220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6220 raw6220Labels permutation346 hz
    mixedMoment B raw6220step0 raw6220step0Labels = mixedMoment B raw6220step1 raw6220step1Labels := by
      have ha : raw6220step1 = (fun i j => raw6220step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6220step1 raw6220step0; decide +kernel
      have hl : raw6220step1Labels = raw6220step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6220step0 raw6220step0Labels permutation116 permutation4
    mixedMoment B raw6220step1 raw6220step1Labels = mixedMoment B raw6220step2 raw6220step2Labels := by
      have ha : raw6220step2 = -raw6220step1 := by apply Matrix.ext; change ∀ i j, raw6220step2 i j = -(raw6220step1 i j); unfold raw6220step2 raw6220step1; decide +kernel
      have hl : raw6220step2Labels = raw6220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical6222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6222 raw6222Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6222 raw6222Labels = mixedMoment B raw6222step0 raw6222step0Labels := by
      have hz : ∀ j, raw6222 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw6222step0 = (fun i j => raw6222 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw6222step0 raw6222; decide +kernel
      have hl : raw6222step0Labels = raw6222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6222 raw6222Labels permutation590 hz
    mixedMoment B raw6222step0 raw6222step0Labels = mixedMoment B raw6222step1 raw6222step1Labels := by
      have hz : ∀ j, raw6222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6222step1 = (fun i j => raw6222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6222step1 raw6222step0; decide +kernel
      have hl : raw6222step1Labels = raw6222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6222step0 raw6222step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical6227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6227 raw6227Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw6227 raw6227Labels = mixedMoment B raw6227step0 raw6227step0Labels := by
      have hz : ∀ j, raw6227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6227step0 = (fun i j => raw6227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6227step0 raw6227; decide +kernel
      have hl : raw6227step0Labels = raw6227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6227 raw6227Labels permutation346 hz
    _ = mixedMoment B node1218 node1218Labels := by rfl

theorem canonical6230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6230 raw6230Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw6230 raw6230Labels = mixedMoment B raw6230step0 raw6230step0Labels := by
      have hz : ∀ j, raw6230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6230step0 = (fun i j => raw6230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6230step0 raw6230; decide +kernel
      have hl : raw6230step0Labels = raw6230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6230 raw6230Labels permutation346 hz
    mixedMoment B raw6230step0 raw6230step0Labels = mixedMoment B raw6230step1 raw6230step1Labels := by
      have ha : raw6230step1 = (fun i j => raw6230step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6230step1 raw6230step0; decide +kernel
      have hl : raw6230step1Labels = raw6230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6230step0 raw6230step0Labels permutation40 permutation2
    _ = mixedMoment B node2758 node2758Labels := by rfl

theorem canonical6235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6235 raw6235Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw6235 raw6235Labels = mixedMoment B raw6235step0 raw6235step0Labels := by
      have hz : ∀ j, raw6235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6235step0 = (fun i j => raw6235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6235step0 raw6235; decide +kernel
      have hl : raw6235step0Labels = raw6235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6235 raw6235Labels permutation346 hz
    _ = mixedMoment B node2486 node2486Labels := by rfl

theorem canonical6237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6237 raw6237Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw6237 raw6237Labels = mixedMoment B raw6237step0 raw6237step0Labels := by
      have ha : raw6237step0 = (fun i j => raw6237 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6237step0 raw6237; decide +kernel
      have hl : raw6237step0Labels = raw6237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6237 raw6237Labels permutation160 permutation2
    _ = mixedMoment B node2714 node2714Labels := by rfl

theorem canonical6241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6241 raw6241Labels = mixedMoment B node2544 node2544Labels := by
  calc
    mixedMoment B raw6241 raw6241Labels = mixedMoment B raw6241step0 raw6241step0Labels := by
      have ha : raw6241step0 = (fun i j => raw6241 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6241step0 raw6241; decide +kernel
      have hl : raw6241step0Labels = raw6241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6241 raw6241Labels permutation176 permutation2
    _ = mixedMoment B node2544 node2544Labels := by rfl

theorem canonical6242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6242 raw6242Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6242 raw6242Labels = mixedMoment B raw6242step0 raw6242step0Labels := by
      have hz : ∀ j, raw6242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6242step0 = (fun i j => raw6242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6242step0 raw6242; decide +kernel
      have hl : raw6242step0Labels = raw6242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6242 raw6242Labels permutation346 hz
    mixedMoment B raw6242step0 raw6242step0Labels = mixedMoment B raw6242step1 raw6242step1Labels := by
      have ha : raw6242step1 = (fun i j => raw6242step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6242step1 raw6242step0; decide +kernel
      have hl : raw6242step1Labels = raw6242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6242step0 raw6242step0Labels permutation34 permutation2
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical6245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6245 raw6245Labels = mixedMoment B node2619 node2619Labels := by
  calc
    mixedMoment B raw6245 raw6245Labels = mixedMoment B raw6245step0 raw6245step0Labels := by
      have hz : ∀ j, raw6245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6245step0 = (fun i j => raw6245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6245step0 raw6245; decide +kernel
      have hl : raw6245step0Labels = raw6245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6245 raw6245Labels permutation346 hz
    mixedMoment B raw6245step0 raw6245step0Labels = mixedMoment B raw6245step1 raw6245step1Labels := by
      have ha : raw6245step1 = (fun i j => raw6245step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6245step1 raw6245step0; decide +kernel
      have hl : raw6245step1Labels = raw6245step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6245step0 raw6245step0Labels permutation38 permutation2
    _ = mixedMoment B node2619 node2619Labels := by rfl

theorem canonical6247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6247 raw6247Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw6247 raw6247Labels = mixedMoment B raw6247step0 raw6247step0Labels := by
      have hz : ∀ j, raw6247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6247step0 = (fun i j => raw6247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6247step0 raw6247; decide +kernel
      have hl : raw6247step0Labels = raw6247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6247 raw6247Labels permutation346 hz
    _ = mixedMoment B node2716 node2716Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6338 raw6338Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6338 raw6338Labels = mixedMoment B raw6338step0 raw6338step0Labels := by
      have hz : ∀ j, raw6338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6338step0 = (fun i j => raw6338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6338step0 raw6338; decide +kernel
      have hl : raw6338step0Labels = raw6338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6338 raw6338Labels permutation346 hz
    mixedMoment B raw6338step0 raw6338step0Labels = mixedMoment B raw6338step1 raw6338step1Labels := by
      have ha : raw6338step1 = (fun i j => raw6338step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6338step1 raw6338step0; decide +kernel
      have hl : raw6338step1Labels = raw6338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6338step0 raw6338step0Labels permutation38 permutation2
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical6339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6339 raw6339Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw6339 raw6339Labels = mixedMoment B raw6339step0 raw6339step0Labels := by
      have hz : ∀ j, raw6339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6339step0 = (fun i j => raw6339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6339step0 raw6339; decide +kernel
      have hl : raw6339step0Labels = raw6339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6339 raw6339Labels permutation346 hz
    mixedMoment B raw6339step0 raw6339step0Labels = mixedMoment B raw6339step1 raw6339step1Labels := by
      have ha : raw6339step1 = (fun i j => raw6339step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6339step1 raw6339step0; decide +kernel
      have hl : raw6339step1Labels = raw6339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6339step0 raw6339step0Labels permutation151 permutation2
    mixedMoment B raw6339step1 raw6339step1Labels = mixedMoment B raw6339step2 raw6339step2Labels := by
      have ha : raw6339step2 = -raw6339step1 := by apply Matrix.ext; change ∀ i j, raw6339step2 i j = -(raw6339step1 i j); unfold raw6339step2 raw6339step1; decide +kernel
      have hl : raw6339step2Labels = raw6339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical6340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6340 raw6340Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw6340 raw6340Labels = mixedMoment B raw6340step0 raw6340step0Labels := by
      have ha : raw6340step0 = (fun i j => raw6340 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6340step0 raw6340; decide +kernel
      have hl : raw6340step0Labels = raw6340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6340 raw6340Labels permutation676 permutation2
    mixedMoment B raw6340step0 raw6340step0Labels = mixedMoment B raw6340step1 raw6340step1Labels := by
      have ha : raw6340step1 = -raw6340step0 := by apply Matrix.ext; change ∀ i j, raw6340step1 i j = -(raw6340step0 i j); unfold raw6340step1 raw6340step0; decide +kernel
      have hl : raw6340step1Labels = raw6340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical6341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6341 raw6341Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw6341 raw6341Labels = mixedMoment B raw6341step0 raw6341step0Labels := by
      have hz : ∀ j, raw6341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6341step0 = (fun i j => raw6341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6341step0 raw6341; decide +kernel
      have hl : raw6341step0Labels = raw6341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6341 raw6341Labels permutation346 hz
    mixedMoment B raw6341step0 raw6341step0Labels = mixedMoment B raw6341step1 raw6341step1Labels := by
      have ha : raw6341step1 = (fun i j => raw6341step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6341step1 raw6341step0; decide +kernel
      have hl : raw6341step1Labels = raw6341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6341step0 raw6341step0Labels permutation149 permutation2
    mixedMoment B raw6341step1 raw6341step1Labels = mixedMoment B raw6341step2 raw6341step2Labels := by
      have ha : raw6341step2 = -raw6341step1 := by apply Matrix.ext; change ∀ i j, raw6341step2 i j = -(raw6341step1 i j); unfold raw6341step2 raw6341step1; decide +kernel
      have hl : raw6341step2Labels = raw6341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical6342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6342 raw6342Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw6342 raw6342Labels = mixedMoment B raw6342step0 raw6342step0Labels := by
      have hz : ∀ j, raw6342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6342step0 = (fun i j => raw6342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6342step0 raw6342; decide +kernel
      have hl : raw6342step0Labels = raw6342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6342 raw6342Labels permutation346 hz
    mixedMoment B raw6342step0 raw6342step0Labels = mixedMoment B raw6342step1 raw6342step1Labels := by
      have ha : raw6342step1 = (fun i j => raw6342step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6342step1 raw6342step0; decide +kernel
      have hl : raw6342step1Labels = raw6342step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6342step0 raw6342step0Labels permutation137 permutation2
    mixedMoment B raw6342step1 raw6342step1Labels = mixedMoment B raw6342step2 raw6342step2Labels := by
      have ha : raw6342step2 = -raw6342step1 := by apply Matrix.ext; change ∀ i j, raw6342step2 i j = -(raw6342step1 i j); unfold raw6342step2 raw6342step1; decide +kernel
      have hl : raw6342step2Labels = raw6342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical6343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6343 raw6343Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw6343 raw6343Labels = mixedMoment B raw6343step0 raw6343step0Labels := by
      have hz : ∀ j, raw6343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6343step0 = (fun i j => raw6343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6343step0 raw6343; decide +kernel
      have hl : raw6343step0Labels = raw6343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6343 raw6343Labels permutation346 hz
    mixedMoment B raw6343step0 raw6343step0Labels = mixedMoment B raw6343step1 raw6343step1Labels := by
      have ha : raw6343step1 = (fun i j => raw6343step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6343step1 raw6343step0; decide +kernel
      have hl : raw6343step1Labels = raw6343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6343step0 raw6343step0Labels permutation116 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical6344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6344 raw6344Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw6344 raw6344Labels = mixedMoment B raw6344step0 raw6344step0Labels := by
      have hz : ∀ j, raw6344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6344step0 = (fun i j => raw6344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6344step0 raw6344; decide +kernel
      have hl : raw6344step0Labels = raw6344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6344 raw6344Labels permutation346 hz
    mixedMoment B raw6344step0 raw6344step0Labels = mixedMoment B raw6344step1 raw6344step1Labels := by
      have ha : raw6344step1 = (fun i j => raw6344step0 (permutation134 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6344step1 raw6344step0; decide +kernel
      have hl : raw6344step1Labels = raw6344step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6344step0 raw6344step0Labels permutation134 permutation0
    mixedMoment B raw6344step1 raw6344step1Labels = mixedMoment B raw6344step2 raw6344step2Labels := by
      have ha : raw6344step2 = -raw6344step1 := by apply Matrix.ext; change ∀ i j, raw6344step2 i j = -(raw6344step1 i j); unfold raw6344step2 raw6344step1; decide +kernel
      have hl : raw6344step2Labels = raw6344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical6345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6345 raw6345Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw6345 raw6345Labels = mixedMoment B raw6345step0 raw6345step0Labels := by
      have hz : ∀ j, raw6345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6345step0 = (fun i j => raw6345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6345step0 raw6345; decide +kernel
      have hl : raw6345step0Labels = raw6345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6345 raw6345Labels permutation346 hz
    mixedMoment B raw6345step0 raw6345step0Labels = mixedMoment B raw6345step1 raw6345step1Labels := by
      have ha : raw6345step1 = (fun i j => raw6345step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6345step1 raw6345step0; decide +kernel
      have hl : raw6345step1Labels = raw6345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6345step0 raw6345step0Labels permutation40 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

theorem canonical6346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6346 raw6346Labels = mixedMoment B node1392 node1392Labels := by
  calc
    mixedMoment B raw6346 raw6346Labels = mixedMoment B raw6346step0 raw6346step0Labels := by
      have ha : raw6346step0 = (fun i j => raw6346 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6346step0 raw6346; decide +kernel
      have hl : raw6346step0Labels = raw6346Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6346 raw6346Labels permutation202 permutation2
    _ = mixedMoment B node1392 node1392Labels := by rfl

theorem canonical6347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6347 raw6347Labels = mixedMoment B node1425 node1425Labels := by
  calc
    mixedMoment B raw6347 raw6347Labels = mixedMoment B raw6347step0 raw6347step0Labels := by
      have hz : ∀ j, raw6347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6347step0 = (fun i j => raw6347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6347step0 raw6347; decide +kernel
      have hl : raw6347step0Labels = raw6347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6347 raw6347Labels permutation346 hz
    _ = mixedMoment B node1425 node1425Labels := by rfl

theorem canonical6348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6348 raw6348Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw6348 raw6348Labels = mixedMoment B raw6348step0 raw6348step0Labels := by
      have hz : ∀ j, raw6348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6348step0 = (fun i j => raw6348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6348step0 raw6348; decide +kernel
      have hl : raw6348step0Labels = raw6348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6348 raw6348Labels permutation346 hz
    mixedMoment B raw6348step0 raw6348step0Labels = mixedMoment B raw6348step1 raw6348step1Labels := by
      have ha : raw6348step1 = (fun i j => raw6348step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6348step1 raw6348step0; decide +kernel
      have hl : raw6348step1Labels = raw6348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6348step0 raw6348step0Labels permutation38 permutation2
    _ = mixedMoment B node1400 node1400Labels := by rfl

theorem canonical6349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6349 raw6349Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw6349 raw6349Labels = mixedMoment B raw6349step0 raw6349step0Labels := by
      have hz : ∀ j, raw6349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6349step0 = (fun i j => raw6349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6349step0 raw6349; decide +kernel
      have hl : raw6349step0Labels = raw6349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6349 raw6349Labels permutation346 hz
    mixedMoment B raw6349step0 raw6349step0Labels = mixedMoment B raw6349step1 raw6349step1Labels := by
      have ha : raw6349step1 = (fun i j => raw6349step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6349step1 raw6349step0; decide +kernel
      have hl : raw6349step1Labels = raw6349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6349step0 raw6349step0Labels permutation38 permutation2
    _ = mixedMoment B node1394 node1394Labels := by rfl

theorem canonical6350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6350 raw6350Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw6350 raw6350Labels = mixedMoment B raw6350step0 raw6350step0Labels := by
      have ha : raw6350step0 = (fun i j => raw6350 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6350step0 raw6350; decide +kernel
      have hl : raw6350step0Labels = raw6350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6350 raw6350Labels permutation184 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

theorem canonical6351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6351 raw6351Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw6351 raw6351Labels = mixedMoment B raw6351step0 raw6351step0Labels := by
      have hz : ∀ j, raw6351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6351step0 = (fun i j => raw6351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6351step0 raw6351; decide +kernel
      have hl : raw6351step0Labels = raw6351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6351 raw6351Labels permutation346 hz
    mixedMoment B raw6351step0 raw6351step0Labels = mixedMoment B raw6351step1 raw6351step1Labels := by
      have ha : raw6351step1 = (fun i j => raw6351step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6351step1 raw6351step0; decide +kernel
      have hl : raw6351step1Labels = raw6351step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6351step0 raw6351step0Labels permutation40 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical6352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6352 raw6352Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw6352 raw6352Labels = mixedMoment B raw6352step0 raw6352step0Labels := by
      have hz : ∀ j, raw6352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6352step0 = (fun i j => raw6352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6352step0 raw6352; decide +kernel
      have hl : raw6352step0Labels = raw6352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6352 raw6352Labels permutation346 hz
    mixedMoment B raw6352step0 raw6352step0Labels = mixedMoment B raw6352step1 raw6352step1Labels := by
      have ha : raw6352step1 = (fun i j => raw6352step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6352step1 raw6352step0; decide +kernel
      have hl : raw6352step1Labels = raw6352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6352step0 raw6352step0Labels permutation40 permutation2
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical6353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6353 raw6353Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw6353 raw6353Labels = mixedMoment B raw6353step0 raw6353step0Labels := by
      have hz : ∀ j, raw6353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6353step0 = (fun i j => raw6353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6353step0 raw6353; decide +kernel
      have hl : raw6353step0Labels = raw6353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6353 raw6353Labels permutation346 hz
    mixedMoment B raw6353step0 raw6353step0Labels = mixedMoment B raw6353step1 raw6353step1Labels := by
      have ha : raw6353step1 = (fun i j => raw6353step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6353step1 raw6353step0; decide +kernel
      have hl : raw6353step1Labels = raw6353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6353step0 raw6353step0Labels permutation40 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical6354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6354 raw6354Labels = mixedMoment B node3013 node3013Labels := by
  calc
    mixedMoment B raw6354 raw6354Labels = mixedMoment B raw6354step0 raw6354step0Labels := by
      have ha : raw6354step0 = (fun i j => raw6354 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6354step0 raw6354; decide +kernel
      have hl : raw6354step0Labels = raw6354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6354 raw6354Labels permutation160 permutation2
    _ = mixedMoment B node3013 node3013Labels := by rfl

theorem canonical6355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6355 raw6355Labels = mixedMoment B node3014 node3014Labels := by
  calc
    mixedMoment B raw6355 raw6355Labels = mixedMoment B raw6355step0 raw6355step0Labels := by
      have hz : ∀ j, raw6355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6355step0 = (fun i j => raw6355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6355step0 raw6355; decide +kernel
      have hl : raw6355step0Labels = raw6355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6355 raw6355Labels permutation346 hz
    _ = mixedMoment B node3014 node3014Labels := by rfl

theorem canonical6356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6356 raw6356Labels = mixedMoment B node2949 node2949Labels := by
  calc
    mixedMoment B raw6356 raw6356Labels = mixedMoment B raw6356step0 raw6356step0Labels := by
      have hz : ∀ j, raw6356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6356step0 = (fun i j => raw6356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6356step0 raw6356; decide +kernel
      have hl : raw6356step0Labels = raw6356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6356 raw6356Labels permutation346 hz
    mixedMoment B raw6356step0 raw6356step0Labels = mixedMoment B raw6356step1 raw6356step1Labels := by
      have ha : raw6356step1 = (fun i j => raw6356step0 (permutation120 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6356step1 raw6356step0; decide +kernel
      have hl : raw6356step1Labels = raw6356step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6356step0 raw6356step0Labels permutation120 permutation4
    _ = mixedMoment B node2949 node2949Labels := by rfl

theorem canonical6357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6357 raw6357Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw6357 raw6357Labels = mixedMoment B raw6357step0 raw6357step0Labels := by
      have hz : ∀ j, raw6357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6357step0 = (fun i j => raw6357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6357step0 raw6357; decide +kernel
      have hl : raw6357step0Labels = raw6357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6357 raw6357Labels permutation346 hz
    mixedMoment B raw6357step0 raw6357step0Labels = mixedMoment B raw6357step1 raw6357step1Labels := by
      have ha : raw6357step1 = (fun i j => raw6357step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6357step1 raw6357step0; decide +kernel
      have hl : raw6357step1Labels = raw6357step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6357step0 raw6357step0Labels permutation151 permutation2
    mixedMoment B raw6357step1 raw6357step1Labels = mixedMoment B raw6357step2 raw6357step2Labels := by
      have ha : raw6357step2 = -raw6357step1 := by apply Matrix.ext; change ∀ i j, raw6357step2 i j = -(raw6357step1 i j); unfold raw6357step2 raw6357step1; decide +kernel
      have hl : raw6357step2Labels = raw6357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2624 node2624Labels := by rfl

theorem canonical6358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6358 raw6358Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw6358 raw6358Labels = mixedMoment B raw6358step0 raw6358step0Labels := by
      have ha : raw6358step0 = (fun i j => raw6358 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6358step0 raw6358; decide +kernel
      have hl : raw6358step0Labels = raw6358Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6358 raw6358Labels permutation202 permutation2
    _ = mixedMoment B node2933 node2933Labels := by rfl

theorem canonical6359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6359 raw6359Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw6359 raw6359Labels = mixedMoment B raw6359step0 raw6359step0Labels := by
      have ha : raw6359step0 = (fun i j => raw6359 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6359step0 raw6359; decide +kernel
      have hl : raw6359step0Labels = raw6359Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6359 raw6359Labels permutation212 permutation2
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical6360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6360 raw6360Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw6360 raw6360Labels = mixedMoment B raw6360step0 raw6360step0Labels := by
      have ha : raw6360step0 = (fun i j => raw6360 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6360step0 raw6360; decide +kernel
      have hl : raw6360step0Labels = raw6360Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6360 raw6360Labels permutation202 permutation2
    _ = mixedMoment B node3084 node3084Labels := by rfl

theorem canonical6361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6361 raw6361Labels = mixedMoment B node2992 node2992Labels := by
  calc
    mixedMoment B raw6361 raw6361Labels = mixedMoment B raw6361step0 raw6361step0Labels := by
      have ha : raw6361step0 = (fun i j => raw6361 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6361step0 raw6361; decide +kernel
      have hl : raw6361step0Labels = raw6361Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6361 raw6361Labels permutation176 permutation2
    _ = mixedMoment B node2992 node2992Labels := by rfl

theorem canonical6362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6362 raw6362Labels = mixedMoment B node2947 node2947Labels := by
  calc
    mixedMoment B raw6362 raw6362Labels = mixedMoment B raw6362step0 raw6362step0Labels := by
      have ha : raw6362step0 = (fun i j => raw6362 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6362step0 raw6362; decide +kernel
      have hl : raw6362step0Labels = raw6362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6362 raw6362Labels permutation568 permutation4
    _ = mixedMoment B node2947 node2947Labels := by rfl

theorem canonical6363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6363 raw6363Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw6363 raw6363Labels = mixedMoment B raw6363step0 raw6363step0Labels := by
      have ha : raw6363step0 = (fun i j => raw6363 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6363step0 raw6363; decide +kernel
      have hl : raw6363step0Labels = raw6363Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6363 raw6363Labels permutation676 permutation2
    mixedMoment B raw6363step0 raw6363step0Labels = mixedMoment B raw6363step1 raw6363step1Labels := by
      have ha : raw6363step1 = -raw6363step0 := by apply Matrix.ext; change ∀ i j, raw6363step1 i j = -(raw6363step0 i j); unfold raw6363step1 raw6363step0; decide +kernel
      have hl : raw6363step1Labels = raw6363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2610 node2610Labels := by rfl

theorem canonical6364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6364 raw6364Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6364 raw6364Labels = mixedMoment B raw6364step0 raw6364step0Labels := by
      have hz : ∀ j, raw6364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6364step0 = (fun i j => raw6364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6364step0 raw6364; decide +kernel
      have hl : raw6364step0Labels = raw6364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6364 raw6364Labels permutation346 hz
    mixedMoment B raw6364step0 raw6364step0Labels = mixedMoment B raw6364step1 raw6364step1Labels := by
      have ha : raw6364step1 = (fun i j => raw6364step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6364step1 raw6364step0; decide +kernel
      have hl : raw6364step1Labels = raw6364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6364step0 raw6364step0Labels permutation44 permutation2
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical6365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6365 raw6365Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw6365 raw6365Labels = mixedMoment B raw6365step0 raw6365step0Labels := by
      have hz : ∀ j, raw6365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6365step0 = (fun i j => raw6365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6365step0 raw6365; decide +kernel
      have hl : raw6365step0Labels = raw6365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6365 raw6365Labels permutation346 hz
    _ = mixedMoment B node3108 node3108Labels := by rfl

theorem canonical6366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6366 raw6366Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw6366 raw6366Labels = mixedMoment B raw6366step0 raw6366step0Labels := by
      have hz : ∀ j, raw6366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6366step0 = (fun i j => raw6366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6366step0 raw6366; decide +kernel
      have hl : raw6366step0Labels = raw6366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6366 raw6366Labels permutation346 hz
    mixedMoment B raw6366step0 raw6366step0Labels = mixedMoment B raw6366step1 raw6366step1Labels := by
      have ha : raw6366step1 = (fun i j => raw6366step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6366step1 raw6366step0; decide +kernel
      have hl : raw6366step1Labels = raw6366step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6366step0 raw6366step0Labels permutation38 permutation2
    _ = mixedMoment B node2942 node2942Labels := by rfl

theorem canonical6367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6367 raw6367Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw6367 raw6367Labels = mixedMoment B raw6367step0 raw6367step0Labels := by
      have hz : ∀ j, raw6367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6367step0 = (fun i j => raw6367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6367step0 raw6367; decide +kernel
      have hl : raw6367step0Labels = raw6367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6367 raw6367Labels permutation346 hz
    mixedMoment B raw6367step0 raw6367step0Labels = mixedMoment B raw6367step1 raw6367step1Labels := by
      have ha : raw6367step1 = (fun i j => raw6367step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6367step1 raw6367step0; decide +kernel
      have hl : raw6367step1Labels = raw6367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6367step0 raw6367step0Labels permutation149 permutation2
    mixedMoment B raw6367step1 raw6367step1Labels = mixedMoment B raw6367step2 raw6367step2Labels := by
      have ha : raw6367step2 = -raw6367step1 := by apply Matrix.ext; change ∀ i j, raw6367step2 i j = -(raw6367step1 i j); unfold raw6367step2 raw6367step1; decide +kernel
      have hl : raw6367step2Labels = raw6367step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical6368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6368 raw6368Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw6368 raw6368Labels = mixedMoment B raw6368step0 raw6368step0Labels := by
      have hz : ∀ j, raw6368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6368step0 = (fun i j => raw6368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6368step0 raw6368; decide +kernel
      have hl : raw6368step0Labels = raw6368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6368 raw6368Labels permutation346 hz
    mixedMoment B raw6368step0 raw6368step0Labels = mixedMoment B raw6368step1 raw6368step1Labels := by
      have ha : raw6368step1 = (fun i j => raw6368step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6368step1 raw6368step0; decide +kernel
      have hl : raw6368step1Labels = raw6368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6368step0 raw6368step0Labels permutation119 permutation4
    _ = mixedMoment B node2964 node2964Labels := by rfl

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

theorem canonical6435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6435 raw6435Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw6435 raw6435Labels = mixedMoment B raw6435step0 raw6435step0Labels := by
      have hz : ∀ j, raw6435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6435step0 = (fun i j => raw6435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6435step0 raw6435; decide +kernel
      have hl : raw6435step0Labels = raw6435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6435 raw6435Labels permutation346 hz
    mixedMoment B raw6435step0 raw6435step0Labels = mixedMoment B raw6435step1 raw6435step1Labels := by
      have ha : raw6435step1 = (fun i j => raw6435step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6435step1 raw6435step0; decide +kernel
      have hl : raw6435step1Labels = raw6435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6435step0 raw6435step0Labels permutation40 permutation2
    mixedMoment B raw6435step1 raw6435step1Labels = mixedMoment B raw6435step2 raw6435step2Labels := by
      have ha : raw6435step2 = -raw6435step1 := by apply Matrix.ext; change ∀ i j, raw6435step2 i j = -(raw6435step1 i j); unfold raw6435step2 raw6435step1; decide +kernel
      have hl : raw6435step2Labels = raw6435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

theorem canonical6436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6436 raw6436Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw6436 raw6436Labels = mixedMoment B raw6436step0 raw6436step0Labels := by
      have ha : raw6436step0 = (fun i j => raw6436 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6436step0 raw6436; decide +kernel
      have hl : raw6436step0Labels = raw6436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6436 raw6436Labels permutation212 permutation2
    mixedMoment B raw6436step0 raw6436step0Labels = mixedMoment B raw6436step1 raw6436step1Labels := by
      have ha : raw6436step1 = -raw6436step0 := by apply Matrix.ext; change ∀ i j, raw6436step1 i j = -(raw6436step0 i j); unfold raw6436step1 raw6436step0; decide +kernel
      have hl : raw6436step1Labels = raw6436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3502 node3502Labels := by rfl

theorem canonical6437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6437 raw6437Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6437 raw6437Labels = mixedMoment B raw6437step0 raw6437step0Labels := by
      have hz : ∀ j, raw6437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6437step0 = (fun i j => raw6437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6437step0 raw6437; decide +kernel
      have hl : raw6437step0Labels = raw6437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6437 raw6437Labels permutation346 hz
    mixedMoment B raw6437step0 raw6437step0Labels = mixedMoment B raw6437step1 raw6437step1Labels := by
      have ha : raw6437step1 = (fun i j => raw6437step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6437step1 raw6437step0; decide +kernel
      have hl : raw6437step1Labels = raw6437step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6437step0 raw6437step0Labels permutation40 permutation2
    mixedMoment B raw6437step1 raw6437step1Labels = mixedMoment B raw6437step2 raw6437step2Labels := by
      have ha : raw6437step2 = -raw6437step1 := by apply Matrix.ext; change ∀ i j, raw6437step2 i j = -(raw6437step1 i j); unfold raw6437step2 raw6437step1; decide +kernel
      have hl : raw6437step2Labels = raw6437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

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

theorem canonical6440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6440 raw6440Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw6440 raw6440Labels = mixedMoment B raw6440step0 raw6440step0Labels := by
      have ha : raw6440step0 = (fun i j => raw6440 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6440step0 raw6440; decide +kernel
      have hl : raw6440step0Labels = raw6440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6440 raw6440Labels permutation170 permutation4
    mixedMoment B raw6440step0 raw6440step0Labels = mixedMoment B raw6440step1 raw6440step1Labels := by
      have ha : raw6440step1 = -raw6440step0 := by apply Matrix.ext; change ∀ i j, raw6440step1 i j = -(raw6440step0 i j); unfold raw6440step1 raw6440step0; decide +kernel
      have hl : raw6440step1Labels = raw6440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2033 node2033Labels := by rfl

theorem canonical6441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6441 raw6441Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw6441 raw6441Labels = mixedMoment B raw6441step0 raw6441step0Labels := by
      have hz : ∀ j, raw6441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6441step0 = (fun i j => raw6441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6441step0 raw6441; decide +kernel
      have hl : raw6441step0Labels = raw6441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6441 raw6441Labels permutation346 hz
    mixedMoment B raw6441step0 raw6441step0Labels = mixedMoment B raw6441step1 raw6441step1Labels := by
      have ha : raw6441step1 = (fun i j => raw6441step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6441step1 raw6441step0; decide +kernel
      have hl : raw6441step1Labels = raw6441step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6441step0 raw6441step0Labels permutation36 permutation4
    mixedMoment B raw6441step1 raw6441step1Labels = mixedMoment B raw6441step2 raw6441step2Labels := by
      have ha : raw6441step2 = -raw6441step1 := by apply Matrix.ext; change ∀ i j, raw6441step2 i j = -(raw6441step1 i j); unfold raw6441step2 raw6441step1; decide +kernel
      have hl : raw6441step2Labels = raw6441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2039 node2039Labels := by rfl

theorem canonical6442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6442 raw6442Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw6442 raw6442Labels = mixedMoment B raw6442step0 raw6442step0Labels := by
      have hz : ∀ j, raw6442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6442step0 = (fun i j => raw6442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6442step0 raw6442; decide +kernel
      have hl : raw6442step0Labels = raw6442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6442 raw6442Labels permutation346 hz
    mixedMoment B raw6442step0 raw6442step0Labels = mixedMoment B raw6442step1 raw6442step1Labels := by
      have ha : raw6442step1 = (fun i j => raw6442step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6442step1 raw6442step0; decide +kernel
      have hl : raw6442step1Labels = raw6442step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6442step0 raw6442step0Labels permutation36 permutation4
    mixedMoment B raw6442step1 raw6442step1Labels = mixedMoment B raw6442step2 raw6442step2Labels := by
      have ha : raw6442step2 = -raw6442step1 := by apply Matrix.ext; change ∀ i j, raw6442step2 i j = -(raw6442step1 i j); unfold raw6442step2 raw6442step1; decide +kernel
      have hl : raw6442step2Labels = raw6442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical6443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6443 raw6443Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw6443 raw6443Labels = mixedMoment B raw6443step0 raw6443step0Labels := by
      have hz : ∀ j, raw6443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6443step0 = (fun i j => raw6443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6443step0 raw6443; decide +kernel
      have hl : raw6443step0Labels = raw6443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6443 raw6443Labels permutation346 hz
    mixedMoment B raw6443step0 raw6443step0Labels = mixedMoment B raw6443step1 raw6443step1Labels := by
      have ha : raw6443step1 = (fun i j => raw6443step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6443step1 raw6443step0; decide +kernel
      have hl : raw6443step1Labels = raw6443step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6443step0 raw6443step0Labels permutation33 permutation4
    mixedMoment B raw6443step1 raw6443step1Labels = mixedMoment B raw6443step2 raw6443step2Labels := by
      have ha : raw6443step2 = -raw6443step1 := by apply Matrix.ext; change ∀ i j, raw6443step2 i j = -(raw6443step1 i j); unfold raw6443step2 raw6443step1; decide +kernel
      have hl : raw6443step2Labels = raw6443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical6444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6444 raw6444Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6444 raw6444Labels = mixedMoment B raw6444step0 raw6444step0Labels := by
      have hz : ∀ j, raw6444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6444step0 = (fun i j => raw6444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6444step0 raw6444; decide +kernel
      have hl : raw6444step0Labels = raw6444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6444 raw6444Labels permutation265 hz
    mixedMoment B raw6444step0 raw6444step0Labels = mixedMoment B raw6444step1 raw6444step1Labels := by
      have ha : raw6444step1 = (fun i j => raw6444step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6444step1 raw6444step0; decide +kernel
      have hl : raw6444step1Labels = raw6444step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6444step0 raw6444step0Labels permutation36 permutation4
    mixedMoment B raw6444step1 raw6444step1Labels = mixedMoment B raw6444step2 raw6444step2Labels := by
      have ha : raw6444step2 = -raw6444step1 := by apply Matrix.ext; change ∀ i j, raw6444step2 i j = -(raw6444step1 i j); unfold raw6444step2 raw6444step1; decide +kernel
      have hl : raw6444step2Labels = raw6444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical6445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6445 raw6445Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw6445 raw6445Labels = mixedMoment B raw6445step0 raw6445step0Labels := by
      have hz : ∀ j, raw6445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6445step0 = (fun i j => raw6445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6445step0 raw6445; decide +kernel
      have hl : raw6445step0Labels = raw6445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6445 raw6445Labels permutation346 hz
    mixedMoment B raw6445step0 raw6445step0Labels = mixedMoment B raw6445step1 raw6445step1Labels := by
      have hz : ∀ j, raw6445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6445step1 = (fun i j => raw6445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6445step1 raw6445step0; decide +kernel
      have hl : raw6445step1Labels = raw6445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6445step0 raw6445step0Labels permutation56 hz
    mixedMoment B raw6445step1 raw6445step1Labels = mixedMoment B raw6445step2 raw6445step2Labels := by
      have ha : raw6445step2 = (fun i j => raw6445step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6445step2 raw6445step1; decide +kernel
      have hl : raw6445step2Labels = raw6445step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6445step1 raw6445step1Labels permutation12 permutation4
    mixedMoment B raw6445step2 raw6445step2Labels = mixedMoment B raw6445step3 raw6445step3Labels := by
      have ha : raw6445step3 = -raw6445step2 := by apply Matrix.ext; change ∀ i j, raw6445step3 i j = -(raw6445step2 i j); unfold raw6445step3 raw6445step2; decide +kernel
      have hl : raw6445step3Labels = raw6445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

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

theorem sound3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3633 node3633Labels = Sparse.eval nodeValue3633 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3633) = mixedMoment B node3633 node3633Labels := rfl
  simpa [nodeValue3633, Sparse.eval] using hc.symm

theorem sound3814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3814 node3814Labels = Sparse.eval nodeValue3814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3814) = mixedMoment B node3814 node3814Labels := rfl
  simpa [nodeValue3814, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1218 node1218Labels = Sparse.eval nodeValue1218 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1218) = mixedMoment B node1218 node1218Labels := rfl
  simpa [nodeValue1218, Sparse.eval] using hc.symm

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

theorem sound1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1392 node1392Labels = Sparse.eval nodeValue1392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1392) = mixedMoment B node1392 node1392Labels := rfl
  simpa [nodeValue1392, Sparse.eval] using hc.symm

theorem sound1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1394 node1394Labels = Sparse.eval nodeValue1394 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1394) = mixedMoment B node1394 node1394Labels := rfl
  simpa [nodeValue1394, Sparse.eval] using hc.symm

theorem sound1400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1400 node1400Labels = Sparse.eval nodeValue1400 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1400) = mixedMoment B node1400 node1400Labels := rfl
  simpa [nodeValue1400, Sparse.eval] using hc.symm

theorem sound1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1406 node1406Labels = Sparse.eval nodeValue1406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1406) = mixedMoment B node1406 node1406Labels := rfl
  simpa [nodeValue1406, Sparse.eval] using hc.symm

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

theorem sound1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1425 node1425Labels = Sparse.eval nodeValue1425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1425) = mixedMoment B node1425 node1425Labels := rfl
  simpa [nodeValue1425, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2033 node2033Labels = Sparse.eval nodeValue2033 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2033) = mixedMoment B node2033 node2033Labels := rfl
  simpa [nodeValue2033, Sparse.eval] using hc.symm

theorem sound2035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2035 node2035Labels = Sparse.eval nodeValue2035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2035) = mixedMoment B node2035 node2035Labels := rfl
  simpa [nodeValue2035, Sparse.eval] using hc.symm

theorem sound2039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2039 node2039Labels = Sparse.eval nodeValue2039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2039) = mixedMoment B node2039 node2039Labels := rfl
  simpa [nodeValue2039, Sparse.eval] using hc.symm

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

theorem sound2054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2054 node2054Labels = Sparse.eval nodeValue2054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2054) = mixedMoment B node2054 node2054Labels := rfl
  simpa [nodeValue2054, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2486 node2486Labels = Sparse.eval nodeValue2486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2486) = mixedMoment B node2486 node2486Labels := rfl
  simpa [nodeValue2486, Sparse.eval] using hc.symm

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

theorem sound2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2544 node2544Labels = Sparse.eval nodeValue2544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2544) = mixedMoment B node2544 node2544Labels := rfl
  simpa [nodeValue2544, Sparse.eval] using hc.symm

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

theorem sound2610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2610 node2610Labels = Sparse.eval nodeValue2610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2610) = mixedMoment B node2610 node2610Labels := rfl
  simpa [nodeValue2610, Sparse.eval] using hc.symm

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

theorem sound2619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2619 node2619Labels = Sparse.eval nodeValue2619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2619) = mixedMoment B node2619 node2619Labels := rfl
  simpa [nodeValue2619, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2624 node2624Labels = Sparse.eval nodeValue2624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2624) = mixedMoment B node2624 node2624Labels := rfl
  simpa [nodeValue2624, Sparse.eval] using hc.symm

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

theorem sound2714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2714 node2714Labels = Sparse.eval nodeValue2714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2714) = mixedMoment B node2714 node2714Labels := rfl
  simpa [nodeValue2714, Sparse.eval] using hc.symm

theorem sound2716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2716 node2716Labels = Sparse.eval nodeValue2716 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2716) = mixedMoment B node2716 node2716Labels := rfl
  simpa [nodeValue2716, Sparse.eval] using hc.symm

theorem sound2724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2724 node2724Labels = Sparse.eval nodeValue2724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2724) = mixedMoment B node2724 node2724Labels := rfl
  simpa [nodeValue2724, Sparse.eval] using hc.symm

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

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

theorem sound2758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2758 node2758Labels = Sparse.eval nodeValue2758 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2758) = mixedMoment B node2758 node2758Labels := rfl
  simpa [nodeValue2758, Sparse.eval] using hc.symm

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

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

theorem sound2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2933 node2933Labels = Sparse.eval nodeValue2933 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2933) = mixedMoment B node2933 node2933Labels := rfl
  simpa [nodeValue2933, Sparse.eval] using hc.symm

theorem sound2942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2942 node2942Labels = Sparse.eval nodeValue2942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2942) = mixedMoment B node2942 node2942Labels := rfl
  simpa [nodeValue2942, Sparse.eval] using hc.symm

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

theorem sound2947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2947 node2947Labels = Sparse.eval nodeValue2947 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2947) = mixedMoment B node2947 node2947Labels := rfl
  simpa [nodeValue2947, Sparse.eval] using hc.symm

theorem sound2949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2949 node2949Labels = Sparse.eval nodeValue2949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2949) = mixedMoment B node2949 node2949Labels := rfl
  simpa [nodeValue2949, Sparse.eval] using hc.symm

theorem sound2954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2954 node2954Labels = Sparse.eval nodeValue2954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2954) = mixedMoment B node2954 node2954Labels := rfl
  simpa [nodeValue2954, Sparse.eval] using hc.symm

theorem sound2964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2964 node2964Labels = Sparse.eval nodeValue2964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2964) = mixedMoment B node2964 node2964Labels := rfl
  simpa [nodeValue2964, Sparse.eval] using hc.symm

theorem sound2984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2984 node2984Labels = Sparse.eval nodeValue2984 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2984) = mixedMoment B node2984 node2984Labels := rfl
  simpa [nodeValue2984, Sparse.eval] using hc.symm

theorem sound2992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2992 node2992Labels = Sparse.eval nodeValue2992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2992) = mixedMoment B node2992 node2992Labels := rfl
  simpa [nodeValue2992, Sparse.eval] using hc.symm

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

theorem sound3013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3013 node3013Labels = Sparse.eval nodeValue3013 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3013) = mixedMoment B node3013 node3013Labels := rfl
  simpa [nodeValue3013, Sparse.eval] using hc.symm

theorem sound3014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3014 node3014Labels = Sparse.eval nodeValue3014 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3014) = mixedMoment B node3014 node3014Labels := rfl
  simpa [nodeValue3014, Sparse.eval] using hc.symm

theorem sound3064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3064 node3064Labels = Sparse.eval nodeValue3064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3064) = mixedMoment B node3064 node3064Labels := rfl
  simpa [nodeValue3064, Sparse.eval] using hc.symm

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

theorem sound3077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3077 node3077Labels = Sparse.eval nodeValue3077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3077) = mixedMoment B node3077 node3077Labels := rfl
  simpa [nodeValue3077, Sparse.eval] using hc.symm

theorem sound3084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3084 node3084Labels = Sparse.eval nodeValue3084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3084) = mixedMoment B node3084 node3084Labels := rfl
  simpa [nodeValue3084, Sparse.eval] using hc.symm

theorem sound3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3086 node3086Labels = Sparse.eval nodeValue3086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3086) = mixedMoment B node3086 node3086Labels := rfl
  simpa [nodeValue3086, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

theorem sound3108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3108 node3108Labels = Sparse.eval nodeValue3108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3108) = mixedMoment B node3108 node3108Labels := rfl
  simpa [nodeValue3108, Sparse.eval] using hc.symm

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

theorem sound3502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3502 node3502Labels = Sparse.eval nodeValue3502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3502) = mixedMoment B node3502 node3502Labels := rfl
  simpa [nodeValue3502, Sparse.eval] using hc.symm

theorem sound3506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3506 node3506Labels = Sparse.eval nodeValue3506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3506) = mixedMoment B node3506 node3506Labels := rfl
  simpa [nodeValue3506, Sparse.eval] using hc.symm

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

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3632 node3632Labels = Sparse.eval nodeValue3632 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3632) = mixedMoment B node3632 node3632Labels := rfl
  simpa [nodeValue3632, Sparse.eval] using hc.symm

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

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3876 node3876Labels = Sparse.eval nodeValue3876 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3876) = mixedMoment B node3876 node3876Labels := rfl
  simpa [nodeValue3876, Sparse.eval] using hc.symm

theorem sound3881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3881 node3881Labels = Sparse.eval nodeValue3881 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3881) = mixedMoment B node3881 node3881Labels := rfl
  simpa [nodeValue3881, Sparse.eval] using hc.symm

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3983 node3983Labels = Sparse.eval nodeValue3983 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3983) = mixedMoment B node3983 node3983Labels := rfl
  simpa [nodeValue3983, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources8
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm264 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA264 + difference 0 4) (sourceB264 + difference 4 0) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA264 + difference 0 4) (sourceB264 + difference 4 0) sourceC264) = raw6220 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6220; decide +kernel
    rw [ha]
    exact (canonical6220 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA264 + difference 1 4) (sourceB264 + difference 4 1) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA264 + difference 1 4) (sourceB264 + difference 4 1) sourceC264) = raw6230 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6230; decide +kernel
    rw [ha]
    exact (canonical6230 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA264 + difference 2 4) (sourceB264 + difference 4 2) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA264 + difference 2 4) (sourceB264 + difference 4 2) sourceC264) = raw6237 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6237; decide +kernel
    rw [ha]
    exact (canonical6237 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA264 + difference 3 4) (sourceB264 + difference 4 3) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA264 + difference 3 4) (sourceB264 + difference 4 3) sourceC264) = raw6242 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6242; decide +kernel
    rw [ha]
    exact (canonical6242 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA264 + difference 4 4) (sourceB264 + difference 4 4) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA264 + difference 4 4) (sourceB264 + difference 4 4) sourceC264) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA264 + difference 5 4) (sourceB264 + difference 4 5) sourceC264) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA264 + difference 5 4) (sourceB264 + difference 4 5) sourceC264) = raw6247 := by
      apply Matrix.ext; unfold tripleCharges sourceA264 sourceB264 sourceC264 difference raw6247; decide +kernel
    rw [ha]
    exact (canonical6247 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA264 + sourceB264) sourceC264) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA264 + sourceB264) sourceC264) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA264 sourceB264 sourceC264 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA264 sourceB264 sourceC264
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm264, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm265 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA265 + difference 5 0) (sourceB265 + difference 0 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA265 + difference 5 0) (sourceB265 + difference 0 5) sourceC265) = raw6227 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6227; decide +kernel
    rw [ha]
    exact (canonical6227 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA265 + difference 5 1) (sourceB265 + difference 1 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA265 + difference 5 1) (sourceB265 + difference 1 5) sourceC265) = raw6235 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6235; decide +kernel
    rw [ha]
    exact (canonical6235 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA265 + difference 5 2) (sourceB265 + difference 2 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA265 + difference 5 2) (sourceB265 + difference 2 5) sourceC265) = raw6241 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6241; decide +kernel
    rw [ha]
    exact (canonical6241 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA265 + difference 5 3) (sourceB265 + difference 3 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2619) := by
    have ha : (tripleCharges (sourceA265 + difference 5 3) (sourceB265 + difference 3 5) sourceC265) = raw6245 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6245; decide +kernel
    rw [ha]
    exact (canonical6245 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA265 + difference 5 4) (sourceB265 + difference 4 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2716) := by
    have ha : (tripleCharges (sourceA265 + difference 5 4) (sourceB265 + difference 4 5) sourceC265) = raw6247 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6247; decide +kernel
    rw [ha]
    exact (canonical6247 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA265 + difference 5 5) (sourceB265 + difference 5 5) sourceC265) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA265 + difference 5 5) (sourceB265 + difference 5 5) sourceC265) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA265 sourceB265 sourceC265 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA265 + sourceB265) sourceC265) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA265 + sourceB265) sourceC265) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA265 sourceB265 sourceC265 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA265 sourceB265 sourceC265
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm265, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm269 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA269 + difference 0 0) (sourceB269 + difference 0 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA269 + difference 0 0) (sourceB269 + difference 0 0) sourceC269) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA269 + difference 0 1) (sourceB269 + difference 1 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA269 + difference 0 1) (sourceB269 + difference 1 0) sourceC269) = raw6339 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6339; decide +kernel
    rw [ha]
    exact (canonical6339 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA269 + difference 0 2) (sourceB269 + difference 2 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA269 + difference 0 2) (sourceB269 + difference 2 0) sourceC269) = raw6340 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6340; decide +kernel
    rw [ha]
    exact (canonical6340 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA269 + difference 0 3) (sourceB269 + difference 3 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA269 + difference 0 3) (sourceB269 + difference 3 0) sourceC269) = raw6341 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6341; decide +kernel
    rw [ha]
    exact (canonical6341 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA269 + difference 0 4) (sourceB269 + difference 4 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA269 + difference 0 4) (sourceB269 + difference 4 0) sourceC269) = raw6342 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6342; decide +kernel
    rw [ha]
    exact (canonical6342 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA269 + difference 0 5) (sourceB269 + difference 5 0) sourceC269) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3983) := by
    have ha : (tripleCharges (sourceA269 + difference 0 5) (sourceB269 + difference 5 0) sourceC269) = raw6343 := by
      apply Matrix.ext; unfold tripleCharges sourceA269 sourceB269 sourceC269 difference raw6343; decide +kernel
    rw [ha]
    exact (canonical6343 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA269 + sourceB269) sourceC269) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA269 + sourceB269) sourceC269) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA269 sourceB269 sourceC269 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA269 sourceB269 sourceC269
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm269, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm270 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA270 + difference 0 0) (sourceB270 + difference 0 0) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA270 + difference 0 0) (sourceB270 + difference 0 0) sourceC270) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA270 + difference 1 0) (sourceB270 + difference 0 1) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA270 + difference 1 0) (sourceB270 + difference 0 1) sourceC270) = raw6345 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6345; decide +kernel
    rw [ha]
    exact (canonical6345 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA270 + difference 2 0) (sourceB270 + difference 0 2) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA270 + difference 2 0) (sourceB270 + difference 0 2) sourceC270) = raw6346 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6346; decide +kernel
    rw [ha]
    exact (canonical6346 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA270 + difference 3 0) (sourceB270 + difference 0 3) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1425) := by
    have ha : (tripleCharges (sourceA270 + difference 3 0) (sourceB270 + difference 0 3) sourceC270) = raw6347 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6347; decide +kernel
    rw [ha]
    exact (canonical6347 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA270 + difference 4 0) (sourceB270 + difference 0 4) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA270 + difference 4 0) (sourceB270 + difference 0 4) sourceC270) = raw6348 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6348; decide +kernel
    rw [ha]
    exact (canonical6348 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA270 + difference 5 0) (sourceB270 + difference 0 5) sourceC270) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1394) := by
    have ha : (tripleCharges (sourceA270 + difference 5 0) (sourceB270 + difference 0 5) sourceC270) = raw6349 := by
      apply Matrix.ext; unfold tripleCharges sourceA270 sourceB270 sourceC270 difference raw6349; decide +kernel
    rw [ha]
    exact (canonical6349 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA270 + sourceB270) sourceC270) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA270 + sourceB270) sourceC270) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA270 sourceB270 sourceC270 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA270 sourceB270 sourceC270
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm270, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm271 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA271 + difference 1 0) (sourceB271 + difference 0 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA271 + difference 1 0) (sourceB271 + difference 0 1) sourceC271) = raw6345 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6345; decide +kernel
    rw [ha]
    exact (canonical6345 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA271 + difference 1 1) (sourceB271 + difference 1 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA271 + difference 1 1) (sourceB271 + difference 1 1) sourceC271) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA271 + difference 1 2) (sourceB271 + difference 2 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA271 + difference 1 2) (sourceB271 + difference 2 1) sourceC271) = raw6350 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6350; decide +kernel
    rw [ha]
    exact (canonical6350 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA271 + difference 1 3) (sourceB271 + difference 3 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA271 + difference 1 3) (sourceB271 + difference 3 1) sourceC271) = raw6351 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6351; decide +kernel
    rw [ha]
    exact (canonical6351 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA271 + difference 1 4) (sourceB271 + difference 4 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA271 + difference 1 4) (sourceB271 + difference 4 1) sourceC271) = raw6352 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6352; decide +kernel
    rw [ha]
    exact (canonical6352 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA271 + difference 1 5) (sourceB271 + difference 5 1) sourceC271) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA271 + difference 1 5) (sourceB271 + difference 5 1) sourceC271) = raw6353 := by
      apply Matrix.ext; unfold tripleCharges sourceA271 sourceB271 sourceC271 difference raw6353; decide +kernel
    rw [ha]
    exact (canonical6353 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA271 + sourceB271) sourceC271) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA271 + sourceB271) sourceC271) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA271 sourceB271 sourceC271 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA271 sourceB271 sourceC271
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm271, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq272 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm272 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA272 + difference 0 1) (sourceB272 + difference 1 0) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3881) := by
    have ha : (tripleCharges (sourceA272 + difference 0 1) (sourceB272 + difference 1 0) sourceC272) = raw6339 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6339; decide +kernel
    rw [ha]
    exact (canonical6339 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA272 + difference 1 1) (sourceB272 + difference 1 1) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA272 + difference 1 1) (sourceB272 + difference 1 1) sourceC272) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA272 + difference 2 1) (sourceB272 + difference 1 2) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA272 + difference 2 1) (sourceB272 + difference 1 2) sourceC272) = raw6354 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6354; decide +kernel
    rw [ha]
    exact (canonical6354 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA272 + difference 3 1) (sourceB272 + difference 1 3) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3014) := by
    have ha : (tripleCharges (sourceA272 + difference 3 1) (sourceB272 + difference 1 3) sourceC272) = raw6355 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6355; decide +kernel
    rw [ha]
    exact (canonical6355 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA272 + difference 4 1) (sourceB272 + difference 1 4) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2949) := by
    have ha : (tripleCharges (sourceA272 + difference 4 1) (sourceB272 + difference 1 4) sourceC272) = raw6356 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6356; decide +kernel
    rw [ha]
    exact (canonical6356 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA272 + difference 5 1) (sourceB272 + difference 1 5) sourceC272) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA272 + difference 5 1) (sourceB272 + difference 1 5) sourceC272) = raw6357 := by
      apply Matrix.ext; unfold tripleCharges sourceA272 sourceB272 sourceC272 difference raw6357; decide +kernel
    rw [ha]
    exact (canonical6357 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA272 + sourceB272) sourceC272) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA272 + sourceB272) sourceC272) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA272 sourceB272 sourceC272 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA272 sourceB272 sourceC272
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm272, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq273 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm273 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA273 + difference 2 0) (sourceB273 + difference 0 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1392) := by
    have ha : (tripleCharges (sourceA273 + difference 2 0) (sourceB273 + difference 0 2) sourceC273) = raw6346 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6346; decide +kernel
    rw [ha]
    exact (canonical6346 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA273 + difference 2 1) (sourceB273 + difference 1 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3013) := by
    have ha : (tripleCharges (sourceA273 + difference 2 1) (sourceB273 + difference 1 2) sourceC273) = raw6354 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6354; decide +kernel
    rw [ha]
    exact (canonical6354 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA273 + difference 2 2) (sourceB273 + difference 2 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA273 + difference 2 2) (sourceB273 + difference 2 2) sourceC273) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA273 + difference 2 3) (sourceB273 + difference 3 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA273 + difference 2 3) (sourceB273 + difference 3 2) sourceC273) = raw6358 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6358; decide +kernel
    rw [ha]
    exact (canonical6358 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA273 + difference 2 4) (sourceB273 + difference 4 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA273 + difference 2 4) (sourceB273 + difference 4 2) sourceC273) = raw6359 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6359; decide +kernel
    rw [ha]
    exact (canonical6359 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA273 + difference 2 5) (sourceB273 + difference 5 2) sourceC273) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3084) := by
    have ha : (tripleCharges (sourceA273 + difference 2 5) (sourceB273 + difference 5 2) sourceC273) = raw6360 := by
      apply Matrix.ext; unfold tripleCharges sourceA273 sourceB273 sourceC273 difference raw6360; decide +kernel
    rw [ha]
    exact (canonical6360 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA273 + sourceB273) sourceC273) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA273 + sourceB273) sourceC273) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA273 sourceB273 sourceC273 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA273 sourceB273 sourceC273
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm273, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq274 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm274 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA274 + difference 0 2) (sourceB274 + difference 2 0) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA274 + difference 0 2) (sourceB274 + difference 2 0) sourceC274) = raw6340 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6340; decide +kernel
    rw [ha]
    exact (canonical6340 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA274 + difference 1 2) (sourceB274 + difference 2 1) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2984) := by
    have ha : (tripleCharges (sourceA274 + difference 1 2) (sourceB274 + difference 2 1) sourceC274) = raw6350 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6350; decide +kernel
    rw [ha]
    exact (canonical6350 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA274 + difference 2 2) (sourceB274 + difference 2 2) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA274 + difference 2 2) (sourceB274 + difference 2 2) sourceC274) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA274 + difference 3 2) (sourceB274 + difference 2 3) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2992) := by
    have ha : (tripleCharges (sourceA274 + difference 3 2) (sourceB274 + difference 2 3) sourceC274) = raw6361 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6361; decide +kernel
    rw [ha]
    exact (canonical6361 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA274 + difference 4 2) (sourceB274 + difference 2 4) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2947) := by
    have ha : (tripleCharges (sourceA274 + difference 4 2) (sourceB274 + difference 2 4) sourceC274) = raw6362 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6362; decide +kernel
    rw [ha]
    exact (canonical6362 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA274 + difference 5 2) (sourceB274 + difference 2 5) sourceC274) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2610) := by
    have ha : (tripleCharges (sourceA274 + difference 5 2) (sourceB274 + difference 2 5) sourceC274) = raw6363 := by
      apply Matrix.ext; unfold tripleCharges sourceA274 sourceB274 sourceC274 difference raw6363; decide +kernel
    rw [ha]
    exact (canonical6363 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA274 + sourceB274) sourceC274) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA274 + sourceB274) sourceC274) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA274 sourceB274 sourceC274 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA274 sourceB274 sourceC274
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm274, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq275 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm275 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA275 + difference 3 0) (sourceB275 + difference 0 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1425) := by
    have ha : (tripleCharges (sourceA275 + difference 3 0) (sourceB275 + difference 0 3) sourceC275) = raw6347 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6347; decide +kernel
    rw [ha]
    exact (canonical6347 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA275 + difference 3 1) (sourceB275 + difference 1 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3014) := by
    have ha : (tripleCharges (sourceA275 + difference 3 1) (sourceB275 + difference 1 3) sourceC275) = raw6355 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6355; decide +kernel
    rw [ha]
    exact (canonical6355 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA275 + difference 3 2) (sourceB275 + difference 2 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2992) := by
    have ha : (tripleCharges (sourceA275 + difference 3 2) (sourceB275 + difference 2 3) sourceC275) = raw6361 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6361; decide +kernel
    rw [ha]
    exact (canonical6361 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA275 + difference 3 3) (sourceB275 + difference 3 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA275 + difference 3 3) (sourceB275 + difference 3 3) sourceC275) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA275 + difference 3 4) (sourceB275 + difference 4 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA275 + difference 3 4) (sourceB275 + difference 4 3) sourceC275) = raw6364 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6364; decide +kernel
    rw [ha]
    exact (canonical6364 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA275 + difference 3 5) (sourceB275 + difference 5 3) sourceC275) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3108) := by
    have ha : (tripleCharges (sourceA275 + difference 3 5) (sourceB275 + difference 5 3) sourceC275) = raw6365 := by
      apply Matrix.ext; unfold tripleCharges sourceA275 sourceB275 sourceC275 difference raw6365; decide +kernel
    rw [ha]
    exact (canonical6365 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA275 + sourceB275) sourceC275) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA275 + sourceB275) sourceC275) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA275 sourceB275 sourceC275 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA275 sourceB275 sourceC275
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm275, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq276 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm276 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA276 + difference 0 3) (sourceB276 + difference 3 0) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3876) := by
    have ha : (tripleCharges (sourceA276 + difference 0 3) (sourceB276 + difference 3 0) sourceC276) = raw6341 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6341; decide +kernel
    rw [ha]
    exact (canonical6341 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA276 + difference 1 3) (sourceB276 + difference 3 1) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA276 + difference 1 3) (sourceB276 + difference 3 1) sourceC276) = raw6351 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6351; decide +kernel
    rw [ha]
    exact (canonical6351 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA276 + difference 2 3) (sourceB276 + difference 3 2) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2933) := by
    have ha : (tripleCharges (sourceA276 + difference 2 3) (sourceB276 + difference 3 2) sourceC276) = raw6358 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6358; decide +kernel
    rw [ha]
    exact (canonical6358 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA276 + difference 3 3) (sourceB276 + difference 3 3) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA276 + difference 3 3) (sourceB276 + difference 3 3) sourceC276) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA276 + difference 4 3) (sourceB276 + difference 3 4) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA276 + difference 4 3) (sourceB276 + difference 3 4) sourceC276) = raw6366 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6366; decide +kernel
    rw [ha]
    exact (canonical6366 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA276 + difference 5 3) (sourceB276 + difference 3 5) sourceC276) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA276 + difference 5 3) (sourceB276 + difference 3 5) sourceC276) = raw6367 := by
      apply Matrix.ext; unfold tripleCharges sourceA276 sourceB276 sourceC276 difference raw6367; decide +kernel
    rw [ha]
    exact (canonical6367 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA276 + sourceB276) sourceC276) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA276 + sourceB276) sourceC276) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA276 sourceB276 sourceC276 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA276 sourceB276 sourceC276
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm276, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq277 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm277 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA277 + difference 4 0) (sourceB277 + difference 0 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1400) := by
    have ha : (tripleCharges (sourceA277 + difference 4 0) (sourceB277 + difference 0 4) sourceC277) = raw6348 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6348; decide +kernel
    rw [ha]
    exact (canonical6348 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA277 + difference 4 1) (sourceB277 + difference 1 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2949) := by
    have ha : (tripleCharges (sourceA277 + difference 4 1) (sourceB277 + difference 1 4) sourceC277) = raw6356 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6356; decide +kernel
    rw [ha]
    exact (canonical6356 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA277 + difference 4 2) (sourceB277 + difference 2 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2947) := by
    have ha : (tripleCharges (sourceA277 + difference 4 2) (sourceB277 + difference 2 4) sourceC277) = raw6362 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6362; decide +kernel
    rw [ha]
    exact (canonical6362 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA277 + difference 4 3) (sourceB277 + difference 3 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA277 + difference 4 3) (sourceB277 + difference 3 4) sourceC277) = raw6366 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6366; decide +kernel
    rw [ha]
    exact (canonical6366 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA277 + difference 4 4) (sourceB277 + difference 4 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA277 + difference 4 4) (sourceB277 + difference 4 4) sourceC277) = raw6338 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6338; decide +kernel
    rw [ha]
    exact (canonical6338 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA277 + difference 4 5) (sourceB277 + difference 5 4) sourceC277) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA277 + difference 4 5) (sourceB277 + difference 5 4) sourceC277) = raw6368 := by
      apply Matrix.ext; unfold tripleCharges sourceA277 sourceB277 sourceC277 difference raw6368; decide +kernel
    rw [ha]
    exact (canonical6368 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA277 + sourceB277) sourceC277) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA277 + sourceB277) sourceC277) = raw6344 := by
      apply Matrix.ext; unfold doubleCharges sourceA277 sourceB277 sourceC277 raw6344; decide +kernel
    rw [ha]
    exact (canonical6344 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA277 sourceB277 sourceC277
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm277, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm281 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA281 + difference 0 0) (sourceB281 + difference 0 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA281 + difference 0 0) (sourceB281 + difference 0 0) sourceC281) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA281 + difference 0 1) (sourceB281 + difference 1 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA281 + difference 0 1) (sourceB281 + difference 1 0) sourceC281) = raw6435 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6435; decide +kernel
    rw [ha]
    exact (canonical6435 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA281 + difference 0 2) (sourceB281 + difference 2 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA281 + difference 0 2) (sourceB281 + difference 2 0) sourceC281) = raw6436 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6436; decide +kernel
    rw [ha]
    exact (canonical6436 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA281 + difference 0 3) (sourceB281 + difference 3 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA281 + difference 0 3) (sourceB281 + difference 3 0) sourceC281) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA281 + difference 0 4) (sourceB281 + difference 4 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA281 + difference 0 4) (sourceB281 + difference 4 0) sourceC281) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA281 + difference 0 5) (sourceB281 + difference 5 0) sourceC281) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2588) := by
    have ha : (tripleCharges (sourceA281 + difference 0 5) (sourceB281 + difference 5 0) sourceC281) = raw6438 := by
      apply Matrix.ext; unfold tripleCharges sourceA281 sourceB281 sourceC281 difference raw6438; decide +kernel
    rw [ha]
    exact (canonical6438 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA281 + sourceB281) sourceC281) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA281 + sourceB281) sourceC281) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA281 sourceB281 sourceC281 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA281 sourceB281 sourceC281
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm281, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm282 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA282 + difference 0 0) (sourceB282 + difference 0 0) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA282 + difference 0 0) (sourceB282 + difference 0 0) sourceC282) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA282 + difference 1 0) (sourceB282 + difference 0 1) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA282 + difference 1 0) (sourceB282 + difference 0 1) sourceC282) = raw6439 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6439; decide +kernel
    rw [ha]
    exact (canonical6439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA282 + difference 2 0) (sourceB282 + difference 0 2) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2033) := by
    have ha : (tripleCharges (sourceA282 + difference 2 0) (sourceB282 + difference 0 2) sourceC282) = raw6440 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6440; decide +kernel
    rw [ha]
    exact (canonical6440 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA282 + difference 3 0) (sourceB282 + difference 0 3) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA282 + difference 3 0) (sourceB282 + difference 0 3) sourceC282) = raw6441 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6441; decide +kernel
    rw [ha]
    exact (canonical6441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA282 + difference 4 0) (sourceB282 + difference 0 4) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA282 + difference 4 0) (sourceB282 + difference 0 4) sourceC282) = raw6442 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6442; decide +kernel
    rw [ha]
    exact (canonical6442 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA282 + difference 5 0) (sourceB282 + difference 0 5) sourceC282) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA282 + difference 5 0) (sourceB282 + difference 0 5) sourceC282) = raw6443 := by
      apply Matrix.ext; unfold tripleCharges sourceA282 sourceB282 sourceC282 difference raw6443; decide +kernel
    rw [ha]
    exact (canonical6443 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA282 + sourceB282) sourceC282) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA282 + sourceB282) sourceC282) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA282 sourceB282 sourceC282 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA282 sourceB282 sourceC282
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm282, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm283 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA283 + difference 1 0) (sourceB283 + difference 0 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2278) := by
    have ha : (tripleCharges (sourceA283 + difference 1 0) (sourceB283 + difference 0 1) sourceC283) = raw6439 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6439; decide +kernel
    rw [ha]
    exact (canonical6439 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA283 + difference 1 1) (sourceB283 + difference 1 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA283 + difference 1 1) (sourceB283 + difference 1 1) sourceC283) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA283 + difference 1 2) (sourceB283 + difference 2 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA283 + difference 1 2) (sourceB283 + difference 2 1) sourceC283) = raw6444 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6444; decide +kernel
    rw [ha]
    exact (canonical6444 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA283 + difference 1 3) (sourceB283 + difference 3 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA283 + difference 1 3) (sourceB283 + difference 3 1) sourceC283) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA283 + difference 1 4) (sourceB283 + difference 4 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA283 + difference 1 4) (sourceB283 + difference 4 1) sourceC283) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA283 + difference 1 5) (sourceB283 + difference 5 1) sourceC283) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA283 + difference 1 5) (sourceB283 + difference 5 1) sourceC283) = raw6446 := by
      apply Matrix.ext; unfold tripleCharges sourceA283 sourceB283 sourceC283 difference raw6446; decide +kernel
    rw [ha]
    exact (canonical6446 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA283 + sourceB283) sourceC283) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA283 + sourceB283) sourceC283) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA283 sourceB283 sourceC283 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA283 sourceB283 sourceC283
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm283, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck224 : Integer.Sparse.reindex keyMap MixedData.row224 = numericRow224 := by decide +kernel

theorem numericCheck224 (x : Master → ℝ) : Integer.Sparse.eval numericRow224 x =
    (1 : ℝ) * reducedSource224 x := by
  norm_num [numericRow224, reducedSource224, Integer.Sparse.eval, Sparse.eval, nodeValue2714, nodeValue2716, nodeValue2724, nodeValue2732, nodeValue2758, nodeValue3814, nodeValue4092]

theorem reindexCheck225 : Integer.Sparse.reindex keyMap MixedData.row225 = numericRow225 := by decide +kernel

theorem numericCheck225 (x : Master → ℝ) : Integer.Sparse.eval numericRow225 x =
    (1 : ℝ) * reducedSource225 x := by
  norm_num [numericRow225, reducedSource225, Integer.Sparse.eval, Sparse.eval, nodeValue1218, nodeValue2486, nodeValue2544, nodeValue2619, nodeValue2716, nodeValue2724, nodeValue4092]

theorem reindexCheck227 : Integer.Sparse.reindex keyMap MixedData.row227 = numericRow227 := by decide +kernel

theorem numericCheck227 (x : Master → ℝ) : Integer.Sparse.eval numericRow227 x =
    (1 : ℝ) * reducedSource227 x := by
  norm_num [numericRow227, reducedSource227, Integer.Sparse.eval, Sparse.eval, nodeValue3086, nodeValue3871, nodeValue3876, nodeValue3881, nodeValue3902, nodeValue3983, nodeValue4091]

theorem reindexCheck228 : Integer.Sparse.reindex keyMap MixedData.row228 = numericRow228 := by decide +kernel

theorem numericCheck228 (x : Master → ℝ) : Integer.Sparse.eval numericRow228 x =
    (1 : ℝ) * reducedSource228 x := by
  norm_num [numericRow228, reducedSource228, Integer.Sparse.eval, Sparse.eval, nodeValue1392, nodeValue1394, nodeValue1400, nodeValue1406, nodeValue1425, nodeValue3086, nodeValue4091]

theorem reindexCheck229 : Integer.Sparse.reindex keyMap MixedData.row229 = numericRow229 := by decide +kernel

theorem numericCheck229 (x : Master → ℝ) : Integer.Sparse.eval numericRow229 x =
    (1 : ℝ) * reducedSource229 x := by
  norm_num [numericRow229, reducedSource229, Integer.Sparse.eval, Sparse.eval, nodeValue1406, nodeValue2954, nodeValue2984, nodeValue3077, nodeValue3086, nodeValue3097, nodeValue4091]

theorem reindexCheck230 : Integer.Sparse.reindex keyMap MixedData.row230 = numericRow230 := by decide +kernel

theorem numericCheck230 (x : Master → ℝ) : Integer.Sparse.eval numericRow230 x =
    (1 : ℝ) * reducedSource230 x := by
  norm_num [numericRow230, reducedSource230, Integer.Sparse.eval, Sparse.eval, nodeValue2624, nodeValue2949, nodeValue3013, nodeValue3014, nodeValue3086, nodeValue3881, nodeValue4091]

theorem reindexCheck231 : Integer.Sparse.reindex keyMap MixedData.row231 = numericRow231 := by decide +kernel

theorem numericCheck231 (x : Master → ℝ) : Integer.Sparse.eval numericRow231 x =
    (1 : ℝ) * reducedSource231 x := by
  norm_num [numericRow231, reducedSource231, Integer.Sparse.eval, Sparse.eval, nodeValue1392, nodeValue2933, nodeValue3013, nodeValue3064, nodeValue3084, nodeValue3086, nodeValue4091]

theorem reindexCheck232 : Integer.Sparse.reindex keyMap MixedData.row232 = numericRow232 := by decide +kernel

theorem numericCheck232 (x : Master → ℝ) : Integer.Sparse.eval numericRow232 x =
    (1 : ℝ) * reducedSource232 x := by
  norm_num [numericRow232, reducedSource232, Integer.Sparse.eval, Sparse.eval, nodeValue2610, nodeValue2947, nodeValue2984, nodeValue2992, nodeValue3086, nodeValue3871, nodeValue4091]

theorem reindexCheck233 : Integer.Sparse.reindex keyMap MixedData.row233 = numericRow233 := by decide +kernel

theorem numericCheck233 (x : Master → ℝ) : Integer.Sparse.eval numericRow233 x =
    (1 : ℝ) * reducedSource233 x := by
  norm_num [numericRow233, reducedSource233, Integer.Sparse.eval, Sparse.eval, nodeValue1425, nodeValue2992, nodeValue3014, nodeValue3086, nodeValue3108, nodeValue4091]

theorem reindexCheck234 : Integer.Sparse.reindex keyMap MixedData.row234 = numericRow234 := by decide +kernel

theorem numericCheck234 (x : Master → ℝ) : Integer.Sparse.eval numericRow234 x =
    (1 : ℝ) * reducedSource234 x := by
  norm_num [numericRow234, reducedSource234, Integer.Sparse.eval, Sparse.eval, nodeValue2618, nodeValue2933, nodeValue2942, nodeValue2954, nodeValue3086, nodeValue3876, nodeValue4091]

theorem reindexCheck235 : Integer.Sparse.reindex keyMap MixedData.row235 = numericRow235 := by decide +kernel

theorem numericCheck235 (x : Master → ℝ) : Integer.Sparse.eval numericRow235 x =
    (1 : ℝ) * reducedSource235 x := by
  norm_num [numericRow235, reducedSource235, Integer.Sparse.eval, Sparse.eval, nodeValue1400, nodeValue2942, nodeValue2947, nodeValue2949, nodeValue2964, nodeValue3086, nodeValue4091]

theorem reindexCheck237 : Integer.Sparse.reindex keyMap MixedData.row237 = numericRow237 := by decide +kernel

theorem numericCheck237 (x : Master → ℝ) : Integer.Sparse.eval numericRow237 x =
    (1 : ℝ) * reducedSource237 x := by
  norm_num [numericRow237, reducedSource237, Integer.Sparse.eval, Sparse.eval, nodeValue2588, nodeValue3502, nodeValue3506, nodeValue3533, nodeValue3540, nodeValue3582, nodeValue4084]

theorem reindexCheck238 : Integer.Sparse.reindex keyMap MixedData.row238 = numericRow238 := by decide +kernel

theorem numericCheck238 (x : Master → ℝ) : Integer.Sparse.eval numericRow238 x =
    (1 : ℝ) * reducedSource238 x := by
  norm_num [numericRow238, reducedSource238, Integer.Sparse.eval, Sparse.eval, nodeValue2033, nodeValue2035, nodeValue2039, nodeValue2054, nodeValue2278, nodeValue3540, nodeValue4084]

theorem reindexCheck239 : Integer.Sparse.reindex keyMap MixedData.row239 = numericRow239 := by decide +kernel

theorem numericCheck239 (x : Master → ℝ) : Integer.Sparse.eval numericRow239 x =
    (1 : ℝ) * reducedSource239 x := by
  norm_num [numericRow239, reducedSource239, Integer.Sparse.eval, Sparse.eval, nodeValue2278, nodeValue2781, nodeValue3540, nodeValue3632, nodeValue3633, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource224 (mixedVector B) = 0 := by
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm264, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2714, h2716, h2724, h2732, h2758, h3814, h4092, reducedSource224] using sourceEq264 B hB

theorem rowSound224 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row224 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck224, numericCheck224, reducedZero224 B hB hF, mul_zero]

theorem reducedZero225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource225 (mixedVector B) = 0 := by
  have h1218 : mixedVector B (Sum.inr 1218) = Sparse.eval nodeValue1218 (mixedVector B) := by
    change mixedMoment B node1218 node1218Labels = _
    exact sound1218 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2544 : mixedVector B (Sum.inr 2544) = Sparse.eval nodeValue2544 (mixedVector B) := by
    change mixedMoment B node2544 node2544Labels = _
    exact sound2544 B hB hF
  have h2619 : mixedVector B (Sum.inr 2619) = Sparse.eval nodeValue2619 (mixedVector B) := by
    change mixedMoment B node2619 node2619Labels = _
    exact sound2619 B hB hF
  have h2716 : mixedVector B (Sum.inr 2716) = Sparse.eval nodeValue2716 (mixedVector B) := by
    change mixedMoment B node2716 node2716Labels = _
    exact sound2716 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm265, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1218, h2486, h2544, h2619, h2716, h2724, h4092, reducedSource225] using sourceEq265 B hB

theorem rowSound225 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row225 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck225, numericCheck225, reducedZero225 B hB hF, mul_zero]

theorem reducedZero227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource227 (mixedVector B) = 0 := by
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h3983 : mixedVector B (Sum.inr 3983) = Sparse.eval nodeValue3983 (mixedVector B) := by
    change mixedMoment B node3983 node3983Labels = _
    exact sound3983 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm269, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3086, h3871, h3876, h3881, h3902, h3983, h4091, reducedSource227] using sourceEq269 B hB

theorem rowSound227 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row227 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck227, numericCheck227, reducedZero227 B hB hF, mul_zero]

theorem reducedZero228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource228 (mixedVector B) = 0 := by
  have h1392 : mixedVector B (Sum.inr 1392) = Sparse.eval nodeValue1392 (mixedVector B) := by
    change mixedMoment B node1392 node1392Labels = _
    exact sound1392 B hB hF
  have h1394 : mixedVector B (Sum.inr 1394) = Sparse.eval nodeValue1394 (mixedVector B) := by
    change mixedMoment B node1394 node1394Labels = _
    exact sound1394 B hB hF
  have h1400 : mixedVector B (Sum.inr 1400) = Sparse.eval nodeValue1400 (mixedVector B) := by
    change mixedMoment B node1400 node1400Labels = _
    exact sound1400 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h1425 : mixedVector B (Sum.inr 1425) = Sparse.eval nodeValue1425 (mixedVector B) := by
    change mixedMoment B node1425 node1425Labels = _
    exact sound1425 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm270, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1392, h1394, h1400, h1406, h1425, h3086, h4091, reducedSource228] using sourceEq270 B hB

theorem rowSound228 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row228 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck228, numericCheck228, reducedZero228 B hB hF, mul_zero]

theorem reducedZero229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource229 (mixedVector B) = 0 := by
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm271, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1406, h2954, h2984, h3077, h3086, h3097, h4091, reducedSource229] using sourceEq271 B hB

theorem rowSound229 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row229 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck229, numericCheck229, reducedZero229 B hB hF, mul_zero]

theorem reducedZero230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource230 (mixedVector B) = 0 := by
  have h2624 : mixedVector B (Sum.inr 2624) = Sparse.eval nodeValue2624 (mixedVector B) := by
    change mixedMoment B node2624 node2624Labels = _
    exact sound2624 B hB hF
  have h2949 : mixedVector B (Sum.inr 2949) = Sparse.eval nodeValue2949 (mixedVector B) := by
    change mixedMoment B node2949 node2949Labels = _
    exact sound2949 B hB hF
  have h3013 : mixedVector B (Sum.inr 3013) = Sparse.eval nodeValue3013 (mixedVector B) := by
    change mixedMoment B node3013 node3013Labels = _
    exact sound3013 B hB hF
  have h3014 : mixedVector B (Sum.inr 3014) = Sparse.eval nodeValue3014 (mixedVector B) := by
    change mixedMoment B node3014 node3014Labels = _
    exact sound3014 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3881 : mixedVector B (Sum.inr 3881) = Sparse.eval nodeValue3881 (mixedVector B) := by
    change mixedMoment B node3881 node3881Labels = _
    exact sound3881 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm272, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2624, h2949, h3013, h3014, h3086, h3881, h4091, reducedSource230] using sourceEq272 B hB

theorem rowSound230 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row230 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck230, numericCheck230, reducedZero230 B hB hF, mul_zero]

theorem reducedZero231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource231 (mixedVector B) = 0 := by
  have h1392 : mixedVector B (Sum.inr 1392) = Sparse.eval nodeValue1392 (mixedVector B) := by
    change mixedMoment B node1392 node1392Labels = _
    exact sound1392 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h3013 : mixedVector B (Sum.inr 3013) = Sparse.eval nodeValue3013 (mixedVector B) := by
    change mixedMoment B node3013 node3013Labels = _
    exact sound3013 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3084 : mixedVector B (Sum.inr 3084) = Sparse.eval nodeValue3084 (mixedVector B) := by
    change mixedMoment B node3084 node3084Labels = _
    exact sound3084 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm273, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1392, h2933, h3013, h3064, h3084, h3086, h4091, reducedSource231] using sourceEq273 B hB

theorem rowSound231 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row231 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck231, numericCheck231, reducedZero231 B hB hF, mul_zero]

theorem reducedZero232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource232 (mixedVector B) = 0 := by
  have h2610 : mixedVector B (Sum.inr 2610) = Sparse.eval nodeValue2610 (mixedVector B) := by
    change mixedMoment B node2610 node2610Labels = _
    exact sound2610 B hB hF
  have h2947 : mixedVector B (Sum.inr 2947) = Sparse.eval nodeValue2947 (mixedVector B) := by
    change mixedMoment B node2947 node2947Labels = _
    exact sound2947 B hB hF
  have h2984 : mixedVector B (Sum.inr 2984) = Sparse.eval nodeValue2984 (mixedVector B) := by
    change mixedMoment B node2984 node2984Labels = _
    exact sound2984 B hB hF
  have h2992 : mixedVector B (Sum.inr 2992) = Sparse.eval nodeValue2992 (mixedVector B) := by
    change mixedMoment B node2992 node2992Labels = _
    exact sound2992 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm274, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2610, h2947, h2984, h2992, h3086, h3871, h4091, reducedSource232] using sourceEq274 B hB

theorem rowSound232 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row232 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck232, numericCheck232, reducedZero232 B hB hF, mul_zero]

theorem reducedZero233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource233 (mixedVector B) = 0 := by
  have h1425 : mixedVector B (Sum.inr 1425) = Sparse.eval nodeValue1425 (mixedVector B) := by
    change mixedMoment B node1425 node1425Labels = _
    exact sound1425 B hB hF
  have h2992 : mixedVector B (Sum.inr 2992) = Sparse.eval nodeValue2992 (mixedVector B) := by
    change mixedMoment B node2992 node2992Labels = _
    exact sound2992 B hB hF
  have h3014 : mixedVector B (Sum.inr 3014) = Sparse.eval nodeValue3014 (mixedVector B) := by
    change mixedMoment B node3014 node3014Labels = _
    exact sound3014 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3108 : mixedVector B (Sum.inr 3108) = Sparse.eval nodeValue3108 (mixedVector B) := by
    change mixedMoment B node3108 node3108Labels = _
    exact sound3108 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm275, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1425, h2992, h3014, h3086, h3108, h4091, reducedSource233] using sourceEq275 B hB

theorem rowSound233 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row233 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck233, numericCheck233, reducedZero233 B hB hF, mul_zero]

theorem reducedZero234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource234 (mixedVector B) = 0 := by
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2933 : mixedVector B (Sum.inr 2933) = Sparse.eval nodeValue2933 (mixedVector B) := by
    change mixedMoment B node2933 node2933Labels = _
    exact sound2933 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3876 : mixedVector B (Sum.inr 3876) = Sparse.eval nodeValue3876 (mixedVector B) := by
    change mixedMoment B node3876 node3876Labels = _
    exact sound3876 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm276, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2618, h2933, h2942, h2954, h3086, h3876, h4091, reducedSource234] using sourceEq276 B hB

theorem rowSound234 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row234 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck234, numericCheck234, reducedZero234 B hB hF, mul_zero]

theorem reducedZero235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource235 (mixedVector B) = 0 := by
  have h1400 : mixedVector B (Sum.inr 1400) = Sparse.eval nodeValue1400 (mixedVector B) := by
    change mixedMoment B node1400 node1400Labels = _
    exact sound1400 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2947 : mixedVector B (Sum.inr 2947) = Sparse.eval nodeValue2947 (mixedVector B) := by
    change mixedMoment B node2947 node2947Labels = _
    exact sound2947 B hB hF
  have h2949 : mixedVector B (Sum.inr 2949) = Sparse.eval nodeValue2949 (mixedVector B) := by
    change mixedMoment B node2949 node2949Labels = _
    exact sound2949 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm277, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1400, h2942, h2947, h2949, h2964, h3086, h4091, reducedSource235] using sourceEq277 B hB

theorem rowSound235 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row235 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck235, numericCheck235, reducedZero235 B hB hF, mul_zero]

theorem reducedZero237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource237 (mixedVector B) = 0 := by
  have h2588 : mixedVector B (Sum.inr 2588) = Sparse.eval nodeValue2588 (mixedVector B) := by
    change mixedMoment B node2588 node2588Labels = _
    exact sound2588 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm281, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2588, h3502, h3506, h3533, h3540, h3582, h4084, reducedSource237] using sourceEq281 B hB

theorem rowSound237 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row237 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck237, numericCheck237, reducedZero237 B hB hF, mul_zero]

theorem reducedZero238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource238 (mixedVector B) = 0 := by
  have h2033 : mixedVector B (Sum.inr 2033) = Sparse.eval nodeValue2033 (mixedVector B) := by
    change mixedMoment B node2033 node2033Labels = _
    exact sound2033 B hB hF
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm282, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2033, h2035, h2039, h2054, h2278, h3540, h4084, reducedSource238] using sourceEq282 B hB

theorem rowSound238 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row238 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck238, numericCheck238, reducedZero238 B hB hF, mul_zero]

theorem reducedZero239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource239 (mixedVector B) = 0 := by
  have h2278 : mixedVector B (Sum.inr 2278) = Sparse.eval nodeValue2278 (mixedVector B) := by
    change mixedMoment B node2278 node2278Labels = _
    exact sound2278 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm283, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2278, h2781, h3540, h3632, h3633, h4084, reducedSource239] using sourceEq283 B hB

theorem rowSound239 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row239 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck239, numericCheck239, reducedZero239 B hB hF, mul_zero]

theorem sourceRowsAt224 : MixedData.sourceRows (224 : Fin 2425) =
    MixedData.row224 := by decide +kernel

theorem sourceRowsAt225 : MixedData.sourceRows (225 : Fin 2425) =
    MixedData.row225 := by decide +kernel

theorem sourceRowsAt226 : MixedData.sourceRows (226 : Fin 2425) =
    MixedData.row226 := by decide +kernel

theorem sourceRowsAt227 : MixedData.sourceRows (227 : Fin 2425) =
    MixedData.row227 := by decide +kernel

theorem sourceRowsAt228 : MixedData.sourceRows (228 : Fin 2425) =
    MixedData.row228 := by decide +kernel

theorem sourceRowsAt229 : MixedData.sourceRows (229 : Fin 2425) =
    MixedData.row229 := by decide +kernel

theorem sourceRowsAt230 : MixedData.sourceRows (230 : Fin 2425) =
    MixedData.row230 := by decide +kernel

theorem sourceRowsAt231 : MixedData.sourceRows (231 : Fin 2425) =
    MixedData.row231 := by decide +kernel

theorem sourceRowsAt232 : MixedData.sourceRows (232 : Fin 2425) =
    MixedData.row232 := by decide +kernel

theorem sourceRowsAt233 : MixedData.sourceRows (233 : Fin 2425) =
    MixedData.row233 := by decide +kernel

theorem sourceRowsAt234 : MixedData.sourceRows (234 : Fin 2425) =
    MixedData.row234 := by decide +kernel

theorem sourceRowsAt235 : MixedData.sourceRows (235 : Fin 2425) =
    MixedData.row235 := by decide +kernel

theorem sourceRowsAt236 : MixedData.sourceRows (236 : Fin 2425) =
    MixedData.row236 := by decide +kernel

theorem sourceRowsAt237 : MixedData.sourceRows (237 : Fin 2425) =
    MixedData.row237 := by decide +kernel

theorem sourceRowsAt238 : MixedData.sourceRows (238 : Fin 2425) =
    MixedData.row238 := by decide +kernel

theorem sourceRowsAt239 : MixedData.sourceRows (239 : Fin 2425) =
    MixedData.row239 := by decide +kernel

theorem chunkSound14_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 14) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 224 ∨ k.val = 225 ∨ k.val = 226 ∨ k.val = 227 ∨ k.val = 228 ∨ k.val = 229 ∨ k.val = 230 ∨ k.val = 231 ∨ k.val = 232 ∨ k.val = 233 ∨ k.val = 234 ∨ k.val = 235 ∨ k.val = 236 ∨ k.val = 237 ∨ k.val = 238 ∨ k.val = 239 := by omega
  rcases heq with h224 | h225 | h226 | h227 | h228 | h229 | h230 | h231 | h232 | h233 | h234 | h235 | h236 | h237 | h238 | h239
  · have he : k = (224 : Fin 2425) := Fin.ext h224
    subst k
    rw [sourceRowsAt224]
    exact rowSound224 B hB hF
  · have he : k = (225 : Fin 2425) := Fin.ext h225
    subst k
    rw [sourceRowsAt225]
    exact rowSound225 B hB hF
  · have he : k = (226 : Fin 2425) := Fin.ext h226
    subst k
    rw [sourceRowsAt226]
    exact rowSound226_e B hB hF
  · have he : k = (227 : Fin 2425) := Fin.ext h227
    subst k
    rw [sourceRowsAt227]
    exact rowSound227 B hB hF
  · have he : k = (228 : Fin 2425) := Fin.ext h228
    subst k
    rw [sourceRowsAt228]
    exact rowSound228 B hB hF
  · have he : k = (229 : Fin 2425) := Fin.ext h229
    subst k
    rw [sourceRowsAt229]
    exact rowSound229 B hB hF
  · have he : k = (230 : Fin 2425) := Fin.ext h230
    subst k
    rw [sourceRowsAt230]
    exact rowSound230 B hB hF
  · have he : k = (231 : Fin 2425) := Fin.ext h231
    subst k
    rw [sourceRowsAt231]
    exact rowSound231 B hB hF
  · have he : k = (232 : Fin 2425) := Fin.ext h232
    subst k
    rw [sourceRowsAt232]
    exact rowSound232 B hB hF
  · have he : k = (233 : Fin 2425) := Fin.ext h233
    subst k
    rw [sourceRowsAt233]
    exact rowSound233 B hB hF
  · have he : k = (234 : Fin 2425) := Fin.ext h234
    subst k
    rw [sourceRowsAt234]
    exact rowSound234 B hB hF
  · have he : k = (235 : Fin 2425) := Fin.ext h235
    subst k
    rw [sourceRowsAt235]
    exact rowSound235 B hB hF
  · have he : k = (236 : Fin 2425) := Fin.ext h236
    subst k
    rw [sourceRowsAt236]
    exact rowSound236_e B hB hF
  · have he : k = (237 : Fin 2425) := Fin.ext h237
    subst k
    rw [sourceRowsAt237]
    exact rowSound237 B hB hF
  · have he : k = (238 : Fin 2425) := Fin.ext h238
    subst k
    rw [sourceRowsAt238]
    exact rowSound238 B hB hF
  · have he : k = (239 : Fin 2425) := Fin.ext h239
    subst k
    rw [sourceRowsAt239]
    exact rowSound239 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound14_e_oai
