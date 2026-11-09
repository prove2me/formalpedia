-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:14:22.216519+00:00
-- url     : https://prove2.me/submissions/5eb6f5e5-ac9c-48b6-a7fb-2d41d4c41de2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E113
import Definitions.Def_OAIQ106E121
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E126
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound76_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3718 raw3718Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw3718 raw3718Labels = mixedMoment B raw3718step0 raw3718step0Labels := by
      have hz : ∀ j, raw3718 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3718step0 = (fun i j => raw3718 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3718step0 raw3718; decide +kernel
      have hl : raw3718step0Labels = raw3718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718 raw3718Labels permutation434 hz
    mixedMoment B raw3718step0 raw3718step0Labels = mixedMoment B raw3718step1 raw3718step1Labels := by
      have hz : ∀ j, raw3718step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3718step1 = (fun i j => raw3718step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3718step1 raw3718step0; decide +kernel
      have hl : raw3718step1Labels = raw3718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step0 raw3718step0Labels permutation80 hz
    mixedMoment B raw3718step1 raw3718step1Labels = mixedMoment B raw3718step2 raw3718step2Labels := by
      have hz : ∀ j, raw3718step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3718step2 = (fun i j => raw3718step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3718step2 raw3718step1; decide +kernel
      have hl : raw3718step2Labels = raw3718step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3718step1 raw3718step1Labels permutation14 hz
    mixedMoment B raw3718step2 raw3718step2Labels = mixedMoment B raw3718step3 raw3718step3Labels := by
      have ha : raw3718step3 = (fun i j => raw3718step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3718step3 raw3718step2; decide +kernel
      have hl : raw3718step3Labels = raw3718step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3718step2 raw3718step2Labels permutation6 permutation2
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical3721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3721 raw3721Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3721 raw3721Labels = mixedMoment B raw3721step0 raw3721step0Labels := by
      have hz : ∀ j, raw3721 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3721step0 = (fun i j => raw3721 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3721step0 raw3721; decide +kernel
      have hl : raw3721step0Labels = raw3721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721 raw3721Labels permutation520 hz
    mixedMoment B raw3721step0 raw3721step0Labels = mixedMoment B raw3721step1 raw3721step1Labels := by
      have hz : ∀ j, raw3721step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3721step1 = (fun i j => raw3721step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3721step1 raw3721step0; decide +kernel
      have hl : raw3721step1Labels = raw3721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step0 raw3721step0Labels permutation104 hz
    mixedMoment B raw3721step1 raw3721step1Labels = mixedMoment B raw3721step2 raw3721step2Labels := by
      have hz : ∀ j, raw3721step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3721step2 = (fun i j => raw3721step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3721step2 raw3721step1; decide +kernel
      have hl : raw3721step2Labels = raw3721step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step1 raw3721step1Labels permutation20 hz
    mixedMoment B raw3721step2 raw3721step2Labels = mixedMoment B raw3721step3 raw3721step3Labels := by
      have hz : ∀ j, raw3721step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3721step3 = (fun i j => raw3721step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3721step3 raw3721step2; decide +kernel
      have hl : raw3721step3Labels = raw3721step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3721step2 raw3721step2Labels permutation4 hz
    mixedMoment B raw3721step3 raw3721step3Labels = mixedMoment B raw3721step4 raw3721step4Labels := by
      have ha : raw3721step4 = (fun i j => raw3721step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3721step4 raw3721step3; decide +kernel
      have hl : raw3721step4Labels = raw3721step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3721step3 raw3721step3Labels permutation1 permutation0
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3734 raw3734Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw3734 raw3734Labels = mixedMoment B raw3734step0 raw3734step0Labels := by
      have hz : ∀ j, raw3734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3734step0 = (fun i j => raw3734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3734step0 raw3734; decide +kernel
      have hl : raw3734step0Labels = raw3734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3734 raw3734Labels permutation346 hz
    mixedMoment B raw3734step0 raw3734step0Labels = mixedMoment B raw3734step1 raw3734step1Labels := by
      have ha : raw3734step1 = (fun i j => raw3734step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3734step1 raw3734step0; decide +kernel
      have hl : raw3734step1Labels = raw3734step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3734step0 raw3734step0Labels permutation33 permutation4
    mixedMoment B raw3734step1 raw3734step1Labels = mixedMoment B raw3734step2 raw3734step2Labels := by
      have ha : raw3734step2 = -raw3734step1 := by apply Matrix.ext; change ∀ i j, raw3734step2 i j = -(raw3734step1 i j); unfold raw3734step2 raw3734step1; decide +kernel
      have hl : raw3734step2Labels = raw3734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4002 raw4002Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4002 raw4002Labels = mixedMoment B raw4002step0 raw4002step0Labels := by
      have hz : ∀ j, raw4002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4002step0 = (fun i j => raw4002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4002step0 raw4002; decide +kernel
      have hl : raw4002step0Labels = raw4002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4002 raw4002Labels permutation434 hz
    mixedMoment B raw4002step0 raw4002step0Labels = mixedMoment B raw4002step1 raw4002step1Labels := by
      have hz : ∀ j, raw4002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4002step1 = (fun i j => raw4002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4002step1 raw4002step0; decide +kernel
      have hl : raw4002step1Labels = raw4002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4002step0 raw4002step0Labels permutation80 hz
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical4004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4004 raw4004Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw4004 raw4004Labels = mixedMoment B raw4004step0 raw4004step0Labels := by
      have hz : ∀ j, raw4004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4004step0 = (fun i j => raw4004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4004step0 raw4004; decide +kernel
      have hl : raw4004step0Labels = raw4004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4004 raw4004Labels permutation434 hz
    mixedMoment B raw4004step0 raw4004step0Labels = mixedMoment B raw4004step1 raw4004step1Labels := by
      have ha : raw4004step1 = (fun i j => raw4004step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4004step1 raw4004step0; decide +kernel
      have hl : raw4004step1Labels = raw4004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4004step0 raw4004step0Labels permutation149 permutation2
    mixedMoment B raw4004step1 raw4004step1Labels = mixedMoment B raw4004step2 raw4004step2Labels := by
      have ha : raw4004step2 = -raw4004step1 := by apply Matrix.ext; change ∀ i j, raw4004step2 i j = -(raw4004step1 i j); unfold raw4004step2 raw4004step1; decide +kernel
      have hl : raw4004step2Labels = raw4004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical4006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4006 raw4006Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw4006 raw4006Labels = mixedMoment B raw4006step0 raw4006step0Labels := by
      have hz : ∀ j, raw4006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4006step0 = (fun i j => raw4006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4006step0 raw4006; decide +kernel
      have hl : raw4006step0Labels = raw4006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4006 raw4006Labels permutation434 hz
    mixedMoment B raw4006step0 raw4006step0Labels = mixedMoment B raw4006step1 raw4006step1Labels := by
      have hz : ∀ j, raw4006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4006step1 = (fun i j => raw4006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4006step1 raw4006step0; decide +kernel
      have hl : raw4006step1Labels = raw4006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4006step0 raw4006step0Labels permutation80 hz
    mixedMoment B raw4006step1 raw4006step1Labels = mixedMoment B raw4006step2 raw4006step2Labels := by
      have ha : raw4006step2 = (fun i j => raw4006step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4006step2 raw4006step1; decide +kernel
      have hl : raw4006step2Labels = raw4006step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4006step1 raw4006step1Labels permutation20 permutation4
    mixedMoment B raw4006step2 raw4006step2Labels = mixedMoment B raw4006step3 raw4006step3Labels := by
      have ha : raw4006step3 = -raw4006step2 := by apply Matrix.ext; change ∀ i j, raw4006step3 i j = -(raw4006step2 i j); unfold raw4006step3 raw4006step2; decide +kernel
      have hl : raw4006step3Labels = raw4006step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4008 raw4008Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4008 raw4008Labels = mixedMoment B raw4008step0 raw4008step0Labels := by
      have hz : ∀ j, raw4008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4008step0 = (fun i j => raw4008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4008step0 raw4008; decide +kernel
      have hl : raw4008step0Labels = raw4008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4008 raw4008Labels permutation434 hz
    mixedMoment B raw4008step0 raw4008step0Labels = mixedMoment B raw4008step1 raw4008step1Labels := by
      have hz : ∀ j, raw4008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4008step1 = (fun i j => raw4008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4008step1 raw4008step0; decide +kernel
      have hl : raw4008step1Labels = raw4008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4008step0 raw4008step0Labels permutation80 hz
    mixedMoment B raw4008step1 raw4008step1Labels = mixedMoment B raw4008step2 raw4008step2Labels := by
      have ha : raw4008step2 = (fun i j => raw4008step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4008step2 raw4008step1; decide +kernel
      have hl : raw4008step2Labels = raw4008step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4008step1 raw4008step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4010 raw4010Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw4010 raw4010Labels = mixedMoment B raw4010step0 raw4010step0Labels := by
      have hz : ∀ j, raw4010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4010step0 = (fun i j => raw4010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4010step0 raw4010; decide +kernel
      have hl : raw4010step0Labels = raw4010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4010 raw4010Labels permutation434 hz
    mixedMoment B raw4010step0 raw4010step0Labels = mixedMoment B raw4010step1 raw4010step1Labels := by
      have ha : raw4010step1 = (fun i j => raw4010step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4010step1 raw4010step0; decide +kernel
      have hl : raw4010step1Labels = raw4010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4010step0 raw4010step0Labels permutation34 permutation2
    _ = mixedMoment B node1224 node1224Labels := by rfl

theorem canonical4012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4012 raw4012Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw4012 raw4012Labels = mixedMoment B raw4012step0 raw4012step0Labels := by
      have hz : ∀ j, raw4012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4012step0 = (fun i j => raw4012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4012step0 raw4012; decide +kernel
      have hl : raw4012step0Labels = raw4012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4012 raw4012Labels permutation434 hz
    mixedMoment B raw4012step0 raw4012step0Labels = mixedMoment B raw4012step1 raw4012step1Labels := by
      have hz : ∀ j, raw4012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4012step1 = (fun i j => raw4012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4012step1 raw4012step0; decide +kernel
      have hl : raw4012step1Labels = raw4012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4012step0 raw4012step0Labels permutation80 hz
    _ = mixedMoment B node1243 node1243Labels := by rfl

theorem canonical4013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4013 raw4013Labels = mixedMoment B node1227 node1227Labels := by
  calc
    mixedMoment B raw4013 raw4013Labels = mixedMoment B raw4013step0 raw4013step0Labels := by
      have hz : ∀ j, raw4013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4013step0 = (fun i j => raw4013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4013step0 raw4013; decide +kernel
      have hl : raw4013step0Labels = raw4013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4013 raw4013Labels permutation434 hz
    mixedMoment B raw4013step0 raw4013step0Labels = mixedMoment B raw4013step1 raw4013step1Labels := by
      have hz : ∀ j, raw4013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4013step1 = (fun i j => raw4013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4013step1 raw4013step0; decide +kernel
      have hl : raw4013step1Labels = raw4013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4013step0 raw4013step0Labels permutation80 hz
    _ = mixedMoment B node1227 node1227Labels := by rfl

theorem canonical4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4014 raw4014Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw4014 raw4014Labels = mixedMoment B raw4014step0 raw4014step0Labels := by
      have hz : ∀ j, raw4014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4014step0 = (fun i j => raw4014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4014step0 raw4014; decide +kernel
      have hl : raw4014step0Labels = raw4014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4014 raw4014Labels permutation434 hz
    mixedMoment B raw4014step0 raw4014step0Labels = mixedMoment B raw4014step1 raw4014step1Labels := by
      have ha : raw4014step1 = (fun i j => raw4014step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4014step1 raw4014step0; decide +kernel
      have hl : raw4014step1Labels = raw4014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4014step0 raw4014step0Labels permutation40 permutation2
    _ = mixedMoment B node2579 node2579Labels := by rfl

theorem canonical4016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4016 raw4016Labels = mixedMoment B node2651 node2651Labels := by
  calc
    mixedMoment B raw4016 raw4016Labels = mixedMoment B raw4016step0 raw4016step0Labels := by
      have hz : ∀ j, raw4016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4016step0 = (fun i j => raw4016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4016step0 raw4016; decide +kernel
      have hl : raw4016step0Labels = raw4016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4016 raw4016Labels permutation434 hz
    mixedMoment B raw4016step0 raw4016step0Labels = mixedMoment B raw4016step1 raw4016step1Labels := by
      have hz : ∀ j, raw4016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4016step1 = (fun i j => raw4016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4016step1 raw4016step0; decide +kernel
      have hl : raw4016step1Labels = raw4016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4016step0 raw4016step0Labels permutation80 hz
    mixedMoment B raw4016step1 raw4016step1Labels = mixedMoment B raw4016step2 raw4016step2Labels := by
      have ha : raw4016step2 = (fun i j => raw4016step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4016step2 raw4016step1; decide +kernel
      have hl : raw4016step2Labels = raw4016step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4016step1 raw4016step1Labels permutation10 permutation2
    _ = mixedMoment B node2651 node2651Labels := by rfl

theorem canonical4018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4018 raw4018Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw4018 raw4018Labels = mixedMoment B raw4018step0 raw4018step0Labels := by
      have hz : ∀ j, raw4018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4018step0 = (fun i j => raw4018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4018step0 raw4018; decide +kernel
      have hl : raw4018step0Labels = raw4018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4018 raw4018Labels permutation434 hz
    mixedMoment B raw4018step0 raw4018step0Labels = mixedMoment B raw4018step1 raw4018step1Labels := by
      have ha : raw4018step1 = (fun i j => raw4018step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4018step1 raw4018step0; decide +kernel
      have hl : raw4018step1Labels = raw4018step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4018step0 raw4018step0Labels permutation34 permutation2
    _ = mixedMoment B node2495 node2495Labels := by rfl

theorem canonical4020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4020 raw4020Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw4020 raw4020Labels = mixedMoment B raw4020step0 raw4020step0Labels := by
      have hz : ∀ j, raw4020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4020step0 = (fun i j => raw4020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4020step0 raw4020; decide +kernel
      have hl : raw4020step0Labels = raw4020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4020 raw4020Labels permutation434 hz
    mixedMoment B raw4020step0 raw4020step0Labels = mixedMoment B raw4020step1 raw4020step1Labels := by
      have hz : ∀ j, raw4020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4020step1 = (fun i j => raw4020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4020step1 raw4020step0; decide +kernel
      have hl : raw4020step1Labels = raw4020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4020step0 raw4020step0Labels permutation80 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical4021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4021 raw4021Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw4021 raw4021Labels = mixedMoment B raw4021step0 raw4021step0Labels := by
      have hz : ∀ j, raw4021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4021step0 = (fun i j => raw4021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4021step0 raw4021; decide +kernel
      have hl : raw4021step0Labels = raw4021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4021 raw4021Labels permutation434 hz
    mixedMoment B raw4021step0 raw4021step0Labels = mixedMoment B raw4021step1 raw4021step1Labels := by
      have hz : ∀ j, raw4021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4021step1 = (fun i j => raw4021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4021step1 raw4021step0; decide +kernel
      have hl : raw4021step1Labels = raw4021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4021step0 raw4021step0Labels permutation80 hz
    mixedMoment B raw4021step1 raw4021step1Labels = mixedMoment B raw4021step2 raw4021step2Labels := by
      have ha : raw4021step2 = (fun i j => raw4021step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4021step2 raw4021step1; decide +kernel
      have hl : raw4021step2Labels = raw4021step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4021step1 raw4021step1Labels permutation31 permutation2
    mixedMoment B raw4021step2 raw4021step2Labels = mixedMoment B raw4021step3 raw4021step3Labels := by
      have ha : raw4021step3 = -raw4021step2 := by apply Matrix.ext; change ∀ i j, raw4021step3 i j = -(raw4021step2 i j); unfold raw4021step3 raw4021step2; decide +kernel
      have hl : raw4021step3Labels = raw4021step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

theorem canonical4022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4022 raw4022Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw4022 raw4022Labels = mixedMoment B raw4022step0 raw4022step0Labels := by
      have ha : raw4022step0 = (fun i j => raw4022 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4022step0 raw4022; decide +kernel
      have hl : raw4022step0Labels = raw4022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4022 raw4022Labels permutation202 permutation2
    _ = mixedMoment B node2547 node2547Labels := by rfl

theorem canonical4023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4023 raw4023Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw4023 raw4023Labels = mixedMoment B raw4023step0 raw4023step0Labels := by
      have hz : ∀ j, raw4023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4023step0 = (fun i j => raw4023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4023step0 raw4023; decide +kernel
      have hl : raw4023step0Labels = raw4023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4023 raw4023Labels permutation434 hz
    mixedMoment B raw4023step0 raw4023step0Labels = mixedMoment B raw4023step1 raw4023step1Labels := by
      have ha : raw4023step1 = (fun i j => raw4023step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4023step1 raw4023step0; decide +kernel
      have hl : raw4023step1Labels = raw4023step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4023step0 raw4023step0Labels permutation44 permutation2
    _ = mixedMoment B node2647 node2647Labels := by rfl

theorem canonical4024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4024 raw4024Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw4024 raw4024Labels = mixedMoment B raw4024step0 raw4024step0Labels := by
      have hz : ∀ j, raw4024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4024step0 = (fun i j => raw4024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4024step0 raw4024; decide +kernel
      have hl : raw4024step0Labels = raw4024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4024 raw4024Labels permutation434 hz
    mixedMoment B raw4024step0 raw4024step0Labels = mixedMoment B raw4024step1 raw4024step1Labels := by
      have ha : raw4024step1 = (fun i j => raw4024step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4024step1 raw4024step0; decide +kernel
      have hl : raw4024step1Labels = raw4024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4024step0 raw4024step0Labels permutation34 permutation2
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4025 raw4025Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw4025 raw4025Labels = mixedMoment B raw4025step0 raw4025step0Labels := by
      have ha : raw4025step0 = (fun i j => raw4025 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4025step0 raw4025; decide +kernel
      have hl : raw4025step0Labels = raw4025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4025 raw4025Labels permutation178 permutation2
    _ = mixedMoment B node2547 node2547Labels := by rfl

theorem canonical4026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4026 raw4026Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw4026 raw4026Labels = mixedMoment B raw4026step0 raw4026step0Labels := by
      have hz : ∀ j, raw4026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4026step0 = (fun i j => raw4026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4026step0 raw4026; decide +kernel
      have hl : raw4026step0Labels = raw4026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4026 raw4026Labels permutation434 hz
    mixedMoment B raw4026step0 raw4026step0Labels = mixedMoment B raw4026step1 raw4026step1Labels := by
      have ha : raw4026step1 = (fun i j => raw4026step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4026step1 raw4026step0; decide +kernel
      have hl : raw4026step1Labels = raw4026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4026step0 raw4026step0Labels permutation38 permutation2
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical4027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4027 raw4027Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw4027 raw4027Labels = mixedMoment B raw4027step0 raw4027step0Labels := by
      have hz : ∀ j, raw4027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4027step0 = (fun i j => raw4027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4027step0 raw4027; decide +kernel
      have hl : raw4027step0Labels = raw4027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4027 raw4027Labels permutation434 hz
    mixedMoment B raw4027step0 raw4027step0Labels = mixedMoment B raw4027step1 raw4027step1Labels := by
      have ha : raw4027step1 = (fun i j => raw4027step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4027step1 raw4027step0; decide +kernel
      have hl : raw4027step1Labels = raw4027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4027step0 raw4027step0Labels permutation149 permutation2
    mixedMoment B raw4027step1 raw4027step1Labels = mixedMoment B raw4027step2 raw4027step2Labels := by
      have ha : raw4027step2 = -raw4027step1 := by apply Matrix.ext; change ∀ i j, raw4027step2 i j = -(raw4027step1 i j); unfold raw4027step2 raw4027step1; decide +kernel
      have hl : raw4027step2Labels = raw4027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1359 node1359Labels := by rfl

theorem canonical4028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4028 raw4028Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw4028 raw4028Labels = mixedMoment B raw4028step0 raw4028step0Labels := by
      have hz : ∀ j, raw4028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4028step0 = (fun i j => raw4028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4028step0 raw4028; decide +kernel
      have hl : raw4028step0Labels = raw4028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4028 raw4028Labels permutation346 hz
    mixedMoment B raw4028step0 raw4028step0Labels = mixedMoment B raw4028step1 raw4028step1Labels := by
      have ha : raw4028step1 = (fun i j => raw4028step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4028step1 raw4028step0; decide +kernel
      have hl : raw4028step1Labels = raw4028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4028step0 raw4028step0Labels permutation38 permutation2
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical4029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4029 raw4029Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw4029 raw4029Labels = mixedMoment B raw4029step0 raw4029step0Labels := by
      have hz : ∀ j, raw4029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4029step0 = (fun i j => raw4029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4029step0 raw4029; decide +kernel
      have hl : raw4029step0Labels = raw4029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4029 raw4029Labels permutation434 hz
    mixedMoment B raw4029step0 raw4029step0Labels = mixedMoment B raw4029step1 raw4029step1Labels := by
      have hz : ∀ j, raw4029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4029step1 = (fun i j => raw4029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4029step1 raw4029step0; decide +kernel
      have hl : raw4029step1Labels = raw4029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4029step0 raw4029step0Labels permutation80 hz
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical4030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4030 raw4030Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw4030 raw4030Labels = mixedMoment B raw4030step0 raw4030step0Labels := by
      have hz : ∀ j, raw4030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4030step0 = (fun i j => raw4030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4030step0 raw4030; decide +kernel
      have hl : raw4030step0Labels = raw4030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4030 raw4030Labels permutation346 hz
    mixedMoment B raw4030step0 raw4030step0Labels = mixedMoment B raw4030step1 raw4030step1Labels := by
      have ha : raw4030step1 = (fun i j => raw4030step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4030step1 raw4030step0; decide +kernel
      have hl : raw4030step1Labels = raw4030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4030step0 raw4030step0Labels permutation44 permutation2
    _ = mixedMoment B node2647 node2647Labels := by rfl

theorem canonical4031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4031 raw4031Labels = mixedMoment B node1424 node1424Labels := by
  calc
    mixedMoment B raw4031 raw4031Labels = mixedMoment B raw4031step0 raw4031step0Labels := by
      have hz : ∀ j, raw4031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4031step0 = (fun i j => raw4031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4031step0 raw4031; decide +kernel
      have hl : raw4031step0Labels = raw4031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4031 raw4031Labels permutation434 hz
    mixedMoment B raw4031step0 raw4031step0Labels = mixedMoment B raw4031step1 raw4031step1Labels := by
      have hz : ∀ j, raw4031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4031step1 = (fun i j => raw4031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4031step1 raw4031step0; decide +kernel
      have hl : raw4031step1Labels = raw4031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4031step0 raw4031step0Labels permutation80 hz
    mixedMoment B raw4031step1 raw4031step1Labels = mixedMoment B raw4031step2 raw4031step2Labels := by
      have ha : raw4031step2 = (fun i j => raw4031step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4031step2 raw4031step1; decide +kernel
      have hl : raw4031step2Labels = raw4031step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4031step1 raw4031step1Labels permutation29 permutation2
    mixedMoment B raw4031step2 raw4031step2Labels = mixedMoment B raw4031step3 raw4031step3Labels := by
      have ha : raw4031step3 = -raw4031step2 := by apply Matrix.ext; change ∀ i j, raw4031step3 i j = -(raw4031step2 i j); unfold raw4031step3 raw4031step2; decide +kernel
      have hl : raw4031step3Labels = raw4031step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1424 node1424Labels := by rfl

theorem canonical4032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4032 raw4032Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw4032 raw4032Labels = mixedMoment B raw4032step0 raw4032step0Labels := by
      have hz : ∀ j, raw4032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4032step0 = (fun i j => raw4032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4032step0 raw4032; decide +kernel
      have hl : raw4032step0Labels = raw4032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4032 raw4032Labels permutation346 hz
    mixedMoment B raw4032step0 raw4032step0Labels = mixedMoment B raw4032step1 raw4032step1Labels := by
      have ha : raw4032step1 = (fun i j => raw4032step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4032step1 raw4032step0; decide +kernel
      have hl : raw4032step1Labels = raw4032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4032step0 raw4032step0Labels permutation149 permutation2
    mixedMoment B raw4032step1 raw4032step1Labels = mixedMoment B raw4032step2 raw4032step2Labels := by
      have ha : raw4032step2 = -raw4032step1 := by apply Matrix.ext; change ∀ i j, raw4032step2 i j = -(raw4032step1 i j); unfold raw4032step2 raw4032step1; decide +kernel
      have hl : raw4032step2Labels = raw4032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1359 node1359Labels := by rfl

theorem canonical4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4085 raw4085Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw4085 raw4085Labels = mixedMoment B raw4085step0 raw4085step0Labels := by
      have hz : ∀ j, raw4085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4085step0 = (fun i j => raw4085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4085step0 raw4085; decide +kernel
      have hl : raw4085step0Labels = raw4085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4085 raw4085Labels permutation434 hz
    mixedMoment B raw4085step0 raw4085step0Labels = mixedMoment B raw4085step1 raw4085step1Labels := by
      have hz : ∀ j, raw4085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4085step1 = (fun i j => raw4085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4085step1 raw4085step0; decide +kernel
      have hl : raw4085step1Labels = raw4085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4085step0 raw4085step0Labels permutation80 hz
    mixedMoment B raw4085step1 raw4085step1Labels = mixedMoment B raw4085step2 raw4085step2Labels := by
      have ha : raw4085step2 = (fun i j => raw4085step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4085step2 raw4085step1; decide +kernel
      have hl : raw4085step2Labels = raw4085step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4085step1 raw4085step1Labels permutation28 permutation2
    _ = mixedMoment B node3549 node3549Labels := by rfl

theorem canonical4086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4086 raw4086Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw4086 raw4086Labels = mixedMoment B raw4086step0 raw4086step0Labels := by
      have hz : ∀ j, raw4086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4086step0 = (fun i j => raw4086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4086step0 raw4086; decide +kernel
      have hl : raw4086step0Labels = raw4086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4086 raw4086Labels permutation434 hz
    mixedMoment B raw4086step0 raw4086step0Labels = mixedMoment B raw4086step1 raw4086step1Labels := by
      have hz : ∀ j, raw4086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4086step1 = (fun i j => raw4086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4086step1 raw4086step0; decide +kernel
      have hl : raw4086step1Labels = raw4086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4086step0 raw4086step0Labels permutation80 hz
    mixedMoment B raw4086step1 raw4086step1Labels = mixedMoment B raw4086step2 raw4086step2Labels := by
      have ha : raw4086step2 = (fun i j => raw4086step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4086step2 raw4086step1; decide +kernel
      have hl : raw4086step2Labels = raw4086step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4086step1 raw4086step1Labels permutation29 permutation2
    _ = mixedMoment B node3396 node3396Labels := by rfl

theorem canonical4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4087 raw4087Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4087 raw4087Labels = mixedMoment B raw4087step0 raw4087step0Labels := by
      have hz : ∀ j, raw4087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4087step0 = (fun i j => raw4087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4087step0 raw4087; decide +kernel
      have hl : raw4087step0Labels = raw4087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4087 raw4087Labels permutation434 hz
    mixedMoment B raw4087step0 raw4087step0Labels = mixedMoment B raw4087step1 raw4087step1Labels := by
      have ha : raw4087step1 = (fun i j => raw4087step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4087step1 raw4087step0; decide +kernel
      have hl : raw4087step1Labels = raw4087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4087step0 raw4087step0Labels permutation44 permutation2
    mixedMoment B raw4087step1 raw4087step1Labels = mixedMoment B raw4087step2 raw4087step2Labels := by
      have ha : raw4087step2 = -raw4087step1 := by apply Matrix.ext; change ∀ i j, raw4087step2 i j = -(raw4087step1 i j); unfold raw4087step2 raw4087step1; decide +kernel
      have hl : raw4087step2Labels = raw4087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3389 node3389Labels := by rfl

theorem canonical4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4088 raw4088Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4088 raw4088Labels = mixedMoment B raw4088step0 raw4088step0Labels := by
      have hz : ∀ j, raw4088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4088step0 = (fun i j => raw4088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4088step0 raw4088; decide +kernel
      have hl : raw4088step0Labels = raw4088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4088 raw4088Labels permutation346 hz
    mixedMoment B raw4088step0 raw4088step0Labels = mixedMoment B raw4088step1 raw4088step1Labels := by
      have ha : raw4088step1 = (fun i j => raw4088step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4088step1 raw4088step0; decide +kernel
      have hl : raw4088step1Labels = raw4088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4088step0 raw4088step0Labels permutation44 permutation2
    mixedMoment B raw4088step1 raw4088step1Labels = mixedMoment B raw4088step2 raw4088step2Labels := by
      have ha : raw4088step2 = -raw4088step1 := by apply Matrix.ext; change ∀ i j, raw4088step2 i j = -(raw4088step1 i j); unfold raw4088step2 raw4088step1; decide +kernel
      have hl : raw4088step2Labels = raw4088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3389 node3389Labels := by rfl

theorem canonical4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4089 raw4089Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4089 raw4089Labels = mixedMoment B raw4089step0 raw4089step0Labels := by
      have hz : ∀ j, raw4089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4089step0 = (fun i j => raw4089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4089step0 raw4089; decide +kernel
      have hl : raw4089step0Labels = raw4089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4089 raw4089Labels permutation434 hz
    mixedMoment B raw4089step0 raw4089step0Labels = mixedMoment B raw4089step1 raw4089step1Labels := by
      have hz : ∀ j, raw4089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4089step1 = (fun i j => raw4089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4089step1 raw4089step0; decide +kernel
      have hl : raw4089step1Labels = raw4089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4089step0 raw4089step0Labels permutation80 hz
    mixedMoment B raw4089step1 raw4089step1Labels = mixedMoment B raw4089step2 raw4089step2Labels := by
      have ha : raw4089step2 = (fun i j => raw4089step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4089step2 raw4089step1; decide +kernel
      have hl : raw4089step2Labels = raw4089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4089step1 raw4089step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

theorem canonical4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4090 raw4090Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4090 raw4090Labels = mixedMoment B raw4090step0 raw4090step0Labels := by
      have hz : ∀ j, raw4090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4090step0 = (fun i j => raw4090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4090step0 raw4090; decide +kernel
      have hl : raw4090step0Labels = raw4090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4090 raw4090Labels permutation434 hz
    mixedMoment B raw4090step0 raw4090step0Labels = mixedMoment B raw4090step1 raw4090step1Labels := by
      have hz : ∀ j, raw4090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4090step1 = (fun i j => raw4090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4090step1 raw4090step0; decide +kernel
      have hl : raw4090step1Labels = raw4090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4090step0 raw4090step0Labels permutation80 hz
    mixedMoment B raw4090step1 raw4090step1Labels = mixedMoment B raw4090step2 raw4090step2Labels := by
      have ha : raw4090step2 = (fun i j => raw4090step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4090step2 raw4090step1; decide +kernel
      have hl : raw4090step2Labels = raw4090step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4090step1 raw4090step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4091 raw4091Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw4091 raw4091Labels = mixedMoment B raw4091step0 raw4091step0Labels := by
      have hz : ∀ j, raw4091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4091step0 = (fun i j => raw4091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4091step0 raw4091; decide +kernel
      have hl : raw4091step0Labels = raw4091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091 raw4091Labels permutation434 hz
    mixedMoment B raw4091step0 raw4091step0Labels = mixedMoment B raw4091step1 raw4091step1Labels := by
      have hz : ∀ j, raw4091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4091step1 = (fun i j => raw4091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4091step1 raw4091step0; decide +kernel
      have hl : raw4091step1Labels = raw4091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091step0 raw4091step0Labels permutation80 hz
    mixedMoment B raw4091step1 raw4091step1Labels = mixedMoment B raw4091step2 raw4091step2Labels := by
      have hz : ∀ j, raw4091step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4091step2 = (fun i j => raw4091step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4091step2 raw4091step1; decide +kernel
      have hl : raw4091step2Labels = raw4091step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091step1 raw4091step1Labels permutation14 hz
    mixedMoment B raw4091step2 raw4091step2Labels = mixedMoment B raw4091step3 raw4091step3Labels := by
      have ha : raw4091step3 = (fun i j => raw4091step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4091step3 raw4091step2; decide +kernel
      have hl : raw4091step3Labels = raw4091step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4091step2 raw4091step2Labels permutation3 permutation4
    mixedMoment B raw4091step3 raw4091step3Labels = mixedMoment B raw4091step4 raw4091step4Labels := by
      have ha : raw4091step4 = -raw4091step3 := by apply Matrix.ext; change ∀ i j, raw4091step4 i j = -(raw4091step3 i j); unfold raw4091step4 raw4091step3; decide +kernel
      have hl : raw4091step4Labels = raw4091step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4092 raw4092Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw4092 raw4092Labels = mixedMoment B raw4092step0 raw4092step0Labels := by
      have hz : ∀ j, raw4092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4092step0 = (fun i j => raw4092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4092step0 raw4092; decide +kernel
      have hl : raw4092step0Labels = raw4092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4092 raw4092Labels permutation434 hz
    mixedMoment B raw4092step0 raw4092step0Labels = mixedMoment B raw4092step1 raw4092step1Labels := by
      have ha : raw4092step1 = (fun i j => raw4092step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4092step1 raw4092step0; decide +kernel
      have hl : raw4092step1Labels = raw4092step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4092step0 raw4092step0Labels permutation33 permutation4
    mixedMoment B raw4092step1 raw4092step1Labels = mixedMoment B raw4092step2 raw4092step2Labels := by
      have ha : raw4092step2 = -raw4092step1 := by apply Matrix.ext; change ∀ i j, raw4092step2 i j = -(raw4092step1 i j); unfold raw4092step2 raw4092step1; decide +kernel
      have hl : raw4092step2Labels = raw4092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical4093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4093 raw4093Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw4093 raw4093Labels = mixedMoment B raw4093step0 raw4093step0Labels := by
      have hz : ∀ j, raw4093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4093step0 = (fun i j => raw4093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4093step0 raw4093; decide +kernel
      have hl : raw4093step0Labels = raw4093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4093 raw4093Labels permutation434 hz
    mixedMoment B raw4093step0 raw4093step0Labels = mixedMoment B raw4093step1 raw4093step1Labels := by
      have hz : ∀ j, raw4093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4093step1 = (fun i j => raw4093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4093step1 raw4093step0; decide +kernel
      have hl : raw4093step1Labels = raw4093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4093step0 raw4093step0Labels permutation80 hz
    mixedMoment B raw4093step1 raw4093step1Labels = mixedMoment B raw4093step2 raw4093step2Labels := by
      have ha : raw4093step2 = (fun i j => raw4093step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4093step2 raw4093step1; decide +kernel
      have hl : raw4093step2Labels = raw4093step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4093step1 raw4093step1Labels permutation9 permutation4
    mixedMoment B raw4093step2 raw4093step2Labels = mixedMoment B raw4093step3 raw4093step3Labels := by
      have ha : raw4093step3 = -raw4093step2 := by apply Matrix.ext; change ∀ i j, raw4093step3 i j = -(raw4093step2 i j); unfold raw4093step3 raw4093step2; decide +kernel
      have hl : raw4093step3Labels = raw4093step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4094 raw4094Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4094 raw4094Labels = mixedMoment B raw4094step0 raw4094step0Labels := by
      have hz : ∀ j, raw4094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4094step0 = (fun i j => raw4094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4094step0 raw4094; decide +kernel
      have hl : raw4094step0Labels = raw4094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4094 raw4094Labels permutation434 hz
    mixedMoment B raw4094step0 raw4094step0Labels = mixedMoment B raw4094step1 raw4094step1Labels := by
      have hz : ∀ j, raw4094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4094step1 = (fun i j => raw4094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4094step1 raw4094step0; decide +kernel
      have hl : raw4094step1Labels = raw4094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4094step0 raw4094step0Labels permutation80 hz
    mixedMoment B raw4094step1 raw4094step1Labels = mixedMoment B raw4094step2 raw4094step2Labels := by
      have ha : raw4094step2 = (fun i j => raw4094step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4094step2 raw4094step1; decide +kernel
      have hl : raw4094step2Labels = raw4094step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4094step1 raw4094step1Labels permutation8 permutation4
    mixedMoment B raw4094step2 raw4094step2Labels = mixedMoment B raw4094step3 raw4094step3Labels := by
      have ha : raw4094step3 = -raw4094step2 := by apply Matrix.ext; change ∀ i j, raw4094step3 i j = -(raw4094step2 i j); unfold raw4094step3 raw4094step2; decide +kernel
      have hl : raw4094step3Labels = raw4094step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

theorem canonical4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4095 raw4095Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw4095 raw4095Labels = mixedMoment B raw4095step0 raw4095step0Labels := by
      have hz : ∀ j, raw4095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4095step0 = (fun i j => raw4095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4095step0 raw4095; decide +kernel
      have hl : raw4095step0Labels = raw4095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4095 raw4095Labels permutation434 hz
    mixedMoment B raw4095step0 raw4095step0Labels = mixedMoment B raw4095step1 raw4095step1Labels := by
      have hz : ∀ j, raw4095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4095step1 = (fun i j => raw4095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4095step1 raw4095step0; decide +kernel
      have hl : raw4095step1Labels = raw4095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4095step0 raw4095step0Labels permutation56 hz
    mixedMoment B raw4095step1 raw4095step1Labels = mixedMoment B raw4095step2 raw4095step2Labels := by
      have ha : raw4095step2 = (fun i j => raw4095step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4095step2 raw4095step1; decide +kernel
      have hl : raw4095step2Labels = raw4095step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4095step1 raw4095step1Labels permutation28 permutation2
    _ = mixedMoment B node3549 node3549Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4096 raw4096Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw4096 raw4096Labels = mixedMoment B raw4096step0 raw4096step0Labels := by
      have hz : ∀ j, raw4096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4096step0 = (fun i j => raw4096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4096step0 raw4096; decide +kernel
      have hl : raw4096step0Labels = raw4096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4096 raw4096Labels permutation346 hz
    mixedMoment B raw4096step0 raw4096step0Labels = mixedMoment B raw4096step1 raw4096step1Labels := by
      have hz : ∀ j, raw4096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4096step1 = (fun i j => raw4096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4096step1 raw4096step0; decide +kernel
      have hl : raw4096step1Labels = raw4096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4096step0 raw4096step0Labels permutation56 hz
    mixedMoment B raw4096step1 raw4096step1Labels = mixedMoment B raw4096step2 raw4096step2Labels := by
      have ha : raw4096step2 = (fun i j => raw4096step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4096step2 raw4096step1; decide +kernel
      have hl : raw4096step2Labels = raw4096step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4096step1 raw4096step1Labels permutation28 permutation2
    _ = mixedMoment B node3549 node3549Labels := by rfl

theorem canonical4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4097 raw4097Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw4097 raw4097Labels = mixedMoment B raw4097step0 raw4097step0Labels := by
      have hz : ∀ j, raw4097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4097step0 = (fun i j => raw4097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4097step0 raw4097; decide +kernel
      have hl : raw4097step0Labels = raw4097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097 raw4097Labels permutation434 hz
    mixedMoment B raw4097step0 raw4097step0Labels = mixedMoment B raw4097step1 raw4097step1Labels := by
      have hz : ∀ j, raw4097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4097step1 = (fun i j => raw4097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4097step1 raw4097step0; decide +kernel
      have hl : raw4097step1Labels = raw4097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step0 raw4097step0Labels permutation80 hz
    mixedMoment B raw4097step1 raw4097step1Labels = mixedMoment B raw4097step2 raw4097step2Labels := by
      have hz : ∀ j, raw4097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4097step2 = (fun i j => raw4097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4097step2 raw4097step1; decide +kernel
      have hl : raw4097step2Labels = raw4097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step1 raw4097step1Labels permutation14 hz
    mixedMoment B raw4097step2 raw4097step2Labels = mixedMoment B raw4097step3 raw4097step3Labels := by
      have ha : raw4097step3 = (fun i j => raw4097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4097step3 raw4097step2; decide +kernel
      have hl : raw4097step3Labels = raw4097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4097step2 raw4097step2Labels permutation7 permutation2
    _ = mixedMoment B node3634 node3634Labels := by rfl

theorem canonical4098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4098 raw4098Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4098 raw4098Labels = mixedMoment B raw4098step0 raw4098step0Labels := by
      have hz : ∀ j, raw4098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4098step0 = (fun i j => raw4098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4098step0 raw4098; decide +kernel
      have hl : raw4098step0Labels = raw4098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4098 raw4098Labels permutation434 hz
    mixedMoment B raw4098step0 raw4098step0Labels = mixedMoment B raw4098step1 raw4098step1Labels := by
      have ha : raw4098step1 = (fun i j => raw4098step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4098step1 raw4098step0; decide +kernel
      have hl : raw4098step1Labels = raw4098step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4098step0 raw4098step0Labels permutation136 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

theorem canonical4099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4099 raw4099Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4099 raw4099Labels = mixedMoment B raw4099step0 raw4099step0Labels := by
      have hz : ∀ j, raw4099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4099step0 = (fun i j => raw4099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4099step0 raw4099; decide +kernel
      have hl : raw4099step0Labels = raw4099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4099 raw4099Labels permutation346 hz
    mixedMoment B raw4099step0 raw4099step0Labels = mixedMoment B raw4099step1 raw4099step1Labels := by
      have ha : raw4099step1 = (fun i j => raw4099step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4099step1 raw4099step0; decide +kernel
      have hl : raw4099step1Labels = raw4099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4099step0 raw4099step0Labels permutation136 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

theorem canonical4100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4100 raw4100Labels = mixedMoment B node3160 node3160Labels := by
  calc
    mixedMoment B raw4100 raw4100Labels = mixedMoment B raw4100step0 raw4100step0Labels := by
      have hz : ∀ j, raw4100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4100step0 = (fun i j => raw4100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4100step0 raw4100; decide +kernel
      have hl : raw4100step0Labels = raw4100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4100 raw4100Labels permutation434 hz
    mixedMoment B raw4100step0 raw4100step0Labels = mixedMoment B raw4100step1 raw4100step1Labels := by
      have hz : ∀ j, raw4100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4100step1 = (fun i j => raw4100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4100step1 raw4100step0; decide +kernel
      have hl : raw4100step1Labels = raw4100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4100step0 raw4100step0Labels permutation80 hz
    mixedMoment B raw4100step1 raw4100step1Labels = mixedMoment B raw4100step2 raw4100step2Labels := by
      have ha : raw4100step2 = (fun i j => raw4100step1 (permutation20 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4100step2 raw4100step1; decide +kernel
      have hl : raw4100step2Labels = raw4100step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4100step1 raw4100step1Labels permutation20 permutation2
    mixedMoment B raw4100step2 raw4100step2Labels = mixedMoment B raw4100step3 raw4100step3Labels := by
      have ha : raw4100step3 = -raw4100step2 := by apply Matrix.ext; change ∀ i j, raw4100step3 i j = -(raw4100step2 i j); unfold raw4100step3 raw4100step2; decide +kernel
      have hl : raw4100step3Labels = raw4100step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3160 node3160Labels := by rfl

theorem canonical4101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4101 raw4101Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw4101 raw4101Labels = mixedMoment B raw4101step0 raw4101step0Labels := by
      have hz : ∀ j, raw4101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4101step0 = (fun i j => raw4101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4101step0 raw4101; decide +kernel
      have hl : raw4101step0Labels = raw4101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4101 raw4101Labels permutation434 hz
    mixedMoment B raw4101step0 raw4101step0Labels = mixedMoment B raw4101step1 raw4101step1Labels := by
      have hz : ∀ j, raw4101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4101step1 = (fun i j => raw4101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4101step1 raw4101step0; decide +kernel
      have hl : raw4101step1Labels = raw4101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4101step0 raw4101step0Labels permutation80 hz
    mixedMoment B raw4101step1 raw4101step1Labels = mixedMoment B raw4101step2 raw4101step2Labels := by
      have ha : raw4101step2 = (fun i j => raw4101step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4101step2 raw4101step1; decide +kernel
      have hl : raw4101step2Labels = raw4101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4101step1 raw4101step1Labels permutation31 permutation4
    _ = mixedMoment B node3396 node3396Labels := by rfl

theorem canonical4102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4102 raw4102Labels = mixedMoment B node3495 node3495Labels := by
  calc
    mixedMoment B raw4102 raw4102Labels = mixedMoment B raw4102step0 raw4102step0Labels := by
      have ha : raw4102step0 = (fun i j => raw4102 (permutation613 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4102step0 raw4102; decide +kernel
      have hl : raw4102step0Labels = raw4102Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4102 raw4102Labels permutation613 permutation2
    _ = mixedMoment B node3495 node3495Labels := by rfl

theorem canonical4103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4103 raw4103Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4103 raw4103Labels = mixedMoment B raw4103step0 raw4103step0Labels := by
      have hz : ∀ j, raw4103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4103step0 = (fun i j => raw4103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4103step0 raw4103; decide +kernel
      have hl : raw4103step0Labels = raw4103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4103 raw4103Labels permutation434 hz
    mixedMoment B raw4103step0 raw4103step0Labels = mixedMoment B raw4103step1 raw4103step1Labels := by
      have ha : raw4103step1 = (fun i j => raw4103step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4103step1 raw4103step0; decide +kernel
      have hl : raw4103step1Labels = raw4103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4103step0 raw4103step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

theorem canonical4104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4104 raw4104Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw4104 raw4104Labels = mixedMoment B raw4104step0 raw4104step0Labels := by
      have hz : ∀ j, raw4104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4104step0 = (fun i j => raw4104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4104step0 raw4104; decide +kernel
      have hl : raw4104step0Labels = raw4104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4104 raw4104Labels permutation434 hz
    mixedMoment B raw4104step0 raw4104step0Labels = mixedMoment B raw4104step1 raw4104step1Labels := by
      have ha : raw4104step1 = (fun i j => raw4104step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4104step1 raw4104step0; decide +kernel
      have hl : raw4104step1Labels = raw4104step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4104step0 raw4104step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

theorem canonical4105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4105 raw4105Labels = mixedMoment B node3495 node3495Labels := by
  calc
    mixedMoment B raw4105 raw4105Labels = mixedMoment B raw4105step0 raw4105step0Labels := by
      have ha : raw4105step0 = (fun i j => raw4105 (permutation608 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4105step0 raw4105; decide +kernel
      have hl : raw4105step0Labels = raw4105Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4105 raw4105Labels permutation608 permutation2
    _ = mixedMoment B node3495 node3495Labels := by rfl

theorem canonical4106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4106 raw4106Labels = mixedMoment B node3154 node3154Labels := by
  calc
    mixedMoment B raw4106 raw4106Labels = mixedMoment B raw4106step0 raw4106step0Labels := by
      have hz : ∀ j, raw4106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4106step0 = (fun i j => raw4106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4106step0 raw4106; decide +kernel
      have hl : raw4106step0Labels = raw4106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4106 raw4106Labels permutation434 hz
    mixedMoment B raw4106step0 raw4106step0Labels = mixedMoment B raw4106step1 raw4106step1Labels := by
      have ha : raw4106step1 = (fun i j => raw4106step0 (permutation104 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4106step1 raw4106step0; decide +kernel
      have hl : raw4106step1Labels = raw4106step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4106step0 raw4106step0Labels permutation104 permutation2
    mixedMoment B raw4106step1 raw4106step1Labels = mixedMoment B raw4106step2 raw4106step2Labels := by
      have ha : raw4106step2 = -raw4106step1 := by apply Matrix.ext; change ∀ i j, raw4106step2 i j = -(raw4106step1 i j); unfold raw4106step2 raw4106step1; decide +kernel
      have hl : raw4106step2Labels = raw4106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3154 node3154Labels := by rfl

theorem canonical4107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4107 raw4107Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4107 raw4107Labels = mixedMoment B raw4107step0 raw4107step0Labels := by
      have hz : ∀ j, raw4107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4107step0 = (fun i j => raw4107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4107step0 raw4107; decide +kernel
      have hl : raw4107step0Labels = raw4107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4107 raw4107Labels permutation434 hz
    mixedMoment B raw4107step0 raw4107step0Labels = mixedMoment B raw4107step1 raw4107step1Labels := by
      have ha : raw4107step1 = (fun i j => raw4107step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4107step1 raw4107step0; decide +kernel
      have hl : raw4107step1Labels = raw4107step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4107step0 raw4107step0Labels permutation149 permutation4
    _ = mixedMoment B node3389 node3389Labels := by rfl

theorem canonical4108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4108 raw4108Labels = mixedMoment B node3154 node3154Labels := by
  calc
    mixedMoment B raw4108 raw4108Labels = mixedMoment B raw4108step0 raw4108step0Labels := by
      have hz : ∀ j, raw4108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4108step0 = (fun i j => raw4108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4108step0 raw4108; decide +kernel
      have hl : raw4108step0Labels = raw4108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4108 raw4108Labels permutation346 hz
    mixedMoment B raw4108step0 raw4108step0Labels = mixedMoment B raw4108step1 raw4108step1Labels := by
      have ha : raw4108step1 = (fun i j => raw4108step0 (permutation104 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4108step1 raw4108step0; decide +kernel
      have hl : raw4108step1Labels = raw4108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4108step0 raw4108step0Labels permutation104 permutation2
    mixedMoment B raw4108step1 raw4108step1Labels = mixedMoment B raw4108step2 raw4108step2Labels := by
      have ha : raw4108step2 = -raw4108step1 := by apply Matrix.ext; change ∀ i j, raw4108step2 i j = -(raw4108step1 i j); unfold raw4108step2 raw4108step1; decide +kernel
      have hl : raw4108step2Labels = raw4108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3154 node3154Labels := by rfl

theorem canonical4109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4109 raw4109Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw4109 raw4109Labels = mixedMoment B raw4109step0 raw4109step0Labels := by
      have hz : ∀ j, raw4109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4109step0 = (fun i j => raw4109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4109step0 raw4109; decide +kernel
      have hl : raw4109step0Labels = raw4109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4109 raw4109Labels permutation434 hz
    mixedMoment B raw4109step0 raw4109step0Labels = mixedMoment B raw4109step1 raw4109step1Labels := by
      have hz : ∀ j, raw4109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4109step1 = (fun i j => raw4109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4109step1 raw4109step0; decide +kernel
      have hl : raw4109step1Labels = raw4109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4109step0 raw4109step0Labels permutation80 hz
    mixedMoment B raw4109step1 raw4109step1Labels = mixedMoment B raw4109step2 raw4109step2Labels := by
      have ha : raw4109step2 = (fun i j => raw4109step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4109step2 raw4109step1; decide +kernel
      have hl : raw4109step2Labels = raw4109step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4109step1 raw4109step1Labels permutation28 permutation2
    _ = mixedMoment B node2063 node2063Labels := by rfl

theorem canonical4200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4200 raw4200Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4200 raw4200Labels = mixedMoment B raw4200step0 raw4200step0Labels := by
      have hz : ∀ j, raw4200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4200step0 = (fun i j => raw4200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4200step0 raw4200; decide +kernel
      have hl : raw4200step0Labels = raw4200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4200 raw4200Labels permutation346 hz
    _ = mixedMoment B node2712 node2712Labels := by rfl

theorem canonical4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4201 raw4201Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw4201 raw4201Labels = mixedMoment B raw4201step0 raw4201step0Labels := by
      have hz : ∀ j, raw4201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4201step0 = (fun i j => raw4201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4201step0 raw4201; decide +kernel
      have hl : raw4201step0Labels = raw4201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4201 raw4201Labels permutation346 hz
    mixedMoment B raw4201step0 raw4201step0Labels = mixedMoment B raw4201step1 raw4201step1Labels := by
      have ha : raw4201step1 = (fun i j => raw4201step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4201step1 raw4201step0; decide +kernel
      have hl : raw4201step1Labels = raw4201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4201step0 raw4201step0Labels permutation145 permutation2
    mixedMoment B raw4201step1 raw4201step1Labels = mixedMoment B raw4201step2 raw4201step2Labels := by
      have ha : raw4201step2 = -raw4201step1 := by apply Matrix.ext; change ∀ i j, raw4201step2 i j = -(raw4201step1 i j); unfold raw4201step2 raw4201step1; decide +kernel
      have hl : raw4201step2Labels = raw4201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4202 raw4202Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw4202 raw4202Labels = mixedMoment B raw4202step0 raw4202step0Labels := by
      have ha : raw4202step0 = (fun i j => raw4202 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4202step0 raw4202; decide +kernel
      have hl : raw4202step0Labels = raw4202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4202 raw4202Labels permutation662 permutation2
    mixedMoment B raw4202step0 raw4202step0Labels = mixedMoment B raw4202step1 raw4202step1Labels := by
      have ha : raw4202step1 = -raw4202step0 := by apply Matrix.ext; change ∀ i j, raw4202step1 i j = -(raw4202step0 i j); unfold raw4202step1 raw4202step0; decide +kernel
      have hl : raw4202step1Labels = raw4202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical4203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4203 raw4203Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw4203 raw4203Labels = mixedMoment B raw4203step0 raw4203step0Labels := by
      have hz : ∀ j, raw4203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4203step0 = (fun i j => raw4203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4203step0 raw4203; decide +kernel
      have hl : raw4203step0Labels = raw4203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4203 raw4203Labels permutation346 hz
    mixedMoment B raw4203step0 raw4203step0Labels = mixedMoment B raw4203step1 raw4203step1Labels := by
      have ha : raw4203step1 = (fun i j => raw4203step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4203step1 raw4203step0; decide +kernel
      have hl : raw4203step1Labels = raw4203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4203step0 raw4203step0Labels permutation149 permutation2
    mixedMoment B raw4203step1 raw4203step1Labels = mixedMoment B raw4203step2 raw4203step2Labels := by
      have ha : raw4203step2 = -raw4203step1 := by apply Matrix.ext; change ∀ i j, raw4203step2 i j = -(raw4203step1 i j); unfold raw4203step2 raw4203step1; decide +kernel
      have hl : raw4203step2Labels = raw4203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4204 raw4204Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw4204 raw4204Labels = mixedMoment B raw4204step0 raw4204step0Labels := by
      have hz : ∀ j, raw4204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4204step0 = (fun i j => raw4204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4204step0 raw4204; decide +kernel
      have hl : raw4204step0Labels = raw4204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4204 raw4204Labels permutation346 hz
    mixedMoment B raw4204step0 raw4204step0Labels = mixedMoment B raw4204step1 raw4204step1Labels := by
      have ha : raw4204step1 = (fun i j => raw4204step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4204step1 raw4204step0; decide +kernel
      have hl : raw4204step1Labels = raw4204step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4204step0 raw4204step0Labels permutation143 permutation2
    mixedMoment B raw4204step1 raw4204step1Labels = mixedMoment B raw4204step2 raw4204step2Labels := by
      have ha : raw4204step2 = -raw4204step1 := by apply Matrix.ext; change ∀ i j, raw4204step2 i j = -(raw4204step1 i j); unfold raw4204step2 raw4204step1; decide +kernel
      have hl : raw4204step2Labels = raw4204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

theorem canonical4205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4205 raw4205Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw4205 raw4205Labels = mixedMoment B raw4205step0 raw4205step0Labels := by
      have hz : ∀ j, raw4205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4205step0 = (fun i j => raw4205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4205step0 raw4205; decide +kernel
      have hl : raw4205step0Labels = raw4205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4205 raw4205Labels permutation346 hz
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical4206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4206 raw4206Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw4206 raw4206Labels = mixedMoment B raw4206step0 raw4206step0Labels := by
      have hz : ∀ j, raw4206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4206step0 = (fun i j => raw4206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4206step0 raw4206; decide +kernel
      have hl : raw4206step0Labels = raw4206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4206 raw4206Labels permutation346 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical4207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4207 raw4207Labels = mixedMoment B node1249 node1249Labels := by
  calc
    mixedMoment B raw4207 raw4207Labels = mixedMoment B raw4207step0 raw4207step0Labels := by
      have hz : ∀ j, raw4207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4207step0 = (fun i j => raw4207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4207step0 raw4207; decide +kernel
      have hl : raw4207step0Labels = raw4207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4207 raw4207Labels permutation346 hz
    mixedMoment B raw4207step0 raw4207step0Labels = mixedMoment B raw4207step1 raw4207step1Labels := by
      have ha : raw4207step1 = (fun i j => raw4207step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4207step1 raw4207step0; decide +kernel
      have hl : raw4207step1Labels = raw4207step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4207step0 raw4207step0Labels permutation40 permutation2
    _ = mixedMoment B node1249 node1249Labels := by rfl

theorem canonical4208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4208 raw4208Labels = mixedMoment B node1206 node1206Labels := by
  calc
    mixedMoment B raw4208 raw4208Labels = mixedMoment B raw4208step0 raw4208step0Labels := by
      have ha : raw4208step0 = (fun i j => raw4208 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4208step0 raw4208; decide +kernel
      have hl : raw4208step0Labels = raw4208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4208 raw4208Labels permutation160 permutation2
    _ = mixedMoment B node1206 node1206Labels := by rfl

theorem canonical4209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4209 raw4209Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4209 raw4209Labels = mixedMoment B raw4209step0 raw4209step0Labels := by
      have hz : ∀ j, raw4209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4209step0 = (fun i j => raw4209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4209step0 raw4209; decide +kernel
      have hl : raw4209step0Labels = raw4209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4209 raw4209Labels permutation346 hz
    mixedMoment B raw4209step0 raw4209step0Labels = mixedMoment B raw4209step1 raw4209step1Labels := by
      have ha : raw4209step1 = (fun i j => raw4209step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4209step1 raw4209step0; decide +kernel
      have hl : raw4209step1Labels = raw4209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4209step0 raw4209step0Labels permutation34 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical4210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4210 raw4210Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4210 raw4210Labels = mixedMoment B raw4210step0 raw4210step0Labels := by
      have hz : ∀ j, raw4210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4210step0 = (fun i j => raw4210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4210step0 raw4210; decide +kernel
      have hl : raw4210step0Labels = raw4210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4210 raw4210Labels permutation346 hz
    _ = mixedMoment B node1217 node1217Labels := by rfl

theorem canonical4211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4211 raw4211Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw4211 raw4211Labels = mixedMoment B raw4211step0 raw4211step0Labels := by
      have hz : ∀ j, raw4211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4211step0 = (fun i j => raw4211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4211step0 raw4211; decide +kernel
      have hl : raw4211step0Labels = raw4211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4211 raw4211Labels permutation346 hz
    _ = mixedMoment B node1209 node1209Labels := by rfl

theorem canonical4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4212 raw4212Labels = mixedMoment B node2562 node2562Labels := by
  calc
    mixedMoment B raw4212 raw4212Labels = mixedMoment B raw4212step0 raw4212step0Labels := by
      have ha : raw4212step0 = (fun i j => raw4212 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4212step0 raw4212; decide +kernel
      have hl : raw4212step0Labels = raw4212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4212 raw4212Labels permutation184 permutation2
    _ = mixedMoment B node2562 node2562Labels := by rfl

theorem canonical4213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4213 raw4213Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw4213 raw4213Labels = mixedMoment B raw4213step0 raw4213step0Labels := by
      have hz : ∀ j, raw4213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4213step0 = (fun i j => raw4213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4213step0 raw4213; decide +kernel
      have hl : raw4213step0Labels = raw4213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4213 raw4213Labels permutation346 hz
    mixedMoment B raw4213step0 raw4213step0Labels = mixedMoment B raw4213step1 raw4213step1Labels := by
      have ha : raw4213step1 = (fun i j => raw4213step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4213step1 raw4213step0; decide +kernel
      have hl : raw4213step1Labels = raw4213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4213step0 raw4213step0Labels permutation40 permutation2
    _ = mixedMoment B node2624 node2624Labels := by rfl

theorem canonical4214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4214 raw4214Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw4214 raw4214Labels = mixedMoment B raw4214step0 raw4214step0Labels := by
      have hz : ∀ j, raw4214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4214step0 = (fun i j => raw4214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4214step0 raw4214; decide +kernel
      have hl : raw4214step0Labels = raw4214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4214 raw4214Labels permutation346 hz
    mixedMoment B raw4214step0 raw4214step0Labels = mixedMoment B raw4214step1 raw4214step1Labels := by
      have ha : raw4214step1 = (fun i j => raw4214step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4214step1 raw4214step0; decide +kernel
      have hl : raw4214step1Labels = raw4214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4214step0 raw4214step0Labels permutation46 permutation2
    _ = mixedMoment B node2624 node2624Labels := by rfl

theorem canonical4215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4215 raw4215Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw4215 raw4215Labels = mixedMoment B raw4215step0 raw4215step0Labels := by
      have hz : ∀ j, raw4215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4215step0 = (fun i j => raw4215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4215step0 raw4215; decide +kernel
      have hl : raw4215step0Labels = raw4215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4215 raw4215Labels permutation346 hz
    mixedMoment B raw4215step0 raw4215step0Labels = mixedMoment B raw4215step1 raw4215step1Labels := by
      have ha : raw4215step1 = (fun i j => raw4215step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4215step1 raw4215step0; decide +kernel
      have hl : raw4215step1Labels = raw4215step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4215step0 raw4215step0Labels permutation40 permutation2
    _ = mixedMoment B node2751 node2751Labels := by rfl

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

theorem sound2294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2294 node2294Labels = Sparse.eval nodeValue2294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2294) = mixedMoment B node2294 node2294Labels := rfl
  simpa [nodeValue2294, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1206 node1206Labels = Sparse.eval nodeValue1206 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1206) = mixedMoment B node1206 node1206Labels := rfl
  simpa [nodeValue1206, Sparse.eval] using hc.symm

theorem sound1209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1209 node1209Labels = Sparse.eval nodeValue1209 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1209) = mixedMoment B node1209 node1209Labels := rfl
  simpa [nodeValue1209, Sparse.eval] using hc.symm

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

theorem sound1217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1217 node1217Labels = Sparse.eval nodeValue1217 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1217) = mixedMoment B node1217 node1217Labels := rfl
  simpa [nodeValue1217, Sparse.eval] using hc.symm

theorem sound1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1224 node1224Labels = Sparse.eval nodeValue1224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1224) = mixedMoment B node1224 node1224Labels := rfl
  simpa [nodeValue1224, Sparse.eval] using hc.symm

theorem sound1227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1227 node1227Labels = Sparse.eval nodeValue1227 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1227) = mixedMoment B node1227 node1227Labels := rfl
  simpa [nodeValue1227, Sparse.eval] using hc.symm

theorem sound1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1243 node1243Labels = Sparse.eval nodeValue1243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1243) = mixedMoment B node1243 node1243Labels := rfl
  simpa [nodeValue1243, Sparse.eval] using hc.symm

theorem sound1249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1249 node1249Labels = Sparse.eval nodeValue1249 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1249) = mixedMoment B node1249 node1249Labels := rfl
  simpa [nodeValue1249, Sparse.eval] using hc.symm

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

theorem sound1359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1359 node1359Labels = Sparse.eval nodeValue1359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1359) = mixedMoment B node1359 node1359Labels := rfl
  simpa [nodeValue1359, Sparse.eval] using hc.symm

theorem sound1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1372 node1372Labels = Sparse.eval nodeValue1372 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1372) = mixedMoment B node1372 node1372Labels := rfl
  simpa [nodeValue1372, Sparse.eval] using hc.symm

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

theorem sound1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1424 node1424Labels = Sparse.eval nodeValue1424 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1424) = mixedMoment B node1424 node1424Labels := rfl
  simpa [nodeValue1424, Sparse.eval] using hc.symm

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

theorem sound2055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2055 node2055Labels = Sparse.eval nodeValue2055 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2055) = mixedMoment B node2055 node2055Labels := rfl
  simpa [nodeValue2055, Sparse.eval] using hc.symm

theorem sound2063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2063 node2063Labels = Sparse.eval nodeValue2063 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2063) = mixedMoment B node2063 node2063Labels := rfl
  simpa [nodeValue2063, Sparse.eval] using hc.symm

theorem sound2065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2065 node2065Labels = Sparse.eval nodeValue2065 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2065) = mixedMoment B node2065 node2065Labels := rfl
  simpa [nodeValue2065, Sparse.eval] using hc.symm

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

theorem sound2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2495 node2495Labels = Sparse.eval nodeValue2495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2495) = mixedMoment B node2495 node2495Labels := rfl
  simpa [nodeValue2495, Sparse.eval] using hc.symm

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

theorem sound2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2519 node2519Labels = Sparse.eval nodeValue2519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2519) = mixedMoment B node2519 node2519Labels := rfl
  simpa [nodeValue2519, Sparse.eval] using hc.symm

theorem sound2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2547 node2547Labels = Sparse.eval nodeValue2547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2547) = mixedMoment B node2547 node2547Labels := rfl
  simpa [nodeValue2547, Sparse.eval] using hc.symm

theorem sound2558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2558 node2558Labels = Sparse.eval nodeValue2558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2558) = mixedMoment B node2558 node2558Labels := rfl
  simpa [nodeValue2558, Sparse.eval] using hc.symm

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

theorem sound2562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2562 node2562Labels = Sparse.eval nodeValue2562 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2562) = mixedMoment B node2562 node2562Labels := rfl
  simpa [nodeValue2562, Sparse.eval] using hc.symm

theorem sound2579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2579 node2579Labels = Sparse.eval nodeValue2579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2579) = mixedMoment B node2579 node2579Labels := rfl
  simpa [nodeValue2579, Sparse.eval] using hc.symm

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

theorem sound2647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2647 node2647Labels = Sparse.eval nodeValue2647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2647) = mixedMoment B node2647 node2647Labels := rfl
  simpa [nodeValue2647, Sparse.eval] using hc.symm

theorem sound2651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2651 node2651Labels = Sparse.eval nodeValue2651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2651) = mixedMoment B node2651 node2651Labels := rfl
  simpa [nodeValue2651, Sparse.eval] using hc.symm

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

theorem sound2712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2712 node2712Labels = Sparse.eval nodeValue2712 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2712) = mixedMoment B node2712 node2712Labels := rfl
  simpa [nodeValue2712, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2734 node2734Labels = Sparse.eval nodeValue2734 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2734) = mixedMoment B node2734 node2734Labels := rfl
  simpa [nodeValue2734, Sparse.eval] using hc.symm

theorem sound2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2743 node2743Labels = Sparse.eval nodeValue2743 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2743) = mixedMoment B node2743 node2743Labels := rfl
  simpa [nodeValue2743, Sparse.eval] using hc.symm

theorem sound2751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2751 node2751Labels = Sparse.eval nodeValue2751 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2751) = mixedMoment B node2751 node2751Labels := rfl
  simpa [nodeValue2751, Sparse.eval] using hc.symm

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

theorem sound2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2777 node2777Labels = Sparse.eval nodeValue2777 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2777) = mixedMoment B node2777 node2777Labels := rfl
  simpa [nodeValue2777, Sparse.eval] using hc.symm

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

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

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

theorem sound3086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3086 node3086Labels = Sparse.eval nodeValue3086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3086) = mixedMoment B node3086 node3086Labels := rfl
  simpa [nodeValue3086, Sparse.eval] using hc.symm

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

theorem sound3154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3154 node3154Labels = Sparse.eval nodeValue3154 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3154) = mixedMoment B node3154 node3154Labels := rfl
  simpa [nodeValue3154, Sparse.eval] using hc.symm

theorem sound3160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3160 node3160Labels = Sparse.eval nodeValue3160 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3160) = mixedMoment B node3160 node3160Labels := rfl
  simpa [nodeValue3160, Sparse.eval] using hc.symm

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

theorem sound3389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3389 node3389Labels = Sparse.eval nodeValue3389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3389) = mixedMoment B node3389 node3389Labels := rfl
  simpa [nodeValue3389, Sparse.eval] using hc.symm

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

theorem sound3393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3393 node3393Labels = Sparse.eval nodeValue3393 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3393) = mixedMoment B node3393 node3393Labels := rfl
  simpa [nodeValue3393, Sparse.eval] using hc.symm

theorem sound3396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3396 node3396Labels = Sparse.eval nodeValue3396 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3396) = mixedMoment B node3396 node3396Labels := rfl
  simpa [nodeValue3396, Sparse.eval] using hc.symm

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

theorem sound3495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3495 node3495Labels = Sparse.eval nodeValue3495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3495) = mixedMoment B node3495 node3495Labels := rfl
  simpa [nodeValue3495, Sparse.eval] using hc.symm

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

theorem sound3543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3543 node3543Labels = Sparse.eval nodeValue3543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3543) = mixedMoment B node3543 node3543Labels := rfl
  simpa [nodeValue3543, Sparse.eval] using hc.symm

theorem sound3545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3545 node3545Labels = Sparse.eval nodeValue3545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3545) = mixedMoment B node3545 node3545Labels := rfl
  simpa [nodeValue3545, Sparse.eval] using hc.symm

theorem sound3549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3549 node3549Labels = Sparse.eval nodeValue3549 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3549) = mixedMoment B node3549 node3549Labels := rfl
  simpa [nodeValue3549, Sparse.eval] using hc.symm

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

theorem sound3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3634 node3634Labels = Sparse.eval nodeValue3634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3634) = mixedMoment B node3634 node3634Labels := rfl
  simpa [nodeValue3634, Sparse.eval] using hc.symm

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

theorem sound3902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3902 node3902Labels = Sparse.eval nodeValue3902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3902) = mixedMoment B node3902 node3902Labels := rfl
  simpa [nodeValue3902, Sparse.eval] using hc.symm

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

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources2
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq78 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm78 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA78 + difference 2 0) (sourceB78 + difference 0 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA78 + difference 2 0) (sourceB78 + difference 0 2) sourceC78) = raw4010 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4010; decide +kernel
    rw [ha]
    exact (canonical4010 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA78 + difference 2 1) (sourceB78 + difference 1 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA78 + difference 2 1) (sourceB78 + difference 1 2) sourceC78) = raw4018 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4018; decide +kernel
    rw [ha]
    exact (canonical4018 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA78 + difference 2 2) (sourceB78 + difference 2 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA78 + difference 2 2) (sourceB78 + difference 2 2) sourceC78) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA78 + difference 2 3) (sourceB78 + difference 3 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA78 + difference 2 3) (sourceB78 + difference 3 2) sourceC78) = raw4022 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4022; decide +kernel
    rw [ha]
    exact (canonical4022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA78 + difference 2 4) (sourceB78 + difference 4 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA78 + difference 2 4) (sourceB78 + difference 4 2) sourceC78) = raw4023 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4023; decide +kernel
    rw [ha]
    exact (canonical4023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA78 + difference 2 5) (sourceB78 + difference 5 2) sourceC78) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA78 + difference 2 5) (sourceB78 + difference 5 2) sourceC78) = raw4024 := by
      apply Matrix.ext; unfold tripleCharges sourceA78 sourceB78 sourceC78 difference raw4024; decide +kernel
    rw [ha]
    exact (canonical4024 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA78 + sourceB78) sourceC78) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA78 + sourceB78) sourceC78) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA78 sourceB78 sourceC78 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA78 sourceB78 sourceC78
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm78, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq79 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm79 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA79 + difference 0 2) (sourceB79 + difference 2 0) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA79 + difference 0 2) (sourceB79 + difference 2 0) sourceC79) = raw4004 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4004; decide +kernel
    rw [ha]
    exact (canonical4004 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA79 + difference 1 2) (sourceB79 + difference 2 1) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA79 + difference 1 2) (sourceB79 + difference 2 1) sourceC79) = raw4014 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4014; decide +kernel
    rw [ha]
    exact (canonical4014 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA79 + difference 2 2) (sourceB79 + difference 2 2) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA79 + difference 2 2) (sourceB79 + difference 2 2) sourceC79) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA79 + difference 3 2) (sourceB79 + difference 2 3) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA79 + difference 3 2) (sourceB79 + difference 2 3) sourceC79) = raw4025 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4025; decide +kernel
    rw [ha]
    exact (canonical4025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA79 + difference 4 2) (sourceB79 + difference 2 4) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA79 + difference 4 2) (sourceB79 + difference 2 4) sourceC79) = raw4026 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4026; decide +kernel
    rw [ha]
    exact (canonical4026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA79 + difference 5 2) (sourceB79 + difference 2 5) sourceC79) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA79 + difference 5 2) (sourceB79 + difference 2 5) sourceC79) = raw4027 := by
      apply Matrix.ext; unfold tripleCharges sourceA79 sourceB79 sourceC79 difference raw4027; decide +kernel
    rw [ha]
    exact (canonical4027 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA79 + sourceB79) sourceC79) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA79 + sourceB79) sourceC79) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA79 sourceB79 sourceC79 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA79 sourceB79 sourceC79
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm79, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq80 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm80 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA80 + difference 4 0) (sourceB80 + difference 0 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA80 + difference 4 0) (sourceB80 + difference 0 4) sourceC80) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA80 + difference 4 1) (sourceB80 + difference 1 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA80 + difference 4 1) (sourceB80 + difference 1 4) sourceC80) = raw4020 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4020; decide +kernel
    rw [ha]
    exact (canonical4020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA80 + difference 4 2) (sourceB80 + difference 2 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA80 + difference 4 2) (sourceB80 + difference 2 4) sourceC80) = raw4026 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4026; decide +kernel
    rw [ha]
    exact (canonical4026 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA80 + difference 4 3) (sourceB80 + difference 3 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA80 + difference 4 3) (sourceB80 + difference 3 4) sourceC80) = raw4028 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4028; decide +kernel
    rw [ha]
    exact (canonical4028 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA80 + difference 4 4) (sourceB80 + difference 4 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA80 + difference 4 4) (sourceB80 + difference 4 4) sourceC80) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA80 + difference 4 5) (sourceB80 + difference 5 4) sourceC80) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA80 + difference 4 5) (sourceB80 + difference 5 4) sourceC80) = raw4029 := by
      apply Matrix.ext; unfold tripleCharges sourceA80 sourceB80 sourceC80 difference raw4029; decide +kernel
    rw [ha]
    exact (canonical4029 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA80 + sourceB80) sourceC80) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA80 + sourceB80) sourceC80) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA80 sourceB80 sourceC80 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA80 sourceB80 sourceC80
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm80, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq81 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm81 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA81 + difference 0 4) (sourceB81 + difference 4 0) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2777) := by
    have ha : (tripleCharges (sourceA81 + difference 0 4) (sourceB81 + difference 4 0) sourceC81) = raw4006 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4006; decide +kernel
    rw [ha]
    exact (canonical4006 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA81 + difference 1 4) (sourceB81 + difference 4 1) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2651) := by
    have ha : (tripleCharges (sourceA81 + difference 1 4) (sourceB81 + difference 4 1) sourceC81) = raw4016 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4016; decide +kernel
    rw [ha]
    exact (canonical4016 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA81 + difference 2 4) (sourceB81 + difference 4 2) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA81 + difference 2 4) (sourceB81 + difference 4 2) sourceC81) = raw4023 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4023; decide +kernel
    rw [ha]
    exact (canonical4023 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA81 + difference 3 4) (sourceB81 + difference 4 3) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA81 + difference 3 4) (sourceB81 + difference 4 3) sourceC81) = raw4030 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4030; decide +kernel
    rw [ha]
    exact (canonical4030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA81 + difference 4 4) (sourceB81 + difference 4 4) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA81 + difference 4 4) (sourceB81 + difference 4 4) sourceC81) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA81 + difference 5 4) (sourceB81 + difference 4 5) sourceC81) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1424) := by
    have ha : (tripleCharges (sourceA81 + difference 5 4) (sourceB81 + difference 4 5) sourceC81) = raw4031 := by
      apply Matrix.ext; unfold tripleCharges sourceA81 sourceB81 sourceC81 difference raw4031; decide +kernel
    rw [ha]
    exact (canonical4031 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA81 + sourceB81) sourceC81) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA81 + sourceB81) sourceC81) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA81 sourceB81 sourceC81 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA81 sourceB81 sourceC81
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm81, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq82 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm82 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA82 + difference 5 0) (sourceB82 + difference 0 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1227) := by
    have ha : (tripleCharges (sourceA82 + difference 5 0) (sourceB82 + difference 0 5) sourceC82) = raw4013 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4013; decide +kernel
    rw [ha]
    exact (canonical4013 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA82 + difference 5 1) (sourceB82 + difference 1 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA82 + difference 5 1) (sourceB82 + difference 1 5) sourceC82) = raw4021 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4021; decide +kernel
    rw [ha]
    exact (canonical4021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA82 + difference 5 2) (sourceB82 + difference 2 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA82 + difference 5 2) (sourceB82 + difference 2 5) sourceC82) = raw4027 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4027; decide +kernel
    rw [ha]
    exact (canonical4027 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA82 + difference 5 3) (sourceB82 + difference 3 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA82 + difference 5 3) (sourceB82 + difference 3 5) sourceC82) = raw4032 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4032; decide +kernel
    rw [ha]
    exact (canonical4032 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA82 + difference 5 4) (sourceB82 + difference 4 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1424) := by
    have ha : (tripleCharges (sourceA82 + difference 5 4) (sourceB82 + difference 4 5) sourceC82) = raw4031 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4031; decide +kernel
    rw [ha]
    exact (canonical4031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA82 + difference 5 5) (sourceB82 + difference 5 5) sourceC82) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2734) := by
    have ha : (tripleCharges (sourceA82 + difference 5 5) (sourceB82 + difference 5 5) sourceC82) = raw4002 := by
      apply Matrix.ext; unfold tripleCharges sourceA82 sourceB82 sourceC82 difference raw4002; decide +kernel
    rw [ha]
    exact (canonical4002 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA82 + sourceB82) sourceC82) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA82 + sourceB82) sourceC82) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA82 sourceB82 sourceC82 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA82 sourceB82 sourceC82
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm82, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq85 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm85 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA85 + difference 0 0) (sourceB85 + difference 0 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA85 + difference 0 0) (sourceB85 + difference 0 0) sourceC85) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA85 + difference 0 1) (sourceB85 + difference 1 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA85 + difference 0 1) (sourceB85 + difference 1 0) sourceC85) = raw4086 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4086; decide +kernel
    rw [ha]
    exact (canonical4086 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA85 + difference 0 2) (sourceB85 + difference 2 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA85 + difference 0 2) (sourceB85 + difference 2 0) sourceC85) = raw4087 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4087; decide +kernel
    rw [ha]
    exact (canonical4087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA85 + difference 0 3) (sourceB85 + difference 3 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA85 + difference 0 3) (sourceB85 + difference 3 0) sourceC85) = raw4088 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4088; decide +kernel
    rw [ha]
    exact (canonical4088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA85 + difference 0 4) (sourceB85 + difference 4 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3545) := by
    have ha : (tripleCharges (sourceA85 + difference 0 4) (sourceB85 + difference 4 0) sourceC85) = raw4089 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4089; decide +kernel
    rw [ha]
    exact (canonical4089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA85 + difference 0 5) (sourceB85 + difference 5 0) sourceC85) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA85 + difference 0 5) (sourceB85 + difference 5 0) sourceC85) = raw4090 := by
      apply Matrix.ext; unfold tripleCharges sourceA85 sourceB85 sourceC85 difference raw4090; decide +kernel
    rw [ha]
    exact (canonical4090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA85 + sourceB85) sourceC85) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA85 + sourceB85) sourceC85) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA85 sourceB85 sourceC85 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA85 sourceB85 sourceC85
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm85, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq86 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm86 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA86 + difference 0 0) (sourceB86 + difference 0 0) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA86 + difference 0 0) (sourceB86 + difference 0 0) sourceC86) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA86 + difference 1 0) (sourceB86 + difference 0 1) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA86 + difference 1 0) (sourceB86 + difference 0 1) sourceC86) = raw4091 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4091; decide +kernel
    rw [ha]
    exact (canonical4091 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA86 + difference 2 0) (sourceB86 + difference 0 2) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA86 + difference 2 0) (sourceB86 + difference 0 2) sourceC86) = raw4092 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4092; decide +kernel
    rw [ha]
    exact (canonical4092 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA86 + difference 3 0) (sourceB86 + difference 0 3) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA86 + difference 3 0) (sourceB86 + difference 0 3) sourceC86) = raw3734 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw3734; decide +kernel
    rw [ha]
    exact (canonical3734 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA86 + difference 4 0) (sourceB86 + difference 0 4) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA86 + difference 4 0) (sourceB86 + difference 0 4) sourceC86) = raw4093 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4093; decide +kernel
    rw [ha]
    exact (canonical4093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA86 + difference 5 0) (sourceB86 + difference 0 5) sourceC86) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2065) := by
    have ha : (tripleCharges (sourceA86 + difference 5 0) (sourceB86 + difference 0 5) sourceC86) = raw4094 := by
      apply Matrix.ext; unfold tripleCharges sourceA86 sourceB86 sourceC86 difference raw4094; decide +kernel
    rw [ha]
    exact (canonical4094 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA86 + sourceB86) sourceC86) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA86 + sourceB86) sourceC86) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA86 sourceB86 sourceC86 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA86 sourceB86 sourceC86
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm86, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq87 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm87 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA87 + difference 1 0) (sourceB87 + difference 0 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA87 + difference 1 0) (sourceB87 + difference 0 1) sourceC87) = raw4091 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4091; decide +kernel
    rw [ha]
    exact (canonical4091 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA87 + difference 1 1) (sourceB87 + difference 1 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA87 + difference 1 1) (sourceB87 + difference 1 1) sourceC87) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA87 + difference 1 2) (sourceB87 + difference 2 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA87 + difference 1 2) (sourceB87 + difference 2 1) sourceC87) = raw4095 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4095; decide +kernel
    rw [ha]
    exact (canonical4095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA87 + difference 1 3) (sourceB87 + difference 3 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA87 + difference 1 3) (sourceB87 + difference 3 1) sourceC87) = raw4096 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4096; decide +kernel
    rw [ha]
    exact (canonical4096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA87 + difference 1 4) (sourceB87 + difference 4 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3634) := by
    have ha : (tripleCharges (sourceA87 + difference 1 4) (sourceB87 + difference 4 1) sourceC87) = raw4097 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw4097; decide +kernel
    rw [ha]
    exact (canonical4097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA87 + difference 1 5) (sourceB87 + difference 5 1) sourceC87) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2294) := by
    have ha : (tripleCharges (sourceA87 + difference 1 5) (sourceB87 + difference 5 1) sourceC87) = raw3718 := by
      apply Matrix.ext; unfold tripleCharges sourceA87 sourceB87 sourceC87 difference raw3718; decide +kernel
    rw [ha]
    exact (canonical3718 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA87 + sourceB87) sourceC87) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA87 + sourceB87) sourceC87) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA87 sourceB87 sourceC87 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA87 sourceB87 sourceC87
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm87, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq88 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm88 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA88 + difference 0 1) (sourceB88 + difference 1 0) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA88 + difference 0 1) (sourceB88 + difference 1 0) sourceC88) = raw4086 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4086; decide +kernel
    rw [ha]
    exact (canonical4086 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA88 + difference 1 1) (sourceB88 + difference 1 1) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA88 + difference 1 1) (sourceB88 + difference 1 1) sourceC88) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA88 + difference 2 1) (sourceB88 + difference 1 2) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA88 + difference 2 1) (sourceB88 + difference 1 2) sourceC88) = raw4098 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4098; decide +kernel
    rw [ha]
    exact (canonical4098 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA88 + difference 3 1) (sourceB88 + difference 1 3) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA88 + difference 3 1) (sourceB88 + difference 1 3) sourceC88) = raw4099 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4099; decide +kernel
    rw [ha]
    exact (canonical4099 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA88 + difference 4 1) (sourceB88 + difference 1 4) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3160) := by
    have ha : (tripleCharges (sourceA88 + difference 4 1) (sourceB88 + difference 1 4) sourceC88) = raw4100 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4100; decide +kernel
    rw [ha]
    exact (canonical4100 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA88 + difference 5 1) (sourceB88 + difference 1 5) sourceC88) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3396) := by
    have ha : (tripleCharges (sourceA88 + difference 5 1) (sourceB88 + difference 1 5) sourceC88) = raw4101 := by
      apply Matrix.ext; unfold tripleCharges sourceA88 sourceB88 sourceC88 difference raw4101; decide +kernel
    rw [ha]
    exact (canonical4101 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA88 + sourceB88) sourceC88) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA88 + sourceB88) sourceC88) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA88 sourceB88 sourceC88 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA88 sourceB88 sourceC88
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm88, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq89 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm89 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA89 + difference 2 0) (sourceB89 + difference 0 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA89 + difference 2 0) (sourceB89 + difference 0 2) sourceC89) = raw4092 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4092; decide +kernel
    rw [ha]
    exact (canonical4092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA89 + difference 2 1) (sourceB89 + difference 1 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3393) := by
    have ha : (tripleCharges (sourceA89 + difference 2 1) (sourceB89 + difference 1 2) sourceC89) = raw4098 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4098; decide +kernel
    rw [ha]
    exact (canonical4098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA89 + difference 2 2) (sourceB89 + difference 2 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA89 + difference 2 2) (sourceB89 + difference 2 2) sourceC89) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA89 + difference 2 3) (sourceB89 + difference 3 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3495) := by
    have ha : (tripleCharges (sourceA89 + difference 2 3) (sourceB89 + difference 3 2) sourceC89) = raw4102 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4102; decide +kernel
    rw [ha]
    exact (canonical4102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA89 + difference 2 4) (sourceB89 + difference 4 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3543) := by
    have ha : (tripleCharges (sourceA89 + difference 2 4) (sourceB89 + difference 4 2) sourceC89) = raw4103 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4103; decide +kernel
    rw [ha]
    exact (canonical4103 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA89 + difference 2 5) (sourceB89 + difference 5 2) sourceC89) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2055) := by
    have ha : (tripleCharges (sourceA89 + difference 2 5) (sourceB89 + difference 5 2) sourceC89) = raw4104 := by
      apply Matrix.ext; unfold tripleCharges sourceA89 sourceB89 sourceC89 difference raw4104; decide +kernel
    rw [ha]
    exact (canonical4104 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA89 + sourceB89) sourceC89) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA89 + sourceB89) sourceC89) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA89 sourceB89 sourceC89 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA89 sourceB89 sourceC89
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm89, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq90 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm90 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA90 + difference 0 2) (sourceB90 + difference 2 0) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA90 + difference 0 2) (sourceB90 + difference 2 0) sourceC90) = raw4087 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4087; decide +kernel
    rw [ha]
    exact (canonical4087 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA90 + difference 1 2) (sourceB90 + difference 2 1) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA90 + difference 1 2) (sourceB90 + difference 2 1) sourceC90) = raw4095 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4095; decide +kernel
    rw [ha]
    exact (canonical4095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA90 + difference 2 2) (sourceB90 + difference 2 2) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA90 + difference 2 2) (sourceB90 + difference 2 2) sourceC90) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA90 + difference 3 2) (sourceB90 + difference 2 3) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3495) := by
    have ha : (tripleCharges (sourceA90 + difference 3 2) (sourceB90 + difference 2 3) sourceC90) = raw4105 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4105; decide +kernel
    rw [ha]
    exact (canonical4105 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA90 + difference 4 2) (sourceB90 + difference 2 4) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3154) := by
    have ha : (tripleCharges (sourceA90 + difference 4 2) (sourceB90 + difference 2 4) sourceC90) = raw4106 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4106; decide +kernel
    rw [ha]
    exact (canonical4106 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA90 + difference 5 2) (sourceB90 + difference 2 5) sourceC90) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3389) := by
    have ha : (tripleCharges (sourceA90 + difference 5 2) (sourceB90 + difference 2 5) sourceC90) = raw4107 := by
      apply Matrix.ext; unfold tripleCharges sourceA90 sourceB90 sourceC90 difference raw4107; decide +kernel
    rw [ha]
    exact (canonical4107 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA90 + sourceB90) sourceC90) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA90 + sourceB90) sourceC90) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA90 sourceB90 sourceC90 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA90 sourceB90 sourceC90
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm90, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq91 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm91 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA91 + difference 4 0) (sourceB91 + difference 0 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA91 + difference 4 0) (sourceB91 + difference 0 4) sourceC91) = raw4093 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4093; decide +kernel
    rw [ha]
    exact (canonical4093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA91 + difference 4 1) (sourceB91 + difference 1 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3160) := by
    have ha : (tripleCharges (sourceA91 + difference 4 1) (sourceB91 + difference 1 4) sourceC91) = raw4100 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4100; decide +kernel
    rw [ha]
    exact (canonical4100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA91 + difference 4 2) (sourceB91 + difference 2 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3154) := by
    have ha : (tripleCharges (sourceA91 + difference 4 2) (sourceB91 + difference 2 4) sourceC91) = raw4106 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4106; decide +kernel
    rw [ha]
    exact (canonical4106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA91 + difference 4 3) (sourceB91 + difference 3 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3154) := by
    have ha : (tripleCharges (sourceA91 + difference 4 3) (sourceB91 + difference 3 4) sourceC91) = raw4108 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4108; decide +kernel
    rw [ha]
    exact (canonical4108 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA91 + difference 4 4) (sourceB91 + difference 4 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3549) := by
    have ha : (tripleCharges (sourceA91 + difference 4 4) (sourceB91 + difference 4 4) sourceC91) = raw4085 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4085; decide +kernel
    rw [ha]
    exact (canonical4085 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA91 + difference 4 5) (sourceB91 + difference 5 4) sourceC91) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2063) := by
    have ha : (tripleCharges (sourceA91 + difference 4 5) (sourceB91 + difference 5 4) sourceC91) = raw4109 := by
      apply Matrix.ext; unfold tripleCharges sourceA91 sourceB91 sourceC91 difference raw4109; decide +kernel
    rw [ha]
    exact (canonical4109 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA91 + sourceB91) sourceC91) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA91 + sourceB91) sourceC91) = raw3721 := by
      apply Matrix.ext; unfold doubleCharges sourceA91 sourceB91 sourceC91 raw3721; decide +kernel
    rw [ha]
    exact (canonical3721 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA91 sourceB91 sourceC91
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm91, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq95 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm95 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA95 + difference 0 0) (sourceB95 + difference 0 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA95 + difference 0 0) (sourceB95 + difference 0 0) sourceC95) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA95 + difference 0 1) (sourceB95 + difference 1 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA95 + difference 0 1) (sourceB95 + difference 1 0) sourceC95) = raw4201 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4201; decide +kernel
    rw [ha]
    exact (canonical4201 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA95 + difference 0 2) (sourceB95 + difference 2 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3064) := by
    have ha : (tripleCharges (sourceA95 + difference 0 2) (sourceB95 + difference 2 0) sourceC95) = raw4202 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4202; decide +kernel
    rw [ha]
    exact (canonical4202 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA95 + difference 0 3) (sourceB95 + difference 3 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA95 + difference 0 3) (sourceB95 + difference 3 0) sourceC95) = raw4203 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4203; decide +kernel
    rw [ha]
    exact (canonical4203 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA95 + difference 0 4) (sourceB95 + difference 4 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3086) := by
    have ha : (tripleCharges (sourceA95 + difference 0 4) (sourceB95 + difference 4 0) sourceC95) = raw4204 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4204; decide +kernel
    rw [ha]
    exact (canonical4204 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA95 + difference 0 5) (sourceB95 + difference 5 0) sourceC95) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA95 + difference 0 5) (sourceB95 + difference 5 0) sourceC95) = raw4205 := by
      apply Matrix.ext; unfold tripleCharges sourceA95 sourceB95 sourceC95 difference raw4205; decide +kernel
    rw [ha]
    exact (canonical4205 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA95 + sourceB95) sourceC95) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA95 + sourceB95) sourceC95) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA95 sourceB95 sourceC95 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA95 sourceB95 sourceC95
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm95, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources3
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq96 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm96 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA96 + difference 0 0) (sourceB96 + difference 0 0) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA96 + difference 0 0) (sourceB96 + difference 0 0) sourceC96) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA96 + difference 1 0) (sourceB96 + difference 0 1) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1249) := by
    have ha : (tripleCharges (sourceA96 + difference 1 0) (sourceB96 + difference 0 1) sourceC96) = raw4207 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4207; decide +kernel
    rw [ha]
    exact (canonical4207 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA96 + difference 2 0) (sourceB96 + difference 0 2) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1206) := by
    have ha : (tripleCharges (sourceA96 + difference 2 0) (sourceB96 + difference 0 2) sourceC96) = raw4208 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4208; decide +kernel
    rw [ha]
    exact (canonical4208 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA96 + difference 3 0) (sourceB96 + difference 0 3) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA96 + difference 3 0) (sourceB96 + difference 0 3) sourceC96) = raw4209 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4209; decide +kernel
    rw [ha]
    exact (canonical4209 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA96 + difference 4 0) (sourceB96 + difference 0 4) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1217) := by
    have ha : (tripleCharges (sourceA96 + difference 4 0) (sourceB96 + difference 0 4) sourceC96) = raw4210 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4210; decide +kernel
    rw [ha]
    exact (canonical4210 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA96 + difference 5 0) (sourceB96 + difference 0 5) sourceC96) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1209) := by
    have ha : (tripleCharges (sourceA96 + difference 5 0) (sourceB96 + difference 0 5) sourceC96) = raw4211 := by
      apply Matrix.ext; unfold tripleCharges sourceA96 sourceB96 sourceC96 difference raw4211; decide +kernel
    rw [ha]
    exact (canonical4211 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA96 + sourceB96) sourceC96) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA96 + sourceB96) sourceC96) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA96 sourceB96 sourceC96 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA96 sourceB96 sourceC96
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm96, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq97 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm97 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA97 + difference 1 0) (sourceB97 + difference 0 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1249) := by
    have ha : (tripleCharges (sourceA97 + difference 1 0) (sourceB97 + difference 0 1) sourceC97) = raw4207 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4207; decide +kernel
    rw [ha]
    exact (canonical4207 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA97 + difference 1 1) (sourceB97 + difference 1 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2712) := by
    have ha : (tripleCharges (sourceA97 + difference 1 1) (sourceB97 + difference 1 1) sourceC97) = raw4200 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4200; decide +kernel
    rw [ha]
    exact (canonical4200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA97 + difference 1 2) (sourceB97 + difference 2 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2562) := by
    have ha : (tripleCharges (sourceA97 + difference 1 2) (sourceB97 + difference 2 1) sourceC97) = raw4212 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4212; decide +kernel
    rw [ha]
    exact (canonical4212 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA97 + difference 1 3) (sourceB97 + difference 3 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA97 + difference 1 3) (sourceB97 + difference 3 1) sourceC97) = raw4213 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4213; decide +kernel
    rw [ha]
    exact (canonical4213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA97 + difference 1 4) (sourceB97 + difference 4 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2624) := by
    have ha : (tripleCharges (sourceA97 + difference 1 4) (sourceB97 + difference 4 1) sourceC97) = raw4214 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4214; decide +kernel
    rw [ha]
    exact (canonical4214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA97 + difference 1 5) (sourceB97 + difference 5 1) sourceC97) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2751) := by
    have ha : (tripleCharges (sourceA97 + difference 1 5) (sourceB97 + difference 5 1) sourceC97) = raw4215 := by
      apply Matrix.ext; unfold tripleCharges sourceA97 sourceB97 sourceC97 difference raw4215; decide +kernel
    rw [ha]
    exact (canonical4215 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA97 + sourceB97) sourceC97) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA97 + sourceB97) sourceC97) = raw4206 := by
      apply Matrix.ext; unfold doubleCharges sourceA97 sourceB97 sourceC97 raw4206; decide +kernel
    rw [ha]
    exact (canonical4206 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA97 sourceB97 sourceC97
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm97, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck64 : Integer.Sparse.reindex keyMap MixedData.row64 = numericRow64 := by decide +kernel

theorem numericCheck64 (x : Master → ℝ) : Integer.Sparse.eval numericRow64 x =
    (1 : ℝ) * reducedSource64 x := by
  norm_num [numericRow64, reducedSource64, Integer.Sparse.eval, Sparse.eval, nodeValue1224, nodeValue2495, nodeValue2547, nodeValue2647, nodeValue2731, nodeValue2734, nodeValue4092]

theorem reindexCheck65 : Integer.Sparse.reindex keyMap MixedData.row65 = numericRow65 := by decide +kernel

theorem numericCheck65 (x : Master → ℝ) : Integer.Sparse.eval numericRow65 x =
    (1 : ℝ) * reducedSource65 x := by
  norm_num [numericRow65, reducedSource65, Integer.Sparse.eval, Sparse.eval, nodeValue1359, nodeValue2547, nodeValue2558, nodeValue2579, nodeValue2734, nodeValue3038, nodeValue4092]

theorem reindexCheck66 : Integer.Sparse.reindex keyMap MixedData.row66 = numericRow66 := by decide +kernel

theorem numericCheck66 (x : Master → ℝ) : Integer.Sparse.eval numericRow66 x =
    (1 : ℝ) * reducedSource66 x := by
  norm_num [numericRow66, reducedSource66, Integer.Sparse.eval, Sparse.eval, nodeValue1243, nodeValue2519, nodeValue2558, nodeValue2734, nodeValue2743, nodeValue4092]

theorem reindexCheck67 : Integer.Sparse.reindex keyMap MixedData.row67 = numericRow67 := by decide +kernel

theorem numericCheck67 (x : Master → ℝ) : Integer.Sparse.eval numericRow67 x =
    (1 : ℝ) * reducedSource67 x := by
  norm_num [numericRow67, reducedSource67, Integer.Sparse.eval, Sparse.eval, nodeValue1424, nodeValue2647, nodeValue2651, nodeValue2734, nodeValue2777, nodeValue4092]

theorem reindexCheck68 : Integer.Sparse.reindex keyMap MixedData.row68 = numericRow68 := by decide +kernel

theorem numericCheck68 (x : Master → ℝ) : Integer.Sparse.eval numericRow68 x =
    (1 : ℝ) * reducedSource68 x := by
  norm_num [numericRow68, reducedSource68, Integer.Sparse.eval, Sparse.eval, nodeValue1227, nodeValue1359, nodeValue1372, nodeValue1424, nodeValue2734, nodeValue4092]

theorem reindexCheck69 : Integer.Sparse.reindex keyMap MixedData.row69 = numericRow69 := by decide +kernel

theorem numericCheck69 (x : Master → ℝ) : Integer.Sparse.eval numericRow69 x =
    (1 : ℝ) * reducedSource69 x := by
  norm_num [numericRow69, reducedSource69, Integer.Sparse.eval, Sparse.eval, nodeValue2065, nodeValue3389, nodeValue3396, nodeValue3545, nodeValue3549, nodeValue4085]

theorem reindexCheck70 : Integer.Sparse.reindex keyMap MixedData.row70 = numericRow70 := by decide +kernel

theorem numericCheck70 (x : Master → ℝ) : Integer.Sparse.eval numericRow70 x =
    (1 : ℝ) * reducedSource70 x := by
  norm_num [numericRow70, reducedSource70, Integer.Sparse.eval, Sparse.eval, nodeValue2055, nodeValue2063, nodeValue2065, nodeValue2294, nodeValue3549, nodeValue4085]

theorem reindexCheck71 : Integer.Sparse.reindex keyMap MixedData.row71 = numericRow71 := by decide +kernel

theorem numericCheck71 (x : Master → ℝ) : Integer.Sparse.eval numericRow71 x =
    (1 : ℝ) * reducedSource71 x := by
  norm_num [numericRow71, reducedSource71, Integer.Sparse.eval, Sparse.eval, nodeValue2294, nodeValue3549, nodeValue3634, nodeValue4085]

theorem reindexCheck72 : Integer.Sparse.reindex keyMap MixedData.row72 = numericRow72 := by decide +kernel

theorem numericCheck72 (x : Master → ℝ) : Integer.Sparse.eval numericRow72 x =
    (1 : ℝ) * reducedSource72 x := by
  norm_num [numericRow72, reducedSource72, Integer.Sparse.eval, Sparse.eval, nodeValue3160, nodeValue3393, nodeValue3396, nodeValue3549, nodeValue4085]

theorem reindexCheck73 : Integer.Sparse.reindex keyMap MixedData.row73 = numericRow73 := by decide +kernel

theorem numericCheck73 (x : Master → ℝ) : Integer.Sparse.eval numericRow73 x =
    (1 : ℝ) * reducedSource73 x := by
  norm_num [numericRow73, reducedSource73, Integer.Sparse.eval, Sparse.eval, nodeValue2055, nodeValue3393, nodeValue3495, nodeValue3543, nodeValue3549, nodeValue4085]

theorem reindexCheck74 : Integer.Sparse.reindex keyMap MixedData.row74 = numericRow74 := by decide +kernel

theorem numericCheck74 (x : Master → ℝ) : Integer.Sparse.eval numericRow74 x =
    (1 : ℝ) * reducedSource74 x := by
  norm_num [numericRow74, reducedSource74, Integer.Sparse.eval, Sparse.eval, nodeValue3154, nodeValue3389, nodeValue3495, nodeValue3549, nodeValue4085]

theorem reindexCheck75 : Integer.Sparse.reindex keyMap MixedData.row75 = numericRow75 := by decide +kernel

theorem numericCheck75 (x : Master → ℝ) : Integer.Sparse.eval numericRow75 x =
    (1 : ℝ) * reducedSource75 x := by
  norm_num [numericRow75, reducedSource75, Integer.Sparse.eval, Sparse.eval, nodeValue2063, nodeValue3154, nodeValue3160, nodeValue3549, nodeValue4085]

theorem reindexCheck77 : Integer.Sparse.reindex keyMap MixedData.row77 = numericRow77 := by decide +kernel

theorem numericCheck77 (x : Master → ℝ) : Integer.Sparse.eval numericRow77 x =
    (1 : ℝ) * reducedSource77 x := by
  norm_num [numericRow77, reducedSource77, Integer.Sparse.eval, Sparse.eval, nodeValue2712, nodeValue3064, nodeValue3077, nodeValue3086, nodeValue3902, nodeValue4091]

theorem reindexCheck78 : Integer.Sparse.reindex keyMap MixedData.row78 = numericRow78 := by decide +kernel

theorem numericCheck78 (x : Master → ℝ) : Integer.Sparse.eval numericRow78 x =
    (1 : ℝ) * reducedSource78 x := by
  norm_num [numericRow78, reducedSource78, Integer.Sparse.eval, Sparse.eval, nodeValue1206, nodeValue1209, nodeValue1217, nodeValue1249, nodeValue2712, nodeValue4091]

theorem reindexCheck79 : Integer.Sparse.reindex keyMap MixedData.row79 = numericRow79 := by decide +kernel

theorem numericCheck79 (x : Master → ℝ) : Integer.Sparse.eval numericRow79 x =
    (1 : ℝ) * reducedSource79 x := by
  norm_num [numericRow79, reducedSource79, Integer.Sparse.eval, Sparse.eval, nodeValue1249, nodeValue2562, nodeValue2624, nodeValue2712, nodeValue2751, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource64 (mixedVector B) = 0 := by
  have h1224 : mixedVector B (Sum.inr 1224) = Sparse.eval nodeValue1224 (mixedVector B) := by
    change mixedMoment B node1224 node1224Labels = _
    exact sound1224 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm78, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1224, h2495, h2547, h2647, h2731, h2734, h4092, reducedSource64] using sourceEq78 B hB

theorem rowSound64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row64 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck64, numericCheck64, reducedZero64 B hB hF, mul_zero]

theorem reducedZero65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource65 (mixedVector B) = 0 := by
  have h1359 : mixedVector B (Sum.inr 1359) = Sparse.eval nodeValue1359 (mixedVector B) := by
    change mixedMoment B node1359 node1359Labels = _
    exact sound1359 B hB hF
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2579 : mixedVector B (Sum.inr 2579) = Sparse.eval nodeValue2579 (mixedVector B) := by
    change mixedMoment B node2579 node2579Labels = _
    exact sound2579 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm79, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1359, h2547, h2558, h2579, h2734, h3038, h4092, reducedSource65] using sourceEq79 B hB

theorem rowSound65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row65 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck65, numericCheck65, reducedZero65 B hB hF, mul_zero]

theorem reducedZero66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource66 (mixedVector B) = 0 := by
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm80, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1243, h2519, h2558, h2734, h2743, h4092, reducedSource66] using sourceEq80 B hB

theorem rowSound66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row66 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck66, numericCheck66, reducedZero66 B hB hF, mul_zero]

theorem reducedZero67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource67 (mixedVector B) = 0 := by
  have h1424 : mixedVector B (Sum.inr 1424) = Sparse.eval nodeValue1424 (mixedVector B) := by
    change mixedMoment B node1424 node1424Labels = _
    exact sound1424 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2651 : mixedVector B (Sum.inr 2651) = Sparse.eval nodeValue2651 (mixedVector B) := by
    change mixedMoment B node2651 node2651Labels = _
    exact sound2651 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h2777 : mixedVector B (Sum.inr 2777) = Sparse.eval nodeValue2777 (mixedVector B) := by
    change mixedMoment B node2777 node2777Labels = _
    exact sound2777 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm81, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1424, h2647, h2651, h2734, h2777, h4092, reducedSource67] using sourceEq81 B hB

theorem rowSound67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row67 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck67, numericCheck67, reducedZero67 B hB hF, mul_zero]

theorem reducedZero68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource68 (mixedVector B) = 0 := by
  have h1227 : mixedVector B (Sum.inr 1227) = Sparse.eval nodeValue1227 (mixedVector B) := by
    change mixedMoment B node1227 node1227Labels = _
    exact sound1227 B hB hF
  have h1359 : mixedVector B (Sum.inr 1359) = Sparse.eval nodeValue1359 (mixedVector B) := by
    change mixedMoment B node1359 node1359Labels = _
    exact sound1359 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h1424 : mixedVector B (Sum.inr 1424) = Sparse.eval nodeValue1424 (mixedVector B) := by
    change mixedMoment B node1424 node1424Labels = _
    exact sound1424 B hB hF
  have h2734 : mixedVector B (Sum.inr 2734) = Sparse.eval nodeValue2734 (mixedVector B) := by
    change mixedMoment B node2734 node2734Labels = _
    exact sound2734 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm82, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1227, h1359, h1372, h1424, h2734, h4092, reducedSource68] using sourceEq82 B hB

theorem rowSound68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row68 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck68, numericCheck68, reducedZero68 B hB hF, mul_zero]

theorem reducedZero69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource69 (mixedVector B) = 0 := by
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h3545 : mixedVector B (Sum.inr 3545) = Sparse.eval nodeValue3545 (mixedVector B) := by
    change mixedMoment B node3545 node3545Labels = _
    exact sound3545 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm85, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2065, h3389, h3396, h3545, h3549, h4085, reducedSource69] using sourceEq85 B hB

theorem rowSound69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row69 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck69, numericCheck69, reducedZero69 B hB hF, mul_zero]

theorem reducedZero70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource70 (mixedVector B) = 0 := by
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h2065 : mixedVector B (Sum.inr 2065) = Sparse.eval nodeValue2065 (mixedVector B) := by
    change mixedMoment B node2065 node2065Labels = _
    exact sound2065 B hB hF
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm86, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2055, h2063, h2065, h2294, h3549, h4085, reducedSource70] using sourceEq86 B hB

theorem rowSound70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row70 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck70, numericCheck70, reducedZero70 B hB hF, mul_zero]

theorem reducedZero71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource71 (mixedVector B) = 0 := by
  have h2294 : mixedVector B (Sum.inr 2294) = Sparse.eval nodeValue2294 (mixedVector B) := by
    change mixedMoment B node2294 node2294Labels = _
    exact sound2294 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h3634 : mixedVector B (Sum.inr 3634) = Sparse.eval nodeValue3634 (mixedVector B) := by
    change mixedMoment B node3634 node3634Labels = _
    exact sound3634 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm87, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2294, h3549, h3634, h4085, reducedSource71] using sourceEq87 B hB

theorem rowSound71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row71 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck71, numericCheck71, reducedZero71 B hB hF, mul_zero]

theorem reducedZero72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource72 (mixedVector B) = 0 := by
  have h3160 : mixedVector B (Sum.inr 3160) = Sparse.eval nodeValue3160 (mixedVector B) := by
    change mixedMoment B node3160 node3160Labels = _
    exact sound3160 B hB hF
  have h3393 : mixedVector B (Sum.inr 3393) = Sparse.eval nodeValue3393 (mixedVector B) := by
    change mixedMoment B node3393 node3393Labels = _
    exact sound3393 B hB hF
  have h3396 : mixedVector B (Sum.inr 3396) = Sparse.eval nodeValue3396 (mixedVector B) := by
    change mixedMoment B node3396 node3396Labels = _
    exact sound3396 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm88, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3160, h3393, h3396, h3549, h4085, reducedSource72] using sourceEq88 B hB

theorem rowSound72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row72 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck72, numericCheck72, reducedZero72 B hB hF, mul_zero]

theorem reducedZero73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource73 (mixedVector B) = 0 := by
  have h2055 : mixedVector B (Sum.inr 2055) = Sparse.eval nodeValue2055 (mixedVector B) := by
    change mixedMoment B node2055 node2055Labels = _
    exact sound2055 B hB hF
  have h3393 : mixedVector B (Sum.inr 3393) = Sparse.eval nodeValue3393 (mixedVector B) := by
    change mixedMoment B node3393 node3393Labels = _
    exact sound3393 B hB hF
  have h3495 : mixedVector B (Sum.inr 3495) = Sparse.eval nodeValue3495 (mixedVector B) := by
    change mixedMoment B node3495 node3495Labels = _
    exact sound3495 B hB hF
  have h3543 : mixedVector B (Sum.inr 3543) = Sparse.eval nodeValue3543 (mixedVector B) := by
    change mixedMoment B node3543 node3543Labels = _
    exact sound3543 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm89, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2055, h3393, h3495, h3543, h3549, h4085, reducedSource73] using sourceEq89 B hB

theorem rowSound73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row73 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck73, numericCheck73, reducedZero73 B hB hF, mul_zero]

theorem reducedZero74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource74 (mixedVector B) = 0 := by
  have h3154 : mixedVector B (Sum.inr 3154) = Sparse.eval nodeValue3154 (mixedVector B) := by
    change mixedMoment B node3154 node3154Labels = _
    exact sound3154 B hB hF
  have h3389 : mixedVector B (Sum.inr 3389) = Sparse.eval nodeValue3389 (mixedVector B) := by
    change mixedMoment B node3389 node3389Labels = _
    exact sound3389 B hB hF
  have h3495 : mixedVector B (Sum.inr 3495) = Sparse.eval nodeValue3495 (mixedVector B) := by
    change mixedMoment B node3495 node3495Labels = _
    exact sound3495 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm90, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3154, h3389, h3495, h3549, h4085, reducedSource74] using sourceEq90 B hB

theorem rowSound74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row74 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck74, numericCheck74, reducedZero74 B hB hF, mul_zero]

theorem reducedZero75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource75 (mixedVector B) = 0 := by
  have h2063 : mixedVector B (Sum.inr 2063) = Sparse.eval nodeValue2063 (mixedVector B) := by
    change mixedMoment B node2063 node2063Labels = _
    exact sound2063 B hB hF
  have h3154 : mixedVector B (Sum.inr 3154) = Sparse.eval nodeValue3154 (mixedVector B) := by
    change mixedMoment B node3154 node3154Labels = _
    exact sound3154 B hB hF
  have h3160 : mixedVector B (Sum.inr 3160) = Sparse.eval nodeValue3160 (mixedVector B) := by
    change mixedMoment B node3160 node3160Labels = _
    exact sound3160 B hB hF
  have h3549 : mixedVector B (Sum.inr 3549) = Sparse.eval nodeValue3549 (mixedVector B) := by
    change mixedMoment B node3549 node3549Labels = _
    exact sound3549 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm91, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2063, h3154, h3160, h3549, h4085, reducedSource75] using sourceEq91 B hB

theorem rowSound75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row75 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck75, numericCheck75, reducedZero75 B hB hF, mul_zero]

theorem reducedZero77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource77 (mixedVector B) = 0 := by
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h3064 : mixedVector B (Sum.inr 3064) = Sparse.eval nodeValue3064 (mixedVector B) := by
    change mixedMoment B node3064 node3064Labels = _
    exact sound3064 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3086 : mixedVector B (Sum.inr 3086) = Sparse.eval nodeValue3086 (mixedVector B) := by
    change mixedMoment B node3086 node3086Labels = _
    exact sound3086 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm95, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2712, h3064, h3077, h3086, h3902, h4091, reducedSource77] using sourceEq95 B hB

theorem rowSound77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row77 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck77, numericCheck77, reducedZero77 B hB hF, mul_zero]

theorem reducedZero78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource78 (mixedVector B) = 0 := by
  have h1206 : mixedVector B (Sum.inr 1206) = Sparse.eval nodeValue1206 (mixedVector B) := by
    change mixedMoment B node1206 node1206Labels = _
    exact sound1206 B hB hF
  have h1209 : mixedVector B (Sum.inr 1209) = Sparse.eval nodeValue1209 (mixedVector B) := by
    change mixedMoment B node1209 node1209Labels = _
    exact sound1209 B hB hF
  have h1217 : mixedVector B (Sum.inr 1217) = Sparse.eval nodeValue1217 (mixedVector B) := by
    change mixedMoment B node1217 node1217Labels = _
    exact sound1217 B hB hF
  have h1249 : mixedVector B (Sum.inr 1249) = Sparse.eval nodeValue1249 (mixedVector B) := by
    change mixedMoment B node1249 node1249Labels = _
    exact sound1249 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm96, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1206, h1209, h1217, h1249, h2712, h4091, reducedSource78] using sourceEq96 B hB

theorem rowSound78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row78 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck78, numericCheck78, reducedZero78 B hB hF, mul_zero]

theorem reducedZero79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource79 (mixedVector B) = 0 := by
  have h1249 : mixedVector B (Sum.inr 1249) = Sparse.eval nodeValue1249 (mixedVector B) := by
    change mixedMoment B node1249 node1249Labels = _
    exact sound1249 B hB hF
  have h2562 : mixedVector B (Sum.inr 2562) = Sparse.eval nodeValue2562 (mixedVector B) := by
    change mixedMoment B node2562 node2562Labels = _
    exact sound2562 B hB hF
  have h2624 : mixedVector B (Sum.inr 2624) = Sparse.eval nodeValue2624 (mixedVector B) := by
    change mixedMoment B node2624 node2624Labels = _
    exact sound2624 B hB hF
  have h2712 : mixedVector B (Sum.inr 2712) = Sparse.eval nodeValue2712 (mixedVector B) := by
    change mixedMoment B node2712 node2712Labels = _
    exact sound2712 B hB hF
  have h2751 : mixedVector B (Sum.inr 2751) = Sparse.eval nodeValue2751 (mixedVector B) := by
    change mixedMoment B node2751 node2751Labels = _
    exact sound2751 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm97, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1249, h2562, h2624, h2712, h2751, h4091, reducedSource79] using sourceEq97 B hB

theorem rowSound79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row79 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck79, numericCheck79, reducedZero79 B hB hF, mul_zero]

theorem sourceRowsAt64 : MixedData.sourceRows (64 : Fin 2425) =
    MixedData.row64 := by decide +kernel

theorem sourceRowsAt65 : MixedData.sourceRows (65 : Fin 2425) =
    MixedData.row65 := by decide +kernel

theorem sourceRowsAt66 : MixedData.sourceRows (66 : Fin 2425) =
    MixedData.row66 := by decide +kernel

theorem sourceRowsAt67 : MixedData.sourceRows (67 : Fin 2425) =
    MixedData.row67 := by decide +kernel

theorem sourceRowsAt68 : MixedData.sourceRows (68 : Fin 2425) =
    MixedData.row68 := by decide +kernel

theorem sourceRowsAt69 : MixedData.sourceRows (69 : Fin 2425) =
    MixedData.row69 := by decide +kernel

theorem sourceRowsAt70 : MixedData.sourceRows (70 : Fin 2425) =
    MixedData.row70 := by decide +kernel

theorem sourceRowsAt71 : MixedData.sourceRows (71 : Fin 2425) =
    MixedData.row71 := by decide +kernel

theorem sourceRowsAt72 : MixedData.sourceRows (72 : Fin 2425) =
    MixedData.row72 := by decide +kernel

theorem sourceRowsAt73 : MixedData.sourceRows (73 : Fin 2425) =
    MixedData.row73 := by decide +kernel

theorem sourceRowsAt74 : MixedData.sourceRows (74 : Fin 2425) =
    MixedData.row74 := by decide +kernel

theorem sourceRowsAt75 : MixedData.sourceRows (75 : Fin 2425) =
    MixedData.row75 := by decide +kernel

theorem sourceRowsAt76 : MixedData.sourceRows (76 : Fin 2425) =
    MixedData.row76 := by decide +kernel

theorem sourceRowsAt77 : MixedData.sourceRows (77 : Fin 2425) =
    MixedData.row77 := by decide +kernel

theorem sourceRowsAt78 : MixedData.sourceRows (78 : Fin 2425) =
    MixedData.row78 := by decide +kernel

theorem sourceRowsAt79 : MixedData.sourceRows (79 : Fin 2425) =
    MixedData.row79 := by decide +kernel

theorem chunkSound4_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 4) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 64 ∨ k.val = 65 ∨ k.val = 66 ∨ k.val = 67 ∨ k.val = 68 ∨ k.val = 69 ∨ k.val = 70 ∨ k.val = 71 ∨ k.val = 72 ∨ k.val = 73 ∨ k.val = 74 ∨ k.val = 75 ∨ k.val = 76 ∨ k.val = 77 ∨ k.val = 78 ∨ k.val = 79 := by omega
  rcases heq with h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79
  · have he : k = (64 : Fin 2425) := Fin.ext h64
    subst k
    rw [sourceRowsAt64]
    exact rowSound64 B hB hF
  · have he : k = (65 : Fin 2425) := Fin.ext h65
    subst k
    rw [sourceRowsAt65]
    exact rowSound65 B hB hF
  · have he : k = (66 : Fin 2425) := Fin.ext h66
    subst k
    rw [sourceRowsAt66]
    exact rowSound66 B hB hF
  · have he : k = (67 : Fin 2425) := Fin.ext h67
    subst k
    rw [sourceRowsAt67]
    exact rowSound67 B hB hF
  · have he : k = (68 : Fin 2425) := Fin.ext h68
    subst k
    rw [sourceRowsAt68]
    exact rowSound68 B hB hF
  · have he : k = (69 : Fin 2425) := Fin.ext h69
    subst k
    rw [sourceRowsAt69]
    exact rowSound69 B hB hF
  · have he : k = (70 : Fin 2425) := Fin.ext h70
    subst k
    rw [sourceRowsAt70]
    exact rowSound70 B hB hF
  · have he : k = (71 : Fin 2425) := Fin.ext h71
    subst k
    rw [sourceRowsAt71]
    exact rowSound71 B hB hF
  · have he : k = (72 : Fin 2425) := Fin.ext h72
    subst k
    rw [sourceRowsAt72]
    exact rowSound72 B hB hF
  · have he : k = (73 : Fin 2425) := Fin.ext h73
    subst k
    rw [sourceRowsAt73]
    exact rowSound73 B hB hF
  · have he : k = (74 : Fin 2425) := Fin.ext h74
    subst k
    rw [sourceRowsAt74]
    exact rowSound74 B hB hF
  · have he : k = (75 : Fin 2425) := Fin.ext h75
    subst k
    rw [sourceRowsAt75]
    exact rowSound75 B hB hF
  · have he : k = (76 : Fin 2425) := Fin.ext h76
    subst k
    rw [sourceRowsAt76]
    exact rowSound76_e B hB hF
  · have he : k = (77 : Fin 2425) := Fin.ext h77
    subst k
    rw [sourceRowsAt77]
    exact rowSound77 B hB hF
  · have he : k = (78 : Fin 2425) := Fin.ext h78
    subst k
    rw [sourceRowsAt78]
    exact rowSound78 B hB hF
  · have he : k = (79 : Fin 2425) := Fin.ext h79
    subst k
    rw [sourceRowsAt79]
    exact rowSound79 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound4_e_oai
