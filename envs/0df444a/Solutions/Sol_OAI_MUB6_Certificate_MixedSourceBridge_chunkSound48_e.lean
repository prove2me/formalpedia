-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:19:45.350201+00:00
-- url     : https://prove2.me/submissions/e925e6ca-80e4-4ffa-bf02-8fb744648370

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E123
import Definitions.Def_OAIQ106E128
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound769_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound779_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound780_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14550 raw14550Labels = mixedMoment B node3839 node3839Labels := by
  calc
    _ = mixedMoment B node3839 node3839Labels := by rfl

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

theorem canonical14560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14560 raw14560Labels = mixedMoment B node3168 node3168Labels := by
  calc
    mixedMoment B raw14560 raw14560Labels = mixedMoment B raw14560step0 raw14560step0Labels := by
      have ha : raw14560step0 = (fun i j => raw14560 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14560step0 raw14560; decide +kernel
      have hl : raw14560step0Labels = raw14560Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14560 raw14560Labels permutation688 permutation2
    mixedMoment B raw14560step0 raw14560step0Labels = mixedMoment B raw14560step1 raw14560step1Labels := by
      have ha : raw14560step1 = -raw14560step0 := by apply Matrix.ext; change ∀ i j, raw14560step1 i j = -(raw14560step0 i j); unfold raw14560step1 raw14560step0; decide +kernel
      have hl : raw14560step1Labels = raw14560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3168 node3168Labels := by rfl

theorem canonical14568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14568 raw14568Labels = mixedMoment B node3170 node3170Labels := by
  calc
    mixedMoment B raw14568 raw14568Labels = mixedMoment B raw14568step0 raw14568step0Labels := by
      have ha : raw14568step0 = (fun i j => raw14568 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14568step0 raw14568; decide +kernel
      have hl : raw14568step0Labels = raw14568Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14568 raw14568Labels permutation686 permutation2
    mixedMoment B raw14568step0 raw14568step0Labels = mixedMoment B raw14568step1 raw14568step1Labels := by
      have ha : raw14568step1 = -raw14568step0 := by apply Matrix.ext; change ∀ i j, raw14568step1 i j = -(raw14568step0 i j); unfold raw14568step1 raw14568step0; decide +kernel
      have hl : raw14568step1Labels = raw14568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3170 node3170Labels := by rfl

theorem canonical14574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14574 raw14574Labels = mixedMoment B node3175 node3175Labels := by
  calc
    mixedMoment B raw14574 raw14574Labels = mixedMoment B raw14574step0 raw14574step0Labels := by
      have ha : raw14574step0 = (fun i j => raw14574 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14574step0 raw14574; decide +kernel
      have hl : raw14574step0Labels = raw14574Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14574 raw14574Labels permutation682 permutation2
    mixedMoment B raw14574step0 raw14574step0Labels = mixedMoment B raw14574step1 raw14574step1Labels := by
      have ha : raw14574step1 = -raw14574step0 := by apply Matrix.ext; change ∀ i j, raw14574step1 i j = -(raw14574step0 i j); unfold raw14574step1 raw14574step0; decide +kernel
      have hl : raw14574step1Labels = raw14574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3175 node3175Labels := by rfl

theorem canonical14578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14578 raw14578Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw14578 raw14578Labels = mixedMoment B raw14578step0 raw14578step0Labels := by
      have ha : raw14578step0 = (fun i j => raw14578 (permutation623 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14578step0 raw14578; decide +kernel
      have hl : raw14578step0Labels = raw14578Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14578 raw14578Labels permutation623 permutation4
    _ = mixedMoment B node3196 node3196Labels := by rfl

theorem canonical14579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14579 raw14579Labels = mixedMoment B node2544 node2544Labels := by
  calc
    _ = mixedMoment B node2544 node2544Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14670 raw14670Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14670 raw14670Labels = mixedMoment B raw14670step0 raw14670step0Labels := by
      have ha : raw14670step0 = (fun i j => raw14670 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14670step0 raw14670; decide +kernel
      have hl : raw14670step0Labels = raw14670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14670 raw14670Labels permutation682 permutation2
    mixedMoment B raw14670step0 raw14670step0Labels = mixedMoment B raw14670step1 raw14670step1Labels := by
      have ha : raw14670step1 = -raw14670step0 := by apply Matrix.ext; change ∀ i j, raw14670step1 i j = -(raw14670step0 i j); unfold raw14670step1 raw14670step0; decide +kernel
      have hl : raw14670step1Labels = raw14670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical14671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14671 raw14671Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw14671 raw14671Labels = mixedMoment B raw14671step0 raw14671step0Labels := by
      have ha : raw14671step0 = (fun i j => raw14671 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14671step0 raw14671; decide +kernel
      have hl : raw14671step0Labels = raw14671Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14671 raw14671Labels permutation681 permutation2
    mixedMoment B raw14671step0 raw14671step0Labels = mixedMoment B raw14671step1 raw14671step1Labels := by
      have ha : raw14671step1 = -raw14671step0 := by apply Matrix.ext; change ∀ i j, raw14671step1 i j = -(raw14671step0 i j); unfold raw14671step1 raw14671step0; decide +kernel
      have hl : raw14671step1Labels = raw14671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical14672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14672 raw14672Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw14672 raw14672Labels = mixedMoment B raw14672step0 raw14672step0Labels := by
      have ha : raw14672step0 = (fun i j => raw14672 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14672step0 raw14672; decide +kernel
      have hl : raw14672step0Labels = raw14672Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14672 raw14672Labels permutation687 permutation2
    mixedMoment B raw14672step0 raw14672step0Labels = mixedMoment B raw14672step1 raw14672step1Labels := by
      have ha : raw14672step1 = -raw14672step0 := by apply Matrix.ext; change ∀ i j, raw14672step1 i j = -(raw14672step0 i j); unfold raw14672step1 raw14672step0; decide +kernel
      have hl : raw14672step1Labels = raw14672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

theorem canonical14673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14673 raw14673Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw14673 raw14673Labels = mixedMoment B raw14673step0 raw14673step0Labels := by
      have ha : raw14673step0 = (fun i j => raw14673 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14673step0 raw14673; decide +kernel
      have hl : raw14673step0Labels = raw14673Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14673 raw14673Labels permutation677 permutation2
    mixedMoment B raw14673step0 raw14673step0Labels = mixedMoment B raw14673step1 raw14673step1Labels := by
      have ha : raw14673step1 = -raw14673step0 := by apply Matrix.ext; change ∀ i j, raw14673step1 i j = -(raw14673step0 i j); unfold raw14673step1 raw14673step0; decide +kernel
      have hl : raw14673step1Labels = raw14673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical14674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14674 raw14674Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw14674 raw14674Labels = mixedMoment B raw14674step0 raw14674step0Labels := by
      have ha : raw14674step0 = (fun i j => raw14674 (permutation639 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14674step0 raw14674; decide +kernel
      have hl : raw14674step0Labels = raw14674Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14674 raw14674Labels permutation639 permutation2
    mixedMoment B raw14674step0 raw14674step0Labels = mixedMoment B raw14674step1 raw14674step1Labels := by
      have ha : raw14674step1 = -raw14674step0 := by apply Matrix.ext; change ∀ i j, raw14674step1 i j = -(raw14674step0 i j); unfold raw14674step1 raw14674step0; decide +kernel
      have hl : raw14674step1Labels = raw14674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3901 node3901Labels := by rfl

theorem canonical14675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14675 raw14675Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw14675 raw14675Labels = mixedMoment B raw14675step0 raw14675step0Labels := by
      have ha : raw14675step0 = (fun i j => raw14675 (permutation554 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14675step0 raw14675; decide +kernel
      have hl : raw14675step0Labels = raw14675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14675 raw14675Labels permutation554 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical14676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14676 raw14676Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw14676 raw14676Labels = mixedMoment B raw14676step0 raw14676step0Labels := by
      have hz : ∀ j, raw14676 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw14676step0 = (fun i j => raw14676 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw14676step0 raw14676; decide +kernel
      have hl : raw14676step0Labels = raw14676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14676 raw14676Labels permutation152 hz
    mixedMoment B raw14676step0 raw14676step0Labels = mixedMoment B raw14676step1 raw14676step1Labels := by
      have ha : raw14676step1 = (fun i j => raw14676step0 (permutation134 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14676step1 raw14676step0; decide +kernel
      have hl : raw14676step1Labels = raw14676step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14676step0 raw14676step0Labels permutation134 permutation0
    mixedMoment B raw14676step1 raw14676step1Labels = mixedMoment B raw14676step2 raw14676step2Labels := by
      have ha : raw14676step2 = -raw14676step1 := by apply Matrix.ext; change ∀ i j, raw14676step2 i j = -(raw14676step1 i j); unfold raw14676step2 raw14676step1; decide +kernel
      have hl : raw14676step2Labels = raw14676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical14677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14677 raw14677Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw14677 raw14677Labels = mixedMoment B raw14677step0 raw14677step0Labels := by
      have ha : raw14677step0 = (fun i j => raw14677 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14677step0 raw14677; decide +kernel
      have hl : raw14677step0Labels = raw14677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14677 raw14677Labels permutation194 permutation4
    mixedMoment B raw14677step0 raw14677step0Labels = mixedMoment B raw14677step1 raw14677step1Labels := by
      have ha : raw14677step1 = -raw14677step0 := by apply Matrix.ext; change ∀ i j, raw14677step1 i j = -(raw14677step0 i j); unfold raw14677step1 raw14677step0; decide +kernel
      have hl : raw14677step1Labels = raw14677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

theorem canonical14678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14678 raw14678Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw14678 raw14678Labels = mixedMoment B raw14678step0 raw14678step0Labels := by
      have ha : raw14678step0 = (fun i j => raw14678 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14678step0 raw14678; decide +kernel
      have hl : raw14678step0Labels = raw14678Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14678 raw14678Labels permutation160 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical14679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14679 raw14679Labels = mixedMoment B node3195 node3195Labels := by
  calc
    mixedMoment B raw14679 raw14679Labels = mixedMoment B raw14679step0 raw14679step0Labels := by
      have ha : raw14679step0 = (fun i j => raw14679 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14679step0 raw14679; decide +kernel
      have hl : raw14679step0Labels = raw14679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14679 raw14679Labels permutation194 permutation4
    mixedMoment B raw14679step0 raw14679step0Labels = mixedMoment B raw14679step1 raw14679step1Labels := by
      have ha : raw14679step1 = -raw14679step0 := by apply Matrix.ext; change ∀ i j, raw14679step1 i j = -(raw14679step0 i j); unfold raw14679step1 raw14679step0; decide +kernel
      have hl : raw14679step1Labels = raw14679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3195 node3195Labels := by rfl

theorem canonical14680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14680 raw14680Labels = mixedMoment B node2919 node2919Labels := by
  calc
    mixedMoment B raw14680 raw14680Labels = mixedMoment B raw14680step0 raw14680step0Labels := by
      have ha : raw14680step0 = (fun i j => raw14680 (permutation559 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14680step0 raw14680; decide +kernel
      have hl : raw14680step0Labels = raw14680Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14680 raw14680Labels permutation559 permutation4
    _ = mixedMoment B node2919 node2919Labels := by rfl

theorem canonical14681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14681 raw14681Labels = mixedMoment B node2611 node2611Labels := by
  calc
    mixedMoment B raw14681 raw14681Labels = mixedMoment B raw14681step0 raw14681step0Labels := by
      have ha : raw14681step0 = (fun i j => raw14681 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14681step0 raw14681; decide +kernel
      have hl : raw14681step0Labels = raw14681Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14681 raw14681Labels permutation682 permutation2
    mixedMoment B raw14681step0 raw14681step0Labels = mixedMoment B raw14681step1 raw14681step1Labels := by
      have ha : raw14681step1 = -raw14681step0 := by apply Matrix.ext; change ∀ i j, raw14681step1 i j = -(raw14681step0 i j); unfold raw14681step1 raw14681step0; decide +kernel
      have hl : raw14681step1Labels = raw14681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2611 node2611Labels := by rfl

theorem canonical14682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14682 raw14682Labels = mixedMoment B node3878 node3878Labels := by
  calc
    mixedMoment B raw14682 raw14682Labels = mixedMoment B raw14682step0 raw14682step0Labels := by
      have ha : raw14682step0 = (fun i j => raw14682 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14682step0 raw14682; decide +kernel
      have hl : raw14682step0Labels = raw14682Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14682 raw14682Labels permutation676 permutation2
    mixedMoment B raw14682step0 raw14682step0Labels = mixedMoment B raw14682step1 raw14682step1Labels := by
      have ha : raw14682step1 = -raw14682step0 := by apply Matrix.ext; change ∀ i j, raw14682step1 i j = -(raw14682step0 i j); unfold raw14682step1 raw14682step0; decide +kernel
      have hl : raw14682step1Labels = raw14682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3878 node3878Labels := by rfl

theorem canonical14683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14683 raw14683Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14683 raw14683Labels = mixedMoment B raw14683step0 raw14683step0Labels := by
      have ha : raw14683step0 = (fun i j => raw14683 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14683step0 raw14683; decide +kernel
      have hl : raw14683step0Labels = raw14683Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14683 raw14683Labels permutation680 permutation2
    mixedMoment B raw14683step0 raw14683step0Labels = mixedMoment B raw14683step1 raw14683step1Labels := by
      have ha : raw14683step1 = -raw14683step0 := by apply Matrix.ext; change ∀ i j, raw14683step1 i j = -(raw14683step0 i j); unfold raw14683step1 raw14683step0; decide +kernel
      have hl : raw14683step1Labels = raw14683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical14684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14684 raw14684Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw14684 raw14684Labels = mixedMoment B raw14684step0 raw14684step0Labels := by
      have ha : raw14684step0 = (fun i j => raw14684 (permutation632 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14684step0 raw14684; decide +kernel
      have hl : raw14684step0Labels = raw14684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14684 raw14684Labels permutation632 permutation2
    mixedMoment B raw14684step0 raw14684step0Labels = mixedMoment B raw14684step1 raw14684step1Labels := by
      have ha : raw14684step1 = -raw14684step0 := by apply Matrix.ext; change ∀ i j, raw14684step1 i j = -(raw14684step0 i j); unfold raw14684step1 raw14684step0; decide +kernel
      have hl : raw14684step1Labels = raw14684step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical14685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14685 raw14685Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw14685 raw14685Labels = mixedMoment B raw14685step0 raw14685step0Labels := by
      have ha : raw14685step0 = (fun i j => raw14685 (permutation536 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14685step0 raw14685; decide +kernel
      have hl : raw14685step0Labels = raw14685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14685 raw14685Labels permutation536 permutation4
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical14686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14686 raw14686Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw14686 raw14686Labels = mixedMoment B raw14686step0 raw14686step0Labels := by
      have ha : raw14686step0 = (fun i j => raw14686 (permutation645 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14686step0 raw14686; decide +kernel
      have hl : raw14686step0Labels = raw14686Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14686 raw14686Labels permutation645 permutation2
    mixedMoment B raw14686step0 raw14686step0Labels = mixedMoment B raw14686step1 raw14686step1Labels := by
      have ha : raw14686step1 = -raw14686step0 := by apply Matrix.ext; change ∀ i j, raw14686step1 i j = -(raw14686step0 i j); unfold raw14686step1 raw14686step0; decide +kernel
      have hl : raw14686step1Labels = raw14686step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3783 node3783Labels := by rfl

theorem canonical14687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14687 raw14687Labels = mixedMoment B node3863 node3863Labels := by
  calc
    mixedMoment B raw14687 raw14687Labels = mixedMoment B raw14687step0 raw14687step0Labels := by
      have ha : raw14687step0 = (fun i j => raw14687 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14687step0 raw14687; decide +kernel
      have hl : raw14687step0Labels = raw14687Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14687 raw14687Labels permutation663 permutation2
    mixedMoment B raw14687step0 raw14687step0Labels = mixedMoment B raw14687step1 raw14687step1Labels := by
      have ha : raw14687step1 = -raw14687step0 := by apply Matrix.ext; change ∀ i j, raw14687step1 i j = -(raw14687step0 i j); unfold raw14687step1 raw14687step0; decide +kernel
      have hl : raw14687step1Labels = raw14687step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3863 node3863Labels := by rfl

theorem canonical14688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14688 raw14688Labels = mixedMoment B node2945 node2945Labels := by
  calc
    mixedMoment B raw14688 raw14688Labels = mixedMoment B raw14688step0 raw14688step0Labels := by
      have ha : raw14688step0 = (fun i j => raw14688 (permutation566 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14688step0 raw14688; decide +kernel
      have hl : raw14688step0Labels = raw14688Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14688 raw14688Labels permutation566 permutation4
    _ = mixedMoment B node2945 node2945Labels := by rfl

theorem canonical14689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14689 raw14689Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw14689 raw14689Labels = mixedMoment B raw14689step0 raw14689step0Labels := by
      have ha : raw14689step0 = (fun i j => raw14689 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14689step0 raw14689; decide +kernel
      have hl : raw14689step0Labels = raw14689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14689 raw14689Labels permutation681 permutation2
    mixedMoment B raw14689step0 raw14689step0Labels = mixedMoment B raw14689step1 raw14689step1Labels := by
      have ha : raw14689step1 = -raw14689step0 := by apply Matrix.ext; change ∀ i j, raw14689step1 i j = -(raw14689step0 i j); unfold raw14689step1 raw14689step0; decide +kernel
      have hl : raw14689step1Labels = raw14689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2612 node2612Labels := by rfl

theorem canonical14690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14690 raw14690Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw14690 raw14690Labels = mixedMoment B raw14690step0 raw14690step0Labels := by
      have ha : raw14690step0 = (fun i j => raw14690 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14690step0 raw14690; decide +kernel
      have hl : raw14690step0Labels = raw14690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14690 raw14690Labels permutation644 permutation2
    mixedMoment B raw14690step0 raw14690step0Labels = mixedMoment B raw14690step1 raw14690step1Labels := by
      have ha : raw14690step1 = -raw14690step0 := by apply Matrix.ext; change ∀ i j, raw14690step1 i j = -(raw14690step0 i j); unfold raw14690step1 raw14690step0; decide +kernel
      have hl : raw14690step1Labels = raw14690step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical14691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14691 raw14691Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw14691 raw14691Labels = mixedMoment B raw14691step0 raw14691step0Labels := by
      have ha : raw14691step0 = (fun i j => raw14691 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14691step0 raw14691; decide +kernel
      have hl : raw14691step0Labels = raw14691Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14691 raw14691Labels permutation640 permutation2
    mixedMoment B raw14691step0 raw14691step0Labels = mixedMoment B raw14691step1 raw14691step1Labels := by
      have ha : raw14691step1 = -raw14691step0 := by apply Matrix.ext; change ∀ i j, raw14691step1 i j = -(raw14691step0 i j); unfold raw14691step1 raw14691step0; decide +kernel
      have hl : raw14691step1Labels = raw14691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical14692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14692 raw14692Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw14692 raw14692Labels = mixedMoment B raw14692step0 raw14692step0Labels := by
      have ha : raw14692step0 = (fun i j => raw14692 (permutation557 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14692step0 raw14692; decide +kernel
      have hl : raw14692step0Labels = raw14692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14692 raw14692Labels permutation557 permutation4
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical14693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14693 raw14693Labels = mixedMoment B node3865 node3865Labels := by
  calc
    mixedMoment B raw14693 raw14693Labels = mixedMoment B raw14693step0 raw14693step0Labels := by
      have ha : raw14693step0 = (fun i j => raw14693 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14693step0 raw14693; decide +kernel
      have hl : raw14693step0Labels = raw14693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14693 raw14693Labels permutation664 permutation2
    mixedMoment B raw14693step0 raw14693step0Labels = mixedMoment B raw14693step1 raw14693step1Labels := by
      have ha : raw14693step1 = -raw14693step0 := by apply Matrix.ext; change ∀ i j, raw14693step1 i j = -(raw14693step0 i j); unfold raw14693step1 raw14693step0; decide +kernel
      have hl : raw14693step1Labels = raw14693step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3865 node3865Labels := by rfl

theorem canonical14694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14694 raw14694Labels = mixedMoment B node2920 node2920Labels := by
  calc
    mixedMoment B raw14694 raw14694Labels = mixedMoment B raw14694step0 raw14694step0Labels := by
      have ha : raw14694step0 = (fun i j => raw14694 (permutation558 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14694step0 raw14694; decide +kernel
      have hl : raw14694step0Labels = raw14694Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14694 raw14694Labels permutation558 permutation4
    _ = mixedMoment B node2920 node2920Labels := by rfl

theorem canonical14695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14695 raw14695Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw14695 raw14695Labels = mixedMoment B raw14695step0 raw14695step0Labels := by
      have ha : raw14695step0 = (fun i j => raw14695 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14695step0 raw14695; decide +kernel
      have hl : raw14695step0Labels = raw14695Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14695 raw14695Labels permutation688 permutation2
    mixedMoment B raw14695step0 raw14695step0Labels = mixedMoment B raw14695step1 raw14695step1Labels := by
      have ha : raw14695step1 = -raw14695step0 := by apply Matrix.ext; change ∀ i j, raw14695step1 i j = -(raw14695step0 i j); unfold raw14695step1 raw14695step0; decide +kernel
      have hl : raw14695step1Labels = raw14695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2623 node2623Labels := by rfl

theorem canonical14696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14696 raw14696Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14696 raw14696Labels = mixedMoment B raw14696step0 raw14696step0Labels := by
      have ha : raw14696step0 = (fun i j => raw14696 (permutation658 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14696step0 raw14696; decide +kernel
      have hl : raw14696step0Labels = raw14696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14696 raw14696Labels permutation658 permutation2
    mixedMoment B raw14696step0 raw14696step0Labels = mixedMoment B raw14696step1 raw14696step1Labels := by
      have ha : raw14696step1 = -raw14696step0 := by apply Matrix.ext; change ∀ i j, raw14696step1 i j = -(raw14696step0 i j); unfold raw14696step1 raw14696step0; decide +kernel
      have hl : raw14696step1Labels = raw14696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical14697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14697 raw14697Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw14697 raw14697Labels = mixedMoment B raw14697step0 raw14697step0Labels := by
      have ha : raw14697step0 = (fun i j => raw14697 (permutation492 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14697step0 raw14697; decide +kernel
      have hl : raw14697step0Labels = raw14697Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14697 raw14697Labels permutation492 permutation4
    _ = mixedMoment B node3922 node3922Labels := by rfl

theorem canonical14698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14698 raw14698Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw14698 raw14698Labels = mixedMoment B raw14698step0 raw14698step0Labels := by
      have ha : raw14698step0 = (fun i j => raw14698 (permutation537 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14698step0 raw14698; decide +kernel
      have hl : raw14698step0Labels = raw14698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14698 raw14698Labels permutation537 permutation4
    _ = mixedMoment B node3069 node3069Labels := by rfl

theorem canonical14699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14699 raw14699Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw14699 raw14699Labels = mixedMoment B raw14699step0 raw14699step0Labels := by
      have ha : raw14699step0 = (fun i j => raw14699 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14699step0 raw14699; decide +kernel
      have hl : raw14699step0Labels = raw14699Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14699 raw14699Labels permutation680 permutation2
    mixedMoment B raw14699step0 raw14699step0Labels = mixedMoment B raw14699step1 raw14699step1Labels := by
      have ha : raw14699step1 = -raw14699step0 := by apply Matrix.ext; change ∀ i j, raw14699step1 i j = -(raw14699step0 i j); unfold raw14699step1 raw14699step0; decide +kernel
      have hl : raw14699step1Labels = raw14699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2617 node2617Labels := by rfl

theorem canonical14700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14700 raw14700Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw14700 raw14700Labels = mixedMoment B raw14700step0 raw14700step0Labels := by
      have ha : raw14700step0 = (fun i j => raw14700 (permutation557 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14700step0 raw14700; decide +kernel
      have hl : raw14700step0Labels = raw14700Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14700 raw14700Labels permutation557 permutation4
    _ = mixedMoment B node2928 node2928Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical14791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14791 raw14791Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14791 raw14791Labels = mixedMoment B raw14791step0 raw14791step0Labels := by
      have ha : raw14791step0 = (fun i j => raw14791 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14791step0 raw14791; decide +kernel
      have hl : raw14791step0Labels = raw14791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14791 raw14791Labels permutation180 permutation4
    mixedMoment B raw14791step0 raw14791step0Labels = mixedMoment B raw14791step1 raw14791step1Labels := by
      have ha : raw14791step1 = -raw14791step0 := by apply Matrix.ext; change ∀ i j, raw14791step1 i j = -(raw14791step0 i j); unfold raw14791step1 raw14791step0; decide +kernel
      have hl : raw14791step1Labels = raw14791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical14792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14792 raw14792Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw14792 raw14792Labels = mixedMoment B raw14792step0 raw14792step0Labels := by
      have ha : raw14792step0 = (fun i j => raw14792 (permutation634 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14792step0 raw14792; decide +kernel
      have hl : raw14792step0Labels = raw14792Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14792 raw14792Labels permutation634 permutation2
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical14793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14793 raw14793Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw14793 raw14793Labels = mixedMoment B raw14793step0 raw14793step0Labels := by
      have ha : raw14793step0 = (fun i j => raw14793 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14793step0 raw14793; decide +kernel
      have hl : raw14793step0Labels = raw14793Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14793 raw14793Labels permutation646 permutation2
    _ = mixedMoment B node3730 node3730Labels := by rfl

theorem canonical14794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14794 raw14794Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw14794 raw14794Labels = mixedMoment B raw14794step0 raw14794step0Labels := by
      have hz : ∀ j, raw14794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14794step0 = (fun i j => raw14794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14794step0 raw14794; decide +kernel
      have hl : raw14794step0Labels = raw14794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14794 raw14794Labels permutation434 hz
    mixedMoment B raw14794step0 raw14794step0Labels = mixedMoment B raw14794step1 raw14794step1Labels := by
      have ha : raw14794step1 = (fun i j => raw14794step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14794step1 raw14794step0; decide +kernel
      have hl : raw14794step1Labels = raw14794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14794step0 raw14794step0Labels permutation145 permutation2
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical14795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14795 raw14795Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw14795 raw14795Labels = mixedMoment B raw14795step0 raw14795step0Labels := by
      have ha : raw14795step0 = (fun i j => raw14795 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14795step0 raw14795; decide +kernel
      have hl : raw14795step0Labels = raw14795Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14795 raw14795Labels permutation646 permutation2
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical14796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14796 raw14796Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw14796 raw14796Labels = mixedMoment B raw14796step0 raw14796step0Labels := by
      have ha : raw14796step0 = (fun i j => raw14796 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14796step0 raw14796; decide +kernel
      have hl : raw14796step0Labels = raw14796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14796 raw14796Labels permutation646 permutation2
    _ = mixedMoment B node2587 node2587Labels := by rfl

theorem canonical14797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14797 raw14797Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14797 raw14797Labels = mixedMoment B raw14797step0 raw14797step0Labels := by
      have hz : ∀ j, raw14797 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14797step0 = (fun i j => raw14797 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14797step0 raw14797; decide +kernel
      have hl : raw14797step0Labels = raw14797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797 raw14797Labels permutation434 hz
    mixedMoment B raw14797step0 raw14797step0Labels = mixedMoment B raw14797step1 raw14797step1Labels := by
      have hz : ∀ j, raw14797step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14797step1 = (fun i j => raw14797step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14797step1 raw14797step0; decide +kernel
      have hl : raw14797step1Labels = raw14797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14797step0 raw14797step0Labels permutation80 hz
    mixedMoment B raw14797step1 raw14797step1Labels = mixedMoment B raw14797step2 raw14797step2Labels := by
      have ha : raw14797step2 = (fun i j => raw14797step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14797step2 raw14797step1; decide +kernel
      have hl : raw14797step2Labels = raw14797step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14797step1 raw14797step1Labels permutation31 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical14798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14798 raw14798Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw14798 raw14798Labels = mixedMoment B raw14798step0 raw14798step0Labels := by
      have ha : raw14798step0 = (fun i j => raw14798 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14798step0 raw14798; decide +kernel
      have hl : raw14798step0Labels = raw14798Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14798 raw14798Labels permutation194 permutation4
    mixedMoment B raw14798step0 raw14798step0Labels = mixedMoment B raw14798step1 raw14798step1Labels := by
      have ha : raw14798step1 = -raw14798step0 := by apply Matrix.ext; change ∀ i j, raw14798step1 i j = -(raw14798step0 i j); unfold raw14798step1 raw14798step0; decide +kernel
      have hl : raw14798step1Labels = raw14798step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2577 node2577Labels := by rfl

theorem canonical14799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14799 raw14799Labels = mixedMoment B node3729 node3729Labels := by
  calc
    mixedMoment B raw14799 raw14799Labels = mixedMoment B raw14799step0 raw14799step0Labels := by
      have ha : raw14799step0 = (fun i j => raw14799 (permutation628 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14799step0 raw14799; decide +kernel
      have hl : raw14799step0Labels = raw14799Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14799 raw14799Labels permutation628 permutation2
    _ = mixedMoment B node3729 node3729Labels := by rfl

theorem canonical14800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14800 raw14800Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw14800 raw14800Labels = mixedMoment B raw14800step0 raw14800step0Labels := by
      have hz : ∀ j, raw14800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14800step0 = (fun i j => raw14800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14800step0 raw14800; decide +kernel
      have hl : raw14800step0Labels = raw14800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14800 raw14800Labels permutation434 hz
    mixedMoment B raw14800step0 raw14800step0Labels = mixedMoment B raw14800step1 raw14800step1Labels := by
      have ha : raw14800step1 = (fun i j => raw14800step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14800step1 raw14800step0; decide +kernel
      have hl : raw14800step1Labels = raw14800step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14800step0 raw14800step0Labels permutation141 permutation2
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical14801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14801 raw14801Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14801 raw14801Labels = mixedMoment B raw14801step0 raw14801step0Labels := by
      have ha : raw14801step0 = (fun i j => raw14801 (permutation642 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14801step0 raw14801; decide +kernel
      have hl : raw14801step0Labels = raw14801Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14801 raw14801Labels permutation642 permutation2
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical14802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14802 raw14802Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw14802 raw14802Labels = mixedMoment B raw14802step0 raw14802step0Labels := by
      have ha : raw14802step0 = (fun i j => raw14802 (permutation628 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14802step0 raw14802; decide +kernel
      have hl : raw14802step0Labels = raw14802Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14802 raw14802Labels permutation628 permutation2
    _ = mixedMoment B node2577 node2577Labels := by rfl

theorem canonical14803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14803 raw14803Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw14803 raw14803Labels = mixedMoment B raw14803step0 raw14803step0Labels := by
      have hz : ∀ j, raw14803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14803step0 = (fun i j => raw14803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14803step0 raw14803; decide +kernel
      have hl : raw14803step0Labels = raw14803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14803 raw14803Labels permutation346 hz
    mixedMoment B raw14803step0 raw14803step0Labels = mixedMoment B raw14803step1 raw14803step1Labels := by
      have ha : raw14803step1 = (fun i j => raw14803step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14803step1 raw14803step0; decide +kernel
      have hl : raw14803step1Labels = raw14803step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14803step0 raw14803step0Labels permutation36 permutation4
    mixedMoment B raw14803step1 raw14803step1Labels = mixedMoment B raw14803step2 raw14803step2Labels := by
      have ha : raw14803step2 = -raw14803step1 := by apply Matrix.ext; change ∀ i j, raw14803step2 i j = -(raw14803step1 i j); unfold raw14803step2 raw14803step1; decide +kernel
      have hl : raw14803step2Labels = raw14803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical14804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14804 raw14804Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw14804 raw14804Labels = mixedMoment B raw14804step0 raw14804step0Labels := by
      have ha : raw14804step0 = (fun i j => raw14804 (permutation156 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14804step0 raw14804; decide +kernel
      have hl : raw14804step0Labels = raw14804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14804 raw14804Labels permutation156 permutation4
    mixedMoment B raw14804step0 raw14804step0Labels = mixedMoment B raw14804step1 raw14804step1Labels := by
      have ha : raw14804step1 = -raw14804step0 := by apply Matrix.ext; change ∀ i j, raw14804step1 i j = -(raw14804step0 i j); unfold raw14804step1 raw14804step0; decide +kernel
      have hl : raw14804step1Labels = raw14804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

theorem canonical14805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14805 raw14805Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw14805 raw14805Labels = mixedMoment B raw14805step0 raw14805step0Labels := by
      have ha : raw14805step0 = (fun i j => raw14805 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14805step0 raw14805; decide +kernel
      have hl : raw14805step0Labels = raw14805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14805 raw14805Labels permutation568 permutation4
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical14806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14806 raw14806Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw14806 raw14806Labels = mixedMoment B raw14806step0 raw14806step0Labels := by
      have ha : raw14806step0 = (fun i j => raw14806 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14806step0 raw14806; decide +kernel
      have hl : raw14806step0Labels = raw14806Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14806 raw14806Labels permutation153 permutation4
    mixedMoment B raw14806step0 raw14806step0Labels = mixedMoment B raw14806step1 raw14806step1Labels := by
      have ha : raw14806step1 = -raw14806step0 := by apply Matrix.ext; change ∀ i j, raw14806step1 i j = -(raw14806step0 i j); unfold raw14806step1 raw14806step0; decide +kernel
      have hl : raw14806step1Labels = raw14806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3781 node3781Labels := by rfl

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

theorem sound2577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2577 node2577Labels = Sparse.eval nodeValue2577 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2577) = mixedMoment B node2577 node2577Labels := rfl
  simpa [nodeValue2577, Sparse.eval] using hc.symm

theorem sound2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2587 node2587Labels = Sparse.eval nodeValue2587 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2587) = mixedMoment B node2587 node2587Labels := rfl
  simpa [nodeValue2587, Sparse.eval] using hc.symm

theorem sound2611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2611 node2611Labels = Sparse.eval nodeValue2611 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2611) = mixedMoment B node2611 node2611Labels := rfl
  simpa [nodeValue2611, Sparse.eval] using hc.symm

theorem sound2612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2612 node2612Labels = Sparse.eval nodeValue2612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2612) = mixedMoment B node2612 node2612Labels := rfl
  simpa [nodeValue2612, Sparse.eval] using hc.symm

theorem sound2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2617 node2617Labels = Sparse.eval nodeValue2617 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2617) = mixedMoment B node2617 node2617Labels := rfl
  simpa [nodeValue2617, Sparse.eval] using hc.symm

theorem sound2623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2623 node2623Labels = Sparse.eval nodeValue2623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2623) = mixedMoment B node2623 node2623Labels := rfl
  simpa [nodeValue2623, Sparse.eval] using hc.symm

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

theorem sound2919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2919 node2919Labels = Sparse.eval nodeValue2919 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2919) = mixedMoment B node2919 node2919Labels := rfl
  simpa [nodeValue2919, Sparse.eval] using hc.symm

theorem sound2920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2920 node2920Labels = Sparse.eval nodeValue2920 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2920) = mixedMoment B node2920 node2920Labels := rfl
  simpa [nodeValue2920, Sparse.eval] using hc.symm

theorem sound2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2928 node2928Labels = Sparse.eval nodeValue2928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2928) = mixedMoment B node2928 node2928Labels := rfl
  simpa [nodeValue2928, Sparse.eval] using hc.symm

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

theorem sound2945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2945 node2945Labels = Sparse.eval nodeValue2945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2945) = mixedMoment B node2945 node2945Labels := rfl
  simpa [nodeValue2945, Sparse.eval] using hc.symm

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

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

theorem sound3069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3069 node3069Labels = Sparse.eval nodeValue3069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3069) = mixedMoment B node3069 node3069Labels := rfl
  simpa [nodeValue3069, Sparse.eval] using hc.symm

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

theorem sound3168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3168 node3168Labels = Sparse.eval nodeValue3168 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3168) = mixedMoment B node3168 node3168Labels := rfl
  simpa [nodeValue3168, Sparse.eval] using hc.symm

theorem sound3170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3170 node3170Labels = Sparse.eval nodeValue3170 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3170) = mixedMoment B node3170 node3170Labels := rfl
  simpa [nodeValue3170, Sparse.eval] using hc.symm

theorem sound3175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3175 node3175Labels = Sparse.eval nodeValue3175 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3175) = mixedMoment B node3175 node3175Labels := rfl
  simpa [nodeValue3175, Sparse.eval] using hc.symm

theorem sound3195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3195 node3195Labels = Sparse.eval nodeValue3195 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3195) = mixedMoment B node3195 node3195Labels := rfl
  simpa [nodeValue3195, Sparse.eval] using hc.symm

theorem sound3196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3196 node3196Labels = Sparse.eval nodeValue3196 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3196) = mixedMoment B node3196 node3196Labels := rfl
  simpa [nodeValue3196, Sparse.eval] using hc.symm

theorem sound3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3197 node3197Labels = Sparse.eval nodeValue3197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3197) = mixedMoment B node3197 node3197Labels := rfl
  simpa [nodeValue3197, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3202 node3202Labels = Sparse.eval nodeValue3202 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3202) = mixedMoment B node3202 node3202Labels := rfl
  simpa [nodeValue3202, Sparse.eval] using hc.symm

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

theorem sound3729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3729 node3729Labels = Sparse.eval nodeValue3729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3729) = mixedMoment B node3729 node3729Labels := rfl
  simpa [nodeValue3729, Sparse.eval] using hc.symm

theorem sound3730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3730 node3730Labels = Sparse.eval nodeValue3730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3730) = mixedMoment B node3730 node3730Labels := rfl
  simpa [nodeValue3730, Sparse.eval] using hc.symm

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

theorem sound3780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3780 node3780Labels = Sparse.eval nodeValue3780 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3780) = mixedMoment B node3780 node3780Labels := rfl
  simpa [nodeValue3780, Sparse.eval] using hc.symm

theorem sound3781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3781 node3781Labels = Sparse.eval nodeValue3781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3781) = mixedMoment B node3781 node3781Labels := rfl
  simpa [nodeValue3781, Sparse.eval] using hc.symm

theorem sound3783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3783 node3783Labels = Sparse.eval nodeValue3783 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3783) = mixedMoment B node3783 node3783Labels := rfl
  simpa [nodeValue3783, Sparse.eval] using hc.symm

theorem sound3789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3789 node3789Labels = Sparse.eval nodeValue3789 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3789) = mixedMoment B node3789 node3789Labels := rfl
  simpa [nodeValue3789, Sparse.eval] using hc.symm

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

theorem sound3839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3839 node3839Labels = Sparse.eval nodeValue3839 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3839) = mixedMoment B node3839 node3839Labels := rfl
  simpa [nodeValue3839, Sparse.eval] using hc.symm

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

theorem sound3840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3840 node3840Labels = Sparse.eval nodeValue3840 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3840) = mixedMoment B node3840 node3840Labels := rfl
  simpa [nodeValue3840, Sparse.eval] using hc.symm

theorem sound3843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3843 node3843Labels = Sparse.eval nodeValue3843 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3843) = mixedMoment B node3843 node3843Labels := rfl
  simpa [nodeValue3843, Sparse.eval] using hc.symm

theorem sound3848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3848 node3848Labels = Sparse.eval nodeValue3848 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3848) = mixedMoment B node3848 node3848Labels := rfl
  simpa [nodeValue3848, Sparse.eval] using hc.symm

theorem sound3854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3854 node3854Labels = Sparse.eval nodeValue3854 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3854) = mixedMoment B node3854 node3854Labels := rfl
  simpa [nodeValue3854, Sparse.eval] using hc.symm

theorem sound3857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3857 node3857Labels = Sparse.eval nodeValue3857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3857) = mixedMoment B node3857 node3857Labels := rfl
  simpa [nodeValue3857, Sparse.eval] using hc.symm

theorem sound3863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3863 node3863Labels = Sparse.eval nodeValue3863 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3863) = mixedMoment B node3863 node3863Labels := rfl
  simpa [nodeValue3863, Sparse.eval] using hc.symm

theorem sound3865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3865 node3865Labels = Sparse.eval nodeValue3865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3865) = mixedMoment B node3865 node3865Labels := rfl
  simpa [nodeValue3865, Sparse.eval] using hc.symm

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3872 node3872Labels = Sparse.eval nodeValue3872 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3872) = mixedMoment B node3872 node3872Labels := rfl
  simpa [nodeValue3872, Sparse.eval] using hc.symm

theorem sound3875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3875 node3875Labels = Sparse.eval nodeValue3875 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3875) = mixedMoment B node3875 node3875Labels := rfl
  simpa [nodeValue3875, Sparse.eval] using hc.symm

theorem sound3878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3878 node3878Labels = Sparse.eval nodeValue3878 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3878) = mixedMoment B node3878 node3878Labels := rfl
  simpa [nodeValue3878, Sparse.eval] using hc.symm

theorem sound3880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3880 node3880Labels = Sparse.eval nodeValue3880 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3880) = mixedMoment B node3880 node3880Labels := rfl
  simpa [nodeValue3880, Sparse.eval] using hc.symm

theorem sound3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3899 node3899Labels = Sparse.eval nodeValue3899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3899) = mixedMoment B node3899 node3899Labels := rfl
  simpa [nodeValue3899, Sparse.eval] using hc.symm

theorem sound3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3901 node3901Labels = Sparse.eval nodeValue3901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3901) = mixedMoment B node3901 node3901Labels := rfl
  simpa [nodeValue3901, Sparse.eval] using hc.symm

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

theorem sound3922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3922 node3922Labels = Sparse.eval nodeValue3922 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3922) = mixedMoment B node3922 node3922Labels := rfl
  simpa [nodeValue3922, Sparse.eval] using hc.symm

theorem sound3964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3964 node3964Labels = Sparse.eval nodeValue3964 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3964) = mixedMoment B node3964 node3964Labels := rfl
  simpa [nodeValue3964, Sparse.eval] using hc.symm

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

theorem sound3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3972 node3972Labels = Sparse.eval nodeValue3972 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3972) = mixedMoment B node3972 node3972Labels := rfl
  simpa [nodeValue3972, Sparse.eval] using hc.symm

theorem sound3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3974 node3974Labels = Sparse.eval nodeValue3974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3974) = mixedMoment B node3974 node3974Labels := rfl
  simpa [nodeValue3974, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources27
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm879 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA879 + difference 5 0) (sourceB879 + difference 0 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA879 + difference 5 0) (sourceB879 + difference 0 5) sourceC879) = raw14579 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14579; decide +kernel
    rw [ha]
    exact (canonical14579 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA879 + difference 5 1) (sourceB879 + difference 1 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3168) := by
    have ha : (tripleCharges (sourceA879 + difference 5 1) (sourceB879 + difference 1 5) sourceC879) = raw14560 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14560; decide +kernel
    rw [ha]
    exact (canonical14560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA879 + difference 5 2) (sourceB879 + difference 2 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3170) := by
    have ha : (tripleCharges (sourceA879 + difference 5 2) (sourceB879 + difference 2 5) sourceC879) = raw14568 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14568; decide +kernel
    rw [ha]
    exact (canonical14568 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA879 + difference 5 3) (sourceB879 + difference 3 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3175) := by
    have ha : (tripleCharges (sourceA879 + difference 5 3) (sourceB879 + difference 3 5) sourceC879) = raw14574 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14574; decide +kernel
    rw [ha]
    exact (canonical14574 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA879 + difference 5 4) (sourceB879 + difference 4 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3196) := by
    have ha : (tripleCharges (sourceA879 + difference 5 4) (sourceB879 + difference 4 5) sourceC879) = raw14578 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14578; decide +kernel
    rw [ha]
    exact (canonical14578 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA879 + difference 5 5) (sourceB879 + difference 5 5) sourceC879) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA879 + difference 5 5) (sourceB879 + difference 5 5) sourceC879) = raw14550 := by
      apply Matrix.ext; unfold tripleCharges sourceA879 sourceB879 sourceC879 difference raw14550; decide +kernel
    rw [ha]
    exact (canonical14550 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA879 + sourceB879) sourceC879) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA879 + sourceB879) sourceC879) = raw14556 := by
      apply Matrix.ext; unfold doubleCharges sourceA879 sourceB879 sourceC879 raw14556; decide +kernel
    rw [ha]
    exact (canonical14556 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA879 sourceB879 sourceC879
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm879, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm883 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA883 + difference 0 0) (sourceB883 + difference 0 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA883 + difference 0 0) (sourceB883 + difference 0 0) sourceC883) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA883 + difference 0 1) (sourceB883 + difference 1 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA883 + difference 0 1) (sourceB883 + difference 1 0) sourceC883) = raw14671 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14671; decide +kernel
    rw [ha]
    exact (canonical14671 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA883 + difference 0 2) (sourceB883 + difference 2 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA883 + difference 0 2) (sourceB883 + difference 2 0) sourceC883) = raw14672 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14672; decide +kernel
    rw [ha]
    exact (canonical14672 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA883 + difference 0 3) (sourceB883 + difference 3 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA883 + difference 0 3) (sourceB883 + difference 3 0) sourceC883) = raw14673 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14673; decide +kernel
    rw [ha]
    exact (canonical14673 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA883 + difference 0 4) (sourceB883 + difference 4 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA883 + difference 0 4) (sourceB883 + difference 4 0) sourceC883) = raw14674 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14674; decide +kernel
    rw [ha]
    exact (canonical14674 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA883 + difference 0 5) (sourceB883 + difference 5 0) sourceC883) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3974) := by
    have ha : (tripleCharges (sourceA883 + difference 0 5) (sourceB883 + difference 5 0) sourceC883) = raw14675 := by
      apply Matrix.ext; unfold tripleCharges sourceA883 sourceB883 sourceC883 difference raw14675; decide +kernel
    rw [ha]
    exact (canonical14675 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA883 + sourceB883) sourceC883) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA883 + sourceB883) sourceC883) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA883 sourceB883 sourceC883 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA883 sourceB883 sourceC883
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm883, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm884 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA884 + difference 0 0) (sourceB884 + difference 0 0) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA884 + difference 0 0) (sourceB884 + difference 0 0) sourceC884) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA884 + difference 1 0) (sourceB884 + difference 0 1) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA884 + difference 1 0) (sourceB884 + difference 0 1) sourceC884) = raw14677 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14677; decide +kernel
    rw [ha]
    exact (canonical14677 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA884 + difference 2 0) (sourceB884 + difference 0 2) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA884 + difference 2 0) (sourceB884 + difference 0 2) sourceC884) = raw14678 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14678; decide +kernel
    rw [ha]
    exact (canonical14678 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA884 + difference 3 0) (sourceB884 + difference 0 3) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3195) := by
    have ha : (tripleCharges (sourceA884 + difference 3 0) (sourceB884 + difference 0 3) sourceC884) = raw14679 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14679; decide +kernel
    rw [ha]
    exact (canonical14679 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA884 + difference 4 0) (sourceB884 + difference 0 4) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2919) := by
    have ha : (tripleCharges (sourceA884 + difference 4 0) (sourceB884 + difference 0 4) sourceC884) = raw14680 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14680; decide +kernel
    rw [ha]
    exact (canonical14680 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA884 + difference 5 0) (sourceB884 + difference 0 5) sourceC884) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2611) := by
    have ha : (tripleCharges (sourceA884 + difference 5 0) (sourceB884 + difference 0 5) sourceC884) = raw14681 := by
      apply Matrix.ext; unfold tripleCharges sourceA884 sourceB884 sourceC884 difference raw14681; decide +kernel
    rw [ha]
    exact (canonical14681 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA884 + sourceB884) sourceC884) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA884 + sourceB884) sourceC884) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA884 sourceB884 sourceC884 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA884 sourceB884 sourceC884
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm884, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm885 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA885 + difference 1 0) (sourceB885 + difference 0 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA885 + difference 1 0) (sourceB885 + difference 0 1) sourceC885) = raw14677 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14677; decide +kernel
    rw [ha]
    exact (canonical14677 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA885 + difference 1 1) (sourceB885 + difference 1 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA885 + difference 1 1) (sourceB885 + difference 1 1) sourceC885) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA885 + difference 1 2) (sourceB885 + difference 2 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA885 + difference 1 2) (sourceB885 + difference 2 1) sourceC885) = raw14682 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14682; decide +kernel
    rw [ha]
    exact (canonical14682 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA885 + difference 1 3) (sourceB885 + difference 3 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA885 + difference 1 3) (sourceB885 + difference 3 1) sourceC885) = raw14683 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14683; decide +kernel
    rw [ha]
    exact (canonical14683 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA885 + difference 1 4) (sourceB885 + difference 4 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA885 + difference 1 4) (sourceB885 + difference 4 1) sourceC885) = raw14684 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14684; decide +kernel
    rw [ha]
    exact (canonical14684 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA885 + difference 1 5) (sourceB885 + difference 5 1) sourceC885) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3964) := by
    have ha : (tripleCharges (sourceA885 + difference 1 5) (sourceB885 + difference 5 1) sourceC885) = raw14685 := by
      apply Matrix.ext; unfold tripleCharges sourceA885 sourceB885 sourceC885 difference raw14685; decide +kernel
    rw [ha]
    exact (canonical14685 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA885 + sourceB885) sourceC885) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA885 + sourceB885) sourceC885) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA885 sourceB885 sourceC885 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA885 sourceB885 sourceC885
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm885, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm886 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA886 + difference 0 1) (sourceB886 + difference 1 0) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA886 + difference 0 1) (sourceB886 + difference 1 0) sourceC886) = raw14671 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14671; decide +kernel
    rw [ha]
    exact (canonical14671 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA886 + difference 1 1) (sourceB886 + difference 1 1) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA886 + difference 1 1) (sourceB886 + difference 1 1) sourceC886) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA886 + difference 2 1) (sourceB886 + difference 1 2) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA886 + difference 2 1) (sourceB886 + difference 1 2) sourceC886) = raw14686 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14686; decide +kernel
    rw [ha]
    exact (canonical14686 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA886 + difference 3 1) (sourceB886 + difference 1 3) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3863) := by
    have ha : (tripleCharges (sourceA886 + difference 3 1) (sourceB886 + difference 1 3) sourceC886) = raw14687 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14687; decide +kernel
    rw [ha]
    exact (canonical14687 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA886 + difference 4 1) (sourceB886 + difference 1 4) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2945) := by
    have ha : (tripleCharges (sourceA886 + difference 4 1) (sourceB886 + difference 1 4) sourceC886) = raw14688 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14688; decide +kernel
    rw [ha]
    exact (canonical14688 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA886 + difference 5 1) (sourceB886 + difference 1 5) sourceC886) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2612) := by
    have ha : (tripleCharges (sourceA886 + difference 5 1) (sourceB886 + difference 1 5) sourceC886) = raw14689 := by
      apply Matrix.ext; unfold tripleCharges sourceA886 sourceB886 sourceC886 difference raw14689; decide +kernel
    rw [ha]
    exact (canonical14689 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA886 + sourceB886) sourceC886) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA886 + sourceB886) sourceC886) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA886 sourceB886 sourceC886 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA886 sourceB886 sourceC886
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm886, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm887 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA887 + difference 2 0) (sourceB887 + difference 0 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA887 + difference 2 0) (sourceB887 + difference 0 2) sourceC887) = raw14678 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14678; decide +kernel
    rw [ha]
    exact (canonical14678 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA887 + difference 2 1) (sourceB887 + difference 1 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3783) := by
    have ha : (tripleCharges (sourceA887 + difference 2 1) (sourceB887 + difference 1 2) sourceC887) = raw14686 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14686; decide +kernel
    rw [ha]
    exact (canonical14686 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA887 + difference 2 2) (sourceB887 + difference 2 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA887 + difference 2 2) (sourceB887 + difference 2 2) sourceC887) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA887 + difference 2 3) (sourceB887 + difference 3 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA887 + difference 2 3) (sourceB887 + difference 3 2) sourceC887) = raw14690 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14690; decide +kernel
    rw [ha]
    exact (canonical14690 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA887 + difference 2 4) (sourceB887 + difference 4 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA887 + difference 2 4) (sourceB887 + difference 4 2) sourceC887) = raw14691 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14691; decide +kernel
    rw [ha]
    exact (canonical14691 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA887 + difference 2 5) (sourceB887 + difference 5 2) sourceC887) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3972) := by
    have ha : (tripleCharges (sourceA887 + difference 2 5) (sourceB887 + difference 5 2) sourceC887) = raw14692 := by
      apply Matrix.ext; unfold tripleCharges sourceA887 sourceB887 sourceC887 difference raw14692; decide +kernel
    rw [ha]
    exact (canonical14692 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA887 + sourceB887) sourceC887) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA887 + sourceB887) sourceC887) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA887 sourceB887 sourceC887 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA887 sourceB887 sourceC887
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm887, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq888 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm888 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA888 + difference 0 2) (sourceB888 + difference 2 0) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3880) := by
    have ha : (tripleCharges (sourceA888 + difference 0 2) (sourceB888 + difference 2 0) sourceC888) = raw14672 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14672; decide +kernel
    rw [ha]
    exact (canonical14672 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA888 + difference 1 2) (sourceB888 + difference 2 1) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3878) := by
    have ha : (tripleCharges (sourceA888 + difference 1 2) (sourceB888 + difference 2 1) sourceC888) = raw14682 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14682; decide +kernel
    rw [ha]
    exact (canonical14682 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA888 + difference 2 2) (sourceB888 + difference 2 2) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA888 + difference 2 2) (sourceB888 + difference 2 2) sourceC888) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA888 + difference 3 2) (sourceB888 + difference 2 3) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3865) := by
    have ha : (tripleCharges (sourceA888 + difference 3 2) (sourceB888 + difference 2 3) sourceC888) = raw14693 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14693; decide +kernel
    rw [ha]
    exact (canonical14693 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA888 + difference 4 2) (sourceB888 + difference 2 4) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2920) := by
    have ha : (tripleCharges (sourceA888 + difference 4 2) (sourceB888 + difference 2 4) sourceC888) = raw14694 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14694; decide +kernel
    rw [ha]
    exact (canonical14694 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA888 + difference 5 2) (sourceB888 + difference 2 5) sourceC888) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2623) := by
    have ha : (tripleCharges (sourceA888 + difference 5 2) (sourceB888 + difference 2 5) sourceC888) = raw14695 := by
      apply Matrix.ext; unfold tripleCharges sourceA888 sourceB888 sourceC888 difference raw14695; decide +kernel
    rw [ha]
    exact (canonical14695 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA888 + sourceB888) sourceC888) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA888 + sourceB888) sourceC888) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA888 sourceB888 sourceC888 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA888 sourceB888 sourceC888
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm888, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq889 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm889 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA889 + difference 3 0) (sourceB889 + difference 0 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3195) := by
    have ha : (tripleCharges (sourceA889 + difference 3 0) (sourceB889 + difference 0 3) sourceC889) = raw14679 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14679; decide +kernel
    rw [ha]
    exact (canonical14679 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA889 + difference 3 1) (sourceB889 + difference 1 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3863) := by
    have ha : (tripleCharges (sourceA889 + difference 3 1) (sourceB889 + difference 1 3) sourceC889) = raw14687 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14687; decide +kernel
    rw [ha]
    exact (canonical14687 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA889 + difference 3 2) (sourceB889 + difference 2 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3865) := by
    have ha : (tripleCharges (sourceA889 + difference 3 2) (sourceB889 + difference 2 3) sourceC889) = raw14693 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14693; decide +kernel
    rw [ha]
    exact (canonical14693 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA889 + difference 3 3) (sourceB889 + difference 3 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA889 + difference 3 3) (sourceB889 + difference 3 3) sourceC889) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA889 + difference 3 4) (sourceB889 + difference 4 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA889 + difference 3 4) (sourceB889 + difference 4 3) sourceC889) = raw14696 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14696; decide +kernel
    rw [ha]
    exact (canonical14696 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA889 + difference 3 5) (sourceB889 + difference 5 3) sourceC889) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3922) := by
    have ha : (tripleCharges (sourceA889 + difference 3 5) (sourceB889 + difference 5 3) sourceC889) = raw14697 := by
      apply Matrix.ext; unfold tripleCharges sourceA889 sourceB889 sourceC889 difference raw14697; decide +kernel
    rw [ha]
    exact (canonical14697 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA889 + sourceB889) sourceC889) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA889 + sourceB889) sourceC889) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA889 sourceB889 sourceC889 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA889 sourceB889 sourceC889
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm889, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq890 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm890 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA890 + difference 0 3) (sourceB890 + difference 3 0) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3875) := by
    have ha : (tripleCharges (sourceA890 + difference 0 3) (sourceB890 + difference 3 0) sourceC890) = raw14673 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14673; decide +kernel
    rw [ha]
    exact (canonical14673 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA890 + difference 1 3) (sourceB890 + difference 3 1) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA890 + difference 1 3) (sourceB890 + difference 3 1) sourceC890) = raw14683 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14683; decide +kernel
    rw [ha]
    exact (canonical14683 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA890 + difference 2 3) (sourceB890 + difference 3 2) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3789) := by
    have ha : (tripleCharges (sourceA890 + difference 2 3) (sourceB890 + difference 3 2) sourceC890) = raw14690 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14690; decide +kernel
    rw [ha]
    exact (canonical14690 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA890 + difference 3 3) (sourceB890 + difference 3 3) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA890 + difference 3 3) (sourceB890 + difference 3 3) sourceC890) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA890 + difference 4 3) (sourceB890 + difference 3 4) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA890 + difference 4 3) (sourceB890 + difference 3 4) sourceC890) = raw14698 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14698; decide +kernel
    rw [ha]
    exact (canonical14698 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA890 + difference 5 3) (sourceB890 + difference 3 5) sourceC890) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2617) := by
    have ha : (tripleCharges (sourceA890 + difference 5 3) (sourceB890 + difference 3 5) sourceC890) = raw14699 := by
      apply Matrix.ext; unfold tripleCharges sourceA890 sourceB890 sourceC890 difference raw14699; decide +kernel
    rw [ha]
    exact (canonical14699 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA890 + sourceB890) sourceC890) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA890 + sourceB890) sourceC890) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA890 sourceB890 sourceC890 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA890 sourceB890 sourceC890
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm890, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq891 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm891 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA891 + difference 4 0) (sourceB891 + difference 0 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2919) := by
    have ha : (tripleCharges (sourceA891 + difference 4 0) (sourceB891 + difference 0 4) sourceC891) = raw14680 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14680; decide +kernel
    rw [ha]
    exact (canonical14680 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA891 + difference 4 1) (sourceB891 + difference 1 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2945) := by
    have ha : (tripleCharges (sourceA891 + difference 4 1) (sourceB891 + difference 1 4) sourceC891) = raw14688 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14688; decide +kernel
    rw [ha]
    exact (canonical14688 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA891 + difference 4 2) (sourceB891 + difference 2 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2920) := by
    have ha : (tripleCharges (sourceA891 + difference 4 2) (sourceB891 + difference 2 4) sourceC891) = raw14694 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14694; decide +kernel
    rw [ha]
    exact (canonical14694 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA891 + difference 4 3) (sourceB891 + difference 3 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3069) := by
    have ha : (tripleCharges (sourceA891 + difference 4 3) (sourceB891 + difference 3 4) sourceC891) = raw14698 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14698; decide +kernel
    rw [ha]
    exact (canonical14698 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA891 + difference 4 4) (sourceB891 + difference 4 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3872) := by
    have ha : (tripleCharges (sourceA891 + difference 4 4) (sourceB891 + difference 4 4) sourceC891) = raw14670 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14670; decide +kernel
    rw [ha]
    exact (canonical14670 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA891 + difference 4 5) (sourceB891 + difference 5 4) sourceC891) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA891 + difference 4 5) (sourceB891 + difference 5 4) sourceC891) = raw14700 := by
      apply Matrix.ext; unfold tripleCharges sourceA891 sourceB891 sourceC891 difference raw14700; decide +kernel
    rw [ha]
    exact (canonical14700 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA891 + sourceB891) sourceC891) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA891 + sourceB891) sourceC891) = raw14676 := by
      apply Matrix.ext; unfold doubleCharges sourceA891 sourceB891 sourceC891 raw14676; decide +kernel
    rw [ha]
    exact (canonical14676 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA891 sourceB891 sourceC891
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm891, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq895 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm895 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA895 + difference 0 0) (sourceB895 + difference 0 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA895 + difference 0 0) (sourceB895 + difference 0 0) sourceC895) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA895 + difference 0 1) (sourceB895 + difference 1 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA895 + difference 0 1) (sourceB895 + difference 1 0) sourceC895) = raw14792 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14792; decide +kernel
    rw [ha]
    exact (canonical14792 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA895 + difference 0 2) (sourceB895 + difference 2 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3730) := by
    have ha : (tripleCharges (sourceA895 + difference 0 2) (sourceB895 + difference 2 0) sourceC895) = raw14793 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14793; decide +kernel
    rw [ha]
    exact (canonical14793 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA895 + difference 0 3) (sourceB895 + difference 3 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA895 + difference 0 3) (sourceB895 + difference 3 0) sourceC895) = raw14794 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14794; decide +kernel
    rw [ha]
    exact (canonical14794 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA895 + difference 0 4) (sourceB895 + difference 4 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3843) := by
    have ha : (tripleCharges (sourceA895 + difference 0 4) (sourceB895 + difference 4 0) sourceC895) = raw14795 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14795; decide +kernel
    rw [ha]
    exact (canonical14795 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA895 + difference 0 5) (sourceB895 + difference 5 0) sourceC895) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2587) := by
    have ha : (tripleCharges (sourceA895 + difference 0 5) (sourceB895 + difference 5 0) sourceC895) = raw14796 := by
      apply Matrix.ext; unfold tripleCharges sourceA895 sourceB895 sourceC895 difference raw14796; decide +kernel
    rw [ha]
    exact (canonical14796 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA895 + sourceB895) sourceC895) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA895 + sourceB895) sourceC895) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA895 sourceB895 sourceC895 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA895 sourceB895 sourceC895
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm895, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources28
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm896 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA896 + difference 1 0) (sourceB896 + difference 0 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA896 + difference 1 0) (sourceB896 + difference 0 1) sourceC896) = raw14798 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14798; decide +kernel
    rw [ha]
    exact (canonical14798 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA896 + difference 1 1) (sourceB896 + difference 1 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA896 + difference 1 1) (sourceB896 + difference 1 1) sourceC896) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA896 + difference 1 2) (sourceB896 + difference 2 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3729) := by
    have ha : (tripleCharges (sourceA896 + difference 1 2) (sourceB896 + difference 2 1) sourceC896) = raw14799 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14799; decide +kernel
    rw [ha]
    exact (canonical14799 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA896 + difference 1 3) (sourceB896 + difference 3 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA896 + difference 1 3) (sourceB896 + difference 3 1) sourceC896) = raw14800 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14800; decide +kernel
    rw [ha]
    exact (canonical14800 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA896 + difference 1 4) (sourceB896 + difference 4 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA896 + difference 1 4) (sourceB896 + difference 4 1) sourceC896) = raw14801 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14801; decide +kernel
    rw [ha]
    exact (canonical14801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA896 + difference 1 5) (sourceB896 + difference 5 1) sourceC896) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA896 + difference 1 5) (sourceB896 + difference 5 1) sourceC896) = raw14802 := by
      apply Matrix.ext; unfold tripleCharges sourceA896 sourceB896 sourceC896 difference raw14802; decide +kernel
    rw [ha]
    exact (canonical14802 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA896 + sourceB896) sourceC896) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA896 + sourceB896) sourceC896) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA896 sourceB896 sourceC896 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA896 sourceB896 sourceC896
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm896, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm897 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA897 + difference 0 1) (sourceB897 + difference 1 0) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3848) := by
    have ha : (tripleCharges (sourceA897 + difference 0 1) (sourceB897 + difference 1 0) sourceC897) = raw14792 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14792; decide +kernel
    rw [ha]
    exact (canonical14792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA897 + difference 1 1) (sourceB897 + difference 1 1) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA897 + difference 1 1) (sourceB897 + difference 1 1) sourceC897) = raw14791 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14791; decide +kernel
    rw [ha]
    exact (canonical14791 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA897 + difference 2 1) (sourceB897 + difference 1 2) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA897 + difference 2 1) (sourceB897 + difference 1 2) sourceC897) = raw14803 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14803; decide +kernel
    rw [ha]
    exact (canonical14803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA897 + difference 3 1) (sourceB897 + difference 1 3) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3780) := by
    have ha : (tripleCharges (sourceA897 + difference 3 1) (sourceB897 + difference 1 3) sourceC897) = raw14804 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14804; decide +kernel
    rw [ha]
    exact (canonical14804 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA897 + difference 4 1) (sourceB897 + difference 1 4) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA897 + difference 4 1) (sourceB897 + difference 1 4) sourceC897) = raw14805 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14805; decide +kernel
    rw [ha]
    exact (canonical14805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA897 + difference 5 1) (sourceB897 + difference 1 5) sourceC897) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3781) := by
    have ha : (tripleCharges (sourceA897 + difference 5 1) (sourceB897 + difference 1 5) sourceC897) = raw14806 := by
      apply Matrix.ext; unfold tripleCharges sourceA897 sourceB897 sourceC897 difference raw14806; decide +kernel
    rw [ha]
    exact (canonical14806 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA897 + sourceB897) sourceC897) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA897 + sourceB897) sourceC897) = raw14797 := by
      apply Matrix.ext; unfold doubleCharges sourceA897 sourceB897 sourceC897 raw14797; decide +kernel
    rw [ha]
    exact (canonical14797 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA897 sourceB897 sourceC897
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm897, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck768 : Integer.Sparse.reindex keyMap MixedData.row768 = numericRow768 := by decide +kernel

theorem numericCheck768 (x : Master → ℝ) : Integer.Sparse.eval numericRow768 x =
    (1 : ℝ) * reducedSource768 x := by
  norm_num [numericRow768, reducedSource768, Integer.Sparse.eval, Sparse.eval, nodeValue2544, nodeValue3168, nodeValue3170, nodeValue3175, nodeValue3196, nodeValue3839, nodeValue4092]

theorem reindexCheck770 : Integer.Sparse.reindex keyMap MixedData.row770 = numericRow770 := by decide +kernel

theorem numericCheck770 (x : Master → ℝ) : Integer.Sparse.eval numericRow770 x =
    (1 : ℝ) * reducedSource770 x := by
  norm_num [numericRow770, reducedSource770, Integer.Sparse.eval, Sparse.eval, nodeValue3871, nodeValue3872, nodeValue3875, nodeValue3880, nodeValue3901, nodeValue3974, nodeValue4091]

theorem reindexCheck771 : Integer.Sparse.reindex keyMap MixedData.row771 = numericRow771 := by decide +kernel

theorem numericCheck771 (x : Master → ℝ) : Integer.Sparse.eval numericRow771 x =
    (1 : ℝ) * reducedSource771 x := by
  norm_num [numericRow771, reducedSource771, Integer.Sparse.eval, Sparse.eval, nodeValue2611, nodeValue2919, nodeValue3195, nodeValue3197, nodeValue3202, nodeValue3872, nodeValue4091]

theorem reindexCheck772 : Integer.Sparse.reindex keyMap MixedData.row772 = numericRow772 := by decide +kernel

theorem numericCheck772 (x : Master → ℝ) : Integer.Sparse.eval numericRow772 x =
    (1 : ℝ) * reducedSource772 x := by
  norm_num [numericRow772, reducedSource772, Integer.Sparse.eval, Sparse.eval, nodeValue3197, nodeValue3872, nodeValue3878, nodeValue3899, nodeValue3964, nodeValue4091]

theorem reindexCheck773 : Integer.Sparse.reindex keyMap MixedData.row773 = numericRow773 := by decide +kernel

theorem numericCheck773 (x : Master → ℝ) : Integer.Sparse.eval numericRow773 x =
    (1 : ℝ) * reducedSource773 x := by
  norm_num [numericRow773, reducedSource773, Integer.Sparse.eval, Sparse.eval, nodeValue2612, nodeValue2945, nodeValue3783, nodeValue3863, nodeValue3871, nodeValue3872, nodeValue4091]

theorem reindexCheck774 : Integer.Sparse.reindex keyMap MixedData.row774 = numericRow774 := by decide +kernel

theorem numericCheck774 (x : Master → ℝ) : Integer.Sparse.eval numericRow774 x =
    (1 : ℝ) * reducedSource774 x := by
  norm_num [numericRow774, reducedSource774, Integer.Sparse.eval, Sparse.eval, nodeValue3202, nodeValue3783, nodeValue3789, nodeValue3801, nodeValue3872, nodeValue3972, nodeValue4091]

theorem reindexCheck775 : Integer.Sparse.reindex keyMap MixedData.row775 = numericRow775 := by decide +kernel

theorem numericCheck775 (x : Master → ℝ) : Integer.Sparse.eval numericRow775 x =
    (1 : ℝ) * reducedSource775 x := by
  norm_num [numericRow775, reducedSource775, Integer.Sparse.eval, Sparse.eval, nodeValue2623, nodeValue2920, nodeValue3865, nodeValue3872, nodeValue3878, nodeValue3880, nodeValue4091]

theorem reindexCheck776 : Integer.Sparse.reindex keyMap MixedData.row776 = numericRow776 := by decide +kernel

theorem numericCheck776 (x : Master → ℝ) : Integer.Sparse.eval numericRow776 x =
    (1 : ℝ) * reducedSource776 x := by
  norm_num [numericRow776, reducedSource776, Integer.Sparse.eval, Sparse.eval, nodeValue3195, nodeValue3863, nodeValue3865, nodeValue3872, nodeValue3922, nodeValue4091]

theorem reindexCheck777 : Integer.Sparse.reindex keyMap MixedData.row777 = numericRow777 := by decide +kernel

theorem numericCheck777 (x : Master → ℝ) : Integer.Sparse.eval numericRow777 x =
    (1 : ℝ) * reducedSource777 x := by
  norm_num [numericRow777, reducedSource777, Integer.Sparse.eval, Sparse.eval, nodeValue2617, nodeValue3069, nodeValue3789, nodeValue3872, nodeValue3875, nodeValue4091]

theorem reindexCheck778 : Integer.Sparse.reindex keyMap MixedData.row778 = numericRow778 := by decide +kernel

theorem numericCheck778 (x : Master → ℝ) : Integer.Sparse.eval numericRow778 x =
    (1 : ℝ) * reducedSource778 x := by
  norm_num [numericRow778, reducedSource778, Integer.Sparse.eval, Sparse.eval, nodeValue2919, nodeValue2920, nodeValue2928, nodeValue2945, nodeValue3069, nodeValue3872, nodeValue4091]

theorem reindexCheck781 : Integer.Sparse.reindex keyMap MixedData.row781 = numericRow781 := by decide +kernel

theorem numericCheck781 (x : Master → ℝ) : Integer.Sparse.eval numericRow781 x =
    (1 : ℝ) * reducedSource781 x := by
  norm_num [numericRow781, reducedSource781, Integer.Sparse.eval, Sparse.eval, nodeValue2587, nodeValue3730, nodeValue3840, nodeValue3843, nodeValue3848, nodeValue3857, nodeValue4092]

theorem reindexCheck782 : Integer.Sparse.reindex keyMap MixedData.row782 = numericRow782 := by decide +kernel

theorem numericCheck782 (x : Master → ℝ) : Integer.Sparse.eval numericRow782 x =
    (1 : ℝ) * reducedSource782 x := by
  norm_num [numericRow782, reducedSource782, Integer.Sparse.eval, Sparse.eval, nodeValue2577, nodeValue3729, nodeValue3840, nodeValue3854, nodeValue4092]

theorem reindexCheck783 : Integer.Sparse.reindex keyMap MixedData.row783 = numericRow783 := by decide +kernel

theorem numericCheck783 (x : Master → ℝ) : Integer.Sparse.eval numericRow783 x =
    (1 : ℝ) * reducedSource783 x := by
  norm_num [numericRow783, reducedSource783, Integer.Sparse.eval, Sparse.eval, nodeValue2974, nodeValue3780, nodeValue3781, nodeValue3813, nodeValue3840, nodeValue3848, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource768 (mixedVector B) = 0 := by
  have h2544 : mixedVector B (Sum.inr 2544) = Sparse.eval nodeValue2544 (mixedVector B) := by
    change mixedMoment B node2544 node2544Labels = _
    exact sound2544 B hB hF
  have h3168 : mixedVector B (Sum.inr 3168) = Sparse.eval nodeValue3168 (mixedVector B) := by
    change mixedMoment B node3168 node3168Labels = _
    exact sound3168 B hB hF
  have h3170 : mixedVector B (Sum.inr 3170) = Sparse.eval nodeValue3170 (mixedVector B) := by
    change mixedMoment B node3170 node3170Labels = _
    exact sound3170 B hB hF
  have h3175 : mixedVector B (Sum.inr 3175) = Sparse.eval nodeValue3175 (mixedVector B) := by
    change mixedMoment B node3175 node3175Labels = _
    exact sound3175 B hB hF
  have h3196 : mixedVector B (Sum.inr 3196) = Sparse.eval nodeValue3196 (mixedVector B) := by
    change mixedMoment B node3196 node3196Labels = _
    exact sound3196 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm879, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2544, h3168, h3170, h3175, h3196, h3839, h4092, reducedSource768] using sourceEq879 B hB

theorem rowSound768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row768 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck768, numericCheck768, reducedZero768 B hB hF, mul_zero]

theorem reducedZero770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource770 (mixedVector B) = 0 := by
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h3974 : mixedVector B (Sum.inr 3974) = Sparse.eval nodeValue3974 (mixedVector B) := by
    change mixedMoment B node3974 node3974Labels = _
    exact sound3974 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm883, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3871, h3872, h3875, h3880, h3901, h3974, h4091, reducedSource770] using sourceEq883 B hB

theorem rowSound770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row770 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck770, numericCheck770, reducedZero770 B hB hF, mul_zero]

theorem reducedZero771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource771 (mixedVector B) = 0 := by
  have h2611 : mixedVector B (Sum.inr 2611) = Sparse.eval nodeValue2611 (mixedVector B) := by
    change mixedMoment B node2611 node2611Labels = _
    exact sound2611 B hB hF
  have h2919 : mixedVector B (Sum.inr 2919) = Sparse.eval nodeValue2919 (mixedVector B) := by
    change mixedMoment B node2919 node2919Labels = _
    exact sound2919 B hB hF
  have h3195 : mixedVector B (Sum.inr 3195) = Sparse.eval nodeValue3195 (mixedVector B) := by
    change mixedMoment B node3195 node3195Labels = _
    exact sound3195 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm884, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2611, h2919, h3195, h3197, h3202, h3872, h4091, reducedSource771] using sourceEq884 B hB

theorem rowSound771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row771 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck771, numericCheck771, reducedZero771 B hB hF, mul_zero]

theorem reducedZero772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource772 (mixedVector B) = 0 := by
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3964 : mixedVector B (Sum.inr 3964) = Sparse.eval nodeValue3964 (mixedVector B) := by
    change mixedMoment B node3964 node3964Labels = _
    exact sound3964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm885, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3197, h3872, h3878, h3899, h3964, h4091, reducedSource772] using sourceEq885 B hB

theorem rowSound772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row772 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck772, numericCheck772, reducedZero772 B hB hF, mul_zero]

theorem reducedZero773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource773 (mixedVector B) = 0 := by
  have h2612 : mixedVector B (Sum.inr 2612) = Sparse.eval nodeValue2612 (mixedVector B) := by
    change mixedMoment B node2612 node2612Labels = _
    exact sound2612 B hB hF
  have h2945 : mixedVector B (Sum.inr 2945) = Sparse.eval nodeValue2945 (mixedVector B) := by
    change mixedMoment B node2945 node2945Labels = _
    exact sound2945 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3863 : mixedVector B (Sum.inr 3863) = Sparse.eval nodeValue3863 (mixedVector B) := by
    change mixedMoment B node3863 node3863Labels = _
    exact sound3863 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm886, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2612, h2945, h3783, h3863, h3871, h3872, h4091, reducedSource773] using sourceEq886 B hB

theorem rowSound773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row773 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck773, numericCheck773, reducedZero773 B hB hF, mul_zero]

theorem reducedZero774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource774 (mixedVector B) = 0 := by
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3783 : mixedVector B (Sum.inr 3783) = Sparse.eval nodeValue3783 (mixedVector B) := by
    change mixedMoment B node3783 node3783Labels = _
    exact sound3783 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3972 : mixedVector B (Sum.inr 3972) = Sparse.eval nodeValue3972 (mixedVector B) := by
    change mixedMoment B node3972 node3972Labels = _
    exact sound3972 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm887, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3202, h3783, h3789, h3801, h3872, h3972, h4091, reducedSource774] using sourceEq887 B hB

theorem rowSound774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row774 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck774, numericCheck774, reducedZero774 B hB hF, mul_zero]

theorem reducedZero775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource775 (mixedVector B) = 0 := by
  have h2623 : mixedVector B (Sum.inr 2623) = Sparse.eval nodeValue2623 (mixedVector B) := by
    change mixedMoment B node2623 node2623Labels = _
    exact sound2623 B hB hF
  have h2920 : mixedVector B (Sum.inr 2920) = Sparse.eval nodeValue2920 (mixedVector B) := by
    change mixedMoment B node2920 node2920Labels = _
    exact sound2920 B hB hF
  have h3865 : mixedVector B (Sum.inr 3865) = Sparse.eval nodeValue3865 (mixedVector B) := by
    change mixedMoment B node3865 node3865Labels = _
    exact sound3865 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3878 : mixedVector B (Sum.inr 3878) = Sparse.eval nodeValue3878 (mixedVector B) := by
    change mixedMoment B node3878 node3878Labels = _
    exact sound3878 B hB hF
  have h3880 : mixedVector B (Sum.inr 3880) = Sparse.eval nodeValue3880 (mixedVector B) := by
    change mixedMoment B node3880 node3880Labels = _
    exact sound3880 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm888, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2623, h2920, h3865, h3872, h3878, h3880, h4091, reducedSource775] using sourceEq888 B hB

theorem rowSound775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row775 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck775, numericCheck775, reducedZero775 B hB hF, mul_zero]

theorem reducedZero776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource776 (mixedVector B) = 0 := by
  have h3195 : mixedVector B (Sum.inr 3195) = Sparse.eval nodeValue3195 (mixedVector B) := by
    change mixedMoment B node3195 node3195Labels = _
    exact sound3195 B hB hF
  have h3863 : mixedVector B (Sum.inr 3863) = Sparse.eval nodeValue3863 (mixedVector B) := by
    change mixedMoment B node3863 node3863Labels = _
    exact sound3863 B hB hF
  have h3865 : mixedVector B (Sum.inr 3865) = Sparse.eval nodeValue3865 (mixedVector B) := by
    change mixedMoment B node3865 node3865Labels = _
    exact sound3865 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3922 : mixedVector B (Sum.inr 3922) = Sparse.eval nodeValue3922 (mixedVector B) := by
    change mixedMoment B node3922 node3922Labels = _
    exact sound3922 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm889, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3195, h3863, h3865, h3872, h3922, h4091, reducedSource776] using sourceEq889 B hB

theorem rowSound776 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row776 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck776, numericCheck776, reducedZero776 B hB hF, mul_zero]

theorem reducedZero777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource777 (mixedVector B) = 0 := by
  have h2617 : mixedVector B (Sum.inr 2617) = Sparse.eval nodeValue2617 (mixedVector B) := by
    change mixedMoment B node2617 node2617Labels = _
    exact sound2617 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3789 : mixedVector B (Sum.inr 3789) = Sparse.eval nodeValue3789 (mixedVector B) := by
    change mixedMoment B node3789 node3789Labels = _
    exact sound3789 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h3875 : mixedVector B (Sum.inr 3875) = Sparse.eval nodeValue3875 (mixedVector B) := by
    change mixedMoment B node3875 node3875Labels = _
    exact sound3875 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm890, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2617, h3069, h3789, h3872, h3875, h4091, reducedSource777] using sourceEq890 B hB

theorem rowSound777 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row777 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck777, numericCheck777, reducedZero777 B hB hF, mul_zero]

theorem reducedZero778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource778 (mixedVector B) = 0 := by
  have h2919 : mixedVector B (Sum.inr 2919) = Sparse.eval nodeValue2919 (mixedVector B) := by
    change mixedMoment B node2919 node2919Labels = _
    exact sound2919 B hB hF
  have h2920 : mixedVector B (Sum.inr 2920) = Sparse.eval nodeValue2920 (mixedVector B) := by
    change mixedMoment B node2920 node2920Labels = _
    exact sound2920 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h2945 : mixedVector B (Sum.inr 2945) = Sparse.eval nodeValue2945 (mixedVector B) := by
    change mixedMoment B node2945 node2945Labels = _
    exact sound2945 B hB hF
  have h3069 : mixedVector B (Sum.inr 3069) = Sparse.eval nodeValue3069 (mixedVector B) := by
    change mixedMoment B node3069 node3069Labels = _
    exact sound3069 B hB hF
  have h3872 : mixedVector B (Sum.inr 3872) = Sparse.eval nodeValue3872 (mixedVector B) := by
    change mixedMoment B node3872 node3872Labels = _
    exact sound3872 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm891, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2919, h2920, h2928, h2945, h3069, h3872, h4091, reducedSource778] using sourceEq891 B hB

theorem rowSound778 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row778 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck778, numericCheck778, reducedZero778 B hB hF, mul_zero]

theorem reducedZero781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource781 (mixedVector B) = 0 := by
  have h2587 : mixedVector B (Sum.inr 2587) = Sparse.eval nodeValue2587 (mixedVector B) := by
    change mixedMoment B node2587 node2587Labels = _
    exact sound2587 B hB hF
  have h3730 : mixedVector B (Sum.inr 3730) = Sparse.eval nodeValue3730 (mixedVector B) := by
    change mixedMoment B node3730 node3730Labels = _
    exact sound3730 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3843 : mixedVector B (Sum.inr 3843) = Sparse.eval nodeValue3843 (mixedVector B) := by
    change mixedMoment B node3843 node3843Labels = _
    exact sound3843 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm895, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2587, h3730, h3840, h3843, h3848, h3857, h4092, reducedSource781] using sourceEq895 B hB

theorem rowSound781 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row781 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck781, numericCheck781, reducedZero781 B hB hF, mul_zero]

theorem reducedZero782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource782 (mixedVector B) = 0 := by
  have h2577 : mixedVector B (Sum.inr 2577) = Sparse.eval nodeValue2577 (mixedVector B) := by
    change mixedMoment B node2577 node2577Labels = _
    exact sound2577 B hB hF
  have h3729 : mixedVector B (Sum.inr 3729) = Sparse.eval nodeValue3729 (mixedVector B) := by
    change mixedMoment B node3729 node3729Labels = _
    exact sound3729 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm896, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2577, h3729, h3840, h3854, h4092, reducedSource782] using sourceEq896 B hB

theorem rowSound782 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row782 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck782, numericCheck782, reducedZero782 B hB hF, mul_zero]

theorem reducedZero783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource783 (mixedVector B) = 0 := by
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3780 : mixedVector B (Sum.inr 3780) = Sparse.eval nodeValue3780 (mixedVector B) := by
    change mixedMoment B node3780 node3780Labels = _
    exact sound3780 B hB hF
  have h3781 : mixedVector B (Sum.inr 3781) = Sparse.eval nodeValue3781 (mixedVector B) := by
    change mixedMoment B node3781 node3781Labels = _
    exact sound3781 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3848 : mixedVector B (Sum.inr 3848) = Sparse.eval nodeValue3848 (mixedVector B) := by
    change mixedMoment B node3848 node3848Labels = _
    exact sound3848 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm897, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2974, h3780, h3781, h3813, h3840, h3848, h4092, reducedSource783] using sourceEq897 B hB

theorem rowSound783 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row783 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck783, numericCheck783, reducedZero783 B hB hF, mul_zero]

theorem sourceRowsAt768 : MixedData.sourceRows (768 : Fin 2425) =
    MixedData.row768 := by decide +kernel

theorem sourceRowsAt769 : MixedData.sourceRows (769 : Fin 2425) =
    MixedData.row769 := by decide +kernel

theorem sourceRowsAt770 : MixedData.sourceRows (770 : Fin 2425) =
    MixedData.row770 := by decide +kernel

theorem sourceRowsAt771 : MixedData.sourceRows (771 : Fin 2425) =
    MixedData.row771 := by decide +kernel

theorem sourceRowsAt772 : MixedData.sourceRows (772 : Fin 2425) =
    MixedData.row772 := by decide +kernel

theorem sourceRowsAt773 : MixedData.sourceRows (773 : Fin 2425) =
    MixedData.row773 := by decide +kernel

theorem sourceRowsAt774 : MixedData.sourceRows (774 : Fin 2425) =
    MixedData.row774 := by decide +kernel

theorem sourceRowsAt775 : MixedData.sourceRows (775 : Fin 2425) =
    MixedData.row775 := by decide +kernel

theorem sourceRowsAt776 : MixedData.sourceRows (776 : Fin 2425) =
    MixedData.row776 := by decide +kernel

theorem sourceRowsAt777 : MixedData.sourceRows (777 : Fin 2425) =
    MixedData.row777 := by decide +kernel

theorem sourceRowsAt778 : MixedData.sourceRows (778 : Fin 2425) =
    MixedData.row778 := by decide +kernel

theorem sourceRowsAt779 : MixedData.sourceRows (779 : Fin 2425) =
    MixedData.row779 := by decide +kernel

theorem sourceRowsAt780 : MixedData.sourceRows (780 : Fin 2425) =
    MixedData.row780 := by decide +kernel

theorem sourceRowsAt781 : MixedData.sourceRows (781 : Fin 2425) =
    MixedData.row781 := by decide +kernel

theorem sourceRowsAt782 : MixedData.sourceRows (782 : Fin 2425) =
    MixedData.row782 := by decide +kernel

theorem sourceRowsAt783 : MixedData.sourceRows (783 : Fin 2425) =
    MixedData.row783 := by decide +kernel

theorem chunkSound48_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 48) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 768 ∨ k.val = 769 ∨ k.val = 770 ∨ k.val = 771 ∨ k.val = 772 ∨ k.val = 773 ∨ k.val = 774 ∨ k.val = 775 ∨ k.val = 776 ∨ k.val = 777 ∨ k.val = 778 ∨ k.val = 779 ∨ k.val = 780 ∨ k.val = 781 ∨ k.val = 782 ∨ k.val = 783 := by omega
  rcases heq with h768 | h769 | h770 | h771 | h772 | h773 | h774 | h775 | h776 | h777 | h778 | h779 | h780 | h781 | h782 | h783
  · have he : k = (768 : Fin 2425) := Fin.ext h768
    subst k
    rw [sourceRowsAt768]
    exact rowSound768 B hB hF
  · have he : k = (769 : Fin 2425) := Fin.ext h769
    subst k
    rw [sourceRowsAt769]
    exact rowSound769_e B hB hF
  · have he : k = (770 : Fin 2425) := Fin.ext h770
    subst k
    rw [sourceRowsAt770]
    exact rowSound770 B hB hF
  · have he : k = (771 : Fin 2425) := Fin.ext h771
    subst k
    rw [sourceRowsAt771]
    exact rowSound771 B hB hF
  · have he : k = (772 : Fin 2425) := Fin.ext h772
    subst k
    rw [sourceRowsAt772]
    exact rowSound772 B hB hF
  · have he : k = (773 : Fin 2425) := Fin.ext h773
    subst k
    rw [sourceRowsAt773]
    exact rowSound773 B hB hF
  · have he : k = (774 : Fin 2425) := Fin.ext h774
    subst k
    rw [sourceRowsAt774]
    exact rowSound774 B hB hF
  · have he : k = (775 : Fin 2425) := Fin.ext h775
    subst k
    rw [sourceRowsAt775]
    exact rowSound775 B hB hF
  · have he : k = (776 : Fin 2425) := Fin.ext h776
    subst k
    rw [sourceRowsAt776]
    exact rowSound776 B hB hF
  · have he : k = (777 : Fin 2425) := Fin.ext h777
    subst k
    rw [sourceRowsAt777]
    exact rowSound777 B hB hF
  · have he : k = (778 : Fin 2425) := Fin.ext h778
    subst k
    rw [sourceRowsAt778]
    exact rowSound778 B hB hF
  · have he : k = (779 : Fin 2425) := Fin.ext h779
    subst k
    rw [sourceRowsAt779]
    exact rowSound779_e B hB hF
  · have he : k = (780 : Fin 2425) := Fin.ext h780
    subst k
    rw [sourceRowsAt780]
    exact rowSound780_e B hB hF
  · have he : k = (781 : Fin 2425) := Fin.ext h781
    subst k
    rw [sourceRowsAt781]
    exact rowSound781 B hB hF
  · have he : k = (782 : Fin 2425) := Fin.ext h782
    subst k
    rw [sourceRowsAt782]
    exact rowSound782 B hB hF
  · have he : k = (783 : Fin 2425) := Fin.ext h783
    subst k
    rw [sourceRowsAt783]
    exact rowSound783 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound48_e_oai
