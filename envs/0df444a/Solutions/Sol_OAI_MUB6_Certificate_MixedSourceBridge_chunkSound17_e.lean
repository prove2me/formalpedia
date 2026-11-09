-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:02:06.157678+00:00
-- url     : https://prove2.me/submissions/262f263b-8db0-4b0c-b367-173872038ab2

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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound281_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound282_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound286_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound287_e

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

theorem canonical6454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6454 raw6454Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw6454 raw6454Labels = mixedMoment B raw6454step0 raw6454step0Labels := by
      have hz : ∀ j, raw6454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6454step0 = (fun i j => raw6454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6454step0 raw6454; decide +kernel
      have hl : raw6454step0Labels = raw6454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6454 raw6454Labels permutation346 hz
    mixedMoment B raw6454step0 raw6454step0Labels = mixedMoment B raw6454step1 raw6454step1Labels := by
      have ha : raw6454step1 = (fun i j => raw6454step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6454step1 raw6454step0; decide +kernel
      have hl : raw6454step1Labels = raw6454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6454step0 raw6454step0Labels permutation37 permutation4
    mixedMoment B raw6454step1 raw6454step1Labels = mixedMoment B raw6454step2 raw6454step2Labels := by
      have ha : raw6454step2 = -raw6454step1 := by apply Matrix.ext; change ∀ i j, raw6454step2 i j = -(raw6454step1 i j); unfold raw6454step2 raw6454step1; decide +kernel
      have hl : raw6454step2Labels = raw6454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical6456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6456 raw6456Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6456 raw6456Labels = mixedMoment B raw6456step0 raw6456step0Labels := by
      have hz : ∀ j, raw6456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6456step0 = (fun i j => raw6456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6456step0 raw6456; decide +kernel
      have hl : raw6456step0Labels = raw6456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6456 raw6456Labels permutation346 hz
    mixedMoment B raw6456step0 raw6456step0Labels = mixedMoment B raw6456step1 raw6456step1Labels := by
      have ha : raw6456step1 = (fun i j => raw6456step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6456step1 raw6456step0; decide +kernel
      have hl : raw6456step1Labels = raw6456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6456step0 raw6456step0Labels permutation32 permutation4
    mixedMoment B raw6456step1 raw6456step1Labels = mixedMoment B raw6456step2 raw6456step2Labels := by
      have ha : raw6456step2 = -raw6456step1 := by apply Matrix.ext; change ∀ i j, raw6456step2 i j = -(raw6456step1 i j); unfold raw6456step2 raw6456step1; decide +kernel
      have hl : raw6456step2Labels = raw6456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6784 raw6784Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6784 raw6784Labels = mixedMoment B raw6784step0 raw6784step0Labels := by
      have hz : ∀ j, raw6784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6784step0 = (fun i j => raw6784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6784step0 raw6784; decide +kernel
      have hl : raw6784step0Labels = raw6784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6784 raw6784Labels permutation346 hz
    mixedMoment B raw6784step0 raw6784step0Labels = mixedMoment B raw6784step1 raw6784step1Labels := by
      have ha : raw6784step1 = (fun i j => raw6784step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6784step1 raw6784step0; decide +kernel
      have hl : raw6784step1Labels = raw6784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6784step0 raw6784step0Labels permutation35 permutation4
    mixedMoment B raw6784step1 raw6784step1Labels = mixedMoment B raw6784step2 raw6784step2Labels := by
      have ha : raw6784step2 = -raw6784step1 := by apply Matrix.ext; change ∀ i j, raw6784step2 i j = -(raw6784step1 i j); unfold raw6784step2 raw6784step1; decide +kernel
      have hl : raw6784step2Labels = raw6784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical6785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6785 raw6785Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw6785 raw6785Labels = mixedMoment B raw6785step0 raw6785step0Labels := by
      have hz : ∀ j, raw6785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6785step0 = (fun i j => raw6785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6785step0 raw6785; decide +kernel
      have hl : raw6785step0Labels = raw6785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6785 raw6785Labels permutation346 hz
    mixedMoment B raw6785step0 raw6785step0Labels = mixedMoment B raw6785step1 raw6785step1Labels := by
      have ha : raw6785step1 = (fun i j => raw6785step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6785step1 raw6785step0; decide +kernel
      have hl : raw6785step1Labels = raw6785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6785step0 raw6785step0Labels permutation41 permutation2
    mixedMoment B raw6785step1 raw6785step1Labels = mixedMoment B raw6785step2 raw6785step2Labels := by
      have ha : raw6785step2 = -raw6785step1 := by apply Matrix.ext; change ∀ i j, raw6785step2 i j = -(raw6785step1 i j); unfold raw6785step2 raw6785step1; decide +kernel
      have hl : raw6785step2Labels = raw6785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical6786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6786 raw6786Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw6786 raw6786Labels = mixedMoment B raw6786step0 raw6786step0Labels := by
      have ha : raw6786step0 = (fun i j => raw6786 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6786step0 raw6786; decide +kernel
      have hl : raw6786step0Labels = raw6786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6786 raw6786Labels permutation200 permutation2
    mixedMoment B raw6786step0 raw6786step0Labels = mixedMoment B raw6786step1 raw6786step1Labels := by
      have ha : raw6786step1 = -raw6786step0 := by apply Matrix.ext; change ∀ i j, raw6786step1 i j = -(raw6786step0 i j); unfold raw6786step1 raw6786step0; decide +kernel
      have hl : raw6786step1Labels = raw6786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3388 node3388Labels := by rfl

theorem canonical6787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6787 raw6787Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6787 raw6787Labels = mixedMoment B raw6787step0 raw6787step0Labels := by
      have hz : ∀ j, raw6787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6787step0 = (fun i j => raw6787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6787step0 raw6787; decide +kernel
      have hl : raw6787step0Labels = raw6787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6787 raw6787Labels permutation346 hz
    mixedMoment B raw6787step0 raw6787step0Labels = mixedMoment B raw6787step1 raw6787step1Labels := by
      have ha : raw6787step1 = (fun i j => raw6787step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6787step1 raw6787step0; decide +kernel
      have hl : raw6787step1Labels = raw6787step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6787step0 raw6787step0Labels permutation38 permutation2
    mixedMoment B raw6787step1 raw6787step1Labels = mixedMoment B raw6787step2 raw6787step2Labels := by
      have ha : raw6787step2 = -raw6787step1 := by apply Matrix.ext; change ∀ i j, raw6787step2 i j = -(raw6787step1 i j); unfold raw6787step2 raw6787step1; decide +kernel
      have hl : raw6787step2Labels = raw6787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

theorem canonical6788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6788 raw6788Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw6788 raw6788Labels = mixedMoment B raw6788step0 raw6788step0Labels := by
      have hz : ∀ j, raw6788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6788step0 = (fun i j => raw6788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6788step0 raw6788; decide +kernel
      have hl : raw6788step0Labels = raw6788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6788 raw6788Labels permutation346 hz
    mixedMoment B raw6788step0 raw6788step0Labels = mixedMoment B raw6788step1 raw6788step1Labels := by
      have ha : raw6788step1 = (fun i j => raw6788step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6788step1 raw6788step0; decide +kernel
      have hl : raw6788step1Labels = raw6788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6788step0 raw6788step0Labels permutation39 permutation2
    mixedMoment B raw6788step1 raw6788step1Labels = mixedMoment B raw6788step2 raw6788step2Labels := by
      have ha : raw6788step2 = -raw6788step1 := by apply Matrix.ext; change ∀ i j, raw6788step2 i j = -(raw6788step1 i j); unfold raw6788step2 raw6788step1; decide +kernel
      have hl : raw6788step2Labels = raw6788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical6790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6790 raw6790Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw6790 raw6790Labels = mixedMoment B raw6790step0 raw6790step0Labels := by
      have hz : ∀ j, raw6790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6790step0 = (fun i j => raw6790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6790step0 raw6790; decide +kernel
      have hl : raw6790step0Labels = raw6790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790 raw6790Labels permutation346 hz
    mixedMoment B raw6790step0 raw6790step0Labels = mixedMoment B raw6790step1 raw6790step1Labels := by
      have hz : ∀ j, raw6790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6790step1 = (fun i j => raw6790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6790step1 raw6790step0; decide +kernel
      have hl : raw6790step1Labels = raw6790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790step0 raw6790step0Labels permutation56 hz
    mixedMoment B raw6790step1 raw6790step1Labels = mixedMoment B raw6790step2 raw6790step2Labels := by
      have ha : raw6790step2 = (fun i j => raw6790step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6790step2 raw6790step1; decide +kernel
      have hl : raw6790step2Labels = raw6790step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6790step1 raw6790step1Labels permutation11 permutation4
    mixedMoment B raw6790step2 raw6790step2Labels = mixedMoment B raw6790step3 raw6790step3Labels := by
      have ha : raw6790step3 = -raw6790step2 := by apply Matrix.ext; change ∀ i j, raw6790step3 i j = -(raw6790step2 i j); unfold raw6790step3 raw6790step2; decide +kernel
      have hl : raw6790step3Labels = raw6790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical6791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6791 raw6791Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw6791 raw6791Labels = mixedMoment B raw6791step0 raw6791step0Labels := by
      have ha : raw6791step0 = (fun i j => raw6791 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6791step0 raw6791; decide +kernel
      have hl : raw6791step0Labels = raw6791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6791 raw6791Labels permutation165 permutation4
    mixedMoment B raw6791step0 raw6791step0Labels = mixedMoment B raw6791step1 raw6791step1Labels := by
      have ha : raw6791step1 = -raw6791step0 := by apply Matrix.ext; change ∀ i j, raw6791step1 i j = -(raw6791step0 i j); unfold raw6791step1 raw6791step0; decide +kernel
      have hl : raw6791step1Labels = raw6791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical6792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6792 raw6792Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw6792 raw6792Labels = mixedMoment B raw6792step0 raw6792step0Labels := by
      have hz : ∀ j, raw6792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6792step0 = (fun i j => raw6792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6792step0 raw6792; decide +kernel
      have hl : raw6792step0Labels = raw6792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6792 raw6792Labels permutation346 hz
    mixedMoment B raw6792step0 raw6792step0Labels = mixedMoment B raw6792step1 raw6792step1Labels := by
      have ha : raw6792step1 = (fun i j => raw6792step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6792step1 raw6792step0; decide +kernel
      have hl : raw6792step1Labels = raw6792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6792step0 raw6792step0Labels permutation35 permutation4
    mixedMoment B raw6792step1 raw6792step1Labels = mixedMoment B raw6792step2 raw6792step2Labels := by
      have ha : raw6792step2 = -raw6792step1 := by apply Matrix.ext; change ∀ i j, raw6792step2 i j = -(raw6792step1 i j); unfold raw6792step2 raw6792step1; decide +kernel
      have hl : raw6792step2Labels = raw6792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

theorem canonical6793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6793 raw6793Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw6793 raw6793Labels = mixedMoment B raw6793step0 raw6793step0Labels := by
      have hz : ∀ j, raw6793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6793step0 = (fun i j => raw6793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6793step0 raw6793; decide +kernel
      have hl : raw6793step0Labels = raw6793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6793 raw6793Labels permutation346 hz
    mixedMoment B raw6793step0 raw6793step0Labels = mixedMoment B raw6793step1 raw6793step1Labels := by
      have ha : raw6793step1 = (fun i j => raw6793step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6793step1 raw6793step0; decide +kernel
      have hl : raw6793step1Labels = raw6793step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6793step0 raw6793step0Labels permutation35 permutation4
    mixedMoment B raw6793step1 raw6793step1Labels = mixedMoment B raw6793step2 raw6793step2Labels := by
      have ha : raw6793step2 = -raw6793step1 := by apply Matrix.ext; change ∀ i j, raw6793step2 i j = -(raw6793step1 i j); unfold raw6793step2 raw6793step1; decide +kernel
      have hl : raw6793step2Labels = raw6793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

theorem canonical6794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6794 raw6794Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw6794 raw6794Labels = mixedMoment B raw6794step0 raw6794step0Labels := by
      have hz : ∀ j, raw6794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6794step0 = (fun i j => raw6794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6794step0 raw6794; decide +kernel
      have hl : raw6794step0Labels = raw6794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6794 raw6794Labels permutation346 hz
    mixedMoment B raw6794step0 raw6794step0Labels = mixedMoment B raw6794step1 raw6794step1Labels := by
      have ha : raw6794step1 = (fun i j => raw6794step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6794step1 raw6794step0; decide +kernel
      have hl : raw6794step1Labels = raw6794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6794step0 raw6794step0Labels permutation34 permutation4
    mixedMoment B raw6794step1 raw6794step1Labels = mixedMoment B raw6794step2 raw6794step2Labels := by
      have ha : raw6794step2 = -raw6794step1 := by apply Matrix.ext; change ∀ i j, raw6794step2 i j = -(raw6794step1 i j); unfold raw6794step2 raw6794step1; decide +kernel
      have hl : raw6794step2Labels = raw6794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

theorem canonical6795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6795 raw6795Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6795 raw6795Labels = mixedMoment B raw6795step0 raw6795step0Labels := by
      have hz : ∀ j, raw6795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6795step0 = (fun i j => raw6795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6795step0 raw6795; decide +kernel
      have hl : raw6795step0Labels = raw6795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6795 raw6795Labels permutation265 hz
    mixedMoment B raw6795step0 raw6795step0Labels = mixedMoment B raw6795step1 raw6795step1Labels := by
      have ha : raw6795step1 = (fun i j => raw6795step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6795step1 raw6795step0; decide +kernel
      have hl : raw6795step1Labels = raw6795step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6795step0 raw6795step0Labels permutation35 permutation4
    mixedMoment B raw6795step1 raw6795step1Labels = mixedMoment B raw6795step2 raw6795step2Labels := by
      have ha : raw6795step2 = -raw6795step1 := by apply Matrix.ext; change ∀ i j, raw6795step2 i j = -(raw6795step1 i j); unfold raw6795step2 raw6795step1; decide +kernel
      have hl : raw6795step2Labels = raw6795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical6796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6796 raw6796Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw6796 raw6796Labels = mixedMoment B raw6796step0 raw6796step0Labels := by
      have hz : ∀ j, raw6796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6796step0 = (fun i j => raw6796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6796step0 raw6796; decide +kernel
      have hl : raw6796step0Labels = raw6796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796 raw6796Labels permutation346 hz
    mixedMoment B raw6796step0 raw6796step0Labels = mixedMoment B raw6796step1 raw6796step1Labels := by
      have hz : ∀ j, raw6796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6796step1 = (fun i j => raw6796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6796step1 raw6796step0; decide +kernel
      have hl : raw6796step1Labels = raw6796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796step0 raw6796step0Labels permutation56 hz
    mixedMoment B raw6796step1 raw6796step1Labels = mixedMoment B raw6796step2 raw6796step2Labels := by
      have ha : raw6796step2 = (fun i j => raw6796step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6796step2 raw6796step1; decide +kernel
      have hl : raw6796step2Labels = raw6796step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6796step1 raw6796step1Labels permutation10 permutation4
    mixedMoment B raw6796step2 raw6796step2Labels = mixedMoment B raw6796step3 raw6796step3Labels := by
      have ha : raw6796step3 = -raw6796step2 := by apply Matrix.ext; change ∀ i j, raw6796step3 i j = -(raw6796step2 i j); unfold raw6796step3 raw6796step2; decide +kernel
      have hl : raw6796step3Labels = raw6796step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

theorem canonical6797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6797 raw6797Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw6797 raw6797Labels = mixedMoment B raw6797step0 raw6797step0Labels := by
      have hz : ∀ j, raw6797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6797step0 = (fun i j => raw6797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6797step0 raw6797; decide +kernel
      have hl : raw6797step0Labels = raw6797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797 raw6797Labels permutation346 hz
    mixedMoment B raw6797step0 raw6797step0Labels = mixedMoment B raw6797step1 raw6797step1Labels := by
      have hz : ∀ j, raw6797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6797step1 = (fun i j => raw6797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6797step1 raw6797step0; decide +kernel
      have hl : raw6797step1Labels = raw6797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797step0 raw6797step0Labels permutation56 hz
    mixedMoment B raw6797step1 raw6797step1Labels = mixedMoment B raw6797step2 raw6797step2Labels := by
      have ha : raw6797step2 = (fun i j => raw6797step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6797step2 raw6797step1; decide +kernel
      have hl : raw6797step2Labels = raw6797step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6797step1 raw6797step1Labels permutation11 permutation4
    mixedMoment B raw6797step2 raw6797step2Labels = mixedMoment B raw6797step3 raw6797step3Labels := by
      have ha : raw6797step3 = -raw6797step2 := by apply Matrix.ext; change ∀ i j, raw6797step3 i j = -(raw6797step2 i j); unfold raw6797step3 raw6797step2; decide +kernel
      have hl : raw6797step3Labels = raw6797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical6798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6798 raw6798Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw6798 raw6798Labels = mixedMoment B raw6798step0 raw6798step0Labels := by
      have hz : ∀ j, raw6798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6798step0 = (fun i j => raw6798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6798step0 raw6798; decide +kernel
      have hl : raw6798step0Labels = raw6798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6798 raw6798Labels permutation346 hz
    mixedMoment B raw6798step0 raw6798step0Labels = mixedMoment B raw6798step1 raw6798step1Labels := by
      have hz : ∀ j, raw6798step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6798step1 = (fun i j => raw6798step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6798step1 raw6798step0; decide +kernel
      have hl : raw6798step1Labels = raw6798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6798step0 raw6798step0Labels permutation56 hz
    mixedMoment B raw6798step1 raw6798step1Labels = mixedMoment B raw6798step2 raw6798step2Labels := by
      have ha : raw6798step2 = (fun i j => raw6798step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6798step2 raw6798step1; decide +kernel
      have hl : raw6798step2Labels = raw6798step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6798step1 raw6798step1Labels permutation11 permutation4
    mixedMoment B raw6798step2 raw6798step2Labels = mixedMoment B raw6798step3 raw6798step3Labels := by
      have ha : raw6798step3 = -raw6798step2 := by apply Matrix.ext; change ∀ i j, raw6798step3 i j = -(raw6798step2 i j); unfold raw6798step3 raw6798step2; decide +kernel
      have hl : raw6798step3Labels = raw6798step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical6799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6799 raw6799Labels = mixedMoment B node3377 node3377Labels := by
  calc
    mixedMoment B raw6799 raw6799Labels = mixedMoment B raw6799step0 raw6799step0Labels := by
      have ha : raw6799step0 = (fun i j => raw6799 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6799step0 raw6799; decide +kernel
      have hl : raw6799step0Labels = raw6799Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6799 raw6799Labels permutation165 permutation4
    mixedMoment B raw6799step0 raw6799step0Labels = mixedMoment B raw6799step1 raw6799step1Labels := by
      have ha : raw6799step1 = -raw6799step0 := by apply Matrix.ext; change ∀ i j, raw6799step1 i j = -(raw6799step0 i j); unfold raw6799step1 raw6799step0; decide +kernel
      have hl : raw6799step1Labels = raw6799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3377 node3377Labels := by rfl

theorem canonical6800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6800 raw6800Labels = mixedMoment B node3159 node3159Labels := by
  calc
    mixedMoment B raw6800 raw6800Labels = mixedMoment B raw6800step0 raw6800step0Labels := by
      have hz : ∀ j, raw6800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6800step0 = (fun i j => raw6800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6800step0 raw6800; decide +kernel
      have hl : raw6800step0Labels = raw6800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6800 raw6800Labels permutation346 hz
    mixedMoment B raw6800step0 raw6800step0Labels = mixedMoment B raw6800step1 raw6800step1Labels := by
      have ha : raw6800step1 = (fun i j => raw6800step0 (permutation83 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6800step1 raw6800step0; decide +kernel
      have hl : raw6800step1Labels = raw6800step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6800step0 raw6800step0Labels permutation83 permutation2
    mixedMoment B raw6800step1 raw6800step1Labels = mixedMoment B raw6800step2 raw6800step2Labels := by
      have ha : raw6800step2 = -raw6800step1 := by apply Matrix.ext; change ∀ i j, raw6800step2 i j = -(raw6800step1 i j); unfold raw6800step2 raw6800step1; decide +kernel
      have hl : raw6800step2Labels = raw6800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3159 node3159Labels := by rfl

theorem canonical6801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6801 raw6801Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw6801 raw6801Labels = mixedMoment B raw6801step0 raw6801step0Labels := by
      have hz : ∀ j, raw6801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6801step0 = (fun i j => raw6801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6801step0 raw6801; decide +kernel
      have hl : raw6801step0Labels = raw6801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6801 raw6801Labels permutation346 hz
    mixedMoment B raw6801step0 raw6801step0Labels = mixedMoment B raw6801step1 raw6801step1Labels := by
      have ha : raw6801step1 = (fun i j => raw6801step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6801step1 raw6801step0; decide +kernel
      have hl : raw6801step1Labels = raw6801step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6801step0 raw6801step0Labels permutation35 permutation4
    mixedMoment B raw6801step1 raw6801step1Labels = mixedMoment B raw6801step2 raw6801step2Labels := by
      have ha : raw6801step2 = -raw6801step1 := by apply Matrix.ext; change ∀ i j, raw6801step2 i j = -(raw6801step1 i j); unfold raw6801step2 raw6801step1; decide +kernel
      have hl : raw6801step2Labels = raw6801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical6802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6802 raw6802Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw6802 raw6802Labels = mixedMoment B raw6802step0 raw6802step0Labels := by
      have hz : ∀ j, raw6802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6802step0 = (fun i j => raw6802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6802step0 raw6802; decide +kernel
      have hl : raw6802step0Labels = raw6802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6802 raw6802Labels permutation346 hz
    mixedMoment B raw6802step0 raw6802step0Labels = mixedMoment B raw6802step1 raw6802step1Labels := by
      have ha : raw6802step1 = (fun i j => raw6802step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6802step1 raw6802step0; decide +kernel
      have hl : raw6802step1Labels = raw6802step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6802step0 raw6802step0Labels permutation34 permutation4
    mixedMoment B raw6802step1 raw6802step1Labels = mixedMoment B raw6802step2 raw6802step2Labels := by
      have ha : raw6802step2 = -raw6802step1 := by apply Matrix.ext; change ∀ i j, raw6802step2 i j = -(raw6802step1 i j); unfold raw6802step2 raw6802step1; decide +kernel
      have hl : raw6802step2Labels = raw6802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3379 node3379Labels := by rfl

theorem canonical6803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6803 raw6803Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw6803 raw6803Labels = mixedMoment B raw6803step0 raw6803step0Labels := by
      have ha : raw6803step0 = (fun i j => raw6803 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6803step0 raw6803; decide +kernel
      have hl : raw6803step0Labels = raw6803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6803 raw6803Labels permutation164 permutation4
    mixedMoment B raw6803step0 raw6803step0Labels = mixedMoment B raw6803step1 raw6803step1Labels := by
      have ha : raw6803step1 = -raw6803step0 := by apply Matrix.ext; change ∀ i j, raw6803step1 i j = -(raw6803step0 i j); unfold raw6803step1 raw6803step0; decide +kernel
      have hl : raw6803step1Labels = raw6803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3531 node3531Labels := by rfl

theorem canonical6804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6804 raw6804Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw6804 raw6804Labels = mixedMoment B raw6804step0 raw6804step0Labels := by
      have ha : raw6804step0 = (fun i j => raw6804 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6804step0 raw6804; decide +kernel
      have hl : raw6804step0Labels = raw6804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6804 raw6804Labels permutation165 permutation4
    mixedMoment B raw6804step0 raw6804step0Labels = mixedMoment B raw6804step1 raw6804step1Labels := by
      have ha : raw6804step1 = -raw6804step0 := by apply Matrix.ext; change ∀ i j, raw6804step1 i j = -(raw6804step0 i j); unfold raw6804step1 raw6804step0; decide +kernel
      have hl : raw6804step1Labels = raw6804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

theorem canonical6805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6805 raw6805Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw6805 raw6805Labels = mixedMoment B raw6805step0 raw6805step0Labels := by
      have ha : raw6805step0 = (fun i j => raw6805 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6805step0 raw6805; decide +kernel
      have hl : raw6805step0Labels = raw6805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6805 raw6805Labels permutation168 permutation4
    mixedMoment B raw6805step0 raw6805step0Labels = mixedMoment B raw6805step1 raw6805step1Labels := by
      have ha : raw6805step1 = -raw6805step0 := by apply Matrix.ext; change ∀ i j, raw6805step1 i j = -(raw6805step0 i j); unfold raw6805step1 raw6805step0; decide +kernel
      have hl : raw6805step1Labels = raw6805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3528 node3528Labels := by rfl

theorem canonical6806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6806 raw6806Labels = mixedMoment B node3153 node3153Labels := by
  calc
    mixedMoment B raw6806 raw6806Labels = mixedMoment B raw6806step0 raw6806step0Labels := by
      have ha : raw6806step0 = (fun i j => raw6806 (permutation434 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6806step0 raw6806; decide +kernel
      have hl : raw6806step0Labels = raw6806Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6806 raw6806Labels permutation434 permutation2
    mixedMoment B raw6806step0 raw6806step0Labels = mixedMoment B raw6806step1 raw6806step1Labels := by
      have ha : raw6806step1 = -raw6806step0 := by apply Matrix.ext; change ∀ i j, raw6806step1 i j = -(raw6806step0 i j); unfold raw6806step1 raw6806step0; decide +kernel
      have hl : raw6806step1Labels = raw6806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3153 node3153Labels := by rfl

theorem canonical6807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6807 raw6807Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw6807 raw6807Labels = mixedMoment B raw6807step0 raw6807step0Labels := by
      have ha : raw6807step0 = (fun i j => raw6807 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6807step0 raw6807; decide +kernel
      have hl : raw6807step0Labels = raw6807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6807 raw6807Labels permutation155 permutation4
    mixedMoment B raw6807step0 raw6807step0Labels = mixedMoment B raw6807step1 raw6807step1Labels := by
      have ha : raw6807step1 = -raw6807step0 := by apply Matrix.ext; change ∀ i j, raw6807step1 i j = -(raw6807step0 i j); unfold raw6807step1 raw6807step0; decide +kernel
      have hl : raw6807step1Labels = raw6807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3497 node3497Labels := by rfl

theorem canonical6808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6808 raw6808Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw6808 raw6808Labels = mixedMoment B raw6808step0 raw6808step0Labels := by
      have ha : raw6808step0 = (fun i j => raw6808 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6808step0 raw6808; decide +kernel
      have hl : raw6808step0Labels = raw6808Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6808 raw6808Labels permutation154 permutation4
    mixedMoment B raw6808step0 raw6808step0Labels = mixedMoment B raw6808step1 raw6808step1Labels := by
      have ha : raw6808step1 = -raw6808step0 := by apply Matrix.ext; change ∀ i j, raw6808step1 i j = -(raw6808step0 i j); unfold raw6808step1 raw6808step0; decide +kernel
      have hl : raw6808step1Labels = raw6808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3488 node3488Labels := by rfl

theorem canonical6809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6809 raw6809Labels = mixedMoment B node3157 node3157Labels := by
  calc
    mixedMoment B raw6809 raw6809Labels = mixedMoment B raw6809step0 raw6809step0Labels := by
      have hz : ∀ j, raw6809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6809step0 = (fun i j => raw6809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6809step0 raw6809; decide +kernel
      have hl : raw6809step0Labels = raw6809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6809 raw6809Labels permutation346 hz
    mixedMoment B raw6809step0 raw6809step0Labels = mixedMoment B raw6809step1 raw6809step1Labels := by
      have ha : raw6809step1 = (fun i j => raw6809step0 (permutation81 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6809step1 raw6809step0; decide +kernel
      have hl : raw6809step1Labels = raw6809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6809step0 raw6809step0Labels permutation81 permutation2
    mixedMoment B raw6809step1 raw6809step1Labels = mixedMoment B raw6809step2 raw6809step2Labels := by
      have ha : raw6809step2 = -raw6809step1 := by apply Matrix.ext; change ∀ i j, raw6809step2 i j = -(raw6809step1 i j); unfold raw6809step2 raw6809step1; decide +kernel
      have hl : raw6809step2Labels = raw6809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3157 node3157Labels := by rfl

theorem canonical6810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6810 raw6810Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw6810 raw6810Labels = mixedMoment B raw6810step0 raw6810step0Labels := by
      have hz : ∀ j, raw6810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6810step0 = (fun i j => raw6810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6810step0 raw6810; decide +kernel
      have hl : raw6810step0Labels = raw6810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6810 raw6810Labels permutation346 hz
    mixedMoment B raw6810step0 raw6810step0Labels = mixedMoment B raw6810step1 raw6810step1Labels := by
      have ha : raw6810step1 = (fun i j => raw6810step0 (permutation80 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6810step1 raw6810step0; decide +kernel
      have hl : raw6810step1Labels = raw6810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6810step0 raw6810step0Labels permutation80 permutation2
    mixedMoment B raw6810step1 raw6810step1Labels = mixedMoment B raw6810step2 raw6810step2Labels := by
      have ha : raw6810step2 = -raw6810step1 := by apply Matrix.ext; change ∀ i j, raw6810step2 i j = -(raw6810step1 i j); unfold raw6810step2 raw6810step1; decide +kernel
      have hl : raw6810step2Labels = raw6810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3156 node3156Labels := by rfl

theorem canonical6811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6811 raw6811Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6811 raw6811Labels = mixedMoment B raw6811step0 raw6811step0Labels := by
      have hz : ∀ j, raw6811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6811step0 = (fun i j => raw6811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6811step0 raw6811; decide +kernel
      have hl : raw6811step0Labels = raw6811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6811 raw6811Labels permutation346 hz
    mixedMoment B raw6811step0 raw6811step0Labels = mixedMoment B raw6811step1 raw6811step1Labels := by
      have ha : raw6811step1 = (fun i j => raw6811step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6811step1 raw6811step0; decide +kernel
      have hl : raw6811step1Labels = raw6811step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6811step0 raw6811step0Labels permutation34 permutation4
    mixedMoment B raw6811step1 raw6811step1Labels = mixedMoment B raw6811step2 raw6811step2Labels := by
      have ha : raw6811step2 = -raw6811step1 := by apply Matrix.ext; change ∀ i j, raw6811step2 i j = -(raw6811step1 i j); unfold raw6811step2 raw6811step1; decide +kernel
      have hl : raw6811step2Labels = raw6811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical6812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6812 raw6812Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw6812 raw6812Labels = mixedMoment B raw6812step0 raw6812step0Labels := by
      have hz : ∀ j, raw6812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6812step0 = (fun i j => raw6812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6812step0 raw6812; decide +kernel
      have hl : raw6812step0Labels = raw6812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6812 raw6812Labels permutation346 hz
    mixedMoment B raw6812step0 raw6812step0Labels = mixedMoment B raw6812step1 raw6812step1Labels := by
      have ha : raw6812step1 = (fun i j => raw6812step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6812step1 raw6812step0; decide +kernel
      have hl : raw6812step1Labels = raw6812step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6812step0 raw6812step0Labels permutation34 permutation4
    mixedMoment B raw6812step1 raw6812step1Labels = mixedMoment B raw6812step2 raw6812step2Labels := by
      have ha : raw6812step2 = -raw6812step1 := by apply Matrix.ext; change ∀ i j, raw6812step2 i j = -(raw6812step1 i j); unfold raw6812step2 raw6812step1; decide +kernel
      have hl : raw6812step2Labels = raw6812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

theorem canonical6903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6903 raw6903Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6903 raw6903Labels = mixedMoment B raw6903step0 raw6903step0Labels := by
      have hz : ∀ j, raw6903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6903step0 = (fun i j => raw6903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6903step0 raw6903; decide +kernel
      have hl : raw6903step0Labels = raw6903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6903 raw6903Labels permutation346 hz
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical6904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6904 raw6904Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6904 raw6904Labels = mixedMoment B raw6904step0 raw6904step0Labels := by
      have hz : ∀ j, raw6904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6904step0 = (fun i j => raw6904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6904step0 raw6904; decide +kernel
      have hl : raw6904step0Labels = raw6904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6904 raw6904Labels permutation346 hz
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical6905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6905 raw6905Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw6905 raw6905Labels = mixedMoment B raw6905step0 raw6905step0Labels := by
      have ha : raw6905step0 = (fun i j => raw6905 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6905step0 raw6905; decide +kernel
      have hl : raw6905step0Labels = raw6905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6905 raw6905Labels permutation176 permutation2
    _ = mixedMoment B node3841 node3841Labels := by rfl

theorem canonical6906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6906 raw6906Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6906 raw6906Labels = mixedMoment B raw6906step0 raw6906step0Labels := by
      have hz : ∀ j, raw6906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6906step0 = (fun i j => raw6906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6906step0 raw6906; decide +kernel
      have hl : raw6906step0Labels = raw6906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6906 raw6906Labels permutation346 hz
    mixedMoment B raw6906step0 raw6906step0Labels = mixedMoment B raw6906step1 raw6906step1Labels := by
      have ha : raw6906step1 = (fun i j => raw6906step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6906step1 raw6906step0; decide +kernel
      have hl : raw6906step1Labels = raw6906step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6906step0 raw6906step0Labels permutation92 permutation4
    mixedMoment B raw6906step1 raw6906step1Labels = mixedMoment B raw6906step2 raw6906step2Labels := by
      have ha : raw6906step2 = -raw6906step1 := by apply Matrix.ext; change ∀ i j, raw6906step2 i j = -(raw6906step1 i j); unfold raw6906step2 raw6906step1; decide +kernel
      have hl : raw6906step2Labels = raw6906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical6907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6907 raw6907Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6907 raw6907Labels = mixedMoment B raw6907step0 raw6907step0Labels := by
      have hz : ∀ j, raw6907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6907step0 = (fun i j => raw6907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6907step0 raw6907; decide +kernel
      have hl : raw6907step0Labels = raw6907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6907 raw6907Labels permutation346 hz
    mixedMoment B raw6907step0 raw6907step0Labels = mixedMoment B raw6907step1 raw6907step1Labels := by
      have ha : raw6907step1 = (fun i j => raw6907step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6907step1 raw6907step0; decide +kernel
      have hl : raw6907step1Labels = raw6907step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6907step0 raw6907step0Labels permutation92 permutation4
    mixedMoment B raw6907step1 raw6907step1Labels = mixedMoment B raw6907step2 raw6907step2Labels := by
      have ha : raw6907step2 = -raw6907step1 := by apply Matrix.ext; change ∀ i j, raw6907step2 i j = -(raw6907step1 i j); unfold raw6907step2 raw6907step1; decide +kernel
      have hl : raw6907step2Labels = raw6907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical6908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6908 raw6908Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw6908 raw6908Labels = mixedMoment B raw6908step0 raw6908step0Labels := by
      have hz : ∀ j, raw6908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6908step0 = (fun i j => raw6908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6908step0 raw6908; decide +kernel
      have hl : raw6908step0Labels = raw6908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6908 raw6908Labels permutation346 hz
    mixedMoment B raw6908step0 raw6908step0Labels = mixedMoment B raw6908step1 raw6908step1Labels := by
      have ha : raw6908step1 = (fun i j => raw6908step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6908step1 raw6908step0; decide +kernel
      have hl : raw6908step1Labels = raw6908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6908step0 raw6908step0Labels permutation33 permutation2
    _ = mixedMoment B node3906 node3906Labels := by rfl

theorem canonical6909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6909 raw6909Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6909 raw6909Labels = mixedMoment B raw6909step0 raw6909step0Labels := by
      have hz : ∀ j, raw6909 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw6909step0 = (fun i j => raw6909 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw6909step0 raw6909; decide +kernel
      have hl : raw6909step0Labels = raw6909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6909 raw6909Labels permutation590 hz
    mixedMoment B raw6909step0 raw6909step0Labels = mixedMoment B raw6909step1 raw6909step1Labels := by
      have hz : ∀ j, raw6909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6909step1 = (fun i j => raw6909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6909step1 raw6909step0; decide +kernel
      have hl : raw6909step1Labels = raw6909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6909step0 raw6909step0Labels permutation80 hz
    mixedMoment B raw6909step1 raw6909step1Labels = mixedMoment B raw6909step2 raw6909step2Labels := by
      have ha : raw6909step2 = (fun i j => raw6909step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6909step2 raw6909step1; decide +kernel
      have hl : raw6909step2Labels = raw6909step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6909step1 raw6909step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical6910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6910 raw6910Labels = mixedMoment B node1278 node1278Labels := by
  calc
    mixedMoment B raw6910 raw6910Labels = mixedMoment B raw6910step0 raw6910step0Labels := by
      have hz : ∀ j, raw6910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6910step0 = (fun i j => raw6910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6910step0 raw6910; decide +kernel
      have hl : raw6910step0Labels = raw6910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6910 raw6910Labels permutation346 hz
    mixedMoment B raw6910step0 raw6910step0Labels = mixedMoment B raw6910step1 raw6910step1Labels := by
      have ha : raw6910step1 = (fun i j => raw6910step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6910step1 raw6910step0; decide +kernel
      have hl : raw6910step1Labels = raw6910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6910step0 raw6910step0Labels permutation38 permutation2
    _ = mixedMoment B node1278 node1278Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6915 raw6915Labels = mixedMoment B node2578 node2578Labels := by
  calc
    mixedMoment B raw6915 raw6915Labels = mixedMoment B raw6915step0 raw6915step0Labels := by
      have ha : raw6915step0 = (fun i j => raw6915 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6915step0 raw6915; decide +kernel
      have hl : raw6915step0Labels = raw6915Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6915 raw6915Labels permutation182 permutation2
    _ = mixedMoment B node2578 node2578Labels := by rfl

theorem canonical6916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6916 raw6916Labels = mixedMoment B node2649 node2649Labels := by
  calc
    mixedMoment B raw6916 raw6916Labels = mixedMoment B raw6916step0 raw6916step0Labels := by
      have hz : ∀ j, raw6916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6916step0 = (fun i j => raw6916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6916step0 raw6916; decide +kernel
      have hl : raw6916step0Labels = raw6916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6916 raw6916Labels permutation346 hz
    mixedMoment B raw6916step0 raw6916step0Labels = mixedMoment B raw6916step1 raw6916step1Labels := by
      have ha : raw6916step1 = (fun i j => raw6916step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6916step1 raw6916step0; decide +kernel
      have hl : raw6916step1Labels = raw6916step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6916step0 raw6916step0Labels permutation83 permutation4
    mixedMoment B raw6916step1 raw6916step1Labels = mixedMoment B raw6916step2 raw6916step2Labels := by
      have ha : raw6916step2 = -raw6916step1 := by apply Matrix.ext; change ∀ i j, raw6916step2 i j = -(raw6916step1 i j); unfold raw6916step2 raw6916step1; decide +kernel
      have hl : raw6916step2Labels = raw6916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2649 node2649Labels := by rfl

theorem canonical6917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6917 raw6917Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw6917 raw6917Labels = mixedMoment B raw6917step0 raw6917step0Labels := by
      have hz : ∀ j, raw6917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6917step0 = (fun i j => raw6917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6917step0 raw6917; decide +kernel
      have hl : raw6917step0Labels = raw6917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6917 raw6917Labels permutation346 hz
    mixedMoment B raw6917step0 raw6917step0Labels = mixedMoment B raw6917step1 raw6917step1Labels := by
      have ha : raw6917step1 = (fun i j => raw6917step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6917step1 raw6917step0; decide +kernel
      have hl : raw6917step1Labels = raw6917step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6917step0 raw6917step0Labels permutation46 permutation2
    _ = mixedMoment B node2758 node2758Labels := by rfl

theorem canonical6918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6918 raw6918Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6918 raw6918Labels = mixedMoment B raw6918step0 raw6918step0Labels := by
      have hz : ∀ j, raw6918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6918step0 = (fun i j => raw6918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6918step0 raw6918; decide +kernel
      have hl : raw6918step0Labels = raw6918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6918 raw6918Labels permutation346 hz
    mixedMoment B raw6918step0 raw6918step0Labels = mixedMoment B raw6918step1 raw6918step1Labels := by
      have ha : raw6918step1 = (fun i j => raw6918step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6918step1 raw6918step0; decide +kernel
      have hl : raw6918step1Labels = raw6918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6918step0 raw6918step0Labels permutation39 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical6919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6919 raw6919Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw6919 raw6919Labels = mixedMoment B raw6919step0 raw6919step0Labels := by
      have ha : raw6919step0 = (fun i j => raw6919 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6919step0 raw6919; decide +kernel
      have hl : raw6919step0Labels = raw6919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6919 raw6919Labels permutation158 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical6920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6920 raw6920Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw6920 raw6920Labels = mixedMoment B raw6920step0 raw6920step0Labels := by
      have hz : ∀ j, raw6920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6920step0 = (fun i j => raw6920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6920step0 raw6920; decide +kernel
      have hl : raw6920step0Labels = raw6920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6920 raw6920Labels permutation346 hz
    mixedMoment B raw6920step0 raw6920step0Labels = mixedMoment B raw6920step1 raw6920step1Labels := by
      have ha : raw6920step1 = (fun i j => raw6920step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6920step1 raw6920step0; decide +kernel
      have hl : raw6920step1Labels = raw6920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6920step0 raw6920step0Labels permutation34 permutation2
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical6921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6921 raw6921Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw6921 raw6921Labels = mixedMoment B raw6921step0 raw6921step0Labels := by
      have hz : ∀ j, raw6921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6921step0 = (fun i j => raw6921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6921step0 raw6921; decide +kernel
      have hl : raw6921step0Labels = raw6921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6921 raw6921Labels permutation346 hz
    mixedMoment B raw6921step0 raw6921step0Labels = mixedMoment B raw6921step1 raw6921step1Labels := by
      have ha : raw6921step1 = (fun i j => raw6921step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6921step1 raw6921step0; decide +kernel
      have hl : raw6921step1Labels = raw6921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6921step0 raw6921step0Labels permutation33 permutation2
    _ = mixedMoment B node2499 node2499Labels := by rfl

theorem canonical6922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6922 raw6922Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw6922 raw6922Labels = mixedMoment B raw6922step0 raw6922step0Labels := by
      have hz : ∀ j, raw6922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6922step0 = (fun i j => raw6922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6922step0 raw6922; decide +kernel
      have hl : raw6922step0Labels = raw6922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6922 raw6922Labels permutation346 hz
    _ = mixedMoment B node2497 node2497Labels := by rfl

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

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

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

theorem sound1278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1278 node1278Labels = Sparse.eval nodeValue1278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1278) = mixedMoment B node1278 node1278Labels := rfl
  simpa [nodeValue1278, Sparse.eval] using hc.symm

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

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

theorem sound2026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2026 node2026Labels = Sparse.eval nodeValue2026 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2026) = mixedMoment B node2026 node2026Labels := rfl
  simpa [nodeValue2026, Sparse.eval] using hc.symm

theorem sound2028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2028 node2028Labels = Sparse.eval nodeValue2028 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2028) = mixedMoment B node2028 node2028Labels := rfl
  simpa [nodeValue2028, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2266 node2266Labels = Sparse.eval nodeValue2266 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2266) = mixedMoment B node2266 node2266Labels := rfl
  simpa [nodeValue2266, Sparse.eval] using hc.symm

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

theorem sound2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2494 node2494Labels = Sparse.eval nodeValue2494 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2494) = mixedMoment B node2494 node2494Labels := rfl
  simpa [nodeValue2494, Sparse.eval] using hc.symm

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

theorem sound2497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2497 node2497Labels = Sparse.eval nodeValue2497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2497) = mixedMoment B node2497 node2497Labels := rfl
  simpa [nodeValue2497, Sparse.eval] using hc.symm

theorem sound2499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2499 node2499Labels = Sparse.eval nodeValue2499 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2499) = mixedMoment B node2499 node2499Labels := rfl
  simpa [nodeValue2499, Sparse.eval] using hc.symm

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

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

theorem sound2578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2578 node2578Labels = Sparse.eval nodeValue2578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2578) = mixedMoment B node2578 node2578Labels := rfl
  simpa [nodeValue2578, Sparse.eval] using hc.symm

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

theorem sound2649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2649 node2649Labels = Sparse.eval nodeValue2649 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2649) = mixedMoment B node2649 node2649Labels := rfl
  simpa [nodeValue2649, Sparse.eval] using hc.symm

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

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

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

theorem sound3153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3153 node3153Labels = Sparse.eval nodeValue3153 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3153) = mixedMoment B node3153 node3153Labels := rfl
  simpa [nodeValue3153, Sparse.eval] using hc.symm

theorem sound3156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3156 node3156Labels = Sparse.eval nodeValue3156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3156) = mixedMoment B node3156 node3156Labels := rfl
  simpa [nodeValue3156, Sparse.eval] using hc.symm

theorem sound3157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3157 node3157Labels = Sparse.eval nodeValue3157 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3157) = mixedMoment B node3157 node3157Labels := rfl
  simpa [nodeValue3157, Sparse.eval] using hc.symm

theorem sound3159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3159 node3159Labels = Sparse.eval nodeValue3159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3159) = mixedMoment B node3159 node3159Labels := rfl
  simpa [nodeValue3159, Sparse.eval] using hc.symm

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

theorem sound3377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3377 node3377Labels = Sparse.eval nodeValue3377 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3377) = mixedMoment B node3377 node3377Labels := rfl
  simpa [nodeValue3377, Sparse.eval] using hc.symm

theorem sound3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3379 node3379Labels = Sparse.eval nodeValue3379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3379) = mixedMoment B node3379 node3379Labels := rfl
  simpa [nodeValue3379, Sparse.eval] using hc.symm

theorem sound3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3388 node3388Labels = Sparse.eval nodeValue3388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3388) = mixedMoment B node3388 node3388Labels := rfl
  simpa [nodeValue3388, Sparse.eval] using hc.symm

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

theorem sound3392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3392 node3392Labels = Sparse.eval nodeValue3392 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3392) = mixedMoment B node3392 node3392Labels := rfl
  simpa [nodeValue3392, Sparse.eval] using hc.symm

theorem sound3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3395 node3395Labels = Sparse.eval nodeValue3395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3395) = mixedMoment B node3395 node3395Labels := rfl
  simpa [nodeValue3395, Sparse.eval] using hc.symm

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

theorem sound3488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3488 node3488Labels = Sparse.eval nodeValue3488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3488) = mixedMoment B node3488 node3488Labels := rfl
  simpa [nodeValue3488, Sparse.eval] using hc.symm

theorem sound3497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3497 node3497Labels = Sparse.eval nodeValue3497 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3497) = mixedMoment B node3497 node3497Labels := rfl
  simpa [nodeValue3497, Sparse.eval] using hc.symm

theorem sound3504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3504 node3504Labels = Sparse.eval nodeValue3504 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3504) = mixedMoment B node3504 node3504Labels := rfl
  simpa [nodeValue3504, Sparse.eval] using hc.symm

theorem sound3506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3506 node3506Labels = Sparse.eval nodeValue3506 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3506) = mixedMoment B node3506 node3506Labels := rfl
  simpa [nodeValue3506, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = 0 := by
  exact mixedMoment_alpha B hF node3531 node3531Labels 1 permutation437
    (by decide +kernel)

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

theorem sound3528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3528 node3528Labels = Sparse.eval nodeValue3528 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3528) = mixedMoment B node3528 node3528Labels := rfl
  simpa [nodeValue3528, Sparse.eval] using hc.symm

theorem sound3531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3531 node3531Labels = Sparse.eval nodeValue3531 (mixedVector B) := by
  simpa only [nodeValue3531, Sparse.eval_nil] using zero3531 B _hB _hF

theorem sound3533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3533 node3533Labels = Sparse.eval nodeValue3533 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3533) = mixedMoment B node3533 node3533Labels := rfl
  simpa [nodeValue3533, Sparse.eval] using hc.symm

theorem sound3535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3535 node3535Labels = Sparse.eval nodeValue3535 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3535) = mixedMoment B node3535 node3535Labels := rfl
  simpa [nodeValue3535, Sparse.eval] using hc.symm

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3544 node3544Labels = Sparse.eval nodeValue3544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3544) = mixedMoment B node3544 node3544Labels := rfl
  simpa [nodeValue3544, Sparse.eval] using hc.symm

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

theorem sound3584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3584 node3584Labels = Sparse.eval nodeValue3584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3584) = mixedMoment B node3584 node3584Labels := rfl
  simpa [nodeValue3584, Sparse.eval] using hc.symm

theorem sound3627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3627 node3627Labels = Sparse.eval nodeValue3627 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3627) = mixedMoment B node3627 node3627Labels := rfl
  simpa [nodeValue3627, Sparse.eval] using hc.symm

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

theorem sound3841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3841 node3841Labels = Sparse.eval nodeValue3841 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3841) = mixedMoment B node3841 node3841Labels := rfl
  simpa [nodeValue3841, Sparse.eval] using hc.symm

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

theorem sound3906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3906 node3906Labels = Sparse.eval nodeValue3906 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3906) = mixedMoment B node3906 node3906Labels := rfl
  simpa [nodeValue3906, Sparse.eval] using hc.symm

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

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources10
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm321 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA321 + difference 1 0) (sourceB321 + difference 0 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2266) := by
    have ha : (tripleCharges (sourceA321 + difference 1 0) (sourceB321 + difference 0 1) sourceC321) = raw6790 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6790; decide +kernel
    rw [ha]
    exact (canonical6790 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA321 + difference 1 1) (sourceB321 + difference 1 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA321 + difference 1 1) (sourceB321 + difference 1 1) sourceC321) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA321 + difference 1 2) (sourceB321 + difference 2 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA321 + difference 1 2) (sourceB321 + difference 2 1) sourceC321) = raw6795 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6795; decide +kernel
    rw [ha]
    exact (canonical6795 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA321 + difference 1 3) (sourceB321 + difference 3 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA321 + difference 1 3) (sourceB321 + difference 3 1) sourceC321) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA321 + difference 1 4) (sourceB321 + difference 4 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA321 + difference 1 4) (sourceB321 + difference 4 1) sourceC321) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA321 + difference 1 5) (sourceB321 + difference 5 1) sourceC321) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA321 + difference 1 5) (sourceB321 + difference 5 1) sourceC321) = raw6798 := by
      apply Matrix.ext; unfold tripleCharges sourceA321 sourceB321 sourceC321 difference raw6798; decide +kernel
    rw [ha]
    exact (canonical6798 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA321 + sourceB321) sourceC321) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA321 + sourceB321) sourceC321) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA321 sourceB321 sourceC321 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA321 sourceB321 sourceC321
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm321, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm322 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA322 + difference 0 1) (sourceB322 + difference 1 0) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA322 + difference 0 1) (sourceB322 + difference 1 0) sourceC322) = raw6785 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6785; decide +kernel
    rw [ha]
    exact (canonical6785 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA322 + difference 1 1) (sourceB322 + difference 1 1) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA322 + difference 1 1) (sourceB322 + difference 1 1) sourceC322) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA322 + difference 2 1) (sourceB322 + difference 1 2) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA322 + difference 2 1) (sourceB322 + difference 1 2) sourceC322) = raw6799 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6799; decide +kernel
    rw [ha]
    exact (canonical6799 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA322 + difference 3 1) (sourceB322 + difference 1 3) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA322 + difference 3 1) (sourceB322 + difference 1 3) sourceC322) = raw6800 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6800; decide +kernel
    rw [ha]
    exact (canonical6800 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA322 + difference 4 1) (sourceB322 + difference 1 4) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA322 + difference 4 1) (sourceB322 + difference 1 4) sourceC322) = raw6801 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6801; decide +kernel
    rw [ha]
    exact (canonical6801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA322 + difference 5 1) (sourceB322 + difference 1 5) sourceC322) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA322 + difference 5 1) (sourceB322 + difference 1 5) sourceC322) = raw6802 := by
      apply Matrix.ext; unfold tripleCharges sourceA322 sourceB322 sourceC322 difference raw6802; decide +kernel
    rw [ha]
    exact (canonical6802 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA322 + sourceB322) sourceC322) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA322 + sourceB322) sourceC322) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA322 sourceB322 sourceC322 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA322 sourceB322 sourceC322
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm322, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm323 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA323 + difference 2 0) (sourceB323 + difference 0 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA323 + difference 2 0) (sourceB323 + difference 0 2) sourceC323) = raw6791 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6791; decide +kernel
    rw [ha]
    exact (canonical6791 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA323 + difference 2 1) (sourceB323 + difference 1 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3377) := by
    have ha : (tripleCharges (sourceA323 + difference 2 1) (sourceB323 + difference 1 2) sourceC323) = raw6799 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6799; decide +kernel
    rw [ha]
    exact (canonical6799 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA323 + difference 2 2) (sourceB323 + difference 2 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA323 + difference 2 2) (sourceB323 + difference 2 2) sourceC323) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA323 + difference 2 3) (sourceB323 + difference 3 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA323 + difference 2 3) (sourceB323 + difference 3 2) sourceC323) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA323 + difference 2 4) (sourceB323 + difference 4 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA323 + difference 2 4) (sourceB323 + difference 4 2) sourceC323) = raw6804 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6804; decide +kernel
    rw [ha]
    exact (canonical6804 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA323 + difference 2 5) (sourceB323 + difference 5 2) sourceC323) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA323 + difference 2 5) (sourceB323 + difference 5 2) sourceC323) = raw6805 := by
      apply Matrix.ext; unfold tripleCharges sourceA323 sourceB323 sourceC323 difference raw6805; decide +kernel
    rw [ha]
    exact (canonical6805 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA323 + sourceB323) sourceC323) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA323 + sourceB323) sourceC323) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA323 sourceB323 sourceC323 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA323 sourceB323 sourceC323
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm323, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm324 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA324 + difference 0 2) (sourceB324 + difference 2 0) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3388) := by
    have ha : (tripleCharges (sourceA324 + difference 0 2) (sourceB324 + difference 2 0) sourceC324) = raw6786 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6786; decide +kernel
    rw [ha]
    exact (canonical6786 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA324 + difference 1 2) (sourceB324 + difference 2 1) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA324 + difference 1 2) (sourceB324 + difference 2 1) sourceC324) = raw6795 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6795; decide +kernel
    rw [ha]
    exact (canonical6795 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA324 + difference 2 2) (sourceB324 + difference 2 2) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA324 + difference 2 2) (sourceB324 + difference 2 2) sourceC324) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA324 + difference 3 2) (sourceB324 + difference 2 3) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3153) := by
    have ha : (tripleCharges (sourceA324 + difference 3 2) (sourceB324 + difference 2 3) sourceC324) = raw6806 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6806; decide +kernel
    rw [ha]
    exact (canonical6806 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA324 + difference 4 2) (sourceB324 + difference 2 4) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA324 + difference 4 2) (sourceB324 + difference 2 4) sourceC324) = raw6807 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6807; decide +kernel
    rw [ha]
    exact (canonical6807 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA324 + difference 5 2) (sourceB324 + difference 2 5) sourceC324) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA324 + difference 5 2) (sourceB324 + difference 2 5) sourceC324) = raw6808 := by
      apply Matrix.ext; unfold tripleCharges sourceA324 sourceB324 sourceC324 difference raw6808; decide +kernel
    rw [ha]
    exact (canonical6808 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA324 + sourceB324) sourceC324) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA324 + sourceB324) sourceC324) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA324 sourceB324 sourceC324 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA324 sourceB324 sourceC324
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm324, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm325 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA325 + difference 3 0) (sourceB325 + difference 0 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2026) := by
    have ha : (tripleCharges (sourceA325 + difference 3 0) (sourceB325 + difference 0 3) sourceC325) = raw6792 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6792; decide +kernel
    rw [ha]
    exact (canonical6792 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA325 + difference 3 1) (sourceB325 + difference 1 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3159) := by
    have ha : (tripleCharges (sourceA325 + difference 3 1) (sourceB325 + difference 1 3) sourceC325) = raw6800 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6800; decide +kernel
    rw [ha]
    exact (canonical6800 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA325 + difference 3 2) (sourceB325 + difference 2 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3153) := by
    have ha : (tripleCharges (sourceA325 + difference 3 2) (sourceB325 + difference 2 3) sourceC325) = raw6806 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6806; decide +kernel
    rw [ha]
    exact (canonical6806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA325 + difference 3 3) (sourceB325 + difference 3 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA325 + difference 3 3) (sourceB325 + difference 3 3) sourceC325) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA325 + difference 3 4) (sourceB325 + difference 4 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA325 + difference 3 4) (sourceB325 + difference 4 3) sourceC325) = raw6809 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6809; decide +kernel
    rw [ha]
    exact (canonical6809 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA325 + difference 3 5) (sourceB325 + difference 5 3) sourceC325) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3156) := by
    have ha : (tripleCharges (sourceA325 + difference 3 5) (sourceB325 + difference 5 3) sourceC325) = raw6810 := by
      apply Matrix.ext; unfold tripleCharges sourceA325 sourceB325 sourceC325 difference raw6810; decide +kernel
    rw [ha]
    exact (canonical6810 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA325 + sourceB325) sourceC325) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA325 + sourceB325) sourceC325) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA325 sourceB325 sourceC325 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA325 sourceB325 sourceC325
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm325, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm326 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA326 + difference 0 3) (sourceB326 + difference 3 0) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA326 + difference 0 3) (sourceB326 + difference 3 0) sourceC326) = raw6787 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6787; decide +kernel
    rw [ha]
    exact (canonical6787 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA326 + difference 1 3) (sourceB326 + difference 3 1) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3627) := by
    have ha : (tripleCharges (sourceA326 + difference 1 3) (sourceB326 + difference 3 1) sourceC326) = raw6796 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6796; decide +kernel
    rw [ha]
    exact (canonical6796 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA326 + difference 2 3) (sourceB326 + difference 3 2) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3531) := by
    have ha : (tripleCharges (sourceA326 + difference 2 3) (sourceB326 + difference 3 2) sourceC326) = raw6803 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6803; decide +kernel
    rw [ha]
    exact (canonical6803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA326 + difference 3 3) (sourceB326 + difference 3 3) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA326 + difference 3 3) (sourceB326 + difference 3 3) sourceC326) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA326 + difference 4 3) (sourceB326 + difference 3 4) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA326 + difference 4 3) (sourceB326 + difference 3 4) sourceC326) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA326 + difference 5 3) (sourceB326 + difference 3 5) sourceC326) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA326 + difference 5 3) (sourceB326 + difference 3 5) sourceC326) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA326 sourceB326 sourceC326 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA326 + sourceB326) sourceC326) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA326 + sourceB326) sourceC326) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA326 sourceB326 sourceC326 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA326 sourceB326 sourceC326
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm326, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm327 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA327 + difference 4 0) (sourceB327 + difference 0 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA327 + difference 4 0) (sourceB327 + difference 0 4) sourceC327) = raw6793 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6793; decide +kernel
    rw [ha]
    exact (canonical6793 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA327 + difference 4 1) (sourceB327 + difference 1 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA327 + difference 4 1) (sourceB327 + difference 1 4) sourceC327) = raw6801 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6801; decide +kernel
    rw [ha]
    exact (canonical6801 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA327 + difference 4 2) (sourceB327 + difference 2 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3497) := by
    have ha : (tripleCharges (sourceA327 + difference 4 2) (sourceB327 + difference 2 4) sourceC327) = raw6807 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6807; decide +kernel
    rw [ha]
    exact (canonical6807 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA327 + difference 4 3) (sourceB327 + difference 3 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA327 + difference 4 3) (sourceB327 + difference 3 4) sourceC327) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA327 + difference 4 4) (sourceB327 + difference 4 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA327 + difference 4 4) (sourceB327 + difference 4 4) sourceC327) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA327 + difference 4 5) (sourceB327 + difference 5 4) sourceC327) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA327 + difference 4 5) (sourceB327 + difference 5 4) sourceC327) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA327 sourceB327 sourceC327 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA327 + sourceB327) sourceC327) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA327 + sourceB327) sourceC327) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA327 sourceB327 sourceC327 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA327 sourceB327 sourceC327
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm327, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm328 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA328 + difference 0 4) (sourceB328 + difference 4 0) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA328 + difference 0 4) (sourceB328 + difference 4 0) sourceC328) = raw6788 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6788; decide +kernel
    rw [ha]
    exact (canonical6788 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA328 + difference 1 4) (sourceB328 + difference 4 1) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3584) := by
    have ha : (tripleCharges (sourceA328 + difference 1 4) (sourceB328 + difference 4 1) sourceC328) = raw6797 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6797; decide +kernel
    rw [ha]
    exact (canonical6797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA328 + difference 2 4) (sourceB328 + difference 4 2) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3504) := by
    have ha : (tripleCharges (sourceA328 + difference 2 4) (sourceB328 + difference 4 2) sourceC328) = raw6804 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6804; decide +kernel
    rw [ha]
    exact (canonical6804 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA328 + difference 3 4) (sourceB328 + difference 4 3) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3157) := by
    have ha : (tripleCharges (sourceA328 + difference 3 4) (sourceB328 + difference 4 3) sourceC328) = raw6809 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6809; decide +kernel
    rw [ha]
    exact (canonical6809 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA328 + difference 4 4) (sourceB328 + difference 4 4) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA328 + difference 4 4) (sourceB328 + difference 4 4) sourceC328) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA328 + difference 5 4) (sourceB328 + difference 4 5) sourceC328) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA328 + difference 5 4) (sourceB328 + difference 4 5) sourceC328) = raw6812 := by
      apply Matrix.ext; unfold tripleCharges sourceA328 sourceB328 sourceC328 difference raw6812; decide +kernel
    rw [ha]
    exact (canonical6812 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA328 + sourceB328) sourceC328) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA328 + sourceB328) sourceC328) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA328 sourceB328 sourceC328 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA328 sourceB328 sourceC328
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm328, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm329 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA329 + difference 5 0) (sourceB329 + difference 0 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2028) := by
    have ha : (tripleCharges (sourceA329 + difference 5 0) (sourceB329 + difference 0 5) sourceC329) = raw6794 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6794; decide +kernel
    rw [ha]
    exact (canonical6794 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA329 + difference 5 1) (sourceB329 + difference 1 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA329 + difference 5 1) (sourceB329 + difference 1 5) sourceC329) = raw6802 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6802; decide +kernel
    rw [ha]
    exact (canonical6802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA329 + difference 5 2) (sourceB329 + difference 2 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3488) := by
    have ha : (tripleCharges (sourceA329 + difference 5 2) (sourceB329 + difference 2 5) sourceC329) = raw6808 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6808; decide +kernel
    rw [ha]
    exact (canonical6808 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA329 + difference 5 3) (sourceB329 + difference 3 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA329 + difference 5 3) (sourceB329 + difference 3 5) sourceC329) = raw6811 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6811; decide +kernel
    rw [ha]
    exact (canonical6811 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA329 + difference 5 4) (sourceB329 + difference 4 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3506) := by
    have ha : (tripleCharges (sourceA329 + difference 5 4) (sourceB329 + difference 4 5) sourceC329) = raw6812 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6812; decide +kernel
    rw [ha]
    exact (canonical6812 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA329 + difference 5 5) (sourceB329 + difference 5 5) sourceC329) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3535) := by
    have ha : (tripleCharges (sourceA329 + difference 5 5) (sourceB329 + difference 5 5) sourceC329) = raw6784 := by
      apply Matrix.ext; unfold tripleCharges sourceA329 sourceB329 sourceC329 difference raw6784; decide +kernel
    rw [ha]
    exact (canonical6784 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA329 + sourceB329) sourceC329) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA329 + sourceB329) sourceC329) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA329 sourceB329 sourceC329 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA329 sourceB329 sourceC329
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm329, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm333 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA333 + difference 0 0) (sourceB333 + difference 0 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA333 + difference 0 0) (sourceB333 + difference 0 0) sourceC333) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA333 + difference 0 1) (sourceB333 + difference 1 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA333 + difference 0 1) (sourceB333 + difference 1 0) sourceC333) = raw6904 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6904; decide +kernel
    rw [ha]
    exact (canonical6904 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA333 + difference 0 2) (sourceB333 + difference 2 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3841) := by
    have ha : (tripleCharges (sourceA333 + difference 0 2) (sourceB333 + difference 2 0) sourceC333) = raw6905 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6905; decide +kernel
    rw [ha]
    exact (canonical6905 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA333 + difference 0 3) (sourceB333 + difference 3 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA333 + difference 0 3) (sourceB333 + difference 3 0) sourceC333) = raw6906 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6906; decide +kernel
    rw [ha]
    exact (canonical6906 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA333 + difference 0 4) (sourceB333 + difference 4 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA333 + difference 0 4) (sourceB333 + difference 4 0) sourceC333) = raw6907 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6907; decide +kernel
    rw [ha]
    exact (canonical6907 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA333 + difference 0 5) (sourceB333 + difference 5 0) sourceC333) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA333 + difference 0 5) (sourceB333 + difference 5 0) sourceC333) = raw6908 := by
      apply Matrix.ext; unfold tripleCharges sourceA333 sourceB333 sourceC333 difference raw6908; decide +kernel
    rw [ha]
    exact (canonical6908 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA333 + sourceB333) sourceC333) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA333 + sourceB333) sourceC333) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA333 sourceB333 sourceC333 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA333 sourceB333 sourceC333
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm333, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm335 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA335 + difference 1 0) (sourceB335 + difference 0 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1278) := by
    have ha : (tripleCharges (sourceA335 + difference 1 0) (sourceB335 + difference 0 1) sourceC335) = raw6910 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6910; decide +kernel
    rw [ha]
    exact (canonical6910 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA335 + difference 1 1) (sourceB335 + difference 1 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA335 + difference 1 1) (sourceB335 + difference 1 1) sourceC335) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA335 + difference 1 2) (sourceB335 + difference 2 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2578) := by
    have ha : (tripleCharges (sourceA335 + difference 1 2) (sourceB335 + difference 2 1) sourceC335) = raw6915 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6915; decide +kernel
    rw [ha]
    exact (canonical6915 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA335 + difference 1 3) (sourceB335 + difference 3 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA335 + difference 1 3) (sourceB335 + difference 3 1) sourceC335) = raw6916 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6916; decide +kernel
    rw [ha]
    exact (canonical6916 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA335 + difference 1 4) (sourceB335 + difference 4 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA335 + difference 1 4) (sourceB335 + difference 4 1) sourceC335) = raw6917 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6917; decide +kernel
    rw [ha]
    exact (canonical6917 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA335 + difference 1 5) (sourceB335 + difference 5 1) sourceC335) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA335 + difference 1 5) (sourceB335 + difference 5 1) sourceC335) = raw6918 := by
      apply Matrix.ext; unfold tripleCharges sourceA335 sourceB335 sourceC335 difference raw6918; decide +kernel
    rw [ha]
    exact (canonical6918 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA335 + sourceB335) sourceC335) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA335 + sourceB335) sourceC335) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA335 sourceB335 sourceC335 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA335 sourceB335 sourceC335
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm335, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm336 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA336 + difference 0 1) (sourceB336 + difference 1 0) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA336 + difference 0 1) (sourceB336 + difference 1 0) sourceC336) = raw6904 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6904; decide +kernel
    rw [ha]
    exact (canonical6904 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA336 + difference 1 1) (sourceB336 + difference 1 1) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA336 + difference 1 1) (sourceB336 + difference 1 1) sourceC336) = raw6903 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6903; decide +kernel
    rw [ha]
    exact (canonical6903 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA336 + difference 2 1) (sourceB336 + difference 1 2) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2494) := by
    have ha : (tripleCharges (sourceA336 + difference 2 1) (sourceB336 + difference 1 2) sourceC336) = raw6919 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6919; decide +kernel
    rw [ha]
    exact (canonical6919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA336 + difference 3 1) (sourceB336 + difference 1 3) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA336 + difference 3 1) (sourceB336 + difference 1 3) sourceC336) = raw6920 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6920; decide +kernel
    rw [ha]
    exact (canonical6920 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA336 + difference 4 1) (sourceB336 + difference 1 4) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA336 + difference 4 1) (sourceB336 + difference 1 4) sourceC336) = raw6921 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6921; decide +kernel
    rw [ha]
    exact (canonical6921 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA336 + difference 5 1) (sourceB336 + difference 1 5) sourceC336) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2497) := by
    have ha : (tripleCharges (sourceA336 + difference 5 1) (sourceB336 + difference 1 5) sourceC336) = raw6922 := by
      apply Matrix.ext; unfold tripleCharges sourceA336 sourceB336 sourceC336 difference raw6922; decide +kernel
    rw [ha]
    exact (canonical6922 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA336 + sourceB336) sourceC336) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA336 + sourceB336) sourceC336) = raw6909 := by
      apply Matrix.ext; unfold doubleCharges sourceA336 sourceB336 sourceC336 raw6909; decide +kernel
    rw [ha]
    exact (canonical6909 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA336 sourceB336 sourceC336
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm336, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck272 : Integer.Sparse.reindex keyMap MixedData.row272 = numericRow272 := by decide +kernel

theorem numericCheck272 (x : Master → ℝ) : Integer.Sparse.eval numericRow272 x =
    (1 : ℝ) * reducedSource272 x := by
  norm_num [numericRow272, reducedSource272, Integer.Sparse.eval, Sparse.eval, nodeValue2266, nodeValue3535, nodeValue3584, nodeValue3626, nodeValue3627, nodeValue4084]

theorem reindexCheck273 : Integer.Sparse.reindex keyMap MixedData.row273 = numericRow273 := by decide +kernel

theorem numericCheck273 (x : Master → ℝ) : Integer.Sparse.eval numericRow273 x =
    (1 : ℝ) * reducedSource273 x := by
  norm_num [numericRow273, reducedSource273, Integer.Sparse.eval, Sparse.eval, nodeValue3159, nodeValue3377, nodeValue3379, nodeValue3395, nodeValue3535, nodeValue4084]

theorem reindexCheck274 : Integer.Sparse.reindex keyMap MixedData.row274 = numericRow274 := by decide +kernel

theorem numericCheck274 (x : Master → ℝ) : Integer.Sparse.eval numericRow274 x =
    (1 : ℝ) * reducedSource274 x := by
  norm_num [numericRow274, reducedSource274, Integer.Sparse.eval, Sparse.eval, nodeValue2021, nodeValue3377, nodeValue3504, nodeValue3528, nodeValue3531, nodeValue3535, nodeValue4084]

theorem reindexCheck275 : Integer.Sparse.reindex keyMap MixedData.row275 = numericRow275 := by decide +kernel

theorem numericCheck275 (x : Master → ℝ) : Integer.Sparse.eval numericRow275 x =
    (1 : ℝ) * reducedSource275 x := by
  norm_num [numericRow275, reducedSource275, Integer.Sparse.eval, Sparse.eval, nodeValue3153, nodeValue3388, nodeValue3488, nodeValue3497, nodeValue3535, nodeValue4084]

theorem reindexCheck276 : Integer.Sparse.reindex keyMap MixedData.row276 = numericRow276 := by decide +kernel

theorem numericCheck276 (x : Master → ℝ) : Integer.Sparse.eval numericRow276 x =
    (1 : ℝ) * reducedSource276 x := by
  norm_num [numericRow276, reducedSource276, Integer.Sparse.eval, Sparse.eval, nodeValue2026, nodeValue3153, nodeValue3156, nodeValue3157, nodeValue3159, nodeValue3535, nodeValue4084]

theorem reindexCheck277 : Integer.Sparse.reindex keyMap MixedData.row277 = numericRow277 := by decide +kernel

theorem numericCheck277 (x : Master → ℝ) : Integer.Sparse.eval numericRow277 x =
    (1 : ℝ) * reducedSource277 x := by
  norm_num [numericRow277, reducedSource277, Integer.Sparse.eval, Sparse.eval, nodeValue3531, nodeValue3533, nodeValue3535, nodeValue3544, nodeValue3627, nodeValue4084]

theorem reindexCheck278 : Integer.Sparse.reindex keyMap MixedData.row278 = numericRow278 := by decide +kernel

theorem numericCheck278 (x : Master → ℝ) : Integer.Sparse.eval numericRow278 x =
    (1 : ℝ) * reducedSource278 x := by
  norm_num [numericRow278, reducedSource278, Integer.Sparse.eval, Sparse.eval, nodeValue2058, nodeValue3395, nodeValue3497, nodeValue3535, nodeValue3541, nodeValue3544, nodeValue4084]

theorem reindexCheck279 : Integer.Sparse.reindex keyMap MixedData.row279 = numericRow279 := by decide +kernel

theorem numericCheck279 (x : Master → ℝ) : Integer.Sparse.eval numericRow279 x =
    (1 : ℝ) * reducedSource279 x := by
  norm_num [numericRow279, reducedSource279, Integer.Sparse.eval, Sparse.eval, nodeValue3157, nodeValue3392, nodeValue3504, nodeValue3506, nodeValue3535, nodeValue3584, nodeValue4084]

theorem reindexCheck280 : Integer.Sparse.reindex keyMap MixedData.row280 = numericRow280 := by decide +kernel

theorem numericCheck280 (x : Master → ℝ) : Integer.Sparse.eval numericRow280 x =
    (1 : ℝ) * reducedSource280 x := by
  norm_num [numericRow280, reducedSource280, Integer.Sparse.eval, Sparse.eval, nodeValue2028, nodeValue3379, nodeValue3488, nodeValue3506, nodeValue3533, nodeValue3535, nodeValue4084]

theorem reindexCheck283 : Integer.Sparse.reindex keyMap MixedData.row283 = numericRow283 := by decide +kernel

theorem numericCheck283 (x : Master → ℝ) : Integer.Sparse.eval numericRow283 x =
    (1 : ℝ) * reducedSource283 x := by
  norm_num [numericRow283, reducedSource283, Integer.Sparse.eval, Sparse.eval, nodeValue2732, nodeValue3814, nodeValue3841, nodeValue3906, nodeValue4092]

theorem reindexCheck284 : Integer.Sparse.reindex keyMap MixedData.row284 = numericRow284 := by decide +kernel

theorem numericCheck284 (x : Master → ℝ) : Integer.Sparse.eval numericRow284 x =
    (1 : ℝ) * reducedSource284 x := by
  norm_num [numericRow284, reducedSource284, Integer.Sparse.eval, Sparse.eval, nodeValue1278, nodeValue2578, nodeValue2649, nodeValue2732, nodeValue2758, nodeValue2773, nodeValue4092]

theorem reindexCheck285 : Integer.Sparse.reindex keyMap MixedData.row285 = numericRow285 := by decide +kernel

theorem numericCheck285 (x : Master → ℝ) : Integer.Sparse.eval numericRow285 x =
    (1 : ℝ) * reducedSource285 x := by
  norm_num [numericRow285, reducedSource285, Integer.Sparse.eval, Sparse.eval, nodeValue2494, nodeValue2497, nodeValue2499, nodeValue2515, nodeValue2732, nodeValue3814, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource272 (mixedVector B) = 0 := by
  have h2266 : mixedVector B (Sum.inr 2266) = Sparse.eval nodeValue2266 (mixedVector B) := by
    change mixedMoment B node2266 node2266Labels = _
    exact sound2266 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm321, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2266, h3535, h3584, h3626, h3627, h4084, reducedSource272] using sourceEq321 B hB

theorem rowSound272 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row272 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck272, numericCheck272, reducedZero272 B hB hF, mul_zero]

theorem reducedZero273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource273 (mixedVector B) = 0 := by
  have h3159 : mixedVector B (Sum.inr 3159) = Sparse.eval nodeValue3159 (mixedVector B) := by
    change mixedMoment B node3159 node3159Labels = _
    exact sound3159 B hB hF
  have h3377 : mixedVector B (Sum.inr 3377) = Sparse.eval nodeValue3377 (mixedVector B) := by
    change mixedMoment B node3377 node3377Labels = _
    exact sound3377 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm322, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3159, h3377, h3379, h3395, h3535, h4084, reducedSource273] using sourceEq322 B hB

theorem rowSound273 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row273 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck273, numericCheck273, reducedZero273 B hB hF, mul_zero]

theorem reducedZero274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource274 (mixedVector B) = 0 := by
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h3377 : mixedVector B (Sum.inr 3377) = Sparse.eval nodeValue3377 (mixedVector B) := by
    change mixedMoment B node3377 node3377Labels = _
    exact sound3377 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm323, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2021, h3377, h3504, h3528, h3531, h3535, h4084, reducedSource274] using sourceEq323 B hB

theorem rowSound274 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row274 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck274, numericCheck274, reducedZero274 B hB hF, mul_zero]

theorem reducedZero275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource275 (mixedVector B) = 0 := by
  have h3153 : mixedVector B (Sum.inr 3153) = Sparse.eval nodeValue3153 (mixedVector B) := by
    change mixedMoment B node3153 node3153Labels = _
    exact sound3153 B hB hF
  have h3388 : mixedVector B (Sum.inr 3388) = Sparse.eval nodeValue3388 (mixedVector B) := by
    change mixedMoment B node3388 node3388Labels = _
    exact sound3388 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm324, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3153, h3388, h3488, h3497, h3535, h4084, reducedSource275] using sourceEq324 B hB

theorem rowSound275 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row275 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck275, numericCheck275, reducedZero275 B hB hF, mul_zero]

theorem reducedZero276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource276 (mixedVector B) = 0 := by
  have h2026 : mixedVector B (Sum.inr 2026) = Sparse.eval nodeValue2026 (mixedVector B) := by
    change mixedMoment B node2026 node2026Labels = _
    exact sound2026 B hB hF
  have h3153 : mixedVector B (Sum.inr 3153) = Sparse.eval nodeValue3153 (mixedVector B) := by
    change mixedMoment B node3153 node3153Labels = _
    exact sound3153 B hB hF
  have h3156 : mixedVector B (Sum.inr 3156) = Sparse.eval nodeValue3156 (mixedVector B) := by
    change mixedMoment B node3156 node3156Labels = _
    exact sound3156 B hB hF
  have h3157 : mixedVector B (Sum.inr 3157) = Sparse.eval nodeValue3157 (mixedVector B) := by
    change mixedMoment B node3157 node3157Labels = _
    exact sound3157 B hB hF
  have h3159 : mixedVector B (Sum.inr 3159) = Sparse.eval nodeValue3159 (mixedVector B) := by
    change mixedMoment B node3159 node3159Labels = _
    exact sound3159 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm325, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2026, h3153, h3156, h3157, h3159, h3535, h4084, reducedSource276] using sourceEq325 B hB

theorem rowSound276 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row276 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck276, numericCheck276, reducedZero276 B hB hF, mul_zero]

theorem reducedZero277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource277 (mixedVector B) = 0 := by
  have h3531 : mixedVector B (Sum.inr 3531) = Sparse.eval nodeValue3531 (mixedVector B) := by
    change mixedMoment B node3531 node3531Labels = _
    exact sound3531 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3627 : mixedVector B (Sum.inr 3627) = Sparse.eval nodeValue3627 (mixedVector B) := by
    change mixedMoment B node3627 node3627Labels = _
    exact sound3627 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm326, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3531, h3533, h3535, h3544, h3627, h4084, reducedSource277] using sourceEq326 B hB

theorem rowSound277 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row277 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck277, numericCheck277, reducedZero277 B hB hF, mul_zero]

theorem reducedZero278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource278 (mixedVector B) = 0 := by
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3497 : mixedVector B (Sum.inr 3497) = Sparse.eval nodeValue3497 (mixedVector B) := by
    change mixedMoment B node3497 node3497Labels = _
    exact sound3497 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm327, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2058, h3395, h3497, h3535, h3541, h3544, h4084, reducedSource278] using sourceEq327 B hB

theorem rowSound278 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row278 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck278, numericCheck278, reducedZero278 B hB hF, mul_zero]

theorem reducedZero279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource279 (mixedVector B) = 0 := by
  have h3157 : mixedVector B (Sum.inr 3157) = Sparse.eval nodeValue3157 (mixedVector B) := by
    change mixedMoment B node3157 node3157Labels = _
    exact sound3157 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3504 : mixedVector B (Sum.inr 3504) = Sparse.eval nodeValue3504 (mixedVector B) := by
    change mixedMoment B node3504 node3504Labels = _
    exact sound3504 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h3584 : mixedVector B (Sum.inr 3584) = Sparse.eval nodeValue3584 (mixedVector B) := by
    change mixedMoment B node3584 node3584Labels = _
    exact sound3584 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm328, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3157, h3392, h3504, h3506, h3535, h3584, h4084, reducedSource279] using sourceEq328 B hB

theorem rowSound279 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row279 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck279, numericCheck279, reducedZero279 B hB hF, mul_zero]

theorem reducedZero280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource280 (mixedVector B) = 0 := by
  have h2028 : mixedVector B (Sum.inr 2028) = Sparse.eval nodeValue2028 (mixedVector B) := by
    change mixedMoment B node2028 node2028Labels = _
    exact sound2028 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3488 : mixedVector B (Sum.inr 3488) = Sparse.eval nodeValue3488 (mixedVector B) := by
    change mixedMoment B node3488 node3488Labels = _
    exact sound3488 B hB hF
  have h3506 : mixedVector B (Sum.inr 3506) = Sparse.eval nodeValue3506 (mixedVector B) := by
    change mixedMoment B node3506 node3506Labels = _
    exact sound3506 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3535 : mixedVector B (Sum.inr 3535) = Sparse.eval nodeValue3535 (mixedVector B) := by
    change mixedMoment B node3535 node3535Labels = _
    exact sound3535 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm329, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2028, h3379, h3488, h3506, h3533, h3535, h4084, reducedSource280] using sourceEq329 B hB

theorem rowSound280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row280 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck280, numericCheck280, reducedZero280 B hB hF, mul_zero]

theorem reducedZero283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource283 (mixedVector B) = 0 := by
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3841 : mixedVector B (Sum.inr 3841) = Sparse.eval nodeValue3841 (mixedVector B) := by
    change mixedMoment B node3841 node3841Labels = _
    exact sound3841 B hB hF
  have h3906 : mixedVector B (Sum.inr 3906) = Sparse.eval nodeValue3906 (mixedVector B) := by
    change mixedMoment B node3906 node3906Labels = _
    exact sound3906 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm333, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2732, h3814, h3841, h3906, h4092, reducedSource283] using sourceEq333 B hB

theorem rowSound283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row283 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck283, numericCheck283, reducedZero283 B hB hF, mul_zero]

theorem reducedZero284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource284 (mixedVector B) = 0 := by
  have h1278 : mixedVector B (Sum.inr 1278) = Sparse.eval nodeValue1278 (mixedVector B) := by
    change mixedMoment B node1278 node1278Labels = _
    exact sound1278 B hB hF
  have h2578 : mixedVector B (Sum.inr 2578) = Sparse.eval nodeValue2578 (mixedVector B) := by
    change mixedMoment B node2578 node2578Labels = _
    exact sound2578 B hB hF
  have h2649 : mixedVector B (Sum.inr 2649) = Sparse.eval nodeValue2649 (mixedVector B) := by
    change mixedMoment B node2649 node2649Labels = _
    exact sound2649 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm335, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1278, h2578, h2649, h2732, h2758, h2773, h4092, reducedSource284] using sourceEq335 B hB

theorem rowSound284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row284 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck284, numericCheck284, reducedZero284 B hB hF, mul_zero]

theorem reducedZero285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource285 (mixedVector B) = 0 := by
  have h2494 : mixedVector B (Sum.inr 2494) = Sparse.eval nodeValue2494 (mixedVector B) := by
    change mixedMoment B node2494 node2494Labels = _
    exact sound2494 B hB hF
  have h2497 : mixedVector B (Sum.inr 2497) = Sparse.eval nodeValue2497 (mixedVector B) := by
    change mixedMoment B node2497 node2497Labels = _
    exact sound2497 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm336, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2494, h2497, h2499, h2515, h2732, h3814, h4092, reducedSource285] using sourceEq336 B hB

theorem rowSound285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row285 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck285, numericCheck285, reducedZero285 B hB hF, mul_zero]

theorem sourceRowsAt272 : MixedData.sourceRows (272 : Fin 2425) =
    MixedData.row272 := by decide +kernel

theorem sourceRowsAt273 : MixedData.sourceRows (273 : Fin 2425) =
    MixedData.row273 := by decide +kernel

theorem sourceRowsAt274 : MixedData.sourceRows (274 : Fin 2425) =
    MixedData.row274 := by decide +kernel

theorem sourceRowsAt275 : MixedData.sourceRows (275 : Fin 2425) =
    MixedData.row275 := by decide +kernel

theorem sourceRowsAt276 : MixedData.sourceRows (276 : Fin 2425) =
    MixedData.row276 := by decide +kernel

theorem sourceRowsAt277 : MixedData.sourceRows (277 : Fin 2425) =
    MixedData.row277 := by decide +kernel

theorem sourceRowsAt278 : MixedData.sourceRows (278 : Fin 2425) =
    MixedData.row278 := by decide +kernel

theorem sourceRowsAt279 : MixedData.sourceRows (279 : Fin 2425) =
    MixedData.row279 := by decide +kernel

theorem sourceRowsAt280 : MixedData.sourceRows (280 : Fin 2425) =
    MixedData.row280 := by decide +kernel

theorem sourceRowsAt281 : MixedData.sourceRows (281 : Fin 2425) =
    MixedData.row281 := by decide +kernel

theorem sourceRowsAt282 : MixedData.sourceRows (282 : Fin 2425) =
    MixedData.row282 := by decide +kernel

theorem sourceRowsAt283 : MixedData.sourceRows (283 : Fin 2425) =
    MixedData.row283 := by decide +kernel

theorem sourceRowsAt284 : MixedData.sourceRows (284 : Fin 2425) =
    MixedData.row284 := by decide +kernel

theorem sourceRowsAt285 : MixedData.sourceRows (285 : Fin 2425) =
    MixedData.row285 := by decide +kernel

theorem sourceRowsAt286 : MixedData.sourceRows (286 : Fin 2425) =
    MixedData.row286 := by decide +kernel

theorem sourceRowsAt287 : MixedData.sourceRows (287 : Fin 2425) =
    MixedData.row287 := by decide +kernel

theorem chunkSound17_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 17) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 272 ∨ k.val = 273 ∨ k.val = 274 ∨ k.val = 275 ∨ k.val = 276 ∨ k.val = 277 ∨ k.val = 278 ∨ k.val = 279 ∨ k.val = 280 ∨ k.val = 281 ∨ k.val = 282 ∨ k.val = 283 ∨ k.val = 284 ∨ k.val = 285 ∨ k.val = 286 ∨ k.val = 287 := by omega
  rcases heq with h272 | h273 | h274 | h275 | h276 | h277 | h278 | h279 | h280 | h281 | h282 | h283 | h284 | h285 | h286 | h287
  · have he : k = (272 : Fin 2425) := Fin.ext h272
    subst k
    rw [sourceRowsAt272]
    exact rowSound272 B hB hF
  · have he : k = (273 : Fin 2425) := Fin.ext h273
    subst k
    rw [sourceRowsAt273]
    exact rowSound273 B hB hF
  · have he : k = (274 : Fin 2425) := Fin.ext h274
    subst k
    rw [sourceRowsAt274]
    exact rowSound274 B hB hF
  · have he : k = (275 : Fin 2425) := Fin.ext h275
    subst k
    rw [sourceRowsAt275]
    exact rowSound275 B hB hF
  · have he : k = (276 : Fin 2425) := Fin.ext h276
    subst k
    rw [sourceRowsAt276]
    exact rowSound276 B hB hF
  · have he : k = (277 : Fin 2425) := Fin.ext h277
    subst k
    rw [sourceRowsAt277]
    exact rowSound277 B hB hF
  · have he : k = (278 : Fin 2425) := Fin.ext h278
    subst k
    rw [sourceRowsAt278]
    exact rowSound278 B hB hF
  · have he : k = (279 : Fin 2425) := Fin.ext h279
    subst k
    rw [sourceRowsAt279]
    exact rowSound279 B hB hF
  · have he : k = (280 : Fin 2425) := Fin.ext h280
    subst k
    rw [sourceRowsAt280]
    exact rowSound280 B hB hF
  · have he : k = (281 : Fin 2425) := Fin.ext h281
    subst k
    rw [sourceRowsAt281]
    exact rowSound281_e B hB hF
  · have he : k = (282 : Fin 2425) := Fin.ext h282
    subst k
    rw [sourceRowsAt282]
    exact rowSound282_e B hB hF
  · have he : k = (283 : Fin 2425) := Fin.ext h283
    subst k
    rw [sourceRowsAt283]
    exact rowSound283 B hB hF
  · have he : k = (284 : Fin 2425) := Fin.ext h284
    subst k
    rw [sourceRowsAt284]
    exact rowSound284 B hB hF
  · have he : k = (285 : Fin 2425) := Fin.ext h285
    subst k
    rw [sourceRowsAt285]
    exact rowSound285 B hB hF
  · have he : k = (286 : Fin 2425) := Fin.ext h286
    subst k
    rw [sourceRowsAt286]
    exact rowSound286_e B hB hF
  · have he : k = (287 : Fin 2425) := Fin.ext h287
    subst k
    rw [sourceRowsAt287]
    exact rowSound287_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound17_e_oai
