-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:00:18.420846+00:00
-- url     : https://prove2.me/submissions/41030183-1128-4e01-9861-7109a8eb6822

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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound244_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound245_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound255_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6115 raw6115Labels = mixedMoment B node2973 node2973Labels := by
  calc
    mixedMoment B raw6115 raw6115Labels = mixedMoment B raw6115step0 raw6115step0Labels := by
      have ha : raw6115step0 = (fun i j => raw6115 (permutation566 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6115step0 raw6115; decide +kernel
      have hl : raw6115step0Labels = raw6115Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6115 raw6115Labels permutation566 permutation4
    _ = mixedMoment B node2973 node2973Labels := by rfl

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

theorem canonical6123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6123 raw6123Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw6123 raw6123Labels = mixedMoment B raw6123step0 raw6123step0Labels := by
      have hz : ∀ j, raw6123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6123step0 = (fun i j => raw6123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6123step0 raw6123; decide +kernel
      have hl : raw6123step0Labels = raw6123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6123 raw6123Labels permutation434 hz
    mixedMoment B raw6123step0 raw6123step0Labels = mixedMoment B raw6123step1 raw6123step1Labels := by
      have hz : ∀ j, raw6123step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6123step1 = (fun i j => raw6123step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6123step1 raw6123step0; decide +kernel
      have hl : raw6123step1Labels = raw6123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6123step0 raw6123step0Labels permutation80 hz
    mixedMoment B raw6123step1 raw6123step1Labels = mixedMoment B raw6123step2 raw6123step2Labels := by
      have ha : raw6123step2 = (fun i j => raw6123step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6123step2 raw6123step1; decide +kernel
      have hl : raw6123step2Labels = raw6123step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6123step1 raw6123step1Labels permutation9 permutation4
    mixedMoment B raw6123step2 raw6123step2Labels = mixedMoment B raw6123step3 raw6123step3Labels := by
      have ha : raw6123step3 = -raw6123step2 := by apply Matrix.ext; change ∀ i j, raw6123step3 i j = -(raw6123step2 i j); unfold raw6123step3 raw6123step2; decide +kernel
      have hl : raw6123step3Labels = raw6123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

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

theorem canonical6448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6448 raw6448Labels = mixedMoment B node3383 node3383Labels := by
  calc
    mixedMoment B raw6448 raw6448Labels = mixedMoment B raw6448step0 raw6448step0Labels := by
      have hz : ∀ j, raw6448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6448step0 = (fun i j => raw6448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6448step0 raw6448; decide +kernel
      have hl : raw6448step0Labels = raw6448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6448 raw6448Labels permutation346 hz
    mixedMoment B raw6448step0 raw6448step0Labels = mixedMoment B raw6448step1 raw6448step1Labels := by
      have ha : raw6448step1 = (fun i j => raw6448step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6448step1 raw6448step0; decide +kernel
      have hl : raw6448step1Labels = raw6448step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6448step0 raw6448step0Labels permutation36 permutation4
    mixedMoment B raw6448step1 raw6448step1Labels = mixedMoment B raw6448step2 raw6448step2Labels := by
      have ha : raw6448step2 = -raw6448step1 := by apply Matrix.ext; change ∀ i j, raw6448step2 i j = -(raw6448step1 i j); unfold raw6448step2 raw6448step1; decide +kernel
      have hl : raw6448step2Labels = raw6448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3383 node3383Labels := by rfl

theorem canonical6449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6449 raw6449Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw6449 raw6449Labels = mixedMoment B raw6449step0 raw6449step0Labels := by
      have hz : ∀ j, raw6449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6449step0 = (fun i j => raw6449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6449step0 raw6449; decide +kernel
      have hl : raw6449step0Labels = raw6449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6449 raw6449Labels permutation346 hz
    mixedMoment B raw6449step0 raw6449step0Labels = mixedMoment B raw6449step1 raw6449step1Labels := by
      have ha : raw6449step1 = (fun i j => raw6449step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6449step1 raw6449step0; decide +kernel
      have hl : raw6449step1Labels = raw6449step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6449step0 raw6449step0Labels permutation33 permutation4
    mixedMoment B raw6449step1 raw6449step1Labels = mixedMoment B raw6449step2 raw6449step2Labels := by
      have ha : raw6449step2 = -raw6449step1 := by apply Matrix.ext; change ∀ i j, raw6449step2 i j = -(raw6449step1 i j); unfold raw6449step2 raw6449step1; decide +kernel
      have hl : raw6449step2Labels = raw6449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

theorem canonical6450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6450 raw6450Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw6450 raw6450Labels = mixedMoment B raw6450step0 raw6450step0Labels := by
      have ha : raw6450step0 = (fun i j => raw6450 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6450step0 raw6450; decide +kernel
      have hl : raw6450step0Labels = raw6450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6450 raw6450Labels permutation170 permutation4
    mixedMoment B raw6450step0 raw6450step0Labels = mixedMoment B raw6450step1 raw6450step1Labels := by
      have ha : raw6450step1 = -raw6450step0 := by apply Matrix.ext; change ∀ i j, raw6450step1 i j = -(raw6450step0 i j); unfold raw6450step1 raw6450step0; decide +kernel
      have hl : raw6450step1Labels = raw6450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical6452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6452 raw6452Labels = mixedMoment B node3490 node3490Labels := by
  calc
    mixedMoment B raw6452 raw6452Labels = mixedMoment B raw6452step0 raw6452step0Labels := by
      have ha : raw6452step0 = (fun i j => raw6452 (permutation156 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6452step0 raw6452; decide +kernel
      have hl : raw6452step0Labels = raw6452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6452 raw6452Labels permutation156 permutation4
    mixedMoment B raw6452step0 raw6452step0Labels = mixedMoment B raw6452step1 raw6452step1Labels := by
      have ha : raw6452step1 = -raw6452step0 := by apply Matrix.ext; change ∀ i j, raw6452step1 i j = -(raw6452step0 i j); unfold raw6452step1 raw6452step0; decide +kernel
      have hl : raw6452step1Labels = raw6452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3490 node3490Labels := by rfl

theorem canonical6453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6453 raw6453Labels = mixedMoment B node3494 node3494Labels := by
  calc
    mixedMoment B raw6453 raw6453Labels = mixedMoment B raw6453step0 raw6453step0Labels := by
      have ha : raw6453step0 = (fun i j => raw6453 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6453step0 raw6453; decide +kernel
      have hl : raw6453step0Labels = raw6453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6453 raw6453Labels permutation153 permutation4
    mixedMoment B raw6453step0 raw6453step0Labels = mixedMoment B raw6453step1 raw6453step1Labels := by
      have ha : raw6453step1 = -raw6453step0 := by apply Matrix.ext; change ∀ i j, raw6453step1 i j = -(raw6453step0 i j); unfold raw6453step1 raw6453step0; decide +kernel
      have hl : raw6453step1Labels = raw6453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3494 node3494Labels := by rfl

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

theorem canonical6455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6455 raw6455Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw6455 raw6455Labels = mixedMoment B raw6455step0 raw6455step0Labels := by
      have hz : ∀ j, raw6455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6455step0 = (fun i j => raw6455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6455step0 raw6455; decide +kernel
      have hl : raw6455step0Labels = raw6455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6455 raw6455Labels permutation346 hz
    mixedMoment B raw6455step0 raw6455step0Labels = mixedMoment B raw6455step1 raw6455step1Labels := by
      have ha : raw6455step1 = (fun i j => raw6455step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6455step1 raw6455step0; decide +kernel
      have hl : raw6455step1Labels = raw6455step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6455step0 raw6455step0Labels permutation138 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical6547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6547 raw6547Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6547 raw6547Labels = mixedMoment B raw6547step0 raw6547step0Labels := by
      have hz : ∀ j, raw6547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6547step0 = (fun i j => raw6547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6547step0 raw6547; decide +kernel
      have hl : raw6547step0Labels = raw6547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6547 raw6547Labels permutation346 hz
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical6548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6548 raw6548Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw6548 raw6548Labels = mixedMoment B raw6548step0 raw6548step0Labels := by
      have hz : ∀ j, raw6548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6548step0 = (fun i j => raw6548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6548step0 raw6548; decide +kernel
      have hl : raw6548step0Labels = raw6548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6548 raw6548Labels permutation346 hz
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical6549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6549 raw6549Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw6549 raw6549Labels = mixedMoment B raw6549step0 raw6549step0Labels := by
      have ha : raw6549step0 = (fun i j => raw6549 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6549step0 raw6549; decide +kernel
      have hl : raw6549step0Labels = raw6549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6549 raw6549Labels permutation176 permutation2
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical6550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6550 raw6550Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6550 raw6550Labels = mixedMoment B raw6550step0 raw6550step0Labels := by
      have hz : ∀ j, raw6550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6550step0 = (fun i j => raw6550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6550step0 raw6550; decide +kernel
      have hl : raw6550step0Labels = raw6550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6550 raw6550Labels permutation346 hz
    mixedMoment B raw6550step0 raw6550step0Labels = mixedMoment B raw6550step1 raw6550step1Labels := by
      have ha : raw6550step1 = (fun i j => raw6550step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6550step1 raw6550step0; decide +kernel
      have hl : raw6550step1Labels = raw6550step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6550step0 raw6550step0Labels permutation85 permutation4
    mixedMoment B raw6550step1 raw6550step1Labels = mixedMoment B raw6550step2 raw6550step2Labels := by
      have ha : raw6550step2 = -raw6550step1 := by apply Matrix.ext; change ∀ i j, raw6550step2 i j = -(raw6550step1 i j); unfold raw6550step2 raw6550step1; decide +kernel
      have hl : raw6550step2Labels = raw6550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical6551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6551 raw6551Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw6551 raw6551Labels = mixedMoment B raw6551step0 raw6551step0Labels := by
      have hz : ∀ j, raw6551 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6551step0 = (fun i j => raw6551 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6551step0 raw6551; decide +kernel
      have hl : raw6551step0Labels = raw6551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6551 raw6551Labels permutation520 hz
    mixedMoment B raw6551step0 raw6551step0Labels = mixedMoment B raw6551step1 raw6551step1Labels := by
      have hz : ∀ j, raw6551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6551step1 = (fun i j => raw6551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6551step1 raw6551step0; decide +kernel
      have hl : raw6551step1Labels = raw6551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6551step0 raw6551step0Labels permutation80 hz
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical6552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6552 raw6552Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw6552 raw6552Labels = mixedMoment B raw6552step0 raw6552step0Labels := by
      have hz : ∀ j, raw6552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6552step0 = (fun i j => raw6552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6552step0 raw6552; decide +kernel
      have hl : raw6552step0Labels = raw6552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6552 raw6552Labels permutation346 hz
    _ = mixedMoment B node3906 node3906Labels := by rfl

theorem canonical6553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6553 raw6553Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6553 raw6553Labels = mixedMoment B raw6553step0 raw6553step0Labels := by
      have hz : ∀ j, raw6553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6553step0 = (fun i j => raw6553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6553step0 raw6553; decide +kernel
      have hl : raw6553step0Labels = raw6553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553 raw6553Labels permutation520 hz
    mixedMoment B raw6553step0 raw6553step0Labels = mixedMoment B raw6553step1 raw6553step1Labels := by
      have hz : ∀ j, raw6553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6553step1 = (fun i j => raw6553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6553step1 raw6553step0; decide +kernel
      have hl : raw6553step1Labels = raw6553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553step0 raw6553step0Labels permutation80 hz
    mixedMoment B raw6553step1 raw6553step1Labels = mixedMoment B raw6553step2 raw6553step2Labels := by
      have ha : raw6553step2 = (fun i j => raw6553step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6553step2 raw6553step1; decide +kernel
      have hl : raw6553step2Labels = raw6553step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6553step1 raw6553step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical6554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6554 raw6554Labels = mixedMoment B node1277 node1277Labels := by
  calc
    mixedMoment B raw6554 raw6554Labels = mixedMoment B raw6554step0 raw6554step0Labels := by
      have hz : ∀ j, raw6554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6554step0 = (fun i j => raw6554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6554step0 raw6554; decide +kernel
      have hl : raw6554step0Labels = raw6554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6554 raw6554Labels permutation346 hz
    mixedMoment B raw6554step0 raw6554step0Labels = mixedMoment B raw6554step1 raw6554step1Labels := by
      have ha : raw6554step1 = (fun i j => raw6554step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6554step1 raw6554step0; decide +kernel
      have hl : raw6554step1Labels = raw6554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6554step0 raw6554step0Labels permutation38 permutation2
    _ = mixedMoment B node1277 node1277Labels := by rfl

theorem canonical6555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6555 raw6555Labels = mixedMoment B node1222 node1222Labels := by
  calc
    mixedMoment B raw6555 raw6555Labels = mixedMoment B raw6555step0 raw6555step0Labels := by
      have ha : raw6555step0 = (fun i j => raw6555 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6555step0 raw6555; decide +kernel
      have hl : raw6555step0Labels = raw6555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6555 raw6555Labels permutation158 permutation2
    _ = mixedMoment B node1222 node1222Labels := by rfl

theorem canonical6556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6556 raw6556Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw6556 raw6556Labels = mixedMoment B raw6556step0 raw6556step0Labels := by
      have hz : ∀ j, raw6556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6556step0 = (fun i j => raw6556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6556step0 raw6556; decide +kernel
      have hl : raw6556step0Labels = raw6556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6556 raw6556Labels permutation346 hz
    mixedMoment B raw6556step0 raw6556step0Labels = mixedMoment B raw6556step1 raw6556step1Labels := by
      have ha : raw6556step1 = (fun i j => raw6556step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6556step1 raw6556step0; decide +kernel
      have hl : raw6556step1Labels = raw6556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6556step0 raw6556step0Labels permutation34 permutation2
    _ = mixedMoment B node1237 node1237Labels := by rfl

theorem canonical6557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6557 raw6557Labels = mixedMoment B node1226 node1226Labels := by
  calc
    mixedMoment B raw6557 raw6557Labels = mixedMoment B raw6557step0 raw6557step0Labels := by
      have hz : ∀ j, raw6557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6557step0 = (fun i j => raw6557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6557step0 raw6557; decide +kernel
      have hl : raw6557step0Labels = raw6557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6557 raw6557Labels permutation346 hz
    _ = mixedMoment B node1226 node1226Labels := by rfl

theorem canonical6558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6558 raw6558Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw6558 raw6558Labels = mixedMoment B raw6558step0 raw6558step0Labels := by
      have hz : ∀ j, raw6558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6558step0 = (fun i j => raw6558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6558step0 raw6558; decide +kernel
      have hl : raw6558step0Labels = raw6558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6558 raw6558Labels permutation346 hz
    _ = mixedMoment B node1224 node1224Labels := by rfl

theorem canonical6559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6559 raw6559Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw6559 raw6559Labels = mixedMoment B raw6559step0 raw6559step0Labels := by
      have ha : raw6559step0 = (fun i j => raw6559 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6559step0 raw6559; decide +kernel
      have hl : raw6559step0Labels = raw6559Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6559 raw6559Labels permutation182 permutation2
    _ = mixedMoment B node2577 node2577Labels := by rfl

theorem canonical6560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6560 raw6560Labels = mixedMoment B node2650 node2650Labels := by
  calc
    mixedMoment B raw6560 raw6560Labels = mixedMoment B raw6560step0 raw6560step0Labels := by
      have hz : ∀ j, raw6560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6560step0 = (fun i j => raw6560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6560step0 raw6560; decide +kernel
      have hl : raw6560step0Labels = raw6560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6560 raw6560Labels permutation346 hz
    mixedMoment B raw6560step0 raw6560step0Labels = mixedMoment B raw6560step1 raw6560step1Labels := by
      have ha : raw6560step1 = (fun i j => raw6560step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6560step1 raw6560step0; decide +kernel
      have hl : raw6560step1Labels = raw6560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6560step0 raw6560step0Labels permutation38 permutation2
    _ = mixedMoment B node2650 node2650Labels := by rfl

theorem canonical6561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6561 raw6561Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw6561 raw6561Labels = mixedMoment B raw6561step0 raw6561step0Labels := by
      have hz : ∀ j, raw6561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6561step0 = (fun i j => raw6561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6561step0 raw6561; decide +kernel
      have hl : raw6561step0Labels = raw6561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6561 raw6561Labels permutation520 hz
    mixedMoment B raw6561step0 raw6561step0Labels = mixedMoment B raw6561step1 raw6561step1Labels := by
      have hz : ∀ j, raw6561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6561step1 = (fun i j => raw6561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6561step1 raw6561step0; decide +kernel
      have hl : raw6561step1Labels = raw6561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6561step0 raw6561step0Labels permutation80 hz
    mixedMoment B raw6561step1 raw6561step1Labels = mixedMoment B raw6561step2 raw6561step2Labels := by
      have ha : raw6561step2 = (fun i j => raw6561step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6561step2 raw6561step1; decide +kernel
      have hl : raw6561step2Labels = raw6561step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6561step1 raw6561step1Labels permutation10 permutation2
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical6562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6562 raw6562Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6562 raw6562Labels = mixedMoment B raw6562step0 raw6562step0Labels := by
      have hz : ∀ j, raw6562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6562step0 = (fun i j => raw6562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6562step0 raw6562; decide +kernel
      have hl : raw6562step0Labels = raw6562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6562 raw6562Labels permutation346 hz
    mixedMoment B raw6562step0 raw6562step0Labels = mixedMoment B raw6562step1 raw6562step1Labels := by
      have ha : raw6562step1 = (fun i j => raw6562step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6562step1 raw6562step0; decide +kernel
      have hl : raw6562step1Labels = raw6562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6562step0 raw6562step0Labels permutation38 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical6563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6563 raw6563Labels = mixedMoment B node2493 node2493Labels := by
  calc
    mixedMoment B raw6563 raw6563Labels = mixedMoment B raw6563step0 raw6563step0Labels := by
      have ha : raw6563step0 = (fun i j => raw6563 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6563step0 raw6563; decide +kernel
      have hl : raw6563step0Labels = raw6563Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6563 raw6563Labels permutation158 permutation2
    _ = mixedMoment B node2493 node2493Labels := by rfl

theorem canonical6564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6564 raw6564Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw6564 raw6564Labels = mixedMoment B raw6564step0 raw6564step0Labels := by
      have hz : ∀ j, raw6564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6564step0 = (fun i j => raw6564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6564step0 raw6564; decide +kernel
      have hl : raw6564step0Labels = raw6564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6564 raw6564Labels permutation346 hz
    mixedMoment B raw6564step0 raw6564step0Labels = mixedMoment B raw6564step1 raw6564step1Labels := by
      have ha : raw6564step1 = (fun i j => raw6564step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6564step1 raw6564step0; decide +kernel
      have hl : raw6564step1Labels = raw6564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6564step0 raw6564step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical6565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6565 raw6565Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw6565 raw6565Labels = mixedMoment B raw6565step0 raw6565step0Labels := by
      have hz : ∀ j, raw6565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6565step0 = (fun i j => raw6565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6565step0 raw6565; decide +kernel
      have hl : raw6565step0Labels = raw6565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6565 raw6565Labels permutation346 hz
    _ = mixedMoment B node2499 node2499Labels := by rfl

theorem canonical6566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6566 raw6566Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw6566 raw6566Labels = mixedMoment B raw6566step0 raw6566step0Labels := by
      have hz : ∀ j, raw6566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6566step0 = (fun i j => raw6566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6566step0 raw6566; decide +kernel
      have hl : raw6566step0Labels = raw6566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6566 raw6566Labels permutation346 hz
    _ = mixedMoment B node2495 node2495Labels := by rfl

theorem canonical6567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6567 raw6567Labels = mixedMoment B node2645 node2645Labels := by
  calc
    mixedMoment B raw6567 raw6567Labels = mixedMoment B raw6567step0 raw6567step0Labels := by
      have ha : raw6567step0 = (fun i j => raw6567 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6567step0 raw6567; decide +kernel
      have hl : raw6567step0Labels = raw6567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6567 raw6567Labels permutation200 permutation2
    _ = mixedMoment B node2645 node2645Labels := by rfl

theorem canonical6568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6568 raw6568Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6568 raw6568Labels = mixedMoment B raw6568step0 raw6568step0Labels := by
      have hz : ∀ j, raw6568 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6568step0 = (fun i j => raw6568 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6568step0 raw6568; decide +kernel
      have hl : raw6568step0Labels = raw6568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6568 raw6568Labels permutation520 hz
    mixedMoment B raw6568step0 raw6568step0Labels = mixedMoment B raw6568step1 raw6568step1Labels := by
      have ha : raw6568step1 = (fun i j => raw6568step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6568step1 raw6568step0; decide +kernel
      have hl : raw6568step1Labels = raw6568step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6568step0 raw6568step0Labels permutation34 permutation2
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical6569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6569 raw6569Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw6569 raw6569Labels = mixedMoment B raw6569step0 raw6569step0Labels := by
      have ha : raw6569step0 = (fun i j => raw6569 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6569step0 raw6569; decide +kernel
      have hl : raw6569step0Labels = raw6569Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6569 raw6569Labels permutation158 permutation2
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical6570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6570 raw6570Labels = mixedMoment B node2554 node2554Labels := by
  calc
    mixedMoment B raw6570 raw6570Labels = mixedMoment B raw6570step0 raw6570step0Labels := by
      have ha : raw6570step0 = (fun i j => raw6570 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6570step0 raw6570; decide +kernel
      have hl : raw6570step0Labels = raw6570Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6570 raw6570Labels permutation178 permutation2
    _ = mixedMoment B node2554 node2554Labels := by rfl

theorem canonical6571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6571 raw6571Labels = mixedMoment B node2549 node2549Labels := by
  calc
    mixedMoment B raw6571 raw6571Labels = mixedMoment B raw6571step0 raw6571step0Labels := by
      have ha : raw6571step0 = (fun i j => raw6571 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6571step0 raw6571; decide +kernel
      have hl : raw6571step0Labels = raw6571Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6571 raw6571Labels permutation176 permutation2
    _ = mixedMoment B node2549 node2549Labels := by rfl

theorem canonical6572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6572 raw6572Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw6572 raw6572Labels = mixedMoment B raw6572step0 raw6572step0Labels := by
      have ha : raw6572step0 = (fun i j => raw6572 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6572step0 raw6572; decide +kernel
      have hl : raw6572step0Labels = raw6572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6572 raw6572Labels permutation176 permutation2
    _ = mixedMoment B node2547 node2547Labels := by rfl

theorem canonical6573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6573 raw6573Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw6573 raw6573Labels = mixedMoment B raw6573step0 raw6573step0Labels := by
      have hz : ∀ j, raw6573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6573step0 = (fun i j => raw6573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6573step0 raw6573; decide +kernel
      have hl : raw6573step0Labels = raw6573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6573 raw6573Labels permutation520 hz
    mixedMoment B raw6573step0 raw6573step0Labels = mixedMoment B raw6573step1 raw6573step1Labels := by
      have hz : ∀ j, raw6573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6573step1 = (fun i j => raw6573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6573step1 raw6573step0; decide +kernel
      have hl : raw6573step1Labels = raw6573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6573step0 raw6573step0Labels permutation80 hz
    _ = mixedMoment B node2743 node2743Labels := by rfl

theorem canonical6574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6574 raw6574Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw6574 raw6574Labels = mixedMoment B raw6574step0 raw6574step0Labels := by
      have hz : ∀ j, raw6574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6574step0 = (fun i j => raw6574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6574step0 raw6574; decide +kernel
      have hl : raw6574step0Labels = raw6574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6574 raw6574Labels permutation346 hz
    mixedMoment B raw6574step0 raw6574step0Labels = mixedMoment B raw6574step1 raw6574step1Labels := by
      have ha : raw6574step1 = (fun i j => raw6574step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6574step1 raw6574step0; decide +kernel
      have hl : raw6574step1Labels = raw6574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6574step0 raw6574step0Labels permutation35 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical6575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6575 raw6575Labels = mixedMoment B node2649 node2649Labels := by
  calc
    mixedMoment B raw6575 raw6575Labels = mixedMoment B raw6575step0 raw6575step0Labels := by
      have hz : ∀ j, raw6575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6575step0 = (fun i j => raw6575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6575step0 raw6575; decide +kernel
      have hl : raw6575step0Labels = raw6575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6575 raw6575Labels permutation346 hz
    mixedMoment B raw6575step0 raw6575step0Labels = mixedMoment B raw6575step1 raw6575step1Labels := by
      have ha : raw6575step1 = (fun i j => raw6575step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6575step1 raw6575step0; decide +kernel
      have hl : raw6575step1Labels = raw6575step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6575step0 raw6575step0Labels permutation38 permutation2
    _ = mixedMoment B node2649 node2649Labels := by rfl

theorem canonical6576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6576 raw6576Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw6576 raw6576Labels = mixedMoment B raw6576step0 raw6576step0Labels := by
      have hz : ∀ j, raw6576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6576step0 = (fun i j => raw6576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6576step0 raw6576; decide +kernel
      have hl : raw6576step0Labels = raw6576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6576 raw6576Labels permutation346 hz
    mixedMoment B raw6576step0 raw6576step0Labels = mixedMoment B raw6576step1 raw6576step1Labels := by
      have ha : raw6576step1 = (fun i j => raw6576step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6576step1 raw6576step0; decide +kernel
      have hl : raw6576step1Labels = raw6576step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6576step0 raw6576step0Labels permutation38 permutation2
    _ = mixedMoment B node2647 node2647Labels := by rfl

theorem canonical6577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6577 raw6577Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6577 raw6577Labels = mixedMoment B raw6577step0 raw6577step0Labels := by
      have hz : ∀ j, raw6577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6577step0 = (fun i j => raw6577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6577step0 raw6577; decide +kernel
      have hl : raw6577step0Labels = raw6577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6577 raw6577Labels permutation346 hz
    mixedMoment B raw6577step0 raw6577step0Labels = mixedMoment B raw6577step1 raw6577step1Labels := by
      have ha : raw6577step1 = (fun i j => raw6577step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6577step1 raw6577step0; decide +kernel
      have hl : raw6577step1Labels = raw6577step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6577step0 raw6577step0Labels permutation33 permutation2
    _ = mixedMoment B node2732 node2732Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1222 node1222Labels = Sparse.eval nodeValue1222 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1222) = mixedMoment B node1222 node1222Labels := rfl
  simpa [nodeValue1222, Sparse.eval] using hc.symm

theorem sound1224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1224 node1224Labels = Sparse.eval nodeValue1224 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1224) = mixedMoment B node1224 node1224Labels := rfl
  simpa [nodeValue1224, Sparse.eval] using hc.symm

theorem sound1226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1226 node1226Labels = Sparse.eval nodeValue1226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1226) = mixedMoment B node1226 node1226Labels := rfl
  simpa [nodeValue1226, Sparse.eval] using hc.symm

theorem sound1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1237 node1237Labels = Sparse.eval nodeValue1237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1237) = mixedMoment B node1237 node1237Labels := rfl
  simpa [nodeValue1237, Sparse.eval] using hc.symm

theorem sound1277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1277 node1277Labels = Sparse.eval nodeValue1277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1277) = mixedMoment B node1277 node1277Labels := rfl
  simpa [nodeValue1277, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2493 node2493Labels = Sparse.eval nodeValue2493 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2493) = mixedMoment B node2493 node2493Labels := rfl
  simpa [nodeValue2493, Sparse.eval] using hc.symm

theorem sound2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2495 node2495Labels = Sparse.eval nodeValue2495 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2495) = mixedMoment B node2495 node2495Labels := rfl
  simpa [nodeValue2495, Sparse.eval] using hc.symm

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

theorem sound2499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2499 node2499Labels = Sparse.eval nodeValue2499 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2499) = mixedMoment B node2499 node2499Labels := rfl
  simpa [nodeValue2499, Sparse.eval] using hc.symm

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

theorem sound2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2547 node2547Labels = Sparse.eval nodeValue2547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2547) = mixedMoment B node2547 node2547Labels := rfl
  simpa [nodeValue2547, Sparse.eval] using hc.symm

theorem sound2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2549 node2549Labels = Sparse.eval nodeValue2549 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2549) = mixedMoment B node2549 node2549Labels := rfl
  simpa [nodeValue2549, Sparse.eval] using hc.symm

theorem sound2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2554 node2554Labels = Sparse.eval nodeValue2554 (mixedVector B) := by
  simpa only [nodeValue2554, Sparse.eval_nil] using zero2554 B _hB _hF

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

theorem sound2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2592 node2592Labels = Sparse.eval nodeValue2592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2592) = mixedMoment B node2592 node2592Labels := rfl
  simpa [nodeValue2592, Sparse.eval] using hc.symm

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

theorem sound2645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2645 node2645Labels = Sparse.eval nodeValue2645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2645) = mixedMoment B node2645 node2645Labels := rfl
  simpa [nodeValue2645, Sparse.eval] using hc.symm

theorem sound2647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2647 node2647Labels = Sparse.eval nodeValue2647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2647) = mixedMoment B node2647 node2647Labels := rfl
  simpa [nodeValue2647, Sparse.eval] using hc.symm

theorem sound2649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2649 node2649Labels = Sparse.eval nodeValue2649 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2649) = mixedMoment B node2649 node2649Labels := rfl
  simpa [nodeValue2649, Sparse.eval] using hc.symm

theorem sound2650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2650 node2650Labels = Sparse.eval nodeValue2650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2650) = mixedMoment B node2650 node2650Labels := rfl
  simpa [nodeValue2650, Sparse.eval] using hc.symm

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

theorem sound2730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2730 node2730Labels = Sparse.eval nodeValue2730 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2730) = mixedMoment B node2730 node2730Labels := rfl
  simpa [nodeValue2730, Sparse.eval] using hc.symm

theorem sound2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2731 node2731Labels = Sparse.eval nodeValue2731 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2731) = mixedMoment B node2731 node2731Labels := rfl
  simpa [nodeValue2731, Sparse.eval] using hc.symm

theorem sound2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2732 node2732Labels = Sparse.eval nodeValue2732 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2732) = mixedMoment B node2732 node2732Labels := rfl
  simpa [nodeValue2732, Sparse.eval] using hc.symm

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2773 node2773Labels = Sparse.eval nodeValue2773 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2773) = mixedMoment B node2773 node2773Labels := rfl
  simpa [nodeValue2773, Sparse.eval] using hc.symm

theorem sound2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2774 node2774Labels = Sparse.eval nodeValue2774 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2774) = mixedMoment B node2774 node2774Labels := rfl
  simpa [nodeValue2774, Sparse.eval] using hc.symm

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

theorem sound2973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2973 node2973Labels = Sparse.eval nodeValue2973 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2973) = mixedMoment B node2973 node2973Labels := rfl
  simpa [nodeValue2973, Sparse.eval] using hc.symm

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

theorem sound3383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3383 node3383Labels = Sparse.eval nodeValue3383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3383) = mixedMoment B node3383 node3383Labels := rfl
  simpa [nodeValue3383, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3494 node3494Labels = 0 := by
  exact mixedMoment_alpha B hF node3494 node3494Labels 1 permutation436
    (by decide +kernel)

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

theorem sound3490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3490 node3490Labels = Sparse.eval nodeValue3490 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3490) = mixedMoment B node3490 node3490Labels := rfl
  simpa [nodeValue3490, Sparse.eval] using hc.symm

theorem sound3494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3494 node3494Labels = Sparse.eval nodeValue3494 (mixedVector B) := by
  simpa only [nodeValue3494, Sparse.eval_nil] using zero3494 B _hB _hF

theorem sound3502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3502 node3502Labels = Sparse.eval nodeValue3502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3502) = mixedMoment B node3502 node3502Labels := rfl
  simpa [nodeValue3502, Sparse.eval] using hc.symm

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

theorem sound3539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3539 node3539Labels = Sparse.eval nodeValue3539 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3539) = mixedMoment B node3539 node3539Labels := rfl
  simpa [nodeValue3539, Sparse.eval] using hc.symm

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

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

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3813 node3813Labels = Sparse.eval nodeValue3813 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3813) = mixedMoment B node3813 node3813Labels := rfl
  simpa [nodeValue3813, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources8
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm286 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA286 + difference 0 2) (sourceB286 + difference 2 0) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA286 + difference 0 2) (sourceB286 + difference 2 0) sourceC286) = raw6436 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6436; decide +kernel
    rw [ha]
    exact (canonical6436 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA286 + difference 1 2) (sourceB286 + difference 2 1) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA286 + difference 1 2) (sourceB286 + difference 2 1) sourceC286) = raw6444 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6444; decide +kernel
    rw [ha]
    exact (canonical6444 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA286 + difference 2 2) (sourceB286 + difference 2 2) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA286 + difference 2 2) (sourceB286 + difference 2 2) sourceC286) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA286 + difference 3 2) (sourceB286 + difference 2 3) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3490) := by
    have ha : (tripleCharges (sourceA286 + difference 3 2) (sourceB286 + difference 2 3) sourceC286) = raw6452 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6452; decide +kernel
    rw [ha]
    exact (canonical6452 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA286 + difference 4 2) (sourceB286 + difference 2 4) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2973) := by
    have ha : (tripleCharges (sourceA286 + difference 4 2) (sourceB286 + difference 2 4) sourceC286) = raw6115 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6115; decide +kernel
    rw [ha]
    exact (canonical6115 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA286 + difference 5 2) (sourceB286 + difference 2 5) sourceC286) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA286 + difference 5 2) (sourceB286 + difference 2 5) sourceC286) = raw6453 := by
      apply Matrix.ext; unfold tripleCharges sourceA286 sourceB286 sourceC286 difference raw6453; decide +kernel
    rw [ha]
    exact (canonical6453 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA286 + sourceB286) sourceC286) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA286 + sourceB286) sourceC286) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA286 sourceB286 sourceC286 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA286 sourceB286 sourceC286
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm286, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm287 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA287 + difference 3 0) (sourceB287 + difference 0 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA287 + difference 3 0) (sourceB287 + difference 0 3) sourceC287) = raw6441 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6441; decide +kernel
    rw [ha]
    exact (canonical6441 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA287 + difference 3 1) (sourceB287 + difference 1 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3383) := by
    have ha : (tripleCharges (sourceA287 + difference 3 1) (sourceB287 + difference 1 3) sourceC287) = raw6448 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6448; decide +kernel
    rw [ha]
    exact (canonical6448 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA287 + difference 3 2) (sourceB287 + difference 2 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3490) := by
    have ha : (tripleCharges (sourceA287 + difference 3 2) (sourceB287 + difference 2 3) sourceC287) = raw6452 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6452; decide +kernel
    rw [ha]
    exact (canonical6452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA287 + difference 3 3) (sourceB287 + difference 3 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA287 + difference 3 3) (sourceB287 + difference 3 3) sourceC287) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA287 + difference 3 4) (sourceB287 + difference 4 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA287 + difference 3 4) (sourceB287 + difference 4 3) sourceC287) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA287 + difference 3 5) (sourceB287 + difference 5 3) sourceC287) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA287 + difference 3 5) (sourceB287 + difference 5 3) sourceC287) = raw6455 := by
      apply Matrix.ext; unfold tripleCharges sourceA287 sourceB287 sourceC287 difference raw6455; decide +kernel
    rw [ha]
    exact (canonical6455 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA287 + sourceB287) sourceC287) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA287 + sourceB287) sourceC287) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA287 sourceB287 sourceC287 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA287 sourceB287 sourceC287
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm287, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources9
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm288 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA288 + difference 0 4) (sourceB288 + difference 4 0) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA288 + difference 0 4) (sourceB288 + difference 4 0) sourceC288) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA288 + difference 1 4) (sourceB288 + difference 4 1) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA288 + difference 1 4) (sourceB288 + difference 4 1) sourceC288) = raw6445 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6445; decide +kernel
    rw [ha]
    exact (canonical6445 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA288 + difference 2 4) (sourceB288 + difference 4 2) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA288 + difference 2 4) (sourceB288 + difference 4 2) sourceC288) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA288 + difference 3 4) (sourceB288 + difference 4 3) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA288 + difference 3 4) (sourceB288 + difference 4 3) sourceC288) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA288 + difference 4 4) (sourceB288 + difference 4 4) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA288 + difference 4 4) (sourceB288 + difference 4 4) sourceC288) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA288 + difference 5 4) (sourceB288 + difference 4 5) sourceC288) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA288 + difference 5 4) (sourceB288 + difference 4 5) sourceC288) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA288 sourceB288 sourceC288 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA288 + sourceB288) sourceC288) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA288 + sourceB288) sourceC288) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA288 sourceB288 sourceC288 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA288 sourceB288 sourceC288
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm288, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm289 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA289 + difference 5 0) (sourceB289 + difference 0 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2054) := by
    have ha : (tripleCharges (sourceA289 + difference 5 0) (sourceB289 + difference 0 5) sourceC289) = raw6443 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6443; decide +kernel
    rw [ha]
    exact (canonical6443 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA289 + difference 5 1) (sourceB289 + difference 1 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3392) := by
    have ha : (tripleCharges (sourceA289 + difference 5 1) (sourceB289 + difference 1 5) sourceC289) = raw6449 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6449; decide +kernel
    rw [ha]
    exact (canonical6449 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA289 + difference 5 2) (sourceB289 + difference 2 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA289 + difference 5 2) (sourceB289 + difference 2 5) sourceC289) = raw6453 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6453; decide +kernel
    rw [ha]
    exact (canonical6453 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA289 + difference 5 3) (sourceB289 + difference 3 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA289 + difference 5 3) (sourceB289 + difference 3 5) sourceC289) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA289 + difference 5 4) (sourceB289 + difference 4 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3544) := by
    have ha : (tripleCharges (sourceA289 + difference 5 4) (sourceB289 + difference 4 5) sourceC289) = raw6456 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6456; decide +kernel
    rw [ha]
    exact (canonical6456 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA289 + difference 5 5) (sourceB289 + difference 5 5) sourceC289) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA289 + difference 5 5) (sourceB289 + difference 5 5) sourceC289) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA289 sourceB289 sourceC289 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA289 + sourceB289) sourceC289) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA289 + sourceB289) sourceC289) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA289 sourceB289 sourceC289 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA289 sourceB289 sourceC289
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm289, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm293 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA293 + difference 0 0) (sourceB293 + difference 0 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA293 + difference 0 0) (sourceB293 + difference 0 0) sourceC293) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA293 + difference 0 1) (sourceB293 + difference 1 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA293 + difference 0 1) (sourceB293 + difference 1 0) sourceC293) = raw6548 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6548; decide +kernel
    rw [ha]
    exact (canonical6548 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA293 + difference 0 2) (sourceB293 + difference 2 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA293 + difference 0 2) (sourceB293 + difference 2 0) sourceC293) = raw6549 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6549; decide +kernel
    rw [ha]
    exact (canonical6549 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA293 + difference 0 3) (sourceB293 + difference 3 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA293 + difference 0 3) (sourceB293 + difference 3 0) sourceC293) = raw6550 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6550; decide +kernel
    rw [ha]
    exact (canonical6550 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA293 + difference 0 4) (sourceB293 + difference 4 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA293 + difference 0 4) (sourceB293 + difference 4 0) sourceC293) = raw6551 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6551; decide +kernel
    rw [ha]
    exact (canonical6551 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA293 + difference 0 5) (sourceB293 + difference 5 0) sourceC293) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3906) := by
    have ha : (tripleCharges (sourceA293 + difference 0 5) (sourceB293 + difference 5 0) sourceC293) = raw6552 := by
      apply Matrix.ext; unfold tripleCharges sourceA293 sourceB293 sourceC293 difference raw6552; decide +kernel
    rw [ha]
    exact (canonical6552 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA293 + sourceB293) sourceC293) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA293 + sourceB293) sourceC293) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA293 sourceB293 sourceC293 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA293 sourceB293 sourceC293
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm293, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm294 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA294 + difference 0 0) (sourceB294 + difference 0 0) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA294 + difference 0 0) (sourceB294 + difference 0 0) sourceC294) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA294 + difference 1 0) (sourceB294 + difference 0 1) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA294 + difference 1 0) (sourceB294 + difference 0 1) sourceC294) = raw6554 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6554; decide +kernel
    rw [ha]
    exact (canonical6554 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA294 + difference 2 0) (sourceB294 + difference 0 2) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1222) := by
    have ha : (tripleCharges (sourceA294 + difference 2 0) (sourceB294 + difference 0 2) sourceC294) = raw6555 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6555; decide +kernel
    rw [ha]
    exact (canonical6555 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA294 + difference 3 0) (sourceB294 + difference 0 3) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA294 + difference 3 0) (sourceB294 + difference 0 3) sourceC294) = raw6556 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6556; decide +kernel
    rw [ha]
    exact (canonical6556 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA294 + difference 4 0) (sourceB294 + difference 0 4) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA294 + difference 4 0) (sourceB294 + difference 0 4) sourceC294) = raw6557 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6557; decide +kernel
    rw [ha]
    exact (canonical6557 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA294 + difference 5 0) (sourceB294 + difference 0 5) sourceC294) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1224) := by
    have ha : (tripleCharges (sourceA294 + difference 5 0) (sourceB294 + difference 0 5) sourceC294) = raw6558 := by
      apply Matrix.ext; unfold tripleCharges sourceA294 sourceB294 sourceC294 difference raw6558; decide +kernel
    rw [ha]
    exact (canonical6558 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA294 + sourceB294) sourceC294) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA294 + sourceB294) sourceC294) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA294 sourceB294 sourceC294 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA294 sourceB294 sourceC294
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm294, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm295 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA295 + difference 1 0) (sourceB295 + difference 0 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1277) := by
    have ha : (tripleCharges (sourceA295 + difference 1 0) (sourceB295 + difference 0 1) sourceC295) = raw6554 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6554; decide +kernel
    rw [ha]
    exact (canonical6554 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA295 + difference 1 1) (sourceB295 + difference 1 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA295 + difference 1 1) (sourceB295 + difference 1 1) sourceC295) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA295 + difference 1 2) (sourceB295 + difference 2 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA295 + difference 1 2) (sourceB295 + difference 2 1) sourceC295) = raw6559 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6559; decide +kernel
    rw [ha]
    exact (canonical6559 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA295 + difference 1 3) (sourceB295 + difference 3 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2650) := by
    have ha : (tripleCharges (sourceA295 + difference 1 3) (sourceB295 + difference 3 1) sourceC295) = raw6560 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6560; decide +kernel
    rw [ha]
    exact (canonical6560 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA295 + difference 1 4) (sourceB295 + difference 4 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2774) := by
    have ha : (tripleCharges (sourceA295 + difference 1 4) (sourceB295 + difference 4 1) sourceC295) = raw6561 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6561; decide +kernel
    rw [ha]
    exact (canonical6561 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA295 + difference 1 5) (sourceB295 + difference 5 1) sourceC295) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA295 + difference 1 5) (sourceB295 + difference 5 1) sourceC295) = raw6562 := by
      apply Matrix.ext; unfold tripleCharges sourceA295 sourceB295 sourceC295 difference raw6562; decide +kernel
    rw [ha]
    exact (canonical6562 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA295 + sourceB295) sourceC295) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA295 + sourceB295) sourceC295) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA295 sourceB295 sourceC295 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA295 sourceB295 sourceC295
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm295, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm296 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA296 + difference 0 1) (sourceB296 + difference 1 0) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3813) := by
    have ha : (tripleCharges (sourceA296 + difference 0 1) (sourceB296 + difference 1 0) sourceC296) = raw6548 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6548; decide +kernel
    rw [ha]
    exact (canonical6548 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA296 + difference 1 1) (sourceB296 + difference 1 1) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA296 + difference 1 1) (sourceB296 + difference 1 1) sourceC296) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA296 + difference 2 1) (sourceB296 + difference 1 2) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA296 + difference 2 1) (sourceB296 + difference 1 2) sourceC296) = raw6563 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6563; decide +kernel
    rw [ha]
    exact (canonical6563 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA296 + difference 3 1) (sourceB296 + difference 1 3) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA296 + difference 3 1) (sourceB296 + difference 1 3) sourceC296) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA296 + difference 4 1) (sourceB296 + difference 1 4) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA296 + difference 4 1) (sourceB296 + difference 1 4) sourceC296) = raw6565 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6565; decide +kernel
    rw [ha]
    exact (canonical6565 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA296 + difference 5 1) (sourceB296 + difference 1 5) sourceC296) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2495) := by
    have ha : (tripleCharges (sourceA296 + difference 5 1) (sourceB296 + difference 1 5) sourceC296) = raw6566 := by
      apply Matrix.ext; unfold tripleCharges sourceA296 sourceB296 sourceC296 difference raw6566; decide +kernel
    rw [ha]
    exact (canonical6566 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA296 + sourceB296) sourceC296) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA296 + sourceB296) sourceC296) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA296 sourceB296 sourceC296 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA296 sourceB296 sourceC296
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm296, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm297 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA297 + difference 2 0) (sourceB297 + difference 0 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1222) := by
    have ha : (tripleCharges (sourceA297 + difference 2 0) (sourceB297 + difference 0 2) sourceC297) = raw6555 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6555; decide +kernel
    rw [ha]
    exact (canonical6555 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA297 + difference 2 1) (sourceB297 + difference 1 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2493) := by
    have ha : (tripleCharges (sourceA297 + difference 2 1) (sourceB297 + difference 1 2) sourceC297) = raw6563 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6563; decide +kernel
    rw [ha]
    exact (canonical6563 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA297 + difference 2 2) (sourceB297 + difference 2 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA297 + difference 2 2) (sourceB297 + difference 2 2) sourceC297) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA297 + difference 2 3) (sourceB297 + difference 3 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2645) := by
    have ha : (tripleCharges (sourceA297 + difference 2 3) (sourceB297 + difference 3 2) sourceC297) = raw6567 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6567; decide +kernel
    rw [ha]
    exact (canonical6567 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA297 + difference 2 4) (sourceB297 + difference 4 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA297 + difference 2 4) (sourceB297 + difference 4 2) sourceC297) = raw6568 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6568; decide +kernel
    rw [ha]
    exact (canonical6568 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA297 + difference 2 5) (sourceB297 + difference 5 2) sourceC297) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2730) := by
    have ha : (tripleCharges (sourceA297 + difference 2 5) (sourceB297 + difference 5 2) sourceC297) = raw6569 := by
      apply Matrix.ext; unfold tripleCharges sourceA297 sourceB297 sourceC297 difference raw6569; decide +kernel
    rw [ha]
    exact (canonical6569 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA297 + sourceB297) sourceC297) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA297 + sourceB297) sourceC297) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA297 sourceB297 sourceC297 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA297 sourceB297 sourceC297
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm297, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm298 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA298 + difference 0 2) (sourceB298 + difference 2 0) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA298 + difference 0 2) (sourceB298 + difference 2 0) sourceC298) = raw6549 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6549; decide +kernel
    rw [ha]
    exact (canonical6549 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA298 + difference 1 2) (sourceB298 + difference 2 1) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2577) := by
    have ha : (tripleCharges (sourceA298 + difference 1 2) (sourceB298 + difference 2 1) sourceC298) = raw6559 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6559; decide +kernel
    rw [ha]
    exact (canonical6559 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA298 + difference 2 2) (sourceB298 + difference 2 2) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA298 + difference 2 2) (sourceB298 + difference 2 2) sourceC298) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA298 + difference 3 2) (sourceB298 + difference 2 3) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA298 + difference 3 2) (sourceB298 + difference 2 3) sourceC298) = raw6570 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6570; decide +kernel
    rw [ha]
    exact (canonical6570 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA298 + difference 4 2) (sourceB298 + difference 2 4) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2549) := by
    have ha : (tripleCharges (sourceA298 + difference 4 2) (sourceB298 + difference 2 4) sourceC298) = raw6571 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6571; decide +kernel
    rw [ha]
    exact (canonical6571 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA298 + difference 5 2) (sourceB298 + difference 2 5) sourceC298) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA298 + difference 5 2) (sourceB298 + difference 2 5) sourceC298) = raw6572 := by
      apply Matrix.ext; unfold tripleCharges sourceA298 sourceB298 sourceC298 difference raw6572; decide +kernel
    rw [ha]
    exact (canonical6572 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA298 + sourceB298) sourceC298) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA298 + sourceB298) sourceC298) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA298 sourceB298 sourceC298 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA298 sourceB298 sourceC298
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm298, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm299 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA299 + difference 3 0) (sourceB299 + difference 0 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA299 + difference 3 0) (sourceB299 + difference 0 3) sourceC299) = raw6556 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6556; decide +kernel
    rw [ha]
    exact (canonical6556 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA299 + difference 3 1) (sourceB299 + difference 1 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA299 + difference 3 1) (sourceB299 + difference 1 3) sourceC299) = raw6564 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6564; decide +kernel
    rw [ha]
    exact (canonical6564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA299 + difference 3 2) (sourceB299 + difference 2 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2554) := by
    have ha : (tripleCharges (sourceA299 + difference 3 2) (sourceB299 + difference 2 3) sourceC299) = raw6570 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6570; decide +kernel
    rw [ha]
    exact (canonical6570 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA299 + difference 3 3) (sourceB299 + difference 3 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA299 + difference 3 3) (sourceB299 + difference 3 3) sourceC299) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA299 + difference 3 4) (sourceB299 + difference 4 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2743) := by
    have ha : (tripleCharges (sourceA299 + difference 3 4) (sourceB299 + difference 4 3) sourceC299) = raw6573 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6573; decide +kernel
    rw [ha]
    exact (canonical6573 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA299 + difference 3 5) (sourceB299 + difference 5 3) sourceC299) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA299 + difference 3 5) (sourceB299 + difference 5 3) sourceC299) = raw6574 := by
      apply Matrix.ext; unfold tripleCharges sourceA299 sourceB299 sourceC299 difference raw6574; decide +kernel
    rw [ha]
    exact (canonical6574 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA299 + sourceB299) sourceC299) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA299 + sourceB299) sourceC299) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA299 sourceB299 sourceC299 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA299 sourceB299 sourceC299
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm299, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm300 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA300 + difference 0 3) (sourceB300 + difference 3 0) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2773) := by
    have ha : (tripleCharges (sourceA300 + difference 0 3) (sourceB300 + difference 3 0) sourceC300) = raw6550 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6550; decide +kernel
    rw [ha]
    exact (canonical6550 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA300 + difference 1 3) (sourceB300 + difference 3 1) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2650) := by
    have ha : (tripleCharges (sourceA300 + difference 1 3) (sourceB300 + difference 3 1) sourceC300) = raw6560 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6560; decide +kernel
    rw [ha]
    exact (canonical6560 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA300 + difference 2 3) (sourceB300 + difference 3 2) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2645) := by
    have ha : (tripleCharges (sourceA300 + difference 2 3) (sourceB300 + difference 3 2) sourceC300) = raw6567 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6567; decide +kernel
    rw [ha]
    exact (canonical6567 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA300 + difference 3 3) (sourceB300 + difference 3 3) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA300 + difference 3 3) (sourceB300 + difference 3 3) sourceC300) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA300 + difference 4 3) (sourceB300 + difference 3 4) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA300 + difference 4 3) (sourceB300 + difference 3 4) sourceC300) = raw6575 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6575; decide +kernel
    rw [ha]
    exact (canonical6575 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA300 + difference 5 3) (sourceB300 + difference 3 5) sourceC300) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2647) := by
    have ha : (tripleCharges (sourceA300 + difference 5 3) (sourceB300 + difference 3 5) sourceC300) = raw6576 := by
      apply Matrix.ext; unfold tripleCharges sourceA300 sourceB300 sourceC300 difference raw6576; decide +kernel
    rw [ha]
    exact (canonical6576 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA300 + sourceB300) sourceC300) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA300 + sourceB300) sourceC300) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA300 sourceB300 sourceC300 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA300 sourceB300 sourceC300
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm300, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm301 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA301 + difference 4 0) (sourceB301 + difference 0 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1226) := by
    have ha : (tripleCharges (sourceA301 + difference 4 0) (sourceB301 + difference 0 4) sourceC301) = raw6557 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6557; decide +kernel
    rw [ha]
    exact (canonical6557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA301 + difference 4 1) (sourceB301 + difference 1 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2499) := by
    have ha : (tripleCharges (sourceA301 + difference 4 1) (sourceB301 + difference 1 4) sourceC301) = raw6565 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6565; decide +kernel
    rw [ha]
    exact (canonical6565 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA301 + difference 4 2) (sourceB301 + difference 2 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2549) := by
    have ha : (tripleCharges (sourceA301 + difference 4 2) (sourceB301 + difference 2 4) sourceC301) = raw6571 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6571; decide +kernel
    rw [ha]
    exact (canonical6571 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA301 + difference 4 3) (sourceB301 + difference 3 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2649) := by
    have ha : (tripleCharges (sourceA301 + difference 4 3) (sourceB301 + difference 3 4) sourceC301) = raw6575 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6575; decide +kernel
    rw [ha]
    exact (canonical6575 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA301 + difference 4 4) (sourceB301 + difference 4 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2731) := by
    have ha : (tripleCharges (sourceA301 + difference 4 4) (sourceB301 + difference 4 4) sourceC301) = raw6547 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6547; decide +kernel
    rw [ha]
    exact (canonical6547 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA301 + difference 4 5) (sourceB301 + difference 5 4) sourceC301) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA301 + difference 4 5) (sourceB301 + difference 5 4) sourceC301) = raw6577 := by
      apply Matrix.ext; unfold tripleCharges sourceA301 sourceB301 sourceC301 difference raw6577; decide +kernel
    rw [ha]
    exact (canonical6577 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA301 + sourceB301) sourceC301) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA301 + sourceB301) sourceC301) = raw6553 := by
      apply Matrix.ext; unfold doubleCharges sourceA301 sourceB301 sourceC301 raw6553; decide +kernel
    rw [ha]
    exact (canonical6553 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA301 sourceB301 sourceC301
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm301, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck240 : Integer.Sparse.reindex keyMap MixedData.row240 = numericRow240 := by decide +kernel

theorem numericCheck240 (x : Master → ℝ) : Integer.Sparse.eval numericRow240 x =
    (1 : ℝ) * reducedSource240 x := by
  norm_num [numericRow240, reducedSource240, Integer.Sparse.eval, Sparse.eval, nodeValue2973, nodeValue3490, nodeValue3494, nodeValue3502, nodeValue3540, nodeValue4084]

theorem reindexCheck241 : Integer.Sparse.reindex keyMap MixedData.row241 = numericRow241 := by decide +kernel

theorem numericCheck241 (x : Master → ℝ) : Integer.Sparse.eval numericRow241 x =
    (1 : ℝ) * reducedSource241 x := by
  norm_num [numericRow241, reducedSource241, Integer.Sparse.eval, Sparse.eval, nodeValue2039, nodeValue2592, nodeValue3383, nodeValue3490, nodeValue3540, nodeValue3541, nodeValue4084]

theorem reindexCheck242 : Integer.Sparse.reindex keyMap MixedData.row242 = numericRow242 := by decide +kernel

theorem numericCheck242 (x : Master → ℝ) : Integer.Sparse.eval numericRow242 x =
    (1 : ℝ) * reducedSource242 x := by
  norm_num [numericRow242, reducedSource242, Integer.Sparse.eval, Sparse.eval, nodeValue3533, nodeValue3539, nodeValue3540, nodeValue3541, nodeValue3544, nodeValue3632, nodeValue4084]

theorem reindexCheck243 : Integer.Sparse.reindex keyMap MixedData.row243 = numericRow243 := by decide +kernel

theorem numericCheck243 (x : Master → ℝ) : Integer.Sparse.eval numericRow243 x =
    (1 : ℝ) * reducedSource243 x := by
  norm_num [numericRow243, reducedSource243, Integer.Sparse.eval, Sparse.eval, nodeValue2054, nodeValue3392, nodeValue3494, nodeValue3540, nodeValue3544, nodeValue3548, nodeValue4084]

theorem reindexCheck246 : Integer.Sparse.reindex keyMap MixedData.row246 = numericRow246 := by decide +kernel

theorem numericCheck246 (x : Master → ℝ) : Integer.Sparse.eval numericRow246 x =
    (1 : ℝ) * reducedSource246 x := by
  norm_num [numericRow246, reducedSource246, Integer.Sparse.eval, Sparse.eval, nodeValue2731, nodeValue2773, nodeValue3813, nodeValue3840, nodeValue3906, nodeValue3907, nodeValue4092]

theorem reindexCheck247 : Integer.Sparse.reindex keyMap MixedData.row247 = numericRow247 := by decide +kernel

theorem numericCheck247 (x : Master → ℝ) : Integer.Sparse.eval numericRow247 x =
    (1 : ℝ) * reducedSource247 x := by
  norm_num [numericRow247, reducedSource247, Integer.Sparse.eval, Sparse.eval, nodeValue1222, nodeValue1224, nodeValue1226, nodeValue1237, nodeValue1277, nodeValue2731, nodeValue4092]

theorem reindexCheck248 : Integer.Sparse.reindex keyMap MixedData.row248 = numericRow248 := by decide +kernel

theorem numericCheck248 (x : Master → ℝ) : Integer.Sparse.eval numericRow248 x =
    (1 : ℝ) * reducedSource248 x := by
  norm_num [numericRow248, reducedSource248, Integer.Sparse.eval, Sparse.eval, nodeValue1277, nodeValue2577, nodeValue2650, nodeValue2731, nodeValue2773, nodeValue2774, nodeValue4092]

theorem reindexCheck249 : Integer.Sparse.reindex keyMap MixedData.row249 = numericRow249 := by decide +kernel

theorem numericCheck249 (x : Master → ℝ) : Integer.Sparse.eval numericRow249 x =
    (1 : ℝ) * reducedSource249 x := by
  norm_num [numericRow249, reducedSource249, Integer.Sparse.eval, Sparse.eval, nodeValue2493, nodeValue2495, nodeValue2499, nodeValue2512, nodeValue2731, nodeValue3813, nodeValue4092]

theorem reindexCheck250 : Integer.Sparse.reindex keyMap MixedData.row250 = numericRow250 := by decide +kernel

theorem numericCheck250 (x : Master → ℝ) : Integer.Sparse.eval numericRow250 x =
    (1 : ℝ) * reducedSource250 x := by
  norm_num [numericRow250, reducedSource250, Integer.Sparse.eval, Sparse.eval, nodeValue1222, nodeValue2493, nodeValue2645, nodeValue2730, nodeValue2731, nodeValue4092]

theorem reindexCheck251 : Integer.Sparse.reindex keyMap MixedData.row251 = numericRow251 := by decide +kernel

theorem numericCheck251 (x : Master → ℝ) : Integer.Sparse.eval numericRow251 x =
    (1 : ℝ) * reducedSource251 x := by
  norm_num [numericRow251, reducedSource251, Integer.Sparse.eval, Sparse.eval, nodeValue2547, nodeValue2549, nodeValue2554, nodeValue2577, nodeValue2731, nodeValue3840, nodeValue4092]

theorem reindexCheck252 : Integer.Sparse.reindex keyMap MixedData.row252 = numericRow252 := by decide +kernel

theorem numericCheck252 (x : Master → ℝ) : Integer.Sparse.eval numericRow252 x =
    (1 : ℝ) * reducedSource252 x := by
  norm_num [numericRow252, reducedSource252, Integer.Sparse.eval, Sparse.eval, nodeValue1237, nodeValue2512, nodeValue2554, nodeValue2731, nodeValue2739, nodeValue2743, nodeValue4092]

theorem reindexCheck253 : Integer.Sparse.reindex keyMap MixedData.row253 = numericRow253 := by decide +kernel

theorem numericCheck253 (x : Master → ℝ) : Integer.Sparse.eval numericRow253 x =
    (1 : ℝ) * reducedSource253 x := by
  norm_num [numericRow253, reducedSource253, Integer.Sparse.eval, Sparse.eval, nodeValue2645, nodeValue2647, nodeValue2649, nodeValue2650, nodeValue2731, nodeValue2773, nodeValue4092]

theorem reindexCheck254 : Integer.Sparse.reindex keyMap MixedData.row254 = numericRow254 := by decide +kernel

theorem numericCheck254 (x : Master → ℝ) : Integer.Sparse.eval numericRow254 x =
    (1 : ℝ) * reducedSource254 x := by
  norm_num [numericRow254, reducedSource254, Integer.Sparse.eval, Sparse.eval, nodeValue1226, nodeValue2499, nodeValue2549, nodeValue2649, nodeValue2731, nodeValue2732, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource240 (mixedVector B) = 0 := by
  have h2973 : mixedVector B (Sum.inr 2973) = Sparse.eval nodeValue2973 (mixedVector B) := by
    change mixedMoment B node2973 node2973Labels = _
    exact sound2973 B hB hF
  have h3490 : mixedVector B (Sum.inr 3490) = Sparse.eval nodeValue3490 (mixedVector B) := by
    change mixedMoment B node3490 node3490Labels = _
    exact sound3490 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm286, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2973, h3490, h3494, h3502, h3540, h4084, reducedSource240] using sourceEq286 B hB

theorem rowSound240 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row240 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck240, numericCheck240, reducedZero240 B hB hF, mul_zero]

theorem reducedZero241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource241 (mixedVector B) = 0 := by
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2592 : mixedVector B (Sum.inr 2592) = Sparse.eval nodeValue2592 (mixedVector B) := by
    change mixedMoment B node2592 node2592Labels = _
    exact sound2592 B hB hF
  have h3383 : mixedVector B (Sum.inr 3383) = Sparse.eval nodeValue3383 (mixedVector B) := by
    change mixedMoment B node3383 node3383Labels = _
    exact sound3383 B hB hF
  have h3490 : mixedVector B (Sum.inr 3490) = Sparse.eval nodeValue3490 (mixedVector B) := by
    change mixedMoment B node3490 node3490Labels = _
    exact sound3490 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm287, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2039, h2592, h3383, h3490, h3540, h3541, h4084, reducedSource241] using sourceEq287 B hB

theorem rowSound241 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row241 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck241, numericCheck241, reducedZero241 B hB hF, mul_zero]

theorem reducedZero242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource242 (mixedVector B) = 0 := by
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm288, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3533, h3539, h3540, h3541, h3544, h3632, h4084, reducedSource242] using sourceEq288 B hB

theorem rowSound242 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row242 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck242, numericCheck242, reducedZero242 B hB hF, mul_zero]

theorem reducedZero243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource243 (mixedVector B) = 0 := by
  have h2054 : mixedVector B (Sum.inr 2054) = Sparse.eval nodeValue2054 (mixedVector B) := by
    change mixedMoment B node2054 node2054Labels = _
    exact sound2054 B hB hF
  have h3392 : mixedVector B (Sum.inr 3392) = Sparse.eval nodeValue3392 (mixedVector B) := by
    change mixedMoment B node3392 node3392Labels = _
    exact sound3392 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3544 : mixedVector B (Sum.inr 3544) = Sparse.eval nodeValue3544 (mixedVector B) := by
    change mixedMoment B node3544 node3544Labels = _
    exact sound3544 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm289, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2054, h3392, h3494, h3540, h3544, h3548, h4084, reducedSource243] using sourceEq289 B hB

theorem rowSound243 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row243 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck243, numericCheck243, reducedZero243 B hB hF, mul_zero]

theorem reducedZero246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource246 (mixedVector B) = 0 := by
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3906 : mixedVector B (Sum.inr 3906) = Sparse.eval nodeValue3906 (mixedVector B) := by
    change mixedMoment B node3906 node3906Labels = _
    exact sound3906 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm293, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2731, h2773, h3813, h3840, h3906, h3907, h4092, reducedSource246] using sourceEq293 B hB

theorem rowSound246 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row246 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck246, numericCheck246, reducedZero246 B hB hF, mul_zero]

theorem reducedZero247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource247 (mixedVector B) = 0 := by
  have h1222 : mixedVector B (Sum.inr 1222) = Sparse.eval nodeValue1222 (mixedVector B) := by
    change mixedMoment B node1222 node1222Labels = _
    exact sound1222 B hB hF
  have h1224 : mixedVector B (Sum.inr 1224) = Sparse.eval nodeValue1224 (mixedVector B) := by
    change mixedMoment B node1224 node1224Labels = _
    exact sound1224 B hB hF
  have h1226 : mixedVector B (Sum.inr 1226) = Sparse.eval nodeValue1226 (mixedVector B) := by
    change mixedMoment B node1226 node1226Labels = _
    exact sound1226 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h1277 : mixedVector B (Sum.inr 1277) = Sparse.eval nodeValue1277 (mixedVector B) := by
    change mixedMoment B node1277 node1277Labels = _
    exact sound1277 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm294, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1222, h1224, h1226, h1237, h1277, h2731, h4092, reducedSource247] using sourceEq294 B hB

theorem rowSound247 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row247 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck247, numericCheck247, reducedZero247 B hB hF, mul_zero]

theorem reducedZero248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource248 (mixedVector B) = 0 := by
  have h1277 : mixedVector B (Sum.inr 1277) = Sparse.eval nodeValue1277 (mixedVector B) := by
    change mixedMoment B node1277 node1277Labels = _
    exact sound1277 B hB hF
  have h2577 : mixedVector B (Sum.inr 2577) = Sparse.eval nodeValue2577 (mixedVector B) := by
    change mixedMoment B node2577 node2577Labels = _
    exact sound2577 B hB hF
  have h2650 : mixedVector B (Sum.inr 2650) = Sparse.eval nodeValue2650 (mixedVector B) := by
    change mixedMoment B node2650 node2650Labels = _
    exact sound2650 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h2774 : mixedVector B (Sum.inr 2774) = Sparse.eval nodeValue2774 (mixedVector B) := by
    change mixedMoment B node2774 node2774Labels = _
    exact sound2774 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm295, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1277, h2577, h2650, h2731, h2773, h2774, h4092, reducedSource248] using sourceEq295 B hB

theorem rowSound248 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row248 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck248, numericCheck248, reducedZero248 B hB hF, mul_zero]

theorem reducedZero249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource249 (mixedVector B) = 0 := by
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2495 : mixedVector B (Sum.inr 2495) = Sparse.eval nodeValue2495 (mixedVector B) := by
    change mixedMoment B node2495 node2495Labels = _
    exact sound2495 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h3813 : mixedVector B (Sum.inr 3813) = Sparse.eval nodeValue3813 (mixedVector B) := by
    change mixedMoment B node3813 node3813Labels = _
    exact sound3813 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm296, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2493, h2495, h2499, h2512, h2731, h3813, h4092, reducedSource249] using sourceEq296 B hB

theorem rowSound249 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row249 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck249, numericCheck249, reducedZero249 B hB hF, mul_zero]

theorem reducedZero250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource250 (mixedVector B) = 0 := by
  have h1222 : mixedVector B (Sum.inr 1222) = Sparse.eval nodeValue1222 (mixedVector B) := by
    change mixedMoment B node1222 node1222Labels = _
    exact sound1222 B hB hF
  have h2493 : mixedVector B (Sum.inr 2493) = Sparse.eval nodeValue2493 (mixedVector B) := by
    change mixedMoment B node2493 node2493Labels = _
    exact sound2493 B hB hF
  have h2645 : mixedVector B (Sum.inr 2645) = Sparse.eval nodeValue2645 (mixedVector B) := by
    change mixedMoment B node2645 node2645Labels = _
    exact sound2645 B hB hF
  have h2730 : mixedVector B (Sum.inr 2730) = Sparse.eval nodeValue2730 (mixedVector B) := by
    change mixedMoment B node2730 node2730Labels = _
    exact sound2730 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm297, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1222, h2493, h2645, h2730, h2731, h4092, reducedSource250] using sourceEq297 B hB

theorem rowSound250 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row250 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck250, numericCheck250, reducedZero250 B hB hF, mul_zero]

theorem reducedZero251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource251 (mixedVector B) = 0 := by
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2549 : mixedVector B (Sum.inr 2549) = Sparse.eval nodeValue2549 (mixedVector B) := by
    change mixedMoment B node2549 node2549Labels = _
    exact sound2549 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2577 : mixedVector B (Sum.inr 2577) = Sparse.eval nodeValue2577 (mixedVector B) := by
    change mixedMoment B node2577 node2577Labels = _
    exact sound2577 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm298, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2547, h2549, h2554, h2577, h2731, h3840, h4092, reducedSource251] using sourceEq298 B hB

theorem rowSound251 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row251 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck251, numericCheck251, reducedZero251 B hB hF, mul_zero]

theorem reducedZero252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource252 (mixedVector B) = 0 := by
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h2554 : mixedVector B (Sum.inr 2554) = Sparse.eval nodeValue2554 (mixedVector B) := by
    change mixedMoment B node2554 node2554Labels = _
    exact sound2554 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h2743 : mixedVector B (Sum.inr 2743) = Sparse.eval nodeValue2743 (mixedVector B) := by
    change mixedMoment B node2743 node2743Labels = _
    exact sound2743 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm299, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1237, h2512, h2554, h2731, h2739, h2743, h4092, reducedSource252] using sourceEq299 B hB

theorem rowSound252 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row252 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck252, numericCheck252, reducedZero252 B hB hF, mul_zero]

theorem reducedZero253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource253 (mixedVector B) = 0 := by
  have h2645 : mixedVector B (Sum.inr 2645) = Sparse.eval nodeValue2645 (mixedVector B) := by
    change mixedMoment B node2645 node2645Labels = _
    exact sound2645 B hB hF
  have h2647 : mixedVector B (Sum.inr 2647) = Sparse.eval nodeValue2647 (mixedVector B) := by
    change mixedMoment B node2647 node2647Labels = _
    exact sound2647 B hB hF
  have h2649 : mixedVector B (Sum.inr 2649) = Sparse.eval nodeValue2649 (mixedVector B) := by
    change mixedMoment B node2649 node2649Labels = _
    exact sound2649 B hB hF
  have h2650 : mixedVector B (Sum.inr 2650) = Sparse.eval nodeValue2650 (mixedVector B) := by
    change mixedMoment B node2650 node2650Labels = _
    exact sound2650 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2773 : mixedVector B (Sum.inr 2773) = Sparse.eval nodeValue2773 (mixedVector B) := by
    change mixedMoment B node2773 node2773Labels = _
    exact sound2773 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm300, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2645, h2647, h2649, h2650, h2731, h2773, h4092, reducedSource253] using sourceEq300 B hB

theorem rowSound253 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row253 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck253, numericCheck253, reducedZero253 B hB hF, mul_zero]

theorem reducedZero254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource254 (mixedVector B) = 0 := by
  have h1226 : mixedVector B (Sum.inr 1226) = Sparse.eval nodeValue1226 (mixedVector B) := by
    change mixedMoment B node1226 node1226Labels = _
    exact sound1226 B hB hF
  have h2499 : mixedVector B (Sum.inr 2499) = Sparse.eval nodeValue2499 (mixedVector B) := by
    change mixedMoment B node2499 node2499Labels = _
    exact sound2499 B hB hF
  have h2549 : mixedVector B (Sum.inr 2549) = Sparse.eval nodeValue2549 (mixedVector B) := by
    change mixedMoment B node2549 node2549Labels = _
    exact sound2549 B hB hF
  have h2649 : mixedVector B (Sum.inr 2649) = Sparse.eval nodeValue2649 (mixedVector B) := by
    change mixedMoment B node2649 node2649Labels = _
    exact sound2649 B hB hF
  have h2731 : mixedVector B (Sum.inr 2731) = Sparse.eval nodeValue2731 (mixedVector B) := by
    change mixedMoment B node2731 node2731Labels = _
    exact sound2731 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm301, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1226, h2499, h2549, h2649, h2731, h2732, h4092, reducedSource254] using sourceEq301 B hB

theorem rowSound254 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row254 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck254, numericCheck254, reducedZero254 B hB hF, mul_zero]

theorem sourceRowsAt240 : MixedData.sourceRows (240 : Fin 2425) =
    MixedData.row240 := by decide +kernel

theorem sourceRowsAt241 : MixedData.sourceRows (241 : Fin 2425) =
    MixedData.row241 := by decide +kernel

theorem sourceRowsAt242 : MixedData.sourceRows (242 : Fin 2425) =
    MixedData.row242 := by decide +kernel

theorem sourceRowsAt243 : MixedData.sourceRows (243 : Fin 2425) =
    MixedData.row243 := by decide +kernel

theorem sourceRowsAt244 : MixedData.sourceRows (244 : Fin 2425) =
    MixedData.row244 := by decide +kernel

theorem sourceRowsAt245 : MixedData.sourceRows (245 : Fin 2425) =
    MixedData.row245 := by decide +kernel

theorem sourceRowsAt246 : MixedData.sourceRows (246 : Fin 2425) =
    MixedData.row246 := by decide +kernel

theorem sourceRowsAt247 : MixedData.sourceRows (247 : Fin 2425) =
    MixedData.row247 := by decide +kernel

theorem sourceRowsAt248 : MixedData.sourceRows (248 : Fin 2425) =
    MixedData.row248 := by decide +kernel

theorem sourceRowsAt249 : MixedData.sourceRows (249 : Fin 2425) =
    MixedData.row249 := by decide +kernel

theorem sourceRowsAt250 : MixedData.sourceRows (250 : Fin 2425) =
    MixedData.row250 := by decide +kernel

theorem sourceRowsAt251 : MixedData.sourceRows (251 : Fin 2425) =
    MixedData.row251 := by decide +kernel

theorem sourceRowsAt252 : MixedData.sourceRows (252 : Fin 2425) =
    MixedData.row252 := by decide +kernel

theorem sourceRowsAt253 : MixedData.sourceRows (253 : Fin 2425) =
    MixedData.row253 := by decide +kernel

theorem sourceRowsAt254 : MixedData.sourceRows (254 : Fin 2425) =
    MixedData.row254 := by decide +kernel

theorem sourceRowsAt255 : MixedData.sourceRows (255 : Fin 2425) =
    MixedData.row255 := by decide +kernel

theorem chunkSound15_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 15) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 240 ∨ k.val = 241 ∨ k.val = 242 ∨ k.val = 243 ∨ k.val = 244 ∨ k.val = 245 ∨ k.val = 246 ∨ k.val = 247 ∨ k.val = 248 ∨ k.val = 249 ∨ k.val = 250 ∨ k.val = 251 ∨ k.val = 252 ∨ k.val = 253 ∨ k.val = 254 ∨ k.val = 255 := by omega
  rcases heq with h240 | h241 | h242 | h243 | h244 | h245 | h246 | h247 | h248 | h249 | h250 | h251 | h252 | h253 | h254 | h255
  · have he : k = (240 : Fin 2425) := Fin.ext h240
    subst k
    rw [sourceRowsAt240]
    exact rowSound240 B hB hF
  · have he : k = (241 : Fin 2425) := Fin.ext h241
    subst k
    rw [sourceRowsAt241]
    exact rowSound241 B hB hF
  · have he : k = (242 : Fin 2425) := Fin.ext h242
    subst k
    rw [sourceRowsAt242]
    exact rowSound242 B hB hF
  · have he : k = (243 : Fin 2425) := Fin.ext h243
    subst k
    rw [sourceRowsAt243]
    exact rowSound243 B hB hF
  · have he : k = (244 : Fin 2425) := Fin.ext h244
    subst k
    rw [sourceRowsAt244]
    exact rowSound244_e B hB hF
  · have he : k = (245 : Fin 2425) := Fin.ext h245
    subst k
    rw [sourceRowsAt245]
    exact rowSound245_e B hB hF
  · have he : k = (246 : Fin 2425) := Fin.ext h246
    subst k
    rw [sourceRowsAt246]
    exact rowSound246 B hB hF
  · have he : k = (247 : Fin 2425) := Fin.ext h247
    subst k
    rw [sourceRowsAt247]
    exact rowSound247 B hB hF
  · have he : k = (248 : Fin 2425) := Fin.ext h248
    subst k
    rw [sourceRowsAt248]
    exact rowSound248 B hB hF
  · have he : k = (249 : Fin 2425) := Fin.ext h249
    subst k
    rw [sourceRowsAt249]
    exact rowSound249 B hB hF
  · have he : k = (250 : Fin 2425) := Fin.ext h250
    subst k
    rw [sourceRowsAt250]
    exact rowSound250 B hB hF
  · have he : k = (251 : Fin 2425) := Fin.ext h251
    subst k
    rw [sourceRowsAt251]
    exact rowSound251 B hB hF
  · have he : k = (252 : Fin 2425) := Fin.ext h252
    subst k
    rw [sourceRowsAt252]
    exact rowSound252 B hB hF
  · have he : k = (253 : Fin 2425) := Fin.ext h253
    subst k
    rw [sourceRowsAt253]
    exact rowSound253 B hB hF
  · have he : k = (254 : Fin 2425) := Fin.ext h254
    subst k
    rw [sourceRowsAt254]
    exact rowSound254 B hB hF
  · have he : k = (255 : Fin 2425) := Fin.ext h255
    subst k
    rw [sourceRowsAt255]
    exact rowSound255_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound15_e_oai
