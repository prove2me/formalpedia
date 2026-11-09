-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:36:32.934193+00:00
-- url     : https://prove2.me/submissions/a2941bd6-e1c5-4931-99b6-cd048401374e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
import Definitions.Def_OAIQ106E104
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical191
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24552 raw24552Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24552 raw24552Labels = mixedMoment B raw24552step0 raw24552step0Labels := by
      have hz : ∀ j, raw24552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24552step0 = (fun i j => raw24552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24552step0 raw24552; decide +kernel
      have hl : raw24552step0Labels = raw24552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24552 raw24552Labels permutation265 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical193
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24746 raw24746Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24746 raw24746Labels = mixedMoment B raw24746step0 raw24746step0Labels := by
      have hz : ∀ j, raw24746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24746step0 = (fun i j => raw24746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24746step0 raw24746; decide +kernel
      have hl : raw24746step0Labels = raw24746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746 raw24746Labels permutation520 hz
    mixedMoment B raw24746step0 raw24746step0Labels = mixedMoment B raw24746step1 raw24746step1Labels := by
      have hz : ∀ j, raw24746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24746step1 = (fun i j => raw24746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24746step1 raw24746step0; decide +kernel
      have hl : raw24746step1Labels = raw24746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746step0 raw24746step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical24747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24747 raw24747Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw24747 raw24747Labels = mixedMoment B raw24747step0 raw24747step0Labels := by
      have ha : raw24747step0 = (fun i j => raw24747 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24747step0 raw24747; decide +kernel
      have hl : raw24747step0Labels = raw24747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24747 raw24747Labels permutation154 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical24750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24750 raw24750Labels = mixedMoment B node1151 node1151Labels := by
  calc
    _ = mixedMoment B node1151 node1151Labels := by rfl

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

theorem canonical27508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27508 raw27508Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw27508 raw27508Labels = mixedMoment B raw27508step0 raw27508step0Labels := by
      have ha : raw27508step0 = (fun i j => raw27508 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27508step0 raw27508; decide +kernel
      have hl : raw27508step0Labels = raw27508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27508 raw27508Labels permutation686 permutation2
    mixedMoment B raw27508step0 raw27508step0Labels = mixedMoment B raw27508step1 raw27508step1Labels := by
      have ha : raw27508step1 = -raw27508step0 := by apply Matrix.ext; change ∀ i j, raw27508step1 i j = -(raw27508step0 i j); unfold raw27508step1 raw27508step0; decide +kernel
      have hl : raw27508step1Labels = raw27508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2347 node2347Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical215
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27529 raw27529Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw27529 raw27529Labels = mixedMoment B raw27529step0 raw27529step0Labels := by
      have ha : raw27529step0 = (fun i j => raw27529 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27529step0 raw27529; decide +kernel
      have hl : raw27529step0Labels = raw27529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27529 raw27529Labels permutation176 permutation2
    _ = mixedMoment B node2422 node2422Labels := by rfl

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

theorem canonical29313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29313 raw29313Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29313 raw29313Labels = mixedMoment B raw29313step0 raw29313step0Labels := by
      have hz : ∀ j, raw29313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29313step0 = (fun i j => raw29313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29313step0 raw29313; decide +kernel
      have hl : raw29313step0Labels = raw29313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29313 raw29313Labels permutation346 hz
    mixedMoment B raw29313step0 raw29313step0Labels = mixedMoment B raw29313step1 raw29313step1Labels := by
      have ha : raw29313step1 = (fun i j => raw29313step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29313step1 raw29313step0; decide +kernel
      have hl : raw29313step1Labels = raw29313step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29313step0 raw29313step0Labels permutation34 permutation4
    mixedMoment B raw29313step1 raw29313step1Labels = mixedMoment B raw29313step2 raw29313step2Labels := by
      have ha : raw29313step2 = -raw29313step1 := by apply Matrix.ext; change ∀ i j, raw29313step2 i j = -(raw29313step1 i j); unfold raw29313step2 raw29313step1; decide +kernel
      have hl : raw29313step2Labels = raw29313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3612 node3612Labels := by rfl

theorem canonical29319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29319 raw29319Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29319 raw29319Labels = mixedMoment B raw29319step0 raw29319step0Labels := by
      have hz : ∀ j, raw29319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29319step0 = (fun i j => raw29319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29319step0 raw29319; decide +kernel
      have hl : raw29319step0Labels = raw29319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319 raw29319Labels permutation434 hz
    mixedMoment B raw29319step0 raw29319step0Labels = mixedMoment B raw29319step1 raw29319step1Labels := by
      have hz : ∀ j, raw29319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29319step1 = (fun i j => raw29319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29319step1 raw29319step0; decide +kernel
      have hl : raw29319step1Labels = raw29319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319step0 raw29319step0Labels permutation80 hz
    mixedMoment B raw29319step1 raw29319step1Labels = mixedMoment B raw29319step2 raw29319step2Labels := by
      have ha : raw29319step2 = -raw29319step1 := by apply Matrix.ext; change ∀ i j, raw29319step2 i j = -(raw29319step1 i j); unfold raw29319step2 raw29319step1; decide +kernel
      have hl : raw29319step2Labels = raw29319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

theorem canonical29328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29328 raw29328Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29328 raw29328Labels = mixedMoment B raw29328step0 raw29328step0Labels := by
      have ha : raw29328step0 = (fun i j => raw29328 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29328step0 raw29328; decide +kernel
      have hl : raw29328step0Labels = raw29328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29328 raw29328Labels permutation164 permutation4
    mixedMoment B raw29328step0 raw29328step0Labels = mixedMoment B raw29328step1 raw29328step1Labels := by
      have ha : raw29328step1 = -raw29328step0 := by apply Matrix.ext; change ∀ i j, raw29328step1 i j = -(raw29328step0 i j); unfold raw29328step1 raw29328step0; decide +kernel
      have hl : raw29328step1Labels = raw29328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical29388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29388 raw29388Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29388 raw29388Labels = mixedMoment B raw29388step0 raw29388step0Labels := by
      have hz : ∀ j, raw29388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29388step0 = (fun i j => raw29388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29388step0 raw29388; decide +kernel
      have hl : raw29388step0Labels = raw29388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29388 raw29388Labels permutation346 hz
    mixedMoment B raw29388step0 raw29388step0Labels = mixedMoment B raw29388step1 raw29388step1Labels := by
      have ha : raw29388step1 = (fun i j => raw29388step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29388step1 raw29388step0; decide +kernel
      have hl : raw29388step1Labels = raw29388step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29388step0 raw29388step0Labels permutation35 permutation4
    mixedMoment B raw29388step1 raw29388step1Labels = mixedMoment B raw29388step2 raw29388step2Labels := by
      have ha : raw29388step2 = -raw29388step1 := by apply Matrix.ext; change ∀ i j, raw29388step2 i j = -(raw29388step1 i j); unfold raw29388step2 raw29388step1; decide +kernel
      have hl : raw29388step2Labels = raw29388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical29391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29391 raw29391Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29391 raw29391Labels = mixedMoment B raw29391step0 raw29391step0Labels := by
      have hz : ∀ j, raw29391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29391step0 = (fun i j => raw29391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29391step0 raw29391; decide +kernel
      have hl : raw29391step0Labels = raw29391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29391 raw29391Labels permutation346 hz
    mixedMoment B raw29391step0 raw29391step0Labels = mixedMoment B raw29391step1 raw29391step1Labels := by
      have ha : raw29391step1 = (fun i j => raw29391step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29391step1 raw29391step0; decide +kernel
      have hl : raw29391step1Labels = raw29391step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29391step0 raw29391step0Labels permutation39 permutation2
    mixedMoment B raw29391step1 raw29391step1Labels = mixedMoment B raw29391step2 raw29391step2Labels := by
      have ha : raw29391step2 = -raw29391step1 := by apply Matrix.ext; change ∀ i j, raw29391step2 i j = -(raw29391step1 i j); unfold raw29391step2 raw29391step1; decide +kernel
      have hl : raw29391step2Labels = raw29391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical29394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29394 raw29394Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29394 raw29394Labels = mixedMoment B raw29394step0 raw29394step0Labels := by
      have hz : ∀ j, raw29394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29394step0 = (fun i j => raw29394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29394step0 raw29394; decide +kernel
      have hl : raw29394step0Labels = raw29394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29394 raw29394Labels permutation346 hz
    mixedMoment B raw29394step0 raw29394step0Labels = mixedMoment B raw29394step1 raw29394step1Labels := by
      have ha : raw29394step1 = (fun i j => raw29394step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29394step1 raw29394step0; decide +kernel
      have hl : raw29394step1Labels = raw29394step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29394step0 raw29394step0Labels permutation32 permutation4
    mixedMoment B raw29394step1 raw29394step1Labels = mixedMoment B raw29394step2 raw29394step2Labels := by
      have ha : raw29394step2 = -raw29394step1 := by apply Matrix.ext; change ∀ i j, raw29394step2 i j = -(raw29394step1 i j); unfold raw29394step2 raw29394step1; decide +kernel
      have hl : raw29394step2Labels = raw29394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical29395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29395 raw29395Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29395 raw29395Labels = mixedMoment B raw29395step0 raw29395step0Labels := by
      have hz : ∀ j, raw29395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29395step0 = (fun i j => raw29395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29395step0 raw29395; decide +kernel
      have hl : raw29395step0Labels = raw29395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29395 raw29395Labels permutation346 hz
    mixedMoment B raw29395step0 raw29395step0Labels = mixedMoment B raw29395step1 raw29395step1Labels := by
      have ha : raw29395step1 = (fun i j => raw29395step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29395step1 raw29395step0; decide +kernel
      have hl : raw29395step1Labels = raw29395step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29395step0 raw29395step0Labels permutation34 permutation4
    mixedMoment B raw29395step1 raw29395step1Labels = mixedMoment B raw29395step2 raw29395step2Labels := by
      have ha : raw29395step2 = -raw29395step1 := by apply Matrix.ext; change ∀ i j, raw29395step2 i j = -(raw29395step1 i j); unfold raw29395step2 raw29395step1; decide +kernel
      have hl : raw29395step2Labels = raw29395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical29400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29400 raw29400Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw29400 raw29400Labels = mixedMoment B raw29400step0 raw29400step0Labels := by
      have hz : ∀ j, raw29400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29400step0 = (fun i j => raw29400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29400step0 raw29400; decide +kernel
      have hl : raw29400step0Labels = raw29400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29400 raw29400Labels permutation346 hz
    mixedMoment B raw29400step0 raw29400step0Labels = mixedMoment B raw29400step1 raw29400step1Labels := by
      have ha : raw29400step1 = (fun i j => raw29400step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29400step1 raw29400step0; decide +kernel
      have hl : raw29400step1Labels = raw29400step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29400step0 raw29400step0Labels permutation34 permutation4
    mixedMoment B raw29400step1 raw29400step1Labels = mixedMoment B raw29400step2 raw29400step2Labels := by
      have ha : raw29400step2 = -raw29400step1 := by apply Matrix.ext; change ∀ i j, raw29400step2 i j = -(raw29400step1 i j); unfold raw29400step2 raw29400step1; decide +kernel
      have hl : raw29400step2Labels = raw29400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

theorem canonical29401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29401 raw29401Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw29401 raw29401Labels = mixedMoment B raw29401step0 raw29401step0Labels := by
      have hz : ∀ j, raw29401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29401step0 = (fun i j => raw29401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29401step0 raw29401; decide +kernel
      have hl : raw29401step0Labels = raw29401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29401 raw29401Labels permutation346 hz
    mixedMoment B raw29401step0 raw29401step0Labels = mixedMoment B raw29401step1 raw29401step1Labels := by
      have ha : raw29401step1 = (fun i j => raw29401step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29401step1 raw29401step0; decide +kernel
      have hl : raw29401step1Labels = raw29401step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29401step0 raw29401step0Labels permutation34 permutation4
    mixedMoment B raw29401step1 raw29401step1Labels = mixedMoment B raw29401step2 raw29401step2Labels := by
      have ha : raw29401step2 = -raw29401step1 := by apply Matrix.ext; change ∀ i j, raw29401step2 i j = -(raw29401step1 i j); unfold raw29401step2 raw29401step1; decide +kernel
      have hl : raw29401step2Labels = raw29401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3348 node3348Labels := by rfl

theorem canonical29402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29402 raw29402Labels = mixedMoment B node3430 node3430Labels := by
  calc
    mixedMoment B raw29402 raw29402Labels = mixedMoment B raw29402step0 raw29402step0Labels := by
      have ha : raw29402step0 = (fun i j => raw29402 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29402step0 raw29402; decide +kernel
      have hl : raw29402step0Labels = raw29402Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29402 raw29402Labels permutation154 permutation4
    mixedMoment B raw29402step0 raw29402step0Labels = mixedMoment B raw29402step1 raw29402step1Labels := by
      have ha : raw29402step1 = -raw29402step0 := by apply Matrix.ext; change ∀ i j, raw29402step1 i j = -(raw29402step0 i j); unfold raw29402step1 raw29402step0; decide +kernel
      have hl : raw29402step1Labels = raw29402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3430 node3430Labels := by rfl

theorem canonical29403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29403 raw29403Labels = mixedMoment B node2674 node2674Labels := by
  calc
    mixedMoment B raw29403 raw29403Labels = mixedMoment B raw29403step0 raw29403step0Labels := by
      have hz : ∀ j, raw29403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29403step0 = (fun i j => raw29403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29403step0 raw29403; decide +kernel
      have hl : raw29403step0Labels = raw29403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29403 raw29403Labels permutation346 hz
    mixedMoment B raw29403step0 raw29403step0Labels = mixedMoment B raw29403step1 raw29403step1Labels := by
      have ha : raw29403step1 = (fun i j => raw29403step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29403step1 raw29403step0; decide +kernel
      have hl : raw29403step1Labels = raw29403step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29403step0 raw29403step0Labels permutation124 permutation2
    _ = mixedMoment B node2674 node2674Labels := by rfl

theorem canonical29404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29404 raw29404Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw29404 raw29404Labels = mixedMoment B raw29404step0 raw29404step0Labels := by
      have ha : raw29404step0 = (fun i j => raw29404 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29404step0 raw29404; decide +kernel
      have hl : raw29404step0Labels = raw29404Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29404 raw29404Labels permutation158 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

theorem canonical29405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29405 raw29405Labels = mixedMoment B node2324 node2324Labels := by
  calc
    mixedMoment B raw29405 raw29405Labels = mixedMoment B raw29405step0 raw29405step0Labels := by
      have ha : raw29405step0 = (fun i j => raw29405 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29405step0 raw29405; decide +kernel
      have hl : raw29405step0Labels = raw29405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29405 raw29405Labels permutation158 permutation2
    _ = mixedMoment B node2324 node2324Labels := by rfl

theorem canonical29406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29406 raw29406Labels = mixedMoment B node2441 node2441Labels := by
  calc
    mixedMoment B raw29406 raw29406Labels = mixedMoment B raw29406step0 raw29406step0Labels := by
      have ha : raw29406step0 = (fun i j => raw29406 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29406step0 raw29406; decide +kernel
      have hl : raw29406step0Labels = raw29406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29406 raw29406Labels permutation158 permutation2
    _ = mixedMoment B node2441 node2441Labels := by rfl

theorem canonical29407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29407 raw29407Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw29407 raw29407Labels = mixedMoment B raw29407step0 raw29407step0Labels := by
      have ha : raw29407step0 = (fun i j => raw29407 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29407step0 raw29407; decide +kernel
      have hl : raw29407step0Labels = raw29407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29407 raw29407Labels permutation159 permutation2
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical29408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29408 raw29408Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw29408 raw29408Labels = mixedMoment B raw29408step0 raw29408step0Labels := by
      have ha : raw29408step0 = (fun i j => raw29408 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29408step0 raw29408; decide +kernel
      have hl : raw29408step0Labels = raw29408Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29408 raw29408Labels permutation587 permutation2
    mixedMoment B raw29408step0 raw29408step0Labels = mixedMoment B raw29408step1 raw29408step1Labels := by
      have ha : raw29408step1 = -raw29408step0 := by apply Matrix.ext; change ∀ i j, raw29408step1 i j = -(raw29408step0 i j); unfold raw29408step1 raw29408step0; decide +kernel
      have hl : raw29408step1Labels = raw29408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical29409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29409 raw29409Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw29409 raw29409Labels = mixedMoment B raw29409step0 raw29409step0Labels := by
      have ha : raw29409step0 = (fun i j => raw29409 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29409step0 raw29409; decide +kernel
      have hl : raw29409step0Labels = raw29409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29409 raw29409Labels permutation177 permutation2
    _ = mixedMoment B node2900 node2900Labels := by rfl

theorem canonical29410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29410 raw29410Labels = mixedMoment B node2320 node2320Labels := by
  calc
    mixedMoment B raw29410 raw29410Labels = mixedMoment B raw29410step0 raw29410step0Labels := by
      have ha : raw29410step0 = (fun i j => raw29410 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29410step0 raw29410; decide +kernel
      have hl : raw29410step0Labels = raw29410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29410 raw29410Labels permutation587 permutation2
    mixedMoment B raw29410step0 raw29410step0Labels = mixedMoment B raw29410step1 raw29410step1Labels := by
      have ha : raw29410step1 = -raw29410step0 := by apply Matrix.ext; change ∀ i j, raw29410step1 i j = -(raw29410step0 i j); unfold raw29410step1 raw29410step0; decide +kernel
      have hl : raw29410step1Labels = raw29410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2320 node2320Labels := by rfl

theorem canonical29411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29411 raw29411Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw29411 raw29411Labels = mixedMoment B raw29411step0 raw29411step0Labels := by
      have ha : raw29411step0 = (fun i j => raw29411 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29411step0 raw29411; decide +kernel
      have hl : raw29411step0Labels = raw29411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29411 raw29411Labels permutation686 permutation2
    mixedMoment B raw29411step0 raw29411step0Labels = mixedMoment B raw29411step1 raw29411step1Labels := by
      have ha : raw29411step1 = -raw29411step0 := by apply Matrix.ext; change ∀ i j, raw29411step1 i j = -(raw29411step0 i j); unfold raw29411step1 raw29411step0; decide +kernel
      have hl : raw29411step1Labels = raw29411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2797 node2797Labels := by rfl

theorem canonical29416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29416 raw29416Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw29416 raw29416Labels = mixedMoment B raw29416step0 raw29416step0Labels := by
      have ha : raw29416step0 = (fun i j => raw29416 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29416step0 raw29416; decide +kernel
      have hl : raw29416step0Labels = raw29416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29416 raw29416Labels permutation152 permutation4
    mixedMoment B raw29416step0 raw29416step0Labels = mixedMoment B raw29416step1 raw29416step1Labels := by
      have ha : raw29416step1 = -raw29416step0 := by apply Matrix.ext; change ∀ i j, raw29416step1 i j = -(raw29416step0 i j); unfold raw29416step1 raw29416step0; decide +kernel
      have hl : raw29416step1Labels = raw29416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1941 node1941Labels := by rfl

theorem canonical29417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29417 raw29417Labels = mixedMoment B node3351 node3351Labels := by
  calc
    mixedMoment B raw29417 raw29417Labels = mixedMoment B raw29417step0 raw29417step0Labels := by
      have ha : raw29417step0 = (fun i j => raw29417 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29417step0 raw29417; decide +kernel
      have hl : raw29417step0Labels = raw29417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29417 raw29417Labels permutation152 permutation4
    mixedMoment B raw29417step0 raw29417step0Labels = mixedMoment B raw29417step1 raw29417step1Labels := by
      have ha : raw29417step1 = -raw29417step0 := by apply Matrix.ext; change ∀ i j, raw29417step1 i j = -(raw29417step0 i j); unfold raw29417step1 raw29417step0; decide +kernel
      have hl : raw29417step1Labels = raw29417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3351 node3351Labels := by rfl

theorem canonical29418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29418 raw29418Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29418 raw29418Labels = mixedMoment B raw29418step0 raw29418step0Labels := by
      have hz : ∀ j, raw29418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29418step0 = (fun i j => raw29418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29418step0 raw29418; decide +kernel
      have hl : raw29418step0Labels = raw29418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29418 raw29418Labels permutation434 hz
    mixedMoment B raw29418step0 raw29418step0Labels = mixedMoment B raw29418step1 raw29418step1Labels := by
      have ha : raw29418step1 = (fun i j => raw29418step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29418step1 raw29418step0; decide +kernel
      have hl : raw29418step1Labels = raw29418step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29418step0 raw29418step0Labels permutation32 permutation4
    mixedMoment B raw29418step1 raw29418step1Labels = mixedMoment B raw29418step2 raw29418step2Labels := by
      have ha : raw29418step2 = -raw29418step1 := by apply Matrix.ext; change ∀ i j, raw29418step2 i j = -(raw29418step1 i j); unfold raw29418step2 raw29418step1; decide +kernel
      have hl : raw29418step2Labels = raw29418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

theorem canonical29419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29419 raw29419Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29419 raw29419Labels = mixedMoment B raw29419step0 raw29419step0Labels := by
      have ha : raw29419step0 = (fun i j => raw29419 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29419step0 raw29419; decide +kernel
      have hl : raw29419step0Labels = raw29419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29419 raw29419Labels permutation170 permutation4
    mixedMoment B raw29419step0 raw29419step0Labels = mixedMoment B raw29419step1 raw29419step1Labels := by
      have ha : raw29419step1 = -raw29419step0 := by apply Matrix.ext; change ∀ i j, raw29419step1 i j = -(raw29419step0 i j); unfold raw29419step1 raw29419step0; decide +kernel
      have hl : raw29419step1Labels = raw29419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical29420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29420 raw29420Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw29420 raw29420Labels = mixedMoment B raw29420step0 raw29420step0Labels := by
      have ha : raw29420step0 = (fun i j => raw29420 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29420step0 raw29420; decide +kernel
      have hl : raw29420step0Labels = raw29420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29420 raw29420Labels permutation164 permutation4
    mixedMoment B raw29420step0 raw29420step0Labels = mixedMoment B raw29420step1 raw29420step1Labels := by
      have ha : raw29420step1 = -raw29420step0 := by apply Matrix.ext; change ∀ i j, raw29420step1 i j = -(raw29420step0 i j); unfold raw29420step1 raw29420step0; decide +kernel
      have hl : raw29420step1Labels = raw29420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1921 node1921Labels := by rfl

theorem canonical29421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29421 raw29421Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw29421 raw29421Labels = mixedMoment B raw29421step0 raw29421step0Labels := by
      have ha : raw29421step0 = (fun i j => raw29421 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29421step0 raw29421; decide +kernel
      have hl : raw29421step0Labels = raw29421Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29421 raw29421Labels permutation164 permutation4
    mixedMoment B raw29421step0 raw29421step0Labels = mixedMoment B raw29421step1 raw29421step1Labels := by
      have ha : raw29421step1 = -raw29421step0 := by apply Matrix.ext; change ∀ i j, raw29421step1 i j = -(raw29421step0 i j); unfold raw29421step1 raw29421step0; decide +kernel
      have hl : raw29421step1Labels = raw29421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3345 node3345Labels := by rfl

theorem canonical29422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29422 raw29422Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29422 raw29422Labels = mixedMoment B raw29422step0 raw29422step0Labels := by
      have hz : ∀ j, raw29422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29422step0 = (fun i j => raw29422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29422step0 raw29422; decide +kernel
      have hl : raw29422step0Labels = raw29422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29422 raw29422Labels permutation434 hz
    mixedMoment B raw29422step0 raw29422step0Labels = mixedMoment B raw29422step1 raw29422step1Labels := by
      have ha : raw29422step1 = (fun i j => raw29422step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29422step1 raw29422step0; decide +kernel
      have hl : raw29422step1Labels = raw29422step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29422step0 raw29422step0Labels permutation34 permutation4
    mixedMoment B raw29422step1 raw29422step1Labels = mixedMoment B raw29422step2 raw29422step2Labels := by
      have ha : raw29422step2 = -raw29422step1 := by apply Matrix.ext; change ∀ i j, raw29422step2 i j = -(raw29422step1 i j); unfold raw29422step2 raw29422step1; decide +kernel
      have hl : raw29422step2Labels = raw29422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical29423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29423 raw29423Labels = mixedMoment B node2668 node2668Labels := by
  calc
    mixedMoment B raw29423 raw29423Labels = mixedMoment B raw29423step0 raw29423step0Labels := by
      have ha : raw29423step0 = (fun i j => raw29423 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29423step0 raw29423; decide +kernel
      have hl : raw29423step0Labels = raw29423Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29423 raw29423Labels permutation577 permutation2
    _ = mixedMoment B node2668 node2668Labels := by rfl

theorem canonical29431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29431 raw29431Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw29431 raw29431Labels = mixedMoment B raw29431step0 raw29431step0Labels := by
      have hz : ∀ j, raw29431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29431step0 = (fun i j => raw29431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29431step0 raw29431; decide +kernel
      have hl : raw29431step0Labels = raw29431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29431 raw29431Labels permutation434 hz
    mixedMoment B raw29431step0 raw29431step0Labels = mixedMoment B raw29431step1 raw29431step1Labels := by
      have ha : raw29431step1 = (fun i j => raw29431step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29431step1 raw29431step0; decide +kernel
      have hl : raw29431step1Labels = raw29431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29431step0 raw29431step0Labels permutation149 permutation2
    mixedMoment B raw29431step1 raw29431step1Labels = mixedMoment B raw29431step2 raw29431step2Labels := by
      have ha : raw29431step2 = -raw29431step1 := by apply Matrix.ext; change ∀ i j, raw29431step2 i j = -(raw29431step1 i j); unfold raw29431step2 raw29431step1; decide +kernel
      have hl : raw29431step2Labels = raw29431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

theorem canonical29432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29432 raw29432Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw29432 raw29432Labels = mixedMoment B raw29432step0 raw29432step0Labels := by
      have hz : ∀ j, raw29432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29432step0 = (fun i j => raw29432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29432step0 raw29432; decide +kernel
      have hl : raw29432step0Labels = raw29432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29432 raw29432Labels permutation434 hz
    mixedMoment B raw29432step0 raw29432step0Labels = mixedMoment B raw29432step1 raw29432step1Labels := by
      have hz : ∀ j, raw29432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw29432step1 = (fun i j => raw29432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw29432step1 raw29432step0; decide +kernel
      have hl : raw29432step1Labels = raw29432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29432step0 raw29432step0Labels permutation56 hz
    _ = mixedMoment B node2522 node2522Labels := by rfl

theorem canonical29433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29433 raw29433Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw29433 raw29433Labels = mixedMoment B raw29433step0 raw29433step0Labels := by
      have hz : ∀ j, raw29433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29433step0 = (fun i j => raw29433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29433step0 raw29433; decide +kernel
      have hl : raw29433step0Labels = raw29433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29433 raw29433Labels permutation434 hz
    _ = mixedMoment B node2560 node2560Labels := by rfl

theorem canonical29434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29434 raw29434Labels = mixedMoment B node2427 node2427Labels := by
  calc
    mixedMoment B raw29434 raw29434Labels = mixedMoment B raw29434step0 raw29434step0Labels := by
      have ha : raw29434step0 = (fun i j => raw29434 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29434step0 raw29434; decide +kernel
      have hl : raw29434step0Labels = raw29434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29434 raw29434Labels permutation176 permutation2
    _ = mixedMoment B node2427 node2427Labels := by rfl

theorem canonical29435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29435 raw29435Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw29435 raw29435Labels = mixedMoment B raw29435step0 raw29435step0Labels := by
      have hz : ∀ j, raw29435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29435step0 = (fun i j => raw29435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29435step0 raw29435; decide +kernel
      have hl : raw29435step0Labels = raw29435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29435 raw29435Labels permutation434 hz
    mixedMoment B raw29435step0 raw29435step0Labels = mixedMoment B raw29435step1 raw29435step1Labels := by
      have ha : raw29435step1 = (fun i j => raw29435step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29435step1 raw29435step0; decide +kernel
      have hl : raw29435step1Labels = raw29435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29435step0 raw29435step0Labels permutation39 permutation2
    _ = mixedMoment B node2435 node2435Labels := by rfl

theorem canonical29436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29436 raw29436Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw29436 raw29436Labels = mixedMoment B raw29436step0 raw29436step0Labels := by
      have hz : ∀ j, raw29436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29436step0 = (fun i j => raw29436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29436step0 raw29436; decide +kernel
      have hl : raw29436step0Labels = raw29436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29436 raw29436Labels permutation434 hz
    mixedMoment B raw29436step0 raw29436step0Labels = mixedMoment B raw29436step1 raw29436step1Labels := by
      have ha : raw29436step1 = (fun i j => raw29436step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29436step1 raw29436step0; decide +kernel
      have hl : raw29436step1Labels = raw29436step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29436step0 raw29436step0Labels permutation149 permutation2
    mixedMoment B raw29436step1 raw29436step1Labels = mixedMoment B raw29436step2 raw29436step2Labels := by
      have ha : raw29436step2 = -raw29436step1 := by apply Matrix.ext; change ∀ i j, raw29436step2 i j = -(raw29436step1 i j); unfold raw29436step2 raw29436step1; decide +kernel
      have hl : raw29436step2Labels = raw29436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

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

theorem canonical29438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29438 raw29438Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw29438 raw29438Labels = mixedMoment B raw29438step0 raw29438step0Labels := by
      have hz : ∀ j, raw29438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29438step0 = (fun i j => raw29438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29438step0 raw29438; decide +kernel
      have hl : raw29438step0Labels = raw29438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29438 raw29438Labels permutation434 hz
    mixedMoment B raw29438step0 raw29438step0Labels = mixedMoment B raw29438step1 raw29438step1Labels := by
      have ha : raw29438step1 = (fun i j => raw29438step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29438step1 raw29438step0; decide +kernel
      have hl : raw29438step1Labels = raw29438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29438step0 raw29438step0Labels permutation33 permutation2
    _ = mixedMoment B node1347 node1347Labels := by rfl

theorem canonical29439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29439 raw29439Labels = mixedMoment B node2831 node2831Labels := by
  calc
    mixedMoment B raw29439 raw29439Labels = mixedMoment B raw29439step0 raw29439step0Labels := by
      have hz : ∀ j, raw29439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29439step0 = (fun i j => raw29439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29439step0 raw29439; decide +kernel
      have hl : raw29439step0Labels = raw29439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29439 raw29439Labels permutation434 hz
    mixedMoment B raw29439step0 raw29439step0Labels = mixedMoment B raw29439step1 raw29439step1Labels := by
      have ha : raw29439step1 = (fun i j => raw29439step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29439step1 raw29439step0; decide +kernel
      have hl : raw29439step1Labels = raw29439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29439step0 raw29439step0Labels permutation33 permutation2
    _ = mixedMoment B node2831 node2831Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical230
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical29440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29440 raw29440Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw29440 raw29440Labels = mixedMoment B raw29440step0 raw29440step0Labels := by
      have hz : ∀ j, raw29440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29440step0 = (fun i j => raw29440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29440step0 raw29440; decide +kernel
      have hl : raw29440step0Labels = raw29440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29440 raw29440Labels permutation434 hz
    mixedMoment B raw29440step0 raw29440step0Labels = mixedMoment B raw29440step1 raw29440step1Labels := by
      have ha : raw29440step1 = (fun i j => raw29440step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29440step1 raw29440step0; decide +kernel
      have hl : raw29440step1Labels = raw29440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29440step0 raw29440step0Labels permutation33 permutation2
    _ = mixedMoment B node2942 node2942Labels := by rfl

theorem canonical29441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29441 raw29441Labels = mixedMoment B node2902 node2902Labels := by
  calc
    mixedMoment B raw29441 raw29441Labels = mixedMoment B raw29441step0 raw29441step0Labels := by
      have ha : raw29441step0 = (fun i j => raw29441 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29441step0 raw29441; decide +kernel
      have hl : raw29441step0Labels = raw29441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29441 raw29441Labels permutation159 permutation2
    _ = mixedMoment B node2902 node2902Labels := by rfl

theorem canonical29442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29442 raw29442Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw29442 raw29442Labels = mixedMoment B raw29442step0 raw29442step0Labels := by
      have hz : ∀ j, raw29442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29442step0 = (fun i j => raw29442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29442step0 raw29442; decide +kernel
      have hl : raw29442step0Labels = raw29442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29442 raw29442Labels permutation434 hz
    _ = mixedMoment B node2964 node2964Labels := by rfl

theorem canonical29443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29443 raw29443Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw29443 raw29443Labels = mixedMoment B raw29443step0 raw29443step0Labels := by
      have hz : ∀ j, raw29443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29443step0 = (fun i j => raw29443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29443step0 raw29443; decide +kernel
      have hl : raw29443step0Labels = raw29443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29443 raw29443Labels permutation434 hz
    mixedMoment B raw29443step0 raw29443step0Labels = mixedMoment B raw29443step1 raw29443step1Labels := by
      have ha : raw29443step1 = (fun i j => raw29443step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29443step1 raw29443step0; decide +kernel
      have hl : raw29443step1Labels = raw29443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29443step0 raw29443step0Labels permutation36 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical29444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29444 raw29444Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29444 raw29444Labels = mixedMoment B raw29444step0 raw29444step0Labels := by
      have hz : ∀ j, raw29444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29444step0 = (fun i j => raw29444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29444step0 raw29444; decide +kernel
      have hl : raw29444step0Labels = raw29444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29444 raw29444Labels permutation434 hz
    mixedMoment B raw29444step0 raw29444step0Labels = mixedMoment B raw29444step1 raw29444step1Labels := by
      have ha : raw29444step1 = (fun i j => raw29444step0 (permutation116 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29444step1 raw29444step0; decide +kernel
      have hl : raw29444step1Labels = raw29444step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29444step0 raw29444step0Labels permutation116 permutation0
    mixedMoment B raw29444step1 raw29444step1Labels = mixedMoment B raw29444step2 raw29444step2Labels := by
      have ha : raw29444step2 = -raw29444step1 := by apply Matrix.ext; change ∀ i j, raw29444step2 i j = -(raw29444step1 i j); unfold raw29444step2 raw29444step1; decide +kernel
      have hl : raw29444step2Labels = raw29444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical29445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29445 raw29445Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw29445 raw29445Labels = mixedMoment B raw29445step0 raw29445step0Labels := by
      have hz : ∀ j, raw29445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29445step0 = (fun i j => raw29445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29445step0 raw29445; decide +kernel
      have hl : raw29445step0Labels = raw29445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29445 raw29445Labels permutation434 hz
    mixedMoment B raw29445step0 raw29445step0Labels = mixedMoment B raw29445step1 raw29445step1Labels := by
      have ha : raw29445step1 = (fun i j => raw29445step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29445step1 raw29445step0; decide +kernel
      have hl : raw29445step1Labels = raw29445step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29445step0 raw29445step0Labels permutation149 permutation4
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical29446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29446 raw29446Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw29446 raw29446Labels = mixedMoment B raw29446step0 raw29446step0Labels := by
      have hz : ∀ j, raw29446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29446step0 = (fun i j => raw29446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29446step0 raw29446; decide +kernel
      have hl : raw29446step0Labels = raw29446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29446 raw29446Labels permutation434 hz
    mixedMoment B raw29446step0 raw29446step0Labels = mixedMoment B raw29446step1 raw29446step1Labels := by
      have ha : raw29446step1 = (fun i j => raw29446step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29446step1 raw29446step0; decide +kernel
      have hl : raw29446step1Labels = raw29446step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29446step0 raw29446step0Labels permutation151 permutation4
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical29447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29447 raw29447Labels = mixedMoment B node2674 node2674Labels := by
  calc
    mixedMoment B raw29447 raw29447Labels = mixedMoment B raw29447step0 raw29447step0Labels := by
      have hz : ∀ j, raw29447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29447step0 = (fun i j => raw29447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29447step0 raw29447; decide +kernel
      have hl : raw29447step0Labels = raw29447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29447 raw29447Labels permutation434 hz
    mixedMoment B raw29447step0 raw29447step0Labels = mixedMoment B raw29447step1 raw29447step1Labels := by
      have ha : raw29447step1 = (fun i j => raw29447step0 (permutation148 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29447step1 raw29447step0; decide +kernel
      have hl : raw29447step1Labels = raw29447step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29447step0 raw29447step0Labels permutation148 permutation4
    _ = mixedMoment B node2674 node2674Labels := by rfl

theorem canonical29448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29448 raw29448Labels = mixedMoment B node2668 node2668Labels := by
  calc
    mixedMoment B raw29448 raw29448Labels = mixedMoment B raw29448step0 raw29448step0Labels := by
      have ha : raw29448step0 = (fun i j => raw29448 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29448step0 raw29448; decide +kernel
      have hl : raw29448step0Labels = raw29448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29448 raw29448Labels permutation674 permutation4
    _ = mixedMoment B node2668 node2668Labels := by rfl

theorem canonical29449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29449 raw29449Labels = mixedMoment B node2584 node2584Labels := by
  calc
    mixedMoment B raw29449 raw29449Labels = mixedMoment B raw29449step0 raw29449step0Labels := by
      have hz : ∀ j, raw29449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29449step0 = (fun i j => raw29449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29449step0 raw29449; decide +kernel
      have hl : raw29449step0Labels = raw29449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29449 raw29449Labels permutation434 hz
    mixedMoment B raw29449step0 raw29449step0Labels = mixedMoment B raw29449step1 raw29449step1Labels := by
      have ha : raw29449step1 = (fun i j => raw29449step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29449step1 raw29449step0; decide +kernel
      have hl : raw29449step1Labels = raw29449step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29449step0 raw29449step0Labels permutation121 permutation2
    _ = mixedMoment B node2584 node2584Labels := by rfl

theorem canonical29450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29450 raw29450Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29450 raw29450Labels = mixedMoment B raw29450step0 raw29450step0Labels := by
      have hz : ∀ j, raw29450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29450step0 = (fun i j => raw29450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29450step0 raw29450; decide +kernel
      have hl : raw29450step0Labels = raw29450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29450 raw29450Labels permutation434 hz
    mixedMoment B raw29450step0 raw29450step0Labels = mixedMoment B raw29450step1 raw29450step1Labels := by
      have ha : raw29450step1 = (fun i j => raw29450step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29450step1 raw29450step0; decide +kernel
      have hl : raw29450step1Labels = raw29450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29450step0 raw29450step0Labels permutation36 permutation2
    mixedMoment B raw29450step1 raw29450step1Labels = mixedMoment B raw29450step2 raw29450step2Labels := by
      have ha : raw29450step2 = -raw29450step1 := by apply Matrix.ext; change ∀ i j, raw29450step2 i j = -(raw29450step1 i j); unfold raw29450step2 raw29450step1; decide +kernel
      have hl : raw29450step2Labels = raw29450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

theorem canonical29451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29451 raw29451Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw29451 raw29451Labels = mixedMoment B raw29451step0 raw29451step0Labels := by
      have hz : ∀ j, raw29451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29451step0 = (fun i j => raw29451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29451step0 raw29451; decide +kernel
      have hl : raw29451step0Labels = raw29451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29451 raw29451Labels permutation434 hz
    mixedMoment B raw29451step0 raw29451step0Labels = mixedMoment B raw29451step1 raw29451step1Labels := by
      have ha : raw29451step1 = (fun i j => raw29451step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29451step1 raw29451step0; decide +kernel
      have hl : raw29451step1Labels = raw29451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29451step0 raw29451step0Labels permutation40 permutation4
    mixedMoment B raw29451step1 raw29451step1Labels = mixedMoment B raw29451step2 raw29451step2Labels := by
      have ha : raw29451step2 = -raw29451step1 := by apply Matrix.ext; change ∀ i j, raw29451step2 i j = -(raw29451step1 i j); unfold raw29451step2 raw29451step1; decide +kernel
      have hl : raw29451step2Labels = raw29451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical29452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29452 raw29452Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw29452 raw29452Labels = mixedMoment B raw29452step0 raw29452step0Labels := by
      have hz : ∀ j, raw29452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29452step0 = (fun i j => raw29452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29452step0 raw29452; decide +kernel
      have hl : raw29452step0Labels = raw29452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29452 raw29452Labels permutation434 hz
    mixedMoment B raw29452step0 raw29452step0Labels = mixedMoment B raw29452step1 raw29452step1Labels := by
      have hz : ∀ j, raw29452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29452step1 = (fun i j => raw29452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29452step1 raw29452step0; decide +kernel
      have hl : raw29452step1Labels = raw29452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29452step0 raw29452step0Labels permutation80 hz
    mixedMoment B raw29452step1 raw29452step1Labels = mixedMoment B raw29452step2 raw29452step2Labels := by
      have ha : raw29452step2 = (fun i j => raw29452step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29452step2 raw29452step1; decide +kernel
      have hl : raw29452step2Labels = raw29452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29452step1 raw29452step1Labels permutation8 permutation4
    mixedMoment B raw29452step2 raw29452step2Labels = mixedMoment B raw29452step3 raw29452step3Labels := by
      have ha : raw29452step3 = -raw29452step2 := by apply Matrix.ext; change ∀ i j, raw29452step3 i j = -(raw29452step2 i j); unfold raw29452step3 raw29452step2; decide +kernel
      have hl : raw29452step3Labels = raw29452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3614 node3614Labels := by rfl

theorem canonical29453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29453 raw29453Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw29453 raw29453Labels = mixedMoment B raw29453step0 raw29453step0Labels := by
      have ha : raw29453step0 = (fun i j => raw29453 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29453step0 raw29453; decide +kernel
      have hl : raw29453step0Labels = raw29453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29453 raw29453Labels permutation178 permutation4
    mixedMoment B raw29453step0 raw29453step0Labels = mixedMoment B raw29453step1 raw29453step1Labels := by
      have ha : raw29453step1 = -raw29453step0 := by apply Matrix.ext; change ∀ i j, raw29453step1 i j = -(raw29453step0 i j); unfold raw29453step1 raw29453step0; decide +kernel
      have hl : raw29453step1Labels = raw29453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical29454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29454 raw29454Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29454 raw29454Labels = mixedMoment B raw29454step0 raw29454step0Labels := by
      have hz : ∀ j, raw29454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29454step0 = (fun i j => raw29454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29454step0 raw29454; decide +kernel
      have hl : raw29454step0Labels = raw29454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29454 raw29454Labels permutation434 hz
    mixedMoment B raw29454step0 raw29454step0Labels = mixedMoment B raw29454step1 raw29454step1Labels := by
      have ha : raw29454step1 = (fun i j => raw29454step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29454step1 raw29454step0; decide +kernel
      have hl : raw29454step1Labels = raw29454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29454step0 raw29454step0Labels permutation38 permutation4
    mixedMoment B raw29454step1 raw29454step1Labels = mixedMoment B raw29454step2 raw29454step2Labels := by
      have ha : raw29454step2 = -raw29454step1 := by apply Matrix.ext; change ∀ i j, raw29454step2 i j = -(raw29454step1 i j); unfold raw29454step2 raw29454step1; decide +kernel
      have hl : raw29454step2Labels = raw29454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

theorem canonical29455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29455 raw29455Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw29455 raw29455Labels = mixedMoment B raw29455step0 raw29455step0Labels := by
      have ha : raw29455step0 = (fun i j => raw29455 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29455step0 raw29455; decide +kernel
      have hl : raw29455step0Labels = raw29455Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29455 raw29455Labels permutation686 permutation2
    mixedMoment B raw29455step0 raw29455step0Labels = mixedMoment B raw29455step1 raw29455step1Labels := by
      have ha : raw29455step1 = -raw29455step0 := by apply Matrix.ext; change ∀ i j, raw29455step1 i j = -(raw29455step0 i j); unfold raw29455step1 raw29455step0; decide +kernel
      have hl : raw29455step1Labels = raw29455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical29456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29456 raw29456Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw29456 raw29456Labels = mixedMoment B raw29456step0 raw29456step0Labels := by
      have hz : ∀ j, raw29456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw29456step0 = (fun i j => raw29456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw29456step0 raw29456; decide +kernel
      have hl : raw29456step0Labels = raw29456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29456 raw29456Labels permutation265 hz
    _ = mixedMoment B node2488 node2488Labels := by rfl

theorem canonical29457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29457 raw29457Labels = mixedMoment B node2545 node2545Labels := by
  calc
    _ = mixedMoment B node2545 node2545Labels := by rfl

theorem canonical29458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29458 raw29458Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw29458 raw29458Labels = mixedMoment B raw29458step0 raw29458step0Labels := by
      have ha : raw29458step0 = (fun i j => raw29458 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29458step0 raw29458; decide +kernel
      have hl : raw29458step0Labels = raw29458Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29458 raw29458Labels permutation176 permutation2
    _ = mixedMoment B node2431 node2431Labels := by rfl

theorem canonical29459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29459 raw29459Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw29459 raw29459Labels = mixedMoment B raw29459step0 raw29459step0Labels := by
      have ha : raw29459step0 = (fun i j => raw29459 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29459step0 raw29459; decide +kernel
      have hl : raw29459step0Labels = raw29459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29459 raw29459Labels permutation177 permutation2
    _ = mixedMoment B node2423 node2423Labels := by rfl

theorem canonical29460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29460 raw29460Labels = mixedMoment B node2350 node2350Labels := by
  calc
    _ = mixedMoment B node2350 node2350Labels := by rfl

theorem canonical29461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29461 raw29461Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw29461 raw29461Labels = mixedMoment B raw29461step0 raw29461step0Labels := by
      have ha : raw29461step0 = (fun i j => raw29461 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29461step0 raw29461; decide +kernel
      have hl : raw29461step0Labels = raw29461Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29461 raw29461Labels permutation153 permutation2
    _ = mixedMoment B node2557 node2557Labels := by rfl

theorem canonical29462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29462 raw29462Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw29462 raw29462Labels = mixedMoment B raw29462step0 raw29462step0Labels := by
      have ha : raw29462step0 = (fun i j => raw29462 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29462step0 raw29462; decide +kernel
      have hl : raw29462step0Labels = raw29462Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29462 raw29462Labels permutation159 permutation2
    _ = mixedMoment B node1330 node1330Labels := by rfl

theorem canonical29463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29463 raw29463Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw29463 raw29463Labels = mixedMoment B raw29463step0 raw29463step0Labels := by
      have ha : raw29463step0 = (fun i j => raw29463 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29463step0 raw29463; decide +kernel
      have hl : raw29463step0Labels = raw29463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29463 raw29463Labels permutation159 permutation2
    _ = mixedMoment B node2824 node2824Labels := by rfl

theorem canonical29464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29464 raw29464Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw29464 raw29464Labels = mixedMoment B raw29464step0 raw29464step0Labels := by
      have ha : raw29464step0 = (fun i j => raw29464 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29464step0 raw29464; decide +kernel
      have hl : raw29464step0Labels = raw29464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29464 raw29464Labels permutation159 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical29465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29465 raw29465Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw29465 raw29465Labels = mixedMoment B raw29465step0 raw29465step0Labels := by
      have ha : raw29465step0 = (fun i j => raw29465 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29465step0 raw29465; decide +kernel
      have hl : raw29465step0Labels = raw29465Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29465 raw29465Labels permutation159 permutation2
    _ = mixedMoment B node2896 node2896Labels := by rfl

theorem canonical29466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29466 raw29466Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw29466 raw29466Labels = mixedMoment B raw29466step0 raw29466step0Labels := by
      have ha : raw29466step0 = (fun i j => raw29466 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29466step0 raw29466; decide +kernel
      have hl : raw29466step0Labels = raw29466Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29466 raw29466Labels permutation158 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

theorem canonical29467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29467 raw29467Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw29467 raw29467Labels = mixedMoment B raw29467step0 raw29467step0Labels := by
      have ha : raw29467step0 = (fun i j => raw29467 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29467step0 raw29467; decide +kernel
      have hl : raw29467step0Labels = raw29467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29467 raw29467Labels permutation162 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical29468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29468 raw29468Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw29468 raw29468Labels = mixedMoment B raw29468step0 raw29468step0Labels := by
      have hz : ∀ j, raw29468 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw29468step0 = (fun i j => raw29468 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw29468step0 raw29468; decide +kernel
      have hl : raw29468step0Labels = raw29468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29468 raw29468Labels permutation590 hz
    mixedMoment B raw29468step0 raw29468step0Labels = mixedMoment B raw29468step1 raw29468step1Labels := by
      have ha : raw29468step1 = (fun i j => raw29468step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29468step1 raw29468step0; decide +kernel
      have hl : raw29468step1Labels = raw29468step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29468step0 raw29468step0Labels permutation140 permutation0
    mixedMoment B raw29468step1 raw29468step1Labels = mixedMoment B raw29468step2 raw29468step2Labels := by
      have ha : raw29468step2 = -raw29468step1 := by apply Matrix.ext; change ∀ i j, raw29468step2 i j = -(raw29468step1 i j); unfold raw29468step2 raw29468step1; decide +kernel
      have hl : raw29468step2Labels = raw29468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical29469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29469 raw29469Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw29469 raw29469Labels = mixedMoment B raw29469step0 raw29469step0Labels := by
      have ha : raw29469step0 = (fun i j => raw29469 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29469step0 raw29469; decide +kernel
      have hl : raw29469step0Labels = raw29469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29469 raw29469Labels permutation582 permutation2
    mixedMoment B raw29469step0 raw29469step0Labels = mixedMoment B raw29469step1 raw29469step1Labels := by
      have ha : raw29469step1 = -raw29469step0 := by apply Matrix.ext; change ∀ i j, raw29469step1 i j = -(raw29469step0 i j); unfold raw29469step1 raw29469step0; decide +kernel
      have hl : raw29469step1Labels = raw29469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3721 node3721Labels := by rfl

theorem canonical29470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29470 raw29470Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw29470 raw29470Labels = mixedMoment B raw29470step0 raw29470step0Labels := by
      have ha : raw29470step0 = (fun i j => raw29470 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29470step0 raw29470; decide +kernel
      have hl : raw29470step0Labels = raw29470Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29470 raw29470Labels permutation201 permutation2
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical29471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29471 raw29471Labels = mixedMoment B node2349 node2349Labels := by
  calc
    mixedMoment B raw29471 raw29471Labels = mixedMoment B raw29471step0 raw29471step0Labels := by
      have ha : raw29471step0 = (fun i j => raw29471 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29471step0 raw29471; decide +kernel
      have hl : raw29471step0Labels = raw29471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29471 raw29471Labels permutation582 permutation2
    mixedMoment B raw29471step0 raw29471step0Labels = mixedMoment B raw29471step1 raw29471step1Labels := by
      have ha : raw29471step1 = -raw29471step0 := by apply Matrix.ext; change ∀ i j, raw29471step1 i j = -(raw29471step0 i j); unfold raw29471step1 raw29471step0; decide +kernel
      have hl : raw29471step1Labels = raw29471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2349 node2349Labels := by rfl

theorem canonical29472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29472 raw29472Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw29472 raw29472Labels = mixedMoment B raw29472step0 raw29472step0Labels := by
      have ha : raw29472step0 = (fun i j => raw29472 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29472step0 raw29472; decide +kernel
      have hl : raw29472step0Labels = raw29472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29472 raw29472Labels permutation158 permutation2
    _ = mixedMoment B node2890 node2890Labels := by rfl

theorem canonical29473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29473 raw29473Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw29473 raw29473Labels = mixedMoment B raw29473step0 raw29473step0Labels := by
      have ha : raw29473step0 = (fun i j => raw29473 (permutation204 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29473step0 raw29473; decide +kernel
      have hl : raw29473step0Labels = raw29473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29473 raw29473Labels permutation204 permutation2
    mixedMoment B raw29473step0 raw29473step0Labels = mixedMoment B raw29473step1 raw29473step1Labels := by
      have ha : raw29473step1 = -raw29473step0 := by apply Matrix.ext; change ∀ i j, raw29473step1 i j = -(raw29473step0 i j); unfold raw29473step1 raw29473step0; decide +kernel
      have hl : raw29473step1Labels = raw29473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical29474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29474 raw29474Labels = mixedMoment B node3430 node3430Labels := by
  calc
    mixedMoment B raw29474 raw29474Labels = mixedMoment B raw29474step0 raw29474step0Labels := by
      have ha : raw29474step0 = (fun i j => raw29474 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29474step0 raw29474; decide +kernel
      have hl : raw29474step0Labels = raw29474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29474 raw29474Labels permutation162 permutation2
    mixedMoment B raw29474step0 raw29474step0Labels = mixedMoment B raw29474step1 raw29474step1Labels := by
      have ha : raw29474step1 = -raw29474step0 := by apply Matrix.ext; change ∀ i j, raw29474step1 i j = -(raw29474step0 i j); unfold raw29474step1 raw29474step0; decide +kernel
      have hl : raw29474step1Labels = raw29474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3430 node3430Labels := by rfl

theorem canonical29475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29475 raw29475Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw29475 raw29475Labels = mixedMoment B raw29475step0 raw29475step0Labels := by
      have ha : raw29475step0 = (fun i j => raw29475 (permutation552 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29475step0 raw29475; decide +kernel
      have hl : raw29475step0Labels = raw29475Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29475 raw29475Labels permutation552 permutation2
    _ = mixedMoment B node2534 node2534Labels := by rfl

theorem canonical29476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29476 raw29476Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw29476 raw29476Labels = mixedMoment B raw29476step0 raw29476step0Labels := by
      have ha : raw29476step0 = (fun i j => raw29476 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29476step0 raw29476; decide +kernel
      have hl : raw29476step0Labels = raw29476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29476 raw29476Labels permutation159 permutation2
    mixedMoment B raw29476step0 raw29476step0Labels = mixedMoment B raw29476step1 raw29476step1Labels := by
      have ha : raw29476step1 = -raw29476step0 := by apply Matrix.ext; change ∀ i j, raw29476step1 i j = -(raw29476step0 i j); unfold raw29476step1 raw29476step0; decide +kernel
      have hl : raw29476step1Labels = raw29476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

theorem canonical29482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29482 raw29482Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw29482 raw29482Labels = mixedMoment B raw29482step0 raw29482step0Labels := by
      have ha : raw29482step0 = (fun i j => raw29482 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29482step0 raw29482; decide +kernel
      have hl : raw29482step0Labels = raw29482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29482 raw29482Labels permutation176 permutation2
    _ = mixedMoment B node3779 node3779Labels := by rfl

theorem canonical29483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29483 raw29483Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw29483 raw29483Labels = mixedMoment B raw29483step0 raw29483step0Labels := by
      have hz : ∀ j, raw29483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw29483step0 = (fun i j => raw29483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw29483step0 raw29483; decide +kernel
      have hl : raw29483step0Labels = raw29483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29483 raw29483Labels permutation265 hz
    _ = mixedMoment B node2489 node2489Labels := by rfl

theorem canonical29484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29484 raw29484Labels = mixedMoment B node2546 node2546Labels := by
  calc
    _ = mixedMoment B node2546 node2546Labels := by rfl

theorem canonical29485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29485 raw29485Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw29485 raw29485Labels = mixedMoment B raw29485step0 raw29485step0Labels := by
      have ha : raw29485step0 = (fun i j => raw29485 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29485step0 raw29485; decide +kernel
      have hl : raw29485step0Labels = raw29485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29485 raw29485Labels permutation176 permutation2
    _ = mixedMoment B node2432 node2432Labels := by rfl

theorem canonical29486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29486 raw29486Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw29486 raw29486Labels = mixedMoment B raw29486step0 raw29486step0Labels := by
      have ha : raw29486step0 = (fun i j => raw29486 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29486step0 raw29486; decide +kernel
      have hl : raw29486step0Labels = raw29486Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29486 raw29486Labels permutation177 permutation2
    _ = mixedMoment B node2422 node2422Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7199 raw7199Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7199 raw7199Labels = mixedMoment B raw7199step0 raw7199step0Labels := by
      have hz : ∀ j, raw7199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7199step0 = (fun i j => raw7199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7199step0 raw7199; decide +kernel
      have hl : raw7199step0Labels = raw7199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7199 raw7199Labels permutation520 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical7209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7209 raw7209Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw7209 raw7209Labels = mixedMoment B raw7209step0 raw7209step0Labels := by
      have ha : raw7209step0 = (fun i j => raw7209 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7209step0 raw7209; decide +kernel
      have hl : raw7209step0Labels = raw7209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7209 raw7209Labels permutation160 permutation2
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical7211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7211 raw7211Labels = mixedMoment B node2473 node2473Labels := by
  calc
    _ = mixedMoment B node2473 node2473Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9013 raw9013Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9013 raw9013Labels = mixedMoment B raw9013step0 raw9013step0Labels := by
      have hz : ∀ j, raw9013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9013step0 = (fun i j => raw9013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9013step0 raw9013; decide +kernel
      have hl : raw9013step0Labels = raw9013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9013 raw9013Labels permutation265 hz
    mixedMoment B raw9013step0 raw9013step0Labels = mixedMoment B raw9013step1 raw9013step1Labels := by
      have ha : raw9013step1 = (fun i j => raw9013step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9013step1 raw9013step0; decide +kernel
      have hl : raw9013step1Labels = raw9013step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9013step0 raw9013step0Labels permutation122 permutation0
    mixedMoment B raw9013step1 raw9013step1Labels = mixedMoment B raw9013step2 raw9013step2Labels := by
      have ha : raw9013step2 = -raw9013step1 := by apply Matrix.ext; change ∀ i j, raw9013step2 i j = -(raw9013step1 i j); unfold raw9013step2 raw9013step1; decide +kernel
      have hl : raw9013step2Labels = raw9013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9025 raw9025Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw9025 raw9025Labels = mixedMoment B raw9025step0 raw9025step0Labels := by
      have ha : raw9025step0 = (fun i j => raw9025 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9025step0 raw9025; decide +kernel
      have hl : raw9025step0Labels = raw9025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9025 raw9025Labels permutation153 permutation2
    _ = mixedMoment B node2981 node2981Labels := by rfl

theorem canonical9031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9031 raw9031Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw9031 raw9031Labels = mixedMoment B raw9031step0 raw9031step0Labels := by
      have hz : ∀ j, raw9031 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9031step0 = (fun i j => raw9031 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9031step0 raw9031; decide +kernel
      have hl : raw9031step0Labels = raw9031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9031 raw9031Labels permutation265 hz
    mixedMoment B raw9031step0 raw9031step0Labels = mixedMoment B raw9031step1 raw9031step1Labels := by
      have ha : raw9031step1 = (fun i j => raw9031step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9031step1 raw9031step0; decide +kernel
      have hl : raw9031step1Labels = raw9031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9031step0 raw9031step0Labels permutation33 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1117 node1117Labels = Sparse.eval nodeValue1117 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1117) = mixedMoment B node1117 node1117Labels := rfl
  simpa [nodeValue1117, Sparse.eval] using hc.symm

theorem sound1151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1151 node1151Labels = Sparse.eval nodeValue1151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1151) = mixedMoment B node1151 node1151Labels := rfl
  simpa [nodeValue1151, Sparse.eval] using hc.symm

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

theorem sound1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1330 node1330Labels = Sparse.eval nodeValue1330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1330) = mixedMoment B node1330 node1330Labels := rfl
  simpa [nodeValue1330, Sparse.eval] using hc.symm

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

theorem sound1347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1347 node1347Labels = Sparse.eval nodeValue1347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1347) = mixedMoment B node1347 node1347Labels := rfl
  simpa [nodeValue1347, Sparse.eval] using hc.symm

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

theorem sound1807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1807 node1807Labels = Sparse.eval nodeValue1807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1807) = mixedMoment B node1807 node1807Labels := rfl
  simpa [nodeValue1807, Sparse.eval] using hc.symm

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

theorem sound1921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1921 node1921Labels = Sparse.eval nodeValue1921 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1921) = mixedMoment B node1921 node1921Labels := rfl
  simpa [nodeValue1921, Sparse.eval] using hc.symm

theorem sound1928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1928 node1928Labels = Sparse.eval nodeValue1928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1928) = mixedMoment B node1928 node1928Labels := rfl
  simpa [nodeValue1928, Sparse.eval] using hc.symm

theorem sound1941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1941 node1941Labels = Sparse.eval nodeValue1941 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1941) = mixedMoment B node1941 node1941Labels := rfl
  simpa [nodeValue1941, Sparse.eval] using hc.symm

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

theorem sound2320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2320 node2320Labels = Sparse.eval nodeValue2320 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2320) = mixedMoment B node2320 node2320Labels := rfl
  simpa [nodeValue2320, Sparse.eval] using hc.symm

theorem sound2324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2324 node2324Labels = Sparse.eval nodeValue2324 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2324) = mixedMoment B node2324 node2324Labels := rfl
  simpa [nodeValue2324, Sparse.eval] using hc.symm

theorem sound2347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2347 node2347Labels = Sparse.eval nodeValue2347 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2347) = mixedMoment B node2347 node2347Labels := rfl
  simpa [nodeValue2347, Sparse.eval] using hc.symm

theorem sound2349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2349 node2349Labels = Sparse.eval nodeValue2349 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2349) = mixedMoment B node2349 node2349Labels := rfl
  simpa [nodeValue2349, Sparse.eval] using hc.symm

theorem sound2350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2350 node2350Labels = Sparse.eval nodeValue2350 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2350) = mixedMoment B node2350 node2350Labels := rfl
  simpa [nodeValue2350, Sparse.eval] using hc.symm

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

theorem sound2422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2422 node2422Labels = Sparse.eval nodeValue2422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2422) = mixedMoment B node2422 node2422Labels := rfl
  simpa [nodeValue2422, Sparse.eval] using hc.symm

theorem sound2423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2423 node2423Labels = Sparse.eval nodeValue2423 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2423) = mixedMoment B node2423 node2423Labels := rfl
  simpa [nodeValue2423, Sparse.eval] using hc.symm

theorem sound2427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2427 node2427Labels = Sparse.eval nodeValue2427 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2427) = mixedMoment B node2427 node2427Labels := rfl
  simpa [nodeValue2427, Sparse.eval] using hc.symm

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

theorem sound2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2432 node2432Labels = Sparse.eval nodeValue2432 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2432) = mixedMoment B node2432 node2432Labels := rfl
  simpa [nodeValue2432, Sparse.eval] using hc.symm

theorem sound2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2435 node2435Labels = Sparse.eval nodeValue2435 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2435) = mixedMoment B node2435 node2435Labels := rfl
  simpa [nodeValue2435, Sparse.eval] using hc.symm

theorem sound2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2441 node2441Labels = Sparse.eval nodeValue2441 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2441) = mixedMoment B node2441 node2441Labels := rfl
  simpa [nodeValue2441, Sparse.eval] using hc.symm

theorem sound2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2473 node2473Labels = Sparse.eval nodeValue2473 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2473) = mixedMoment B node2473 node2473Labels := rfl
  simpa [nodeValue2473, Sparse.eval] using hc.symm

theorem sound2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2480 node2480Labels = Sparse.eval nodeValue2480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2480) = mixedMoment B node2480 node2480Labels := rfl
  simpa [nodeValue2480, Sparse.eval] using hc.symm

theorem sound2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2483 node2483Labels = Sparse.eval nodeValue2483 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2483) = mixedMoment B node2483 node2483Labels := rfl
  simpa [nodeValue2483, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

theorem sound2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2489 node2489Labels = Sparse.eval nodeValue2489 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2489) = mixedMoment B node2489 node2489Labels := rfl
  simpa [nodeValue2489, Sparse.eval] using hc.symm

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

theorem zero2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = 0 := by
  exact mixedMoment_alpha B hF node2546 node2546Labels 1 permutation158
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

theorem sound2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2522 node2522Labels = Sparse.eval nodeValue2522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2522) = mixedMoment B node2522 node2522Labels := rfl
  simpa [nodeValue2522, Sparse.eval] using hc.symm

theorem sound2534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2534 node2534Labels = Sparse.eval nodeValue2534 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2534) = mixedMoment B node2534 node2534Labels := rfl
  simpa [nodeValue2534, Sparse.eval] using hc.symm

theorem sound2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2545 node2545Labels = Sparse.eval nodeValue2545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2545) = mixedMoment B node2545 node2545Labels := rfl
  simpa [nodeValue2545, Sparse.eval] using hc.symm

theorem sound2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2546 node2546Labels = Sparse.eval nodeValue2546 (mixedVector B) := by
  simpa only [nodeValue2546, Sparse.eval_nil] using zero2546 B _hB _hF

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2557 node2557Labels = Sparse.eval nodeValue2557 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2557) = mixedMoment B node2557 node2557Labels := rfl
  simpa [nodeValue2557, Sparse.eval] using hc.symm

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

theorem sound2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2560 node2560Labels = Sparse.eval nodeValue2560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2560) = mixedMoment B node2560 node2560Labels := rfl
  simpa [nodeValue2560, Sparse.eval] using hc.symm

theorem sound2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2584 node2584Labels = Sparse.eval nodeValue2584 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2584) = mixedMoment B node2584 node2584Labels := rfl
  simpa [nodeValue2584, Sparse.eval] using hc.symm

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

theorem sound2668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2668 node2668Labels = Sparse.eval nodeValue2668 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2668) = mixedMoment B node2668 node2668Labels := rfl
  simpa [nodeValue2668, Sparse.eval] using hc.symm

theorem sound2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2670 node2670Labels = Sparse.eval nodeValue2670 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2670) = mixedMoment B node2670 node2670Labels := rfl
  simpa [nodeValue2670, Sparse.eval] using hc.symm

theorem sound2674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2674 node2674Labels = Sparse.eval nodeValue2674 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2674) = mixedMoment B node2674 node2674Labels := rfl
  simpa [nodeValue2674, Sparse.eval] using hc.symm

theorem sound2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2681 node2681Labels = Sparse.eval nodeValue2681 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2681) = mixedMoment B node2681 node2681Labels := rfl
  simpa [nodeValue2681, Sparse.eval] using hc.symm

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

theorem sound2797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2797 node2797Labels = Sparse.eval nodeValue2797 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2797) = mixedMoment B node2797 node2797Labels := rfl
  simpa [nodeValue2797, Sparse.eval] using hc.symm

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

theorem sound2824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2824 node2824Labels = Sparse.eval nodeValue2824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2824) = mixedMoment B node2824 node2824Labels := rfl
  simpa [nodeValue2824, Sparse.eval] using hc.symm

theorem sound2831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2831 node2831Labels = Sparse.eval nodeValue2831 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2831) = mixedMoment B node2831 node2831Labels := rfl
  simpa [nodeValue2831, Sparse.eval] using hc.symm

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

theorem sound2890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2890 node2890Labels = Sparse.eval nodeValue2890 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2890) = mixedMoment B node2890 node2890Labels := rfl
  simpa [nodeValue2890, Sparse.eval] using hc.symm

theorem sound2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2896 node2896Labels = Sparse.eval nodeValue2896 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2896) = mixedMoment B node2896 node2896Labels := rfl
  simpa [nodeValue2896, Sparse.eval] using hc.symm

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

theorem sound2916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2916 node2916Labels = Sparse.eval nodeValue2916 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2916) = mixedMoment B node2916 node2916Labels := rfl
  simpa [nodeValue2916, Sparse.eval] using hc.symm

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

theorem sound2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2928 node2928Labels = Sparse.eval nodeValue2928 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2928) = mixedMoment B node2928 node2928Labels := rfl
  simpa [nodeValue2928, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

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

theorem sound2981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2981 node2981Labels = Sparse.eval nodeValue2981 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2981) = mixedMoment B node2981 node2981Labels := rfl
  simpa [nodeValue2981, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3351 node3351Labels = 0 := by
  exact mixedMoment_alpha B hF node3351 node3351Labels 1 permutation446
    (by decide +kernel)

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

theorem sound3345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3345 node3345Labels = Sparse.eval nodeValue3345 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3345) = mixedMoment B node3345 node3345Labels := rfl
  simpa [nodeValue3345, Sparse.eval] using hc.symm

theorem sound3348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3348 node3348Labels = Sparse.eval nodeValue3348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3348) = mixedMoment B node3348 node3348Labels := rfl
  simpa [nodeValue3348, Sparse.eval] using hc.symm

theorem sound3351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3351 node3351Labels = Sparse.eval nodeValue3351 (mixedVector B) := by
  simpa only [nodeValue3351, Sparse.eval_nil] using zero3351 B _hB _hF

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

theorem sound3430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3430 node3430Labels = Sparse.eval nodeValue3430 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3430) = mixedMoment B node3430 node3430Labels := rfl
  simpa [nodeValue3430, Sparse.eval] using hc.symm

theorem sound3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3433 node3433Labels = Sparse.eval nodeValue3433 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3433) = mixedMoment B node3433 node3433Labels := rfl
  simpa [nodeValue3433, Sparse.eval] using hc.symm

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

theorem sound3476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3476 node3476Labels = Sparse.eval nodeValue3476 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3476) = mixedMoment B node3476 node3476Labels := rfl
  simpa [nodeValue3476, Sparse.eval] using hc.symm

theorem sound3478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3478 node3478Labels = Sparse.eval nodeValue3478 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3478) = mixedMoment B node3478 node3478Labels := rfl
  simpa [nodeValue3478, Sparse.eval] using hc.symm

theorem sound3480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3480 node3480Labels = Sparse.eval nodeValue3480 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3480) = mixedMoment B node3480 node3480Labels := rfl
  simpa [nodeValue3480, Sparse.eval] using hc.symm

theorem sound3482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3482 node3482Labels = Sparse.eval nodeValue3482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3482) = mixedMoment B node3482 node3482Labels := rfl
  simpa [nodeValue3482, Sparse.eval] using hc.symm

theorem sound3516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3516 node3516Labels = Sparse.eval nodeValue3516 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3516) = mixedMoment B node3516 node3516Labels := rfl
  simpa [nodeValue3516, Sparse.eval] using hc.symm

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

theorem sound3522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3522 node3522Labels = Sparse.eval nodeValue3522 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3522) = mixedMoment B node3522 node3522Labels := rfl
  simpa [nodeValue3522, Sparse.eval] using hc.symm

theorem sound3538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3538 node3538Labels = Sparse.eval nodeValue3538 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3538) = mixedMoment B node3538 node3538Labels := rfl
  simpa [nodeValue3538, Sparse.eval] using hc.symm

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

theorem sound3612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3612 node3612Labels = Sparse.eval nodeValue3612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3612) = mixedMoment B node3612 node3612Labels := rfl
  simpa [nodeValue3612, Sparse.eval] using hc.symm

theorem sound3614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3614 node3614Labels = Sparse.eval nodeValue3614 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3614) = mixedMoment B node3614 node3614Labels := rfl
  simpa [nodeValue3614, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3690 node3690Labels = Sparse.eval nodeValue3690 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3690) = mixedMoment B node3690 node3690Labels := rfl
  simpa [nodeValue3690, Sparse.eval] using hc.symm

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

theorem sound3779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3779 node3779Labels = Sparse.eval nodeValue3779 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3779) = mixedMoment B node3779 node3779Labels := rfl
  simpa [nodeValue3779, Sparse.eval] using hc.symm

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

theorem sound4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4082 node4082Labels = Sparse.eval nodeValue4082 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4082) = mixedMoment B node4082 node4082Labels := rfl
  simpa [nodeValue4082, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources65
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2108 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2108 + difference 0 3) (sourceB2108 + difference 3 0) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2108 + difference 0 3) (sourceB2108 + difference 3 0) sourceC2108) = raw29391 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29391; decide +kernel
    rw [ha]
    exact (canonical29391 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2108 + difference 1 3) (sourceB2108 + difference 3 1) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3612) := by
    have ha : (tripleCharges (sourceA2108 + difference 1 3) (sourceB2108 + difference 3 1) sourceC2108) = raw29313 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29313; decide +kernel
    rw [ha]
    exact (canonical29313 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2108 + difference 2 3) (sourceB2108 + difference 3 2) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2108 + difference 2 3) (sourceB2108 + difference 3 2) sourceC2108) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2108 + difference 3 3) (sourceB2108 + difference 3 3) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2108 + difference 3 3) (sourceB2108 + difference 3 3) sourceC2108) = raw29388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29388; decide +kernel
    rw [ha]
    exact (canonical29388 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2108 + difference 4 3) (sourceB2108 + difference 3 4) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2108 + difference 4 3) (sourceB2108 + difference 3 4) sourceC2108) = raw29394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29394; decide +kernel
    rw [ha]
    exact (canonical29394 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2108 + difference 5 3) (sourceB2108 + difference 3 5) sourceC2108) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2108 + difference 5 3) (sourceB2108 + difference 3 5) sourceC2108) = raw29395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2108 sourceB2108 sourceC2108 difference raw29395; decide +kernel
    rw [ha]
    exact (canonical29395 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2108 + sourceB2108) sourceC2108) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2108 + sourceB2108) sourceC2108) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2108 sourceB2108 sourceC2108 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2108 sourceB2108 sourceC2108
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2108, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2110 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 0) (sourceB2110 + difference 0 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1928) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 0) (sourceB2110 + difference 0 5) sourceC2110) = raw29400 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29400; decide +kernel
    rw [ha]
    exact (canonical29400 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 1) (sourceB2110 + difference 1 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3348) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 1) (sourceB2110 + difference 1 5) sourceC2110) = raw29401 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29401; decide +kernel
    rw [ha]
    exact (canonical29401 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 2) (sourceB2110 + difference 2 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3430) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 2) (sourceB2110 + difference 2 5) sourceC2110) = raw29402 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29402; decide +kernel
    rw [ha]
    exact (canonical29402 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 3) (sourceB2110 + difference 3 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 3) (sourceB2110 + difference 3 5) sourceC2110) = raw29395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29395; decide +kernel
    rw [ha]
    exact (canonical29395 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 4) (sourceB2110 + difference 4 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 4) (sourceB2110 + difference 4 5) sourceC2110) = raw29403 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29403; decide +kernel
    rw [ha]
    exact (canonical29403 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2110 + difference 5 5) (sourceB2110 + difference 5 5) sourceC2110) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3480) := by
    have ha : (tripleCharges (sourceA2110 + difference 5 5) (sourceB2110 + difference 5 5) sourceC2110) = raw29388 := by
      apply Matrix.ext; unfold tripleCharges sourceA2110 sourceB2110 sourceC2110 difference raw29388; decide +kernel
    rw [ha]
    exact (canonical29388 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2110 + sourceB2110) sourceC2110) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2110 + sourceB2110) sourceC2110) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2110 sourceB2110 sourceC2110 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2110 sourceB2110 sourceC2110
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2110, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2111 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 0) (sourceB2111 + difference 0 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 0) (sourceB2111 + difference 0 2) sourceC2111) = raw29404 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29404; decide +kernel
    rw [ha]
    exact (canonical29404 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 1) (sourceB2111 + difference 1 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2324) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 1) (sourceB2111 + difference 1 2) sourceC2111) = raw29405 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29405; decide +kernel
    rw [ha]
    exact (canonical29405 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 2) (sourceB2111 + difference 2 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2473) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 2) (sourceB2111 + difference 2 2) sourceC2111) = raw7211 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw7211; decide +kernel
    rw [ha]
    exact (canonical7211 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 3) (sourceB2111 + difference 3 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2441) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 3) (sourceB2111 + difference 3 2) sourceC2111) = raw29406 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29406; decide +kernel
    rw [ha]
    exact (canonical29406 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 4) (sourceB2111 + difference 4 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 4) (sourceB2111 + difference 4 2) sourceC2111) = raw7209 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw7209; decide +kernel
    rw [ha]
    exact (canonical7209 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2111 + difference 2 5) (sourceB2111 + difference 5 2) sourceC2111) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA2111 + difference 2 5) (sourceB2111 + difference 5 2) sourceC2111) = raw29407 := by
      apply Matrix.ext; unfold tripleCharges sourceA2111 sourceB2111 sourceC2111 difference raw29407; decide +kernel
    rw [ha]
    exact (canonical29407 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2111 + sourceB2111) sourceC2111) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2111 + sourceB2111) sourceC2111) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA2111 sourceB2111 sourceC2111 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2111 sourceB2111 sourceC2111
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2111, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources66
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq2112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2112 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2112 + difference 0 2) (sourceB2112 + difference 2 0) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3690) := by
    have ha : (tripleCharges (sourceA2112 + difference 0 2) (sourceB2112 + difference 2 0) sourceC2112) = raw29408 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29408; decide +kernel
    rw [ha]
    exact (canonical29408 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2112 + difference 1 2) (sourceB2112 + difference 2 1) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA2112 + difference 1 2) (sourceB2112 + difference 2 1) sourceC2112) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2112 + difference 2 2) (sourceB2112 + difference 2 2) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA2112 + difference 2 2) (sourceB2112 + difference 2 2) sourceC2112) = raw9025 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw9025; decide +kernel
    rw [ha]
    exact (canonical9025 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2112 + difference 3 2) (sourceB2112 + difference 2 3) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2900) := by
    have ha : (tripleCharges (sourceA2112 + difference 3 2) (sourceB2112 + difference 2 3) sourceC2112) = raw29409 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29409; decide +kernel
    rw [ha]
    exact (canonical29409 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2112 + difference 4 2) (sourceB2112 + difference 2 4) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2320) := by
    have ha : (tripleCharges (sourceA2112 + difference 4 2) (sourceB2112 + difference 2 4) sourceC2112) = raw29410 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29410; decide +kernel
    rw [ha]
    exact (canonical29410 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2112 + difference 5 2) (sourceB2112 + difference 2 5) sourceC2112) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2797) := by
    have ha : (tripleCharges (sourceA2112 + difference 5 2) (sourceB2112 + difference 2 5) sourceC2112) = raw29411 := by
      apply Matrix.ext; unfold tripleCharges sourceA2112 sourceB2112 sourceC2112 difference raw29411; decide +kernel
    rw [ha]
    exact (canonical29411 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2112 + sourceB2112) sourceC2112) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2112 + sourceB2112) sourceC2112) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA2112 sourceB2112 sourceC2112 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2112 sourceB2112 sourceC2112
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2112, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2114 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 0) (sourceB2114 + difference 0 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1941) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 0) (sourceB2114 + difference 0 4) sourceC2114) = raw29416 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29416; decide +kernel
    rw [ha]
    exact (canonical29416 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 1) (sourceB2114 + difference 1 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3351) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 1) (sourceB2114 + difference 1 4) sourceC2114) = raw29417 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29417; decide +kernel
    rw [ha]
    exact (canonical29417 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 2) (sourceB2114 + difference 2 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 2) (sourceB2114 + difference 2 4) sourceC2114) = raw29394 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29394; decide +kernel
    rw [ha]
    exact (canonical29394 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 3) (sourceB2114 + difference 3 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3482) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 3) (sourceB2114 + difference 3 4) sourceC2114) = raw29418 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29418; decide +kernel
    rw [ha]
    exact (canonical29418 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 4) (sourceB2114 + difference 4 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 4) (sourceB2114 + difference 4 4) sourceC2114) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2114 + difference 4 5) (sourceB2114 + difference 5 4) sourceC2114) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2114 + difference 4 5) (sourceB2114 + difference 5 4) sourceC2114) = raw29419 := by
      apply Matrix.ext; unfold tripleCharges sourceA2114 sourceB2114 sourceC2114 difference raw29419; decide +kernel
    rw [ha]
    exact (canonical29419 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2114 + sourceB2114) sourceC2114) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2114 + sourceB2114) sourceC2114) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2114 sourceB2114 sourceC2114 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2114 sourceB2114 sourceC2114
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2114, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2115 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 0) (sourceB2115 + difference 0 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1921) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 0) (sourceB2115 + difference 0 5) sourceC2115) = raw29420 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29420; decide +kernel
    rw [ha]
    exact (canonical29420 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 1) (sourceB2115 + difference 1 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3345) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 1) (sourceB2115 + difference 1 5) sourceC2115) = raw29421 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29421; decide +kernel
    rw [ha]
    exact (canonical29421 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 2) (sourceB2115 + difference 2 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 2) (sourceB2115 + difference 2 5) sourceC2115) = raw29395 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29395; decide +kernel
    rw [ha]
    exact (canonical29395 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 3) (sourceB2115 + difference 3 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 3) (sourceB2115 + difference 3 5) sourceC2115) = raw29422 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29422; decide +kernel
    rw [ha]
    exact (canonical29422 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 4) (sourceB2115 + difference 4 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2668) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 4) (sourceB2115 + difference 4 5) sourceC2115) = raw29423 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29423; decide +kernel
    rw [ha]
    exact (canonical29423 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2115 + difference 5 5) (sourceB2115 + difference 5 5) sourceC2115) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3476) := by
    have ha : (tripleCharges (sourceA2115 + difference 5 5) (sourceB2115 + difference 5 5) sourceC2115) = raw29328 := by
      apply Matrix.ext; unfold tripleCharges sourceA2115 sourceB2115 sourceC2115 difference raw29328; decide +kernel
    rw [ha]
    exact (canonical29328 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2115 + sourceB2115) sourceC2115) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2115 + sourceB2115) sourceC2115) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2115 sourceB2115 sourceC2115 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2115 sourceB2115 sourceC2115
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2115, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2118 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2118 + difference 0 2) (sourceB2118 + difference 2 0) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA2118 + difference 0 2) (sourceB2118 + difference 2 0) sourceC2118) = raw29431 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29431; decide +kernel
    rw [ha]
    exact (canonical29431 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2118 + difference 1 2) (sourceB2118 + difference 2 1) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2522) := by
    have ha : (tripleCharges (sourceA2118 + difference 1 2) (sourceB2118 + difference 2 1) sourceC2118) = raw29432 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29432; decide +kernel
    rw [ha]
    exact (canonical29432 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2118 + difference 2 2) (sourceB2118 + difference 2 2) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA2118 + difference 2 2) (sourceB2118 + difference 2 2) sourceC2118) = raw29433 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29433; decide +kernel
    rw [ha]
    exact (canonical29433 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2118 + difference 3 2) (sourceB2118 + difference 2 3) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2427) := by
    have ha : (tripleCharges (sourceA2118 + difference 3 2) (sourceB2118 + difference 2 3) sourceC2118) = raw29434 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29434; decide +kernel
    rw [ha]
    exact (canonical29434 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2118 + difference 4 2) (sourceB2118 + difference 2 4) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2435) := by
    have ha : (tripleCharges (sourceA2118 + difference 4 2) (sourceB2118 + difference 2 4) sourceC2118) = raw29435 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29435; decide +kernel
    rw [ha]
    exact (canonical29435 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2118 + difference 5 2) (sourceB2118 + difference 2 5) sourceC2118) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1807) := by
    have ha : (tripleCharges (sourceA2118 + difference 5 2) (sourceB2118 + difference 2 5) sourceC2118) = raw29436 := by
      apply Matrix.ext; unfold tripleCharges sourceA2118 sourceB2118 sourceC2118 difference raw29436; decide +kernel
    rw [ha]
    exact (canonical29436 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2118 + sourceB2118) sourceC2118) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA2118 + sourceB2118) sourceC2118) = raw29437 := by
      apply Matrix.ext; unfold doubleCharges sourceA2118 sourceB2118 sourceC2118 raw29437; decide +kernel
    rw [ha]
    exact (canonical29437 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2118 sourceB2118 sourceC2118
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2118, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2119 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 0) (sourceB2119 + difference 0 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 0) (sourceB2119 + difference 0 2) sourceC2119) = raw29438 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29438; decide +kernel
    rw [ha]
    exact (canonical29438 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 1) (sourceB2119 + difference 1 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2831) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 1) (sourceB2119 + difference 1 2) sourceC2119) = raw29439 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29439; decide +kernel
    rw [ha]
    exact (canonical29439 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 2) (sourceB2119 + difference 2 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2942) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 2) (sourceB2119 + difference 2 2) sourceC2119) = raw29440 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29440; decide +kernel
    rw [ha]
    exact (canonical29440 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 3) (sourceB2119 + difference 3 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2902) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 3) (sourceB2119 + difference 3 2) sourceC2119) = raw29441 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29441; decide +kernel
    rw [ha]
    exact (canonical29441 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 4) (sourceB2119 + difference 4 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2964) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 4) (sourceB2119 + difference 4 2) sourceC2119) = raw29442 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29442; decide +kernel
    rw [ha]
    exact (canonical29442 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2119 + difference 2 5) (sourceB2119 + difference 5 2) sourceC2119) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA2119 + difference 2 5) (sourceB2119 + difference 5 2) sourceC2119) = raw29443 := by
      apply Matrix.ext; unfold tripleCharges sourceA2119 sourceB2119 sourceC2119 difference raw29443; decide +kernel
    rw [ha]
    exact (canonical29443 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2119 + sourceB2119) sourceC2119) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2119 + sourceB2119) sourceC2119) = raw29444 := by
      apply Matrix.ext; unfold doubleCharges sourceA2119 sourceB2119 sourceC2119 raw29444; decide +kernel
    rw [ha]
    exact (canonical29444 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2119 sourceB2119 sourceC2119
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2119, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2120 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 0) (sourceB2120 + difference 0 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 0) (sourceB2120 + difference 0 0) sourceC2120) = raw29445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29445; decide +kernel
    rw [ha]
    exact (canonical29445 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 1) (sourceB2120 + difference 1 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2681) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 1) (sourceB2120 + difference 1 0) sourceC2120) = raw29446 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29446; decide +kernel
    rw [ha]
    exact (canonical29446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 2) (sourceB2120 + difference 2 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2674) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 2) (sourceB2120 + difference 2 0) sourceC2120) = raw29447 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29447; decide +kernel
    rw [ha]
    exact (canonical29447 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 3) (sourceB2120 + difference 3 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2668) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 3) (sourceB2120 + difference 3 0) sourceC2120) = raw29448 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29448; decide +kernel
    rw [ha]
    exact (canonical29448 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 4) (sourceB2120 + difference 4 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2584) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 4) (sourceB2120 + difference 4 0) sourceC2120) = raw29449 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29449; decide +kernel
    rw [ha]
    exact (canonical29449 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2120 + difference 0 5) (sourceB2120 + difference 5 0) sourceC2120) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2120 + difference 0 5) (sourceB2120 + difference 5 0) sourceC2120) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2120 sourceB2120 sourceC2120 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2120 + sourceB2120) sourceC2120) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2120 + sourceB2120) sourceC2120) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2120 sourceB2120 sourceC2120 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2120 sourceB2120 sourceC2120
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2120, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2121 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2121 + difference 0 5) (sourceB2121 + difference 5 0) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2121 + difference 0 5) (sourceB2121 + difference 5 0) sourceC2121) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2121 + difference 1 5) (sourceB2121 + difference 5 1) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3538) := by
    have ha : (tripleCharges (sourceA2121 + difference 1 5) (sourceB2121 + difference 5 1) sourceC2121) = raw29451 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29451; decide +kernel
    rw [ha]
    exact (canonical29451 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2121 + difference 2 5) (sourceB2121 + difference 5 2) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3614) := by
    have ha : (tripleCharges (sourceA2121 + difference 2 5) (sourceB2121 + difference 5 2) sourceC2121) = raw29452 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29452; decide +kernel
    rw [ha]
    exact (canonical29452 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2121 + difference 3 5) (sourceB2121 + difference 5 3) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2121 + difference 3 5) (sourceB2121 + difference 5 3) sourceC2121) = raw29453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29453; decide +kernel
    rw [ha]
    exact (canonical29453 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2121 + difference 4 5) (sourceB2121 + difference 5 4) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3522) := by
    have ha : (tripleCharges (sourceA2121 + difference 4 5) (sourceB2121 + difference 5 4) sourceC2121) = raw29454 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29454; decide +kernel
    rw [ha]
    exact (canonical29454 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2121 + difference 5 5) (sourceB2121 + difference 5 5) sourceC2121) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2670) := by
    have ha : (tripleCharges (sourceA2121 + difference 5 5) (sourceB2121 + difference 5 5) sourceC2121) = raw29445 := by
      apply Matrix.ext; unfold tripleCharges sourceA2121 sourceB2121 sourceC2121 difference raw29445; decide +kernel
    rw [ha]
    exact (canonical29445 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2121 + sourceB2121) sourceC2121) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2121 + sourceB2121) sourceC2121) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2121 sourceB2121 sourceC2121 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2121 sourceB2121 sourceC2121
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2121, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2122 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2122 + difference 0 2) (sourceB2122 + difference 2 0) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3719) := by
    have ha : (tripleCharges (sourceA2122 + difference 0 2) (sourceB2122 + difference 2 0) sourceC2122) = raw29455 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29455; decide +kernel
    rw [ha]
    exact (canonical29455 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2122 + difference 1 2) (sourceB2122 + difference 2 1) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA2122 + difference 1 2) (sourceB2122 + difference 2 1) sourceC2122) = raw29456 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29456; decide +kernel
    rw [ha]
    exact (canonical29456 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2122 + difference 2 2) (sourceB2122 + difference 2 2) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA2122 + difference 2 2) (sourceB2122 + difference 2 2) sourceC2122) = raw29457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29457; decide +kernel
    rw [ha]
    exact (canonical29457 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2122 + difference 3 2) (sourceB2122 + difference 2 3) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2122 + difference 3 2) (sourceB2122 + difference 2 3) sourceC2122) = raw29458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29458; decide +kernel
    rw [ha]
    exact (canonical29458 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2122 + difference 4 2) (sourceB2122 + difference 2 4) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2423) := by
    have ha : (tripleCharges (sourceA2122 + difference 4 2) (sourceB2122 + difference 2 4) sourceC2122) = raw29459 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw29459; decide +kernel
    rw [ha]
    exact (canonical29459 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2122 + difference 5 2) (sourceB2122 + difference 2 5) sourceC2122) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA2122 + difference 5 2) (sourceB2122 + difference 2 5) sourceC2122) = raw27508 := by
      apply Matrix.ext; unfold tripleCharges sourceA2122 sourceB2122 sourceC2122 difference raw27508; decide +kernel
    rw [ha]
    exact (canonical27508 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2122 + sourceB2122) sourceC2122) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2122 + sourceB2122) sourceC2122) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2122 sourceB2122 sourceC2122 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2122 sourceB2122 sourceC2122
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2122, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2123 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 0) (sourceB2123 + difference 0 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1151) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 0) (sourceB2123 + difference 0 3) sourceC2123) = raw24750 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw24750; decide +kernel
    rw [ha]
    exact (canonical24750 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 1) (sourceB2123 + difference 1 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2350) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 1) (sourceB2123 + difference 1 3) sourceC2123) = raw29460 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29460; decide +kernel
    rw [ha]
    exact (canonical29460 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 2) (sourceB2123 + difference 2 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2431) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 2) (sourceB2123 + difference 2 3) sourceC2123) = raw29458 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29458; decide +kernel
    rw [ha]
    exact (canonical29458 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 3) (sourceB2123 + difference 3 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 3) (sourceB2123 + difference 3 3) sourceC2123) = raw29457 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29457; decide +kernel
    rw [ha]
    exact (canonical29457 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 4) (sourceB2123 + difference 4 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 4) (sourceB2123 + difference 4 3) sourceC2123) = raw24747 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw24747; decide +kernel
    rw [ha]
    exact (canonical24747 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2123 + difference 3 5) (sourceB2123 + difference 5 3) sourceC2123) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA2123 + difference 3 5) (sourceB2123 + difference 5 3) sourceC2123) = raw29461 := by
      apply Matrix.ext; unfold tripleCharges sourceA2123 sourceB2123 sourceC2123 difference raw29461; decide +kernel
    rw [ha]
    exact (canonical29461 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2123 + sourceB2123) sourceC2123) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA2123 + sourceB2123) sourceC2123) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA2123 sourceB2123 sourceC2123 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2123 sourceB2123 sourceC2123
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2123, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2124 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 0) (sourceB2124 + difference 0 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 0) (sourceB2124 + difference 0 2) sourceC2124) = raw29462 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29462; decide +kernel
    rw [ha]
    exact (canonical29462 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 1) (sourceB2124 + difference 1 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2824) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 1) (sourceB2124 + difference 1 2) sourceC2124) = raw29463 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29463; decide +kernel
    rw [ha]
    exact (canonical29463 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 2) (sourceB2124 + difference 2 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 2) (sourceB2124 + difference 2 2) sourceC2124) = raw29464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29464; decide +kernel
    rw [ha]
    exact (canonical29464 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 3) (sourceB2124 + difference 3 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 3) (sourceB2124 + difference 3 2) sourceC2124) = raw29465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29465; decide +kernel
    rw [ha]
    exact (canonical29465 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 4) (sourceB2124 + difference 4 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2928) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 4) (sourceB2124 + difference 4 2) sourceC2124) = raw29466 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29466; decide +kernel
    rw [ha]
    exact (canonical29466 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2124 + difference 2 5) (sourceB2124 + difference 5 2) sourceC2124) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA2124 + difference 2 5) (sourceB2124 + difference 5 2) sourceC2124) = raw29467 := by
      apply Matrix.ext; unfold tripleCharges sourceA2124 sourceB2124 sourceC2124 difference raw29467; decide +kernel
    rw [ha]
    exact (canonical29467 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2124 + sourceB2124) sourceC2124) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2124 + sourceB2124) sourceC2124) = raw29468 := by
      apply Matrix.ext; unfold doubleCharges sourceA2124 sourceB2124 sourceC2124 raw29468; decide +kernel
    rw [ha]
    exact (canonical29468 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2124 sourceB2124 sourceC2124
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2124, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2125 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2125 + difference 0 3) (sourceB2125 + difference 3 0) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3721) := by
    have ha : (tripleCharges (sourceA2125 + difference 0 3) (sourceB2125 + difference 3 0) sourceC2125) = raw29469 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29469; decide +kernel
    rw [ha]
    exact (canonical29469 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2125 + difference 1 3) (sourceB2125 + difference 3 1) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2125 + difference 1 3) (sourceB2125 + difference 3 1) sourceC2125) = raw29470 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29470; decide +kernel
    rw [ha]
    exact (canonical29470 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2125 + difference 2 3) (sourceB2125 + difference 3 2) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2896) := by
    have ha : (tripleCharges (sourceA2125 + difference 2 3) (sourceB2125 + difference 3 2) sourceC2125) = raw29465 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29465; decide +kernel
    rw [ha]
    exact (canonical29465 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2125 + difference 3 3) (sourceB2125 + difference 3 3) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2916) := by
    have ha : (tripleCharges (sourceA2125 + difference 3 3) (sourceB2125 + difference 3 3) sourceC2125) = raw29464 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29464; decide +kernel
    rw [ha]
    exact (canonical29464 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2125 + difference 4 3) (sourceB2125 + difference 3 4) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA2125 + difference 4 3) (sourceB2125 + difference 3 4) sourceC2125) = raw29471 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29471; decide +kernel
    rw [ha]
    exact (canonical29471 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2125 + difference 5 3) (sourceB2125 + difference 3 5) sourceC2125) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2890) := by
    have ha : (tripleCharges (sourceA2125 + difference 5 3) (sourceB2125 + difference 3 5) sourceC2125) = raw29472 := by
      apply Matrix.ext; unfold tripleCharges sourceA2125 sourceB2125 sourceC2125 difference raw29472; decide +kernel
    rw [ha]
    exact (canonical29472 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2125 + sourceB2125) sourceC2125) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2125 + sourceB2125) sourceC2125) = raw29468 := by
      apply Matrix.ext; unfold doubleCharges sourceA2125 sourceB2125 sourceC2125 raw29468; decide +kernel
    rw [ha]
    exact (canonical29468 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2125 sourceB2125 sourceC2125
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2125, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2126 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 0) (sourceB2126 + difference 0 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 0) (sourceB2126 + difference 0 0) sourceC2126) = raw29453 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29453; decide +kernel
    rw [ha]
    exact (canonical29453 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 1) (sourceB2126 + difference 1 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3516) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 1) (sourceB2126 + difference 1 0) sourceC2126) = raw29473 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29473; decide +kernel
    rw [ha]
    exact (canonical29473 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 2) (sourceB2126 + difference 2 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3430) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 2) (sourceB2126 + difference 2 0) sourceC2126) = raw29474 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29474; decide +kernel
    rw [ha]
    exact (canonical29474 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 3) (sourceB2126 + difference 3 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3478) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 3) (sourceB2126 + difference 3 0) sourceC2126) = raw29450 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29450; decide +kernel
    rw [ha]
    exact (canonical29450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 4) (sourceB2126 + difference 4 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2534) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 4) (sourceB2126 + difference 4 0) sourceC2126) = raw29475 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29475; decide +kernel
    rw [ha]
    exact (canonical29475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2126 + difference 0 5) (sourceB2126 + difference 5 0) sourceC2126) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3433) := by
    have ha : (tripleCharges (sourceA2126 + difference 0 5) (sourceB2126 + difference 5 0) sourceC2126) = raw29476 := by
      apply Matrix.ext; unfold tripleCharges sourceA2126 sourceB2126 sourceC2126 difference raw29476; decide +kernel
    rw [ha]
    exact (canonical29476 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2126 + sourceB2126) sourceC2126) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4082) := by
    have ha : (doubleCharges (sourceA2126 + sourceB2126) sourceC2126) = raw29319 := by
      apply Matrix.ext; unfold doubleCharges sourceA2126 sourceB2126 sourceC2126 raw29319; decide +kernel
    rw [ha]
    exact (canonical29319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA2126 sourceB2126 sourceC2126
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2126, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq2129 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm2129 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA2129 + difference 0 2) (sourceB2129 + difference 2 0) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3779) := by
    have ha : (tripleCharges (sourceA2129 + difference 0 2) (sourceB2129 + difference 2 0) sourceC2129) = raw29482 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29482; decide +kernel
    rw [ha]
    exact (canonical29482 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA2129 + difference 1 2) (sourceB2129 + difference 2 1) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2489) := by
    have ha : (tripleCharges (sourceA2129 + difference 1 2) (sourceB2129 + difference 2 1) sourceC2129) = raw29483 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29483; decide +kernel
    rw [ha]
    exact (canonical29483 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA2129 + difference 2 2) (sourceB2129 + difference 2 2) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2546) := by
    have ha : (tripleCharges (sourceA2129 + difference 2 2) (sourceB2129 + difference 2 2) sourceC2129) = raw29484 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29484; decide +kernel
    rw [ha]
    exact (canonical29484 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA2129 + difference 3 2) (sourceB2129 + difference 2 3) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2432) := by
    have ha : (tripleCharges (sourceA2129 + difference 3 2) (sourceB2129 + difference 2 3) sourceC2129) = raw29485 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29485; decide +kernel
    rw [ha]
    exact (canonical29485 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA2129 + difference 4 2) (sourceB2129 + difference 2 4) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2129 + difference 4 2) (sourceB2129 + difference 2 4) sourceC2129) = raw29486 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw29486; decide +kernel
    rw [ha]
    exact (canonical29486 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA2129 + difference 5 2) (sourceB2129 + difference 2 5) sourceC2129) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA2129 + difference 5 2) (sourceB2129 + difference 2 5) sourceC2129) = raw27529 := by
      apply Matrix.ext; unfold tripleCharges sourceA2129 sourceB2129 sourceC2129 difference raw27529; decide +kernel
    rw [ha]
    exact (canonical27529 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA2129 + sourceB2129) sourceC2129) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA2129 + sourceB2129) sourceC2129) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA2129 sourceB2129 sourceC2129 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA2129 sourceB2129 sourceC2129
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm2129, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1760 : Integer.Sparse.reindex keyMap MixedData.row1760 = numericRow1760 := by decide +kernel

theorem numericCheck1760 (x : Master → ℝ) : Integer.Sparse.eval numericRow1760 x =
    (1 : ℝ) * reducedSource1760 x := by
  norm_num [numericRow1760, reducedSource1760, Integer.Sparse.eval, Sparse.eval, nodeValue3476, nodeValue3478, nodeValue3480, nodeValue3482, nodeValue3522, nodeValue3612, nodeValue4082]

theorem reindexCheck1761 : Integer.Sparse.reindex keyMap MixedData.row1761 = numericRow1761 := by decide +kernel

theorem numericCheck1761 (x : Master → ℝ) : Integer.Sparse.eval numericRow1761 x =
    (1 : ℝ) * reducedSource1761 x := by
  norm_num [numericRow1761, reducedSource1761, Integer.Sparse.eval, Sparse.eval, nodeValue1928, nodeValue2674, nodeValue3348, nodeValue3430, nodeValue3478, nodeValue3480, nodeValue4082]

theorem reindexCheck1762 : Integer.Sparse.reindex keyMap MixedData.row1762 = numericRow1762 := by decide +kernel

theorem numericCheck1762 (x : Master → ℝ) : Integer.Sparse.eval numericRow1762 x =
    (1 : ℝ) * reducedSource1762 x := by
  norm_num [numericRow1762, reducedSource1762, Integer.Sparse.eval, Sparse.eval, nodeValue1117, nodeValue2324, nodeValue2441, nodeValue2473, nodeValue2480, nodeValue2483, nodeValue4091]

theorem reindexCheck1763 : Integer.Sparse.reindex keyMap MixedData.row1763 = numericRow1763 := by decide +kernel

theorem numericCheck1763 (x : Master → ℝ) : Integer.Sparse.eval numericRow1763 x =
    (1 : ℝ) * reducedSource1763 x := by
  norm_num [numericRow1763, reducedSource1763, Integer.Sparse.eval, Sparse.eval, nodeValue2320, nodeValue2797, nodeValue2900, nodeValue2931, nodeValue2981, nodeValue3690, nodeValue4091]

theorem reindexCheck1764 : Integer.Sparse.reindex keyMap MixedData.row1764 = numericRow1764 := by decide +kernel

theorem numericCheck1764 (x : Master → ℝ) : Integer.Sparse.eval numericRow1764 x =
    (1 : ℝ) * reducedSource1764 x := by
  norm_num [numericRow1764, reducedSource1764, Integer.Sparse.eval, Sparse.eval, nodeValue1941, nodeValue3351, nodeValue3476, nodeValue3482, nodeValue4082]

theorem reindexCheck1765 : Integer.Sparse.reindex keyMap MixedData.row1765 = numericRow1765 := by decide +kernel

theorem numericCheck1765 (x : Master → ℝ) : Integer.Sparse.eval numericRow1765 x =
    (1 : ℝ) * reducedSource1765 x := by
  norm_num [numericRow1765, reducedSource1765, Integer.Sparse.eval, Sparse.eval, nodeValue1921, nodeValue2668, nodeValue3345, nodeValue3476, nodeValue3478, nodeValue4082]

theorem reindexCheck1766 : Integer.Sparse.reindex keyMap MixedData.row1766 = numericRow1766 := by decide +kernel

theorem numericCheck1766 (x : Master → ℝ) : Integer.Sparse.eval numericRow1766 x =
    (1 : ℝ) * reducedSource1766 x := by
  norm_num [numericRow1766, reducedSource1766, Integer.Sparse.eval, Sparse.eval, nodeValue1807, nodeValue2427, nodeValue2435, nodeValue2522, nodeValue2560, nodeValue3391, nodeValue4084]

theorem reindexCheck1767 : Integer.Sparse.reindex keyMap MixedData.row1767 = numericRow1767 := by decide +kernel

theorem numericCheck1767 (x : Master → ℝ) : Integer.Sparse.eval numericRow1767 x =
    (1 : ℝ) * reducedSource1767 x := by
  norm_num [numericRow1767, reducedSource1767, Integer.Sparse.eval, Sparse.eval, nodeValue1347, nodeValue2831, nodeValue2902, nodeValue2942, nodeValue2954, nodeValue2964, nodeValue4091]

theorem reindexCheck1768 : Integer.Sparse.reindex keyMap MixedData.row1768 = numericRow1768 := by decide +kernel

theorem numericCheck1768 (x : Master → ℝ) : Integer.Sparse.eval numericRow1768 x =
    (1 : ℝ) * reducedSource1768 x := by
  norm_num [numericRow1768, reducedSource1768, Integer.Sparse.eval, Sparse.eval, nodeValue2584, nodeValue2668, nodeValue2670, nodeValue2674, nodeValue2681, nodeValue3478, nodeValue4082]

theorem reindexCheck1769 : Integer.Sparse.reindex keyMap MixedData.row1769 = numericRow1769 := by decide +kernel

theorem numericCheck1769 (x : Master → ℝ) : Integer.Sparse.eval numericRow1769 x =
    (1 : ℝ) * reducedSource1769 x := by
  norm_num [numericRow1769, reducedSource1769, Integer.Sparse.eval, Sparse.eval, nodeValue2670, nodeValue3478, nodeValue3516, nodeValue3522, nodeValue3538, nodeValue3614, nodeValue4082]

theorem reindexCheck1770 : Integer.Sparse.reindex keyMap MixedData.row1770 = numericRow1770 := by decide +kernel

theorem numericCheck1770 (x : Master → ℝ) : Integer.Sparse.eval numericRow1770 x =
    (1 : ℝ) * reducedSource1770 x := by
  norm_num [numericRow1770, reducedSource1770, Integer.Sparse.eval, Sparse.eval, nodeValue2347, nodeValue2423, nodeValue2431, nodeValue2488, nodeValue2545, nodeValue3719, nodeValue4092]

theorem reindexCheck1771 : Integer.Sparse.reindex keyMap MixedData.row1771 = numericRow1771 := by decide +kernel

theorem numericCheck1771 (x : Master → ℝ) : Integer.Sparse.eval numericRow1771 x =
    (1 : ℝ) * reducedSource1771 x := by
  norm_num [numericRow1771, reducedSource1771, Integer.Sparse.eval, Sparse.eval, nodeValue1151, nodeValue2350, nodeValue2431, nodeValue2545, nodeValue2553, nodeValue2557, nodeValue4092]

theorem reindexCheck1772 : Integer.Sparse.reindex keyMap MixedData.row1772 = numericRow1772 := by decide +kernel

theorem numericCheck1772 (x : Master → ℝ) : Integer.Sparse.eval numericRow1772 x =
    (1 : ℝ) * reducedSource1772 x := by
  norm_num [numericRow1772, reducedSource1772, Integer.Sparse.eval, Sparse.eval, nodeValue1330, nodeValue2824, nodeValue2896, nodeValue2916, nodeValue2924, nodeValue2928, nodeValue4091]

theorem reindexCheck1773 : Integer.Sparse.reindex keyMap MixedData.row1773 = numericRow1773 := by decide +kernel

theorem numericCheck1773 (x : Master → ℝ) : Integer.Sparse.eval numericRow1773 x =
    (1 : ℝ) * reducedSource1773 x := by
  norm_num [numericRow1773, reducedSource1773, Integer.Sparse.eval, Sparse.eval, nodeValue2349, nodeValue2890, nodeValue2896, nodeValue2916, nodeValue3721, nodeValue4091]

theorem reindexCheck1774 : Integer.Sparse.reindex keyMap MixedData.row1774 = numericRow1774 := by decide +kernel

theorem numericCheck1774 (x : Master → ℝ) : Integer.Sparse.eval numericRow1774 x =
    (1 : ℝ) * reducedSource1774 x := by
  norm_num [numericRow1774, reducedSource1774, Integer.Sparse.eval, Sparse.eval, nodeValue2534, nodeValue3430, nodeValue3433, nodeValue3478, nodeValue3516, nodeValue4082]

theorem reindexCheck1775 : Integer.Sparse.reindex keyMap MixedData.row1775 = numericRow1775 := by decide +kernel

theorem numericCheck1775 (x : Master → ℝ) : Integer.Sparse.eval numericRow1775 x =
    (1 : ℝ) * reducedSource1775 x := by
  norm_num [numericRow1775, reducedSource1775, Integer.Sparse.eval, Sparse.eval, nodeValue2422, nodeValue2432, nodeValue2489, nodeValue2546, nodeValue3779, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows110
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1760 (mixedVector B) = 0 := by
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3612 : mixedVector B (Sum.inr 3612) = Sparse.eval nodeValue3612 (mixedVector B) := by
    change mixedMoment B node3612 node3612Labels = _
    exact sound3612 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2108, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3476, h3478, h3480, h3482, h3522, h3612, h4082, reducedSource1760] using sourceEq2108 B hB

theorem rowSound1760 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1760 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1760, numericCheck1760, reducedZero1760 B hB hF, mul_zero]

theorem reducedZero1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1761 (mixedVector B) = 0 := by
  have h1928 : mixedVector B (Sum.inr 1928) = Sparse.eval nodeValue1928 (mixedVector B) := by
    change mixedMoment B node1928 node1928Labels = _
    exact sound1928 B hB hF
  have h2674 : mixedVector B (Sum.inr 2674) = Sparse.eval nodeValue2674 (mixedVector B) := by
    change mixedMoment B node2674 node2674Labels = _
    exact sound2674 B hB hF
  have h3348 : mixedVector B (Sum.inr 3348) = Sparse.eval nodeValue3348 (mixedVector B) := by
    change mixedMoment B node3348 node3348Labels = _
    exact sound3348 B hB hF
  have h3430 : mixedVector B (Sum.inr 3430) = Sparse.eval nodeValue3430 (mixedVector B) := by
    change mixedMoment B node3430 node3430Labels = _
    exact sound3430 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3480 : mixedVector B (Sum.inr 3480) = Sparse.eval nodeValue3480 (mixedVector B) := by
    change mixedMoment B node3480 node3480Labels = _
    exact sound3480 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2110, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1928, h2674, h3348, h3430, h3478, h3480, h4082, reducedSource1761] using sourceEq2110 B hB

theorem rowSound1761 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1761 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1761, numericCheck1761, reducedZero1761 B hB hF, mul_zero]

theorem reducedZero1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1762 (mixedVector B) = 0 := by
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h2324 : mixedVector B (Sum.inr 2324) = Sparse.eval nodeValue2324 (mixedVector B) := by
    change mixedMoment B node2324 node2324Labels = _
    exact sound2324 B hB hF
  have h2441 : mixedVector B (Sum.inr 2441) = Sparse.eval nodeValue2441 (mixedVector B) := by
    change mixedMoment B node2441 node2441Labels = _
    exact sound2441 B hB hF
  have h2473 : mixedVector B (Sum.inr 2473) = Sparse.eval nodeValue2473 (mixedVector B) := by
    change mixedMoment B node2473 node2473Labels = _
    exact sound2473 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2111, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1117, h2324, h2441, h2473, h2480, h2483, h4091, reducedSource1762] using sourceEq2111 B hB

theorem rowSound1762 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1762 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1762, numericCheck1762, reducedZero1762 B hB hF, mul_zero]

theorem reducedZero1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1763 (mixedVector B) = 0 := by
  have h2320 : mixedVector B (Sum.inr 2320) = Sparse.eval nodeValue2320 (mixedVector B) := by
    change mixedMoment B node2320 node2320Labels = _
    exact sound2320 B hB hF
  have h2797 : mixedVector B (Sum.inr 2797) = Sparse.eval nodeValue2797 (mixedVector B) := by
    change mixedMoment B node2797 node2797Labels = _
    exact sound2797 B hB hF
  have h2900 : mixedVector B (Sum.inr 2900) = Sparse.eval nodeValue2900 (mixedVector B) := by
    change mixedMoment B node2900 node2900Labels = _
    exact sound2900 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h3690 : mixedVector B (Sum.inr 3690) = Sparse.eval nodeValue3690 (mixedVector B) := by
    change mixedMoment B node3690 node3690Labels = _
    exact sound3690 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2112, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2320, h2797, h2900, h2931, h2981, h3690, h4091, reducedSource1763] using sourceEq2112 B hB

theorem rowSound1763 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1763 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1763, numericCheck1763, reducedZero1763 B hB hF, mul_zero]

theorem reducedZero1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1764 (mixedVector B) = 0 := by
  have h1941 : mixedVector B (Sum.inr 1941) = Sparse.eval nodeValue1941 (mixedVector B) := by
    change mixedMoment B node1941 node1941Labels = _
    exact sound1941 B hB hF
  have h3351 : mixedVector B (Sum.inr 3351) = Sparse.eval nodeValue3351 (mixedVector B) := by
    change mixedMoment B node3351 node3351Labels = _
    exact sound3351 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3482 : mixedVector B (Sum.inr 3482) = Sparse.eval nodeValue3482 (mixedVector B) := by
    change mixedMoment B node3482 node3482Labels = _
    exact sound3482 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2114, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1941, h3351, h3476, h3482, h4082, reducedSource1764] using sourceEq2114 B hB

theorem rowSound1764 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1764 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1764, numericCheck1764, reducedZero1764 B hB hF, mul_zero]

theorem reducedZero1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1765 (mixedVector B) = 0 := by
  have h1921 : mixedVector B (Sum.inr 1921) = Sparse.eval nodeValue1921 (mixedVector B) := by
    change mixedMoment B node1921 node1921Labels = _
    exact sound1921 B hB hF
  have h2668 : mixedVector B (Sum.inr 2668) = Sparse.eval nodeValue2668 (mixedVector B) := by
    change mixedMoment B node2668 node2668Labels = _
    exact sound2668 B hB hF
  have h3345 : mixedVector B (Sum.inr 3345) = Sparse.eval nodeValue3345 (mixedVector B) := by
    change mixedMoment B node3345 node3345Labels = _
    exact sound3345 B hB hF
  have h3476 : mixedVector B (Sum.inr 3476) = Sparse.eval nodeValue3476 (mixedVector B) := by
    change mixedMoment B node3476 node3476Labels = _
    exact sound3476 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2115, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1921, h2668, h3345, h3476, h3478, h4082, reducedSource1765] using sourceEq2115 B hB

theorem rowSound1765 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1765 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1765, numericCheck1765, reducedZero1765 B hB hF, mul_zero]

theorem reducedZero1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1766 (mixedVector B) = 0 := by
  have h1807 : mixedVector B (Sum.inr 1807) = Sparse.eval nodeValue1807 (mixedVector B) := by
    change mixedMoment B node1807 node1807Labels = _
    exact sound1807 B hB hF
  have h2427 : mixedVector B (Sum.inr 2427) = Sparse.eval nodeValue2427 (mixedVector B) := by
    change mixedMoment B node2427 node2427Labels = _
    exact sound2427 B hB hF
  have h2435 : mixedVector B (Sum.inr 2435) = Sparse.eval nodeValue2435 (mixedVector B) := by
    change mixedMoment B node2435 node2435Labels = _
    exact sound2435 B hB hF
  have h2522 : mixedVector B (Sum.inr 2522) = Sparse.eval nodeValue2522 (mixedVector B) := by
    change mixedMoment B node2522 node2522Labels = _
    exact sound2522 B hB hF
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm2118, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1807, h2427, h2435, h2522, h2560, h3391, h4084, reducedSource1766] using sourceEq2118 B hB

theorem rowSound1766 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1766 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1766, numericCheck1766, reducedZero1766 B hB hF, mul_zero]

theorem reducedZero1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1767 (mixedVector B) = 0 := by
  have h1347 : mixedVector B (Sum.inr 1347) = Sparse.eval nodeValue1347 (mixedVector B) := by
    change mixedMoment B node1347 node1347Labels = _
    exact sound1347 B hB hF
  have h2831 : mixedVector B (Sum.inr 2831) = Sparse.eval nodeValue2831 (mixedVector B) := by
    change mixedMoment B node2831 node2831Labels = _
    exact sound2831 B hB hF
  have h2902 : mixedVector B (Sum.inr 2902) = Sparse.eval nodeValue2902 (mixedVector B) := by
    change mixedMoment B node2902 node2902Labels = _
    exact sound2902 B hB hF
  have h2942 : mixedVector B (Sum.inr 2942) = Sparse.eval nodeValue2942 (mixedVector B) := by
    change mixedMoment B node2942 node2942Labels = _
    exact sound2942 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h2964 : mixedVector B (Sum.inr 2964) = Sparse.eval nodeValue2964 (mixedVector B) := by
    change mixedMoment B node2964 node2964Labels = _
    exact sound2964 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2119, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1347, h2831, h2902, h2942, h2954, h2964, h4091, reducedSource1767] using sourceEq2119 B hB

theorem rowSound1767 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1767 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1767, numericCheck1767, reducedZero1767 B hB hF, mul_zero]

theorem reducedZero1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1768 (mixedVector B) = 0 := by
  have h2584 : mixedVector B (Sum.inr 2584) = Sparse.eval nodeValue2584 (mixedVector B) := by
    change mixedMoment B node2584 node2584Labels = _
    exact sound2584 B hB hF
  have h2668 : mixedVector B (Sum.inr 2668) = Sparse.eval nodeValue2668 (mixedVector B) := by
    change mixedMoment B node2668 node2668Labels = _
    exact sound2668 B hB hF
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h2674 : mixedVector B (Sum.inr 2674) = Sparse.eval nodeValue2674 (mixedVector B) := by
    change mixedMoment B node2674 node2674Labels = _
    exact sound2674 B hB hF
  have h2681 : mixedVector B (Sum.inr 2681) = Sparse.eval nodeValue2681 (mixedVector B) := by
    change mixedMoment B node2681 node2681Labels = _
    exact sound2681 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2120, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2584, h2668, h2670, h2674, h2681, h3478, h4082, reducedSource1768] using sourceEq2120 B hB

theorem rowSound1768 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1768 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1768, numericCheck1768, reducedZero1768 B hB hF, mul_zero]

theorem reducedZero1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1769 (mixedVector B) = 0 := by
  have h2670 : mixedVector B (Sum.inr 2670) = Sparse.eval nodeValue2670 (mixedVector B) := by
    change mixedMoment B node2670 node2670Labels = _
    exact sound2670 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h3522 : mixedVector B (Sum.inr 3522) = Sparse.eval nodeValue3522 (mixedVector B) := by
    change mixedMoment B node3522 node3522Labels = _
    exact sound3522 B hB hF
  have h3538 : mixedVector B (Sum.inr 3538) = Sparse.eval nodeValue3538 (mixedVector B) := by
    change mixedMoment B node3538 node3538Labels = _
    exact sound3538 B hB hF
  have h3614 : mixedVector B (Sum.inr 3614) = Sparse.eval nodeValue3614 (mixedVector B) := by
    change mixedMoment B node3614 node3614Labels = _
    exact sound3614 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2121, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2670, h3478, h3516, h3522, h3538, h3614, h4082, reducedSource1769] using sourceEq2121 B hB

theorem rowSound1769 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1769 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1769, numericCheck1769, reducedZero1769 B hB hF, mul_zero]

theorem reducedZero1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1770 (mixedVector B) = 0 := by
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2423 : mixedVector B (Sum.inr 2423) = Sparse.eval nodeValue2423 (mixedVector B) := by
    change mixedMoment B node2423 node2423Labels = _
    exact sound2423 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h3719 : mixedVector B (Sum.inr 3719) = Sparse.eval nodeValue3719 (mixedVector B) := by
    change mixedMoment B node3719 node3719Labels = _
    exact sound3719 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2122, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2347, h2423, h2431, h2488, h2545, h3719, h4092, reducedSource1770] using sourceEq2122 B hB

theorem rowSound1770 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1770 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1770, numericCheck1770, reducedZero1770 B hB hF, mul_zero]

theorem reducedZero1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1771 (mixedVector B) = 0 := by
  have h1151 : mixedVector B (Sum.inr 1151) = Sparse.eval nodeValue1151 (mixedVector B) := by
    change mixedMoment B node1151 node1151Labels = _
    exact sound1151 B hB hF
  have h2350 : mixedVector B (Sum.inr 2350) = Sparse.eval nodeValue2350 (mixedVector B) := by
    change mixedMoment B node2350 node2350Labels = _
    exact sound2350 B hB hF
  have h2431 : mixedVector B (Sum.inr 2431) = Sparse.eval nodeValue2431 (mixedVector B) := by
    change mixedMoment B node2431 node2431Labels = _
    exact sound2431 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm2123, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1151, h2350, h2431, h2545, h2553, h2557, h4092, reducedSource1771] using sourceEq2123 B hB

theorem rowSound1771 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1771 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1771, numericCheck1771, reducedZero1771 B hB hF, mul_zero]

theorem reducedZero1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1772 (mixedVector B) = 0 := by
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h2824 : mixedVector B (Sum.inr 2824) = Sparse.eval nodeValue2824 (mixedVector B) := by
    change mixedMoment B node2824 node2824Labels = _
    exact sound2824 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h2928 : mixedVector B (Sum.inr 2928) = Sparse.eval nodeValue2928 (mixedVector B) := by
    change mixedMoment B node2928 node2928Labels = _
    exact sound2928 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2124, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1330, h2824, h2896, h2916, h2924, h2928, h4091, reducedSource1772] using sourceEq2124 B hB

theorem rowSound1772 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1772 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1772, numericCheck1772, reducedZero1772 B hB hF, mul_zero]

theorem reducedZero1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1773 (mixedVector B) = 0 := by
  have h2349 : mixedVector B (Sum.inr 2349) = Sparse.eval nodeValue2349 (mixedVector B) := by
    change mixedMoment B node2349 node2349Labels = _
    exact sound2349 B hB hF
  have h2890 : mixedVector B (Sum.inr 2890) = Sparse.eval nodeValue2890 (mixedVector B) := by
    change mixedMoment B node2890 node2890Labels = _
    exact sound2890 B hB hF
  have h2896 : mixedVector B (Sum.inr 2896) = Sparse.eval nodeValue2896 (mixedVector B) := by
    change mixedMoment B node2896 node2896Labels = _
    exact sound2896 B hB hF
  have h2916 : mixedVector B (Sum.inr 2916) = Sparse.eval nodeValue2916 (mixedVector B) := by
    change mixedMoment B node2916 node2916Labels = _
    exact sound2916 B hB hF
  have h3721 : mixedVector B (Sum.inr 3721) = Sparse.eval nodeValue3721 (mixedVector B) := by
    change mixedMoment B node3721 node3721Labels = _
    exact sound3721 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2125, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2349, h2890, h2896, h2916, h3721, h4091, reducedSource1773] using sourceEq2125 B hB

theorem rowSound1773 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1773 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1773, numericCheck1773, reducedZero1773 B hB hF, mul_zero]

theorem reducedZero1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1774 (mixedVector B) = 0 := by
  have h2534 : mixedVector B (Sum.inr 2534) = Sparse.eval nodeValue2534 (mixedVector B) := by
    change mixedMoment B node2534 node2534Labels = _
    exact sound2534 B hB hF
  have h3430 : mixedVector B (Sum.inr 3430) = Sparse.eval nodeValue3430 (mixedVector B) := by
    change mixedMoment B node3430 node3430Labels = _
    exact sound3430 B hB hF
  have h3433 : mixedVector B (Sum.inr 3433) = Sparse.eval nodeValue3433 (mixedVector B) := by
    change mixedMoment B node3433 node3433Labels = _
    exact sound3433 B hB hF
  have h3478 : mixedVector B (Sum.inr 3478) = Sparse.eval nodeValue3478 (mixedVector B) := by
    change mixedMoment B node3478 node3478Labels = _
    exact sound3478 B hB hF
  have h3516 : mixedVector B (Sum.inr 3516) = Sparse.eval nodeValue3516 (mixedVector B) := by
    change mixedMoment B node3516 node3516Labels = _
    exact sound3516 B hB hF
  have h4082 : mixedVector B (Sum.inr 4082) = Sparse.eval nodeValue4082 (mixedVector B) := by
    change mixedMoment B node4082 node4082Labels = _
    exact sound4082 B hB hF
  simpa only [sourceForm2126, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2534, h3430, h3433, h3478, h3516, h4082, reducedSource1774] using sourceEq2126 B hB

theorem rowSound1774 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1774 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1774, numericCheck1774, reducedZero1774 B hB hF, mul_zero]

theorem reducedZero1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1775 (mixedVector B) = 0 := by
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2432 : mixedVector B (Sum.inr 2432) = Sparse.eval nodeValue2432 (mixedVector B) := by
    change mixedMoment B node2432 node2432Labels = _
    exact sound2432 B hB hF
  have h2489 : mixedVector B (Sum.inr 2489) = Sparse.eval nodeValue2489 (mixedVector B) := by
    change mixedMoment B node2489 node2489Labels = _
    exact sound2489 B hB hF
  have h2546 : mixedVector B (Sum.inr 2546) = Sparse.eval nodeValue2546 (mixedVector B) := by
    change mixedMoment B node2546 node2546Labels = _
    exact sound2546 B hB hF
  have h3779 : mixedVector B (Sum.inr 3779) = Sparse.eval nodeValue3779 (mixedVector B) := by
    change mixedMoment B node3779 node3779Labels = _
    exact sound3779 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm2129, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2422, h2432, h2489, h2546, h3779, h4091, reducedSource1775] using sourceEq2129 B hB

theorem rowSound1775 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1775 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1775, numericCheck1775, reducedZero1775 B hB hF, mul_zero]

theorem sourceRowsAt1760 : MixedData.sourceRows (1760 : Fin 2425) =
    MixedData.row1760 := by decide +kernel

theorem sourceRowsAt1761 : MixedData.sourceRows (1761 : Fin 2425) =
    MixedData.row1761 := by decide +kernel

theorem sourceRowsAt1762 : MixedData.sourceRows (1762 : Fin 2425) =
    MixedData.row1762 := by decide +kernel

theorem sourceRowsAt1763 : MixedData.sourceRows (1763 : Fin 2425) =
    MixedData.row1763 := by decide +kernel

theorem sourceRowsAt1764 : MixedData.sourceRows (1764 : Fin 2425) =
    MixedData.row1764 := by decide +kernel

theorem sourceRowsAt1765 : MixedData.sourceRows (1765 : Fin 2425) =
    MixedData.row1765 := by decide +kernel

theorem sourceRowsAt1766 : MixedData.sourceRows (1766 : Fin 2425) =
    MixedData.row1766 := by decide +kernel

theorem sourceRowsAt1767 : MixedData.sourceRows (1767 : Fin 2425) =
    MixedData.row1767 := by decide +kernel

theorem sourceRowsAt1768 : MixedData.sourceRows (1768 : Fin 2425) =
    MixedData.row1768 := by decide +kernel

theorem sourceRowsAt1769 : MixedData.sourceRows (1769 : Fin 2425) =
    MixedData.row1769 := by decide +kernel

theorem sourceRowsAt1770 : MixedData.sourceRows (1770 : Fin 2425) =
    MixedData.row1770 := by decide +kernel

theorem sourceRowsAt1771 : MixedData.sourceRows (1771 : Fin 2425) =
    MixedData.row1771 := by decide +kernel

theorem sourceRowsAt1772 : MixedData.sourceRows (1772 : Fin 2425) =
    MixedData.row1772 := by decide +kernel

theorem sourceRowsAt1773 : MixedData.sourceRows (1773 : Fin 2425) =
    MixedData.row1773 := by decide +kernel

theorem sourceRowsAt1774 : MixedData.sourceRows (1774 : Fin 2425) =
    MixedData.row1774 := by decide +kernel

theorem sourceRowsAt1775 : MixedData.sourceRows (1775 : Fin 2425) =
    MixedData.row1775 := by decide +kernel

theorem chunkSound110_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 110) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1760 ∨ k.val = 1761 ∨ k.val = 1762 ∨ k.val = 1763 ∨ k.val = 1764 ∨ k.val = 1765 ∨ k.val = 1766 ∨ k.val = 1767 ∨ k.val = 1768 ∨ k.val = 1769 ∨ k.val = 1770 ∨ k.val = 1771 ∨ k.val = 1772 ∨ k.val = 1773 ∨ k.val = 1774 ∨ k.val = 1775 := by omega
  rcases heq with h1760 | h1761 | h1762 | h1763 | h1764 | h1765 | h1766 | h1767 | h1768 | h1769 | h1770 | h1771 | h1772 | h1773 | h1774 | h1775
  · have he : k = (1760 : Fin 2425) := Fin.ext h1760
    subst k
    rw [sourceRowsAt1760]
    exact rowSound1760 B hB hF
  · have he : k = (1761 : Fin 2425) := Fin.ext h1761
    subst k
    rw [sourceRowsAt1761]
    exact rowSound1761 B hB hF
  · have he : k = (1762 : Fin 2425) := Fin.ext h1762
    subst k
    rw [sourceRowsAt1762]
    exact rowSound1762 B hB hF
  · have he : k = (1763 : Fin 2425) := Fin.ext h1763
    subst k
    rw [sourceRowsAt1763]
    exact rowSound1763 B hB hF
  · have he : k = (1764 : Fin 2425) := Fin.ext h1764
    subst k
    rw [sourceRowsAt1764]
    exact rowSound1764 B hB hF
  · have he : k = (1765 : Fin 2425) := Fin.ext h1765
    subst k
    rw [sourceRowsAt1765]
    exact rowSound1765 B hB hF
  · have he : k = (1766 : Fin 2425) := Fin.ext h1766
    subst k
    rw [sourceRowsAt1766]
    exact rowSound1766 B hB hF
  · have he : k = (1767 : Fin 2425) := Fin.ext h1767
    subst k
    rw [sourceRowsAt1767]
    exact rowSound1767 B hB hF
  · have he : k = (1768 : Fin 2425) := Fin.ext h1768
    subst k
    rw [sourceRowsAt1768]
    exact rowSound1768 B hB hF
  · have he : k = (1769 : Fin 2425) := Fin.ext h1769
    subst k
    rw [sourceRowsAt1769]
    exact rowSound1769 B hB hF
  · have he : k = (1770 : Fin 2425) := Fin.ext h1770
    subst k
    rw [sourceRowsAt1770]
    exact rowSound1770 B hB hF
  · have he : k = (1771 : Fin 2425) := Fin.ext h1771
    subst k
    rw [sourceRowsAt1771]
    exact rowSound1771 B hB hF
  · have he : k = (1772 : Fin 2425) := Fin.ext h1772
    subst k
    rw [sourceRowsAt1772]
    exact rowSound1772 B hB hF
  · have he : k = (1773 : Fin 2425) := Fin.ext h1773
    subst k
    rw [sourceRowsAt1773]
    exact rowSound1773 B hB hF
  · have he : k = (1774 : Fin 2425) := Fin.ext h1774
    subst k
    rw [sourceRowsAt1774]
    exact rowSound1774 B hB hF
  · have he : k = (1775 : Fin 2425) := Fin.ext h1775
    subst k
    rw [sourceRowsAt1775]
    exact rowSound1775 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound110_e_oai
