-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:02:35.2955+00:00
-- url     : https://prove2.me/submissions/62fcaf0c-b87d-4c4f-ae8a-941e5d4b30bc

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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound296_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound301_e

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

theorem canonical6789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6789 raw6789Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw6789 raw6789Labels = mixedMoment B raw6789step0 raw6789step0Labels := by
      have hz : ∀ j, raw6789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6789step0 = (fun i j => raw6789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6789step0 raw6789; decide +kernel
      have hl : raw6789step0Labels = raw6789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6789 raw6789Labels permutation346 hz
    mixedMoment B raw6789step0 raw6789step0Labels = mixedMoment B raw6789step1 raw6789step1Labels := by
      have ha : raw6789step1 = (fun i j => raw6789step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6789step1 raw6789step0; decide +kernel
      have hl : raw6789step1Labels = raw6789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6789step0 raw6789step0Labels permutation38 permutation2
    mixedMoment B raw6789step1 raw6789step1Labels = mixedMoment B raw6789step2 raw6789step2Labels := by
      have ha : raw6789step2 = -raw6789step1 := by apply Matrix.ext; change ∀ i j, raw6789step2 i j = -(raw6789step1 i j); unfold raw6789step2 raw6789step1; decide +kernel
      have hl : raw6789step2Labels = raw6789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

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

theorem canonical7021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7021 raw7021Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw7021 raw7021Labels = mixedMoment B raw7021step0 raw7021step0Labels := by
      have hz : ∀ j, raw7021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7021step0 = (fun i j => raw7021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7021step0 raw7021; decide +kernel
      have hl : raw7021step0Labels = raw7021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7021 raw7021Labels permutation346 hz
    mixedMoment B raw7021step0 raw7021step0Labels = mixedMoment B raw7021step1 raw7021step1Labels := by
      have ha : raw7021step1 = (fun i j => raw7021step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7021step1 raw7021step0; decide +kernel
      have hl : raw7021step1Labels = raw7021step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7021step0 raw7021step0Labels permutation38 permutation2
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical7022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7022 raw7022Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw7022 raw7022Labels = mixedMoment B raw7022step0 raw7022step0Labels := by
      have hz : ∀ j, raw7022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7022step0 = (fun i j => raw7022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7022step0 raw7022; decide +kernel
      have hl : raw7022step0Labels = raw7022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7022 raw7022Labels permutation346 hz
    mixedMoment B raw7022step0 raw7022step0Labels = mixedMoment B raw7022step1 raw7022step1Labels := by
      have ha : raw7022step1 = (fun i j => raw7022step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7022step1 raw7022step0; decide +kernel
      have hl : raw7022step1Labels = raw7022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7022step0 raw7022step0Labels permutation151 permutation2
    mixedMoment B raw7022step1 raw7022step1Labels = mixedMoment B raw7022step2 raw7022step2Labels := by
      have ha : raw7022step2 = -raw7022step1 := by apply Matrix.ext; change ∀ i j, raw7022step2 i j = -(raw7022step1 i j); unfold raw7022step2 raw7022step1; decide +kernel
      have hl : raw7022step2Labels = raw7022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical7023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7023 raw7023Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw7023 raw7023Labels = mixedMoment B raw7023step0 raw7023step0Labels := by
      have ha : raw7023step0 = (fun i j => raw7023 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7023step0 raw7023; decide +kernel
      have hl : raw7023step0Labels = raw7023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7023 raw7023Labels permutation676 permutation2
    mixedMoment B raw7023step0 raw7023step0Labels = mixedMoment B raw7023step1 raw7023step1Labels := by
      have ha : raw7023step1 = -raw7023step0 := by apply Matrix.ext; change ∀ i j, raw7023step1 i j = -(raw7023step0 i j); unfold raw7023step1 raw7023step0; decide +kernel
      have hl : raw7023step1Labels = raw7023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

theorem canonical7024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7024 raw7024Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw7024 raw7024Labels = mixedMoment B raw7024step0 raw7024step0Labels := by
      have hz : ∀ j, raw7024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7024step0 = (fun i j => raw7024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7024step0 raw7024; decide +kernel
      have hl : raw7024step0Labels = raw7024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7024 raw7024Labels permutation346 hz
    mixedMoment B raw7024step0 raw7024step0Labels = mixedMoment B raw7024step1 raw7024step1Labels := by
      have ha : raw7024step1 = (fun i j => raw7024step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7024step1 raw7024step0; decide +kernel
      have hl : raw7024step1Labels = raw7024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7024step0 raw7024step0Labels permutation149 permutation2
    mixedMoment B raw7024step1 raw7024step1Labels = mixedMoment B raw7024step2 raw7024step2Labels := by
      have ha : raw7024step2 = -raw7024step1 := by apply Matrix.ext; change ∀ i j, raw7024step2 i j = -(raw7024step1 i j); unfold raw7024step2 raw7024step1; decide +kernel
      have hl : raw7024step2Labels = raw7024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical7025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7025 raw7025Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw7025 raw7025Labels = mixedMoment B raw7025step0 raw7025step0Labels := by
      have hz : ∀ j, raw7025 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7025step0 = (fun i j => raw7025 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7025step0 raw7025; decide +kernel
      have hl : raw7025step0Labels = raw7025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7025 raw7025Labels permutation520 hz
    mixedMoment B raw7025step0 raw7025step0Labels = mixedMoment B raw7025step1 raw7025step1Labels := by
      have hz : ∀ j, raw7025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7025step1 = (fun i j => raw7025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7025step1 raw7025step0; decide +kernel
      have hl : raw7025step1Labels = raw7025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7025step0 raw7025step0Labels permutation80 hz
    mixedMoment B raw7025step1 raw7025step1Labels = mixedMoment B raw7025step2 raw7025step2Labels := by
      have ha : raw7025step2 = (fun i j => raw7025step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7025step2 raw7025step1; decide +kernel
      have hl : raw7025step2Labels = raw7025step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7025step1 raw7025step1Labels permutation29 permutation2
    mixedMoment B raw7025step2 raw7025step2Labels = mixedMoment B raw7025step3 raw7025step3Labels := by
      have ha : raw7025step3 = -raw7025step2 := by apply Matrix.ext; change ∀ i j, raw7025step3 i j = -(raw7025step2 i j); unfold raw7025step3 raw7025step2; decide +kernel
      have hl : raw7025step3Labels = raw7025step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical7026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7026 raw7026Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw7026 raw7026Labels = mixedMoment B raw7026step0 raw7026step0Labels := by
      have hz : ∀ j, raw7026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7026step0 = (fun i j => raw7026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7026step0 raw7026; decide +kernel
      have hl : raw7026step0Labels = raw7026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7026 raw7026Labels permutation346 hz
    mixedMoment B raw7026step0 raw7026step0Labels = mixedMoment B raw7026step1 raw7026step1Labels := by
      have ha : raw7026step1 = (fun i j => raw7026step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7026step1 raw7026step0; decide +kernel
      have hl : raw7026step1Labels = raw7026step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7026step0 raw7026step0Labels permutation92 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical7027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7027 raw7027Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw7027 raw7027Labels = mixedMoment B raw7027step0 raw7027step0Labels := by
      have hz : ∀ j, raw7027 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7027step0 = (fun i j => raw7027 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7027step0 raw7027; decide +kernel
      have hl : raw7027step0Labels = raw7027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7027 raw7027Labels permutation520 hz
    mixedMoment B raw7027step0 raw7027step0Labels = mixedMoment B raw7027step1 raw7027step1Labels := by
      have hz : ∀ j, raw7027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7027step1 = (fun i j => raw7027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7027step1 raw7027step0; decide +kernel
      have hl : raw7027step1Labels = raw7027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7027step0 raw7027step0Labels permutation80 hz
    mixedMoment B raw7027step1 raw7027step1Labels = mixedMoment B raw7027step2 raw7027step2Labels := by
      have ha : raw7027step2 = (fun i j => raw7027step1 (permutation20 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7027step2 raw7027step1; decide +kernel
      have hl : raw7027step2Labels = raw7027step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7027step1 raw7027step1Labels permutation20 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical7028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7028 raw7028Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw7028 raw7028Labels = mixedMoment B raw7028step0 raw7028step0Labels := by
      have hz : ∀ j, raw7028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7028step0 = (fun i j => raw7028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7028step0 raw7028; decide +kernel
      have hl : raw7028step0Labels = raw7028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7028 raw7028Labels permutation346 hz
    mixedMoment B raw7028step0 raw7028step0Labels = mixedMoment B raw7028step1 raw7028step1Labels := by
      have ha : raw7028step1 = (fun i j => raw7028step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7028step1 raw7028step0; decide +kernel
      have hl : raw7028step1Labels = raw7028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7028step0 raw7028step0Labels permutation40 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

theorem canonical7029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7029 raw7029Labels = mixedMoment B node1357 node1357Labels := by
  calc
    mixedMoment B raw7029 raw7029Labels = mixedMoment B raw7029step0 raw7029step0Labels := by
      have ha : raw7029step0 = (fun i j => raw7029 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7029step0 raw7029; decide +kernel
      have hl : raw7029step0Labels = raw7029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7029 raw7029Labels permutation200 permutation2
    _ = mixedMoment B node1357 node1357Labels := by rfl

theorem canonical7030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7030 raw7030Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw7030 raw7030Labels = mixedMoment B raw7030step0 raw7030step0Labels := by
      have hz : ∀ j, raw7030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7030step0 = (fun i j => raw7030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7030step0 raw7030; decide +kernel
      have hl : raw7030step0Labels = raw7030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7030 raw7030Labels permutation346 hz
    _ = mixedMoment B node1422 node1422Labels := by rfl

theorem canonical7031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7031 raw7031Labels = mixedMoment B node1362 node1362Labels := by
  calc
    mixedMoment B raw7031 raw7031Labels = mixedMoment B raw7031step0 raw7031step0Labels := by
      have hz : ∀ j, raw7031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7031step0 = (fun i j => raw7031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7031step0 raw7031; decide +kernel
      have hl : raw7031step0Labels = raw7031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7031 raw7031Labels permutation346 hz
    mixedMoment B raw7031step0 raw7031step0Labels = mixedMoment B raw7031step1 raw7031step1Labels := by
      have ha : raw7031step1 = (fun i j => raw7031step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7031step1 raw7031step0; decide +kernel
      have hl : raw7031step1Labels = raw7031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7031step0 raw7031step0Labels permutation38 permutation2
    _ = mixedMoment B node1362 node1362Labels := by rfl

theorem canonical7032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7032 raw7032Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw7032 raw7032Labels = mixedMoment B raw7032step0 raw7032step0Labels := by
      have hz : ∀ j, raw7032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7032step0 = (fun i j => raw7032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7032step0 raw7032; decide +kernel
      have hl : raw7032step0Labels = raw7032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7032 raw7032Labels permutation346 hz
    mixedMoment B raw7032step0 raw7032step0Labels = mixedMoment B raw7032step1 raw7032step1Labels := by
      have ha : raw7032step1 = (fun i j => raw7032step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7032step1 raw7032step0; decide +kernel
      have hl : raw7032step1Labels = raw7032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7032step0 raw7032step0Labels permutation38 permutation2
    _ = mixedMoment B node1359 node1359Labels := by rfl

theorem canonical7033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7033 raw7033Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw7033 raw7033Labels = mixedMoment B raw7033step0 raw7033step0Labels := by
      have ha : raw7033step0 = (fun i j => raw7033 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7033step0 raw7033; decide +kernel
      have hl : raw7033step0Labels = raw7033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7033 raw7033Labels permutation184 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

theorem canonical7034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7034 raw7034Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw7034 raw7034Labels = mixedMoment B raw7034step0 raw7034step0Labels := by
      have hz : ∀ j, raw7034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7034step0 = (fun i j => raw7034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7034step0 raw7034; decide +kernel
      have hl : raw7034step0Labels = raw7034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7034 raw7034Labels permutation346 hz
    mixedMoment B raw7034step0 raw7034step0Labels = mixedMoment B raw7034step1 raw7034step1Labels := by
      have ha : raw7034step1 = (fun i j => raw7034step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7034step1 raw7034step0; decide +kernel
      have hl : raw7034step1Labels = raw7034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7034step0 raw7034step0Labels permutation40 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical7035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7035 raw7035Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw7035 raw7035Labels = mixedMoment B raw7035step0 raw7035step0Labels := by
      have hz : ∀ j, raw7035 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7035step0 = (fun i j => raw7035 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7035step0 raw7035; decide +kernel
      have hl : raw7035step0Labels = raw7035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7035 raw7035Labels permutation520 hz
    mixedMoment B raw7035step0 raw7035step0Labels = mixedMoment B raw7035step1 raw7035step1Labels := by
      have hz : ∀ j, raw7035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7035step1 = (fun i j => raw7035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7035step1 raw7035step0; decide +kernel
      have hl : raw7035step1Labels = raw7035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7035step0 raw7035step0Labels permutation80 hz
    mixedMoment B raw7035step1 raw7035step1Labels = mixedMoment B raw7035step2 raw7035step2Labels := by
      have ha : raw7035step2 = (fun i j => raw7035step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7035step2 raw7035step1; decide +kernel
      have hl : raw7035step2Labels = raw7035step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7035step1 raw7035step1Labels permutation10 permutation2
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical7036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7036 raw7036Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw7036 raw7036Labels = mixedMoment B raw7036step0 raw7036step0Labels := by
      have hz : ∀ j, raw7036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7036step0 = (fun i j => raw7036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7036step0 raw7036; decide +kernel
      have hl : raw7036step0Labels = raw7036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7036 raw7036Labels permutation346 hz
    mixedMoment B raw7036step0 raw7036step0Labels = mixedMoment B raw7036step1 raw7036step1Labels := by
      have ha : raw7036step1 = (fun i j => raw7036step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7036step1 raw7036step0; decide +kernel
      have hl : raw7036step1Labels = raw7036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7036step0 raw7036step0Labels permutation40 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical7037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7037 raw7037Labels = mixedMoment B node3007 node3007Labels := by
  calc
    mixedMoment B raw7037 raw7037Labels = mixedMoment B raw7037step0 raw7037step0Labels := by
      have ha : raw7037step0 = (fun i j => raw7037 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7037step0 raw7037; decide +kernel
      have hl : raw7037step0Labels = raw7037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7037 raw7037Labels permutation158 permutation2
    _ = mixedMoment B node3007 node3007Labels := by rfl

theorem canonical7038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7038 raw7038Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw7038 raw7038Labels = mixedMoment B raw7038step0 raw7038step0Labels := by
      have hz : ∀ j, raw7038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7038step0 = (fun i j => raw7038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7038step0 raw7038; decide +kernel
      have hl : raw7038step0Labels = raw7038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7038 raw7038Labels permutation346 hz
    mixedMoment B raw7038step0 raw7038step0Labels = mixedMoment B raw7038step1 raw7038step1Labels := by
      have ha : raw7038step1 = (fun i j => raw7038step0 (permutation96 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7038step1 raw7038step0; decide +kernel
      have hl : raw7038step1Labels = raw7038step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7038step0 raw7038step0Labels permutation96 permutation4
    _ = mixedMoment B node2582 node2582Labels := by rfl

theorem canonical7039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7039 raw7039Labels = mixedMoment B node3010 node3010Labels := by
  calc
    mixedMoment B raw7039 raw7039Labels = mixedMoment B raw7039step0 raw7039step0Labels := by
      have hz : ∀ j, raw7039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7039step0 = (fun i j => raw7039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7039step0 raw7039; decide +kernel
      have hl : raw7039step0Labels = raw7039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7039 raw7039Labels permutation346 hz
    _ = mixedMoment B node3010 node3010Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical55
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7040 raw7040Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw7040 raw7040Labels = mixedMoment B raw7040step0 raw7040step0Labels := by
      have hz : ∀ j, raw7040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7040step0 = (fun i j => raw7040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7040step0 raw7040; decide +kernel
      have hl : raw7040step0Labels = raw7040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7040 raw7040Labels permutation346 hz
    mixedMoment B raw7040step0 raw7040step0Labels = mixedMoment B raw7040step1 raw7040step1Labels := by
      have ha : raw7040step1 = (fun i j => raw7040step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7040step1 raw7040step0; decide +kernel
      have hl : raw7040step1Labels = raw7040step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7040step0 raw7040step0Labels permutation151 permutation2
    mixedMoment B raw7040step1 raw7040step1Labels = mixedMoment B raw7040step2 raw7040step2Labels := by
      have ha : raw7040step2 = -raw7040step1 := by apply Matrix.ext; change ∀ i j, raw7040step2 i j = -(raw7040step1 i j); unfold raw7040step2 raw7040step1; decide +kernel
      have hl : raw7040step2Labels = raw7040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2579 node2579Labels := by rfl

theorem canonical7041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7041 raw7041Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw7041 raw7041Labels = mixedMoment B raw7041step0 raw7041step0Labels := by
      have ha : raw7041step0 = (fun i j => raw7041 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7041step0 raw7041; decide +kernel
      have hl : raw7041step0Labels = raw7041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7041 raw7041Labels permutation200 permutation2
    _ = mixedMoment B node2861 node2861Labels := by rfl

theorem canonical7042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7042 raw7042Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw7042 raw7042Labels = mixedMoment B raw7042step0 raw7042step0Labels := by
      have hz : ∀ j, raw7042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7042step0 = (fun i j => raw7042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7042step0 raw7042; decide +kernel
      have hl : raw7042step0Labels = raw7042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7042 raw7042Labels permutation520 hz
    mixedMoment B raw7042step0 raw7042step0Labels = mixedMoment B raw7042step1 raw7042step1Labels := by
      have ha : raw7042step1 = (fun i j => raw7042step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7042step1 raw7042step0; decide +kernel
      have hl : raw7042step1Labels = raw7042step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7042step0 raw7042step0Labels permutation44 permutation2
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical7043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7043 raw7043Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw7043 raw7043Labels = mixedMoment B raw7043step0 raw7043step0Labels := by
      have ha : raw7043step0 = (fun i j => raw7043 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7043step0 raw7043; decide +kernel
      have hl : raw7043step0Labels = raw7043Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7043 raw7043Labels permutation200 permutation2
    _ = mixedMoment B node3036 node3036Labels := by rfl

theorem canonical7044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7044 raw7044Labels = mixedMoment B node2580 node2580Labels := by
  calc
    mixedMoment B raw7044 raw7044Labels = mixedMoment B raw7044step0 raw7044step0Labels := by
      have ha : raw7044step0 = (fun i j => raw7044 (permutation504 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7044step0 raw7044; decide +kernel
      have hl : raw7044step0Labels = raw7044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7044 raw7044Labels permutation504 permutation4
    _ = mixedMoment B node2580 node2580Labels := by rfl

theorem canonical7045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7045 raw7045Labels = mixedMoment B node2971 node2971Labels := by
  calc
    mixedMoment B raw7045 raw7045Labels = mixedMoment B raw7045step0 raw7045step0Labels := by
      have ha : raw7045step0 = (fun i j => raw7045 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7045step0 raw7045; decide +kernel
      have hl : raw7045step0Labels = raw7045Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7045 raw7045Labels permutation182 permutation2
    _ = mixedMoment B node2971 node2971Labels := by rfl

theorem canonical7046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7046 raw7046Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw7046 raw7046Labels = mixedMoment B raw7046step0 raw7046step0Labels := by
      have ha : raw7046step0 = (fun i j => raw7046 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7046step0 raw7046; decide +kernel
      have hl : raw7046step0Labels = raw7046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7046 raw7046Labels permutation676 permutation2
    mixedMoment B raw7046step0 raw7046step0Labels = mixedMoment B raw7046step1 raw7046step1Labels := by
      have ha : raw7046step1 = -raw7046step0 := by apply Matrix.ext; change ∀ i j, raw7046step1 i j = -(raw7046step0 i j); unfold raw7046step1 raw7046step0; decide +kernel
      have hl : raw7046step1Labels = raw7046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2547 node2547Labels := by rfl

theorem canonical7047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7047 raw7047Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw7047 raw7047Labels = mixedMoment B raw7047step0 raw7047step0Labels := by
      have hz : ∀ j, raw7047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7047step0 = (fun i j => raw7047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7047step0 raw7047; decide +kernel
      have hl : raw7047step0Labels = raw7047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7047 raw7047Labels permutation346 hz
    mixedMoment B raw7047step0 raw7047step0Labels = mixedMoment B raw7047step1 raw7047step1Labels := by
      have ha : raw7047step1 = (fun i j => raw7047step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7047step1 raw7047step0; decide +kernel
      have hl : raw7047step1Labels = raw7047step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7047step0 raw7047step0Labels permutation38 permutation2
    _ = mixedMoment B node2867 node2867Labels := by rfl

theorem canonical7048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7048 raw7048Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw7048 raw7048Labels = mixedMoment B raw7048step0 raw7048step0Labels := by
      have hz : ∀ j, raw7048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7048step0 = (fun i j => raw7048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7048step0 raw7048; decide +kernel
      have hl : raw7048step0Labels = raw7048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7048 raw7048Labels permutation346 hz
    mixedMoment B raw7048step0 raw7048step0Labels = mixedMoment B raw7048step1 raw7048step1Labels := by
      have ha : raw7048step1 = (fun i j => raw7048step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7048step1 raw7048step0; decide +kernel
      have hl : raw7048step1Labels = raw7048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7048step0 raw7048step0Labels permutation149 permutation2
    mixedMoment B raw7048step1 raw7048step1Labels = mixedMoment B raw7048step2 raw7048step2Labels := by
      have ha : raw7048step2 = -raw7048step1 := by apply Matrix.ext; change ∀ i j, raw7048step2 i j = -(raw7048step1 i j); unfold raw7048step2 raw7048step1; decide +kernel
      have hl : raw7048step2Labels = raw7048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

theorem canonical7049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7049 raw7049Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw7049 raw7049Labels = mixedMoment B raw7049step0 raw7049step0Labels := by
      have hz : ∀ j, raw7049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7049step0 = (fun i j => raw7049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7049step0 raw7049; decide +kernel
      have hl : raw7049step0Labels = raw7049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7049 raw7049Labels permutation346 hz
    mixedMoment B raw7049step0 raw7049step0Labels = mixedMoment B raw7049step1 raw7049step1Labels := by
      have ha : raw7049step1 = (fun i j => raw7049step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7049step1 raw7049step0; decide +kernel
      have hl : raw7049step1Labels = raw7049step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7049step0 raw7049step0Labels permutation39 permutation2
    _ = mixedMoment B node3040 node3040Labels := by rfl

theorem canonical7092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7092 raw7092Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw7092 raw7092Labels = mixedMoment B raw7092step0 raw7092step0Labels := by
      have hz : ∀ j, raw7092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7092step0 = (fun i j => raw7092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7092step0 raw7092; decide +kernel
      have hl : raw7092step0Labels = raw7092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7092 raw7092Labels permutation346 hz
    mixedMoment B raw7092step0 raw7092step0Labels = mixedMoment B raw7092step1 raw7092step1Labels := by
      have ha : raw7092step1 = (fun i j => raw7092step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7092step1 raw7092step0; decide +kernel
      have hl : raw7092step1Labels = raw7092step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7092step0 raw7092step0Labels permutation40 permutation2
    mixedMoment B raw7092step1 raw7092step1Labels = mixedMoment B raw7092step2 raw7092step2Labels := by
      have ha : raw7092step2 = -raw7092step1 := by apply Matrix.ext; change ∀ i j, raw7092step2 i j = -(raw7092step1 i j); unfold raw7092step2 raw7092step1; decide +kernel
      have hl : raw7092step2Labels = raw7092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3379 node3379Labels := by rfl

theorem canonical7093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7093 raw7093Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw7093 raw7093Labels = mixedMoment B raw7093step0 raw7093step0Labels := by
      have ha : raw7093step0 = (fun i j => raw7093 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7093step0 raw7093; decide +kernel
      have hl : raw7093step0Labels = raw7093Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7093 raw7093Labels permutation212 permutation2
    mixedMoment B raw7093step0 raw7093step0Labels = mixedMoment B raw7093step1 raw7093step1Labels := by
      have ha : raw7093step1 = -raw7093step0 := by apply Matrix.ext; change ∀ i j, raw7093step1 i j = -(raw7093step0 i j); unfold raw7093step1 raw7093step0; decide +kernel
      have hl : raw7093step1Labels = raw7093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3375 node3375Labels := by rfl

theorem canonical7094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7094 raw7094Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw7094 raw7094Labels = mixedMoment B raw7094step0 raw7094step0Labels := by
      have hz : ∀ j, raw7094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7094step0 = (fun i j => raw7094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7094step0 raw7094; decide +kernel
      have hl : raw7094step0Labels = raw7094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7094 raw7094Labels permutation346 hz
    mixedMoment B raw7094step0 raw7094step0Labels = mixedMoment B raw7094step1 raw7094step1Labels := by
      have ha : raw7094step1 = (fun i j => raw7094step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7094step1 raw7094step0; decide +kernel
      have hl : raw7094step1Labels = raw7094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7094step0 raw7094step0Labels permutation139 permutation2
    _ = mixedMoment B node2560 node2560Labels := by rfl

theorem canonical7095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7095 raw7095Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw7095 raw7095Labels = mixedMoment B raw7095step0 raw7095step0Labels := by
      have hz : ∀ j, raw7095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7095step0 = (fun i j => raw7095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7095step0 raw7095; decide +kernel
      have hl : raw7095step0Labels = raw7095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7095 raw7095Labels permutation346 hz
    mixedMoment B raw7095step0 raw7095step0Labels = mixedMoment B raw7095step1 raw7095step1Labels := by
      have hz : ∀ j, raw7095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7095step1 = (fun i j => raw7095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7095step1 raw7095step0; decide +kernel
      have hl : raw7095step1Labels = raw7095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7095step0 raw7095step0Labels permutation56 hz
    mixedMoment B raw7095step1 raw7095step1Labels = mixedMoment B raw7095step2 raw7095step2Labels := by
      have ha : raw7095step2 = (fun i j => raw7095step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7095step2 raw7095step1; decide +kernel
      have hl : raw7095step2Labels = raw7095step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7095step1 raw7095step1Labels permutation13 permutation4
    mixedMoment B raw7095step2 raw7095step2Labels = mixedMoment B raw7095step3 raw7095step3Labels := by
      have ha : raw7095step3 = -raw7095step2 := by apply Matrix.ext; change ∀ i j, raw7095step3 i j = -(raw7095step2 i j); unfold raw7095step3 raw7095step2; decide +kernel
      have hl : raw7095step3Labels = raw7095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical7096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7096 raw7096Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw7096 raw7096Labels = mixedMoment B raw7096step0 raw7096step0Labels := by
      have ha : raw7096step0 = (fun i j => raw7096 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7096step0 raw7096; decide +kernel
      have hl : raw7096step0Labels = raw7096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7096 raw7096Labels permutation171 permutation4
    mixedMoment B raw7096step0 raw7096step0Labels = mixedMoment B raw7096step1 raw7096step1Labels := by
      have ha : raw7096step1 = -raw7096step0 := by apply Matrix.ext; change ∀ i j, raw7096step1 i j = -(raw7096step0 i j); unfold raw7096step1 raw7096step0; decide +kernel
      have hl : raw7096step1Labels = raw7096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2034 node2034Labels := by rfl

theorem canonical7097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7097 raw7097Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw7097 raw7097Labels = mixedMoment B raw7097step0 raw7097step0Labels := by
      have hz : ∀ j, raw7097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7097step0 = (fun i j => raw7097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7097step0 raw7097; decide +kernel
      have hl : raw7097step0Labels = raw7097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7097 raw7097Labels permutation346 hz
    mixedMoment B raw7097step0 raw7097step0Labels = mixedMoment B raw7097step1 raw7097step1Labels := by
      have ha : raw7097step1 = (fun i j => raw7097step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7097step1 raw7097step0; decide +kernel
      have hl : raw7097step1Labels = raw7097step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7097step0 raw7097step0Labels permutation37 permutation4
    mixedMoment B raw7097step1 raw7097step1Labels = mixedMoment B raw7097step2 raw7097step2Labels := by
      have ha : raw7097step2 = -raw7097step1 := by apply Matrix.ext; change ∀ i j, raw7097step2 i j = -(raw7097step1 i j); unfold raw7097step2 raw7097step1; decide +kernel
      have hl : raw7097step2Labels = raw7097step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical7098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7098 raw7098Labels = mixedMoment B node3382 node3382Labels := by
  calc
    mixedMoment B raw7098 raw7098Labels = mixedMoment B raw7098step0 raw7098step0Labels := by
      have ha : raw7098step0 = (fun i j => raw7098 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7098step0 raw7098; decide +kernel
      have hl : raw7098step0Labels = raw7098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7098 raw7098Labels permutation171 permutation4
    mixedMoment B raw7098step0 raw7098step0Labels = mixedMoment B raw7098step1 raw7098step1Labels := by
      have ha : raw7098step1 = -raw7098step0 := by apply Matrix.ext; change ∀ i j, raw7098step1 i j = -(raw7098step0 i j); unfold raw7098step1 raw7098step0; decide +kernel
      have hl : raw7098step1Labels = raw7098step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3382 node3382Labels := by rfl

theorem canonical7099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7099 raw7099Labels = mixedMoment B node3151 node3151Labels := by
  calc
    mixedMoment B raw7099 raw7099Labels = mixedMoment B raw7099step0 raw7099step0Labels := by
      have hz : ∀ j, raw7099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7099step0 = (fun i j => raw7099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7099step0 raw7099; decide +kernel
      have hl : raw7099step0Labels = raw7099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7099 raw7099Labels permutation346 hz
    mixedMoment B raw7099step0 raw7099step0Labels = mixedMoment B raw7099step1 raw7099step1Labels := by
      have ha : raw7099step1 = (fun i j => raw7099step0 (permutation82 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7099step1 raw7099step0; decide +kernel
      have hl : raw7099step1Labels = raw7099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7099step0 raw7099step0Labels permutation82 permutation2
    mixedMoment B raw7099step1 raw7099step1Labels = mixedMoment B raw7099step2 raw7099step2Labels := by
      have ha : raw7099step2 = -raw7099step1 := by apply Matrix.ext; change ∀ i j, raw7099step2 i j = -(raw7099step1 i j); unfold raw7099step2 raw7099step1; decide +kernel
      have hl : raw7099step2Labels = raw7099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3151 node3151Labels := by rfl

theorem canonical7100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7100 raw7100Labels = mixedMoment B node2555 node2555Labels := by
  calc
    mixedMoment B raw7100 raw7100Labels = mixedMoment B raw7100step0 raw7100step0Labels := by
      have ha : raw7100step0 = (fun i j => raw7100 (permutation619 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7100step0 raw7100; decide +kernel
      have hl : raw7100step0Labels = raw7100Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7100 raw7100Labels permutation619 permutation2
    _ = mixedMoment B node2555 node2555Labels := by rfl

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

theorem canonical7193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7193 raw7193Labels = mixedMoment B node2709 node2709Labels := by
  calc
    _ = mixedMoment B node2709 node2709Labels := by rfl

theorem canonical7194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7194 raw7194Labels = mixedMoment B node3800 node3800Labels := by
  calc
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical7195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7195 raw7195Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw7195 raw7195Labels = mixedMoment B raw7195step0 raw7195step0Labels := by
      have ha : raw7195step0 = (fun i j => raw7195 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7195step0 raw7195; decide +kernel
      have hl : raw7195step0Labels = raw7195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7195 raw7195Labels permutation176 permutation2
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical7196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7196 raw7196Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw7196 raw7196Labels = mixedMoment B raw7196step0 raw7196step0Labels := by
      have ha : raw7196step0 = (fun i j => raw7196 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7196step0 raw7196; decide +kernel
      have hl : raw7196step0Labels = raw7196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7196 raw7196Labels permutation200 permutation2
    _ = mixedMoment B node3871 node3871Labels := by rfl

theorem canonical7197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7197 raw7197Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw7197 raw7197Labels = mixedMoment B raw7197step0 raw7197step0Labels := by
      have hz : ∀ j, raw7197 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7197step0 = (fun i j => raw7197 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7197step0 raw7197; decide +kernel
      have hl : raw7197step0Labels = raw7197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7197 raw7197Labels permutation520 hz
    _ = mixedMoment B node3902 node3902Labels := by rfl

theorem canonical7198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7198 raw7198Labels = mixedMoment B node3901 node3901Labels := by
  calc
    _ = mixedMoment B node3901 node3901Labels := by rfl

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

theorem canonical7200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7200 raw7200Labels = mixedMoment B node1247 node1247Labels := by
  calc
    mixedMoment B raw7200 raw7200Labels = mixedMoment B raw7200step0 raw7200step0Labels := by
      have ha : raw7200step0 = (fun i j => raw7200 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7200step0 raw7200; decide +kernel
      have hl : raw7200step0Labels = raw7200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7200 raw7200Labels permutation182 permutation2
    _ = mixedMoment B node1247 node1247Labels := by rfl

theorem canonical7201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7201 raw7201Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7201 raw7201Labels = mixedMoment B raw7201step0 raw7201step0Labels := by
      have ha : raw7201step0 = (fun i j => raw7201 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7201step0 raw7201; decide +kernel
      have hl : raw7201step0Labels = raw7201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7201 raw7201Labels permutation160 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

theorem canonical7202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7202 raw7202Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7202 raw7202Labels = mixedMoment B raw7202step0 raw7202step0Labels := by
      have ha : raw7202step0 = (fun i j => raw7202 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7202step0 raw7202; decide +kernel
      have hl : raw7202step0Labels = raw7202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7202 raw7202Labels permutation154 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

theorem canonical7203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7203 raw7203Labels = mixedMoment B node1208 node1208Labels := by
  calc
    _ = mixedMoment B node1208 node1208Labels := by rfl

theorem canonical7204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7204 raw7204Labels = mixedMoment B node1206 node1206Labels := by
  calc
    _ = mixedMoment B node1206 node1206Labels := by rfl

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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound3054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3054 node3054Labels = Sparse.eval nodeValue3054 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3054) = mixedMoment B node3054 node3054Labels := rfl
  simpa [nodeValue3054, Sparse.eval] using hc.symm

theorem sound3907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3907 node3907Labels = Sparse.eval nodeValue3907 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3907) = mixedMoment B node3907 node3907Labels := rfl
  simpa [nodeValue3907, Sparse.eval] using hc.symm

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

theorem sound1208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1208 node1208Labels = Sparse.eval nodeValue1208 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1208) = mixedMoment B node1208 node1208Labels := rfl
  simpa [nodeValue1208, Sparse.eval] using hc.symm

theorem sound1213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1213 node1213Labels = Sparse.eval nodeValue1213 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1213) = mixedMoment B node1213 node1213Labels := rfl
  simpa [nodeValue1213, Sparse.eval] using hc.symm

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

theorem sound1247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1247 node1247Labels = Sparse.eval nodeValue1247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1247) = mixedMoment B node1247 node1247Labels := rfl
  simpa [nodeValue1247, Sparse.eval] using hc.symm

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

theorem sound1357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1357 node1357Labels = Sparse.eval nodeValue1357 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1357) = mixedMoment B node1357 node1357Labels := rfl
  simpa [nodeValue1357, Sparse.eval] using hc.symm

theorem sound1359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1359 node1359Labels = Sparse.eval nodeValue1359 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1359) = mixedMoment B node1359 node1359Labels := rfl
  simpa [nodeValue1359, Sparse.eval] using hc.symm

theorem sound1362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1362 node1362Labels = Sparse.eval nodeValue1362 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1362) = mixedMoment B node1362 node1362Labels := rfl
  simpa [nodeValue1362, Sparse.eval] using hc.symm

theorem sound1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1367 node1367Labels = Sparse.eval nodeValue1367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1367) = mixedMoment B node1367 node1367Labels := rfl
  simpa [nodeValue1367, Sparse.eval] using hc.symm

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

theorem sound1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1422 node1422Labels = Sparse.eval nodeValue1422 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1422) = mixedMoment B node1422 node1422Labels := rfl
  simpa [nodeValue1422, Sparse.eval] using hc.symm

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

theorem sound2034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2034 node2034Labels = Sparse.eval nodeValue2034 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2034) = mixedMoment B node2034 node2034Labels := rfl
  simpa [nodeValue2034, Sparse.eval] using hc.symm

theorem sound2037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2037 node2037Labels = Sparse.eval nodeValue2037 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2037) = mixedMoment B node2037 node2037Labels := rfl
  simpa [nodeValue2037, Sparse.eval] using hc.symm

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

theorem sound2058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2058 node2058Labels = Sparse.eval nodeValue2058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2058) = mixedMoment B node2058 node2058Labels := rfl
  simpa [nodeValue2058, Sparse.eval] using hc.symm

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

theorem sound2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2547 node2547Labels = Sparse.eval nodeValue2547 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2547) = mixedMoment B node2547 node2547Labels := rfl
  simpa [nodeValue2547, Sparse.eval] using hc.symm

theorem sound2555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2555 node2555Labels = Sparse.eval nodeValue2555 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2555) = mixedMoment B node2555 node2555Labels := rfl
  simpa [nodeValue2555, Sparse.eval] using hc.symm

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

theorem sound2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2560 node2560Labels = Sparse.eval nodeValue2560 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2560) = mixedMoment B node2560 node2560Labels := rfl
  simpa [nodeValue2560, Sparse.eval] using hc.symm

theorem sound2579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2579 node2579Labels = Sparse.eval nodeValue2579 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2579) = mixedMoment B node2579 node2579Labels := rfl
  simpa [nodeValue2579, Sparse.eval] using hc.symm

theorem sound2580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2580 node2580Labels = Sparse.eval nodeValue2580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2580) = mixedMoment B node2580 node2580Labels := rfl
  simpa [nodeValue2580, Sparse.eval] using hc.symm

theorem sound2582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2582 node2582Labels = Sparse.eval nodeValue2582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2582) = mixedMoment B node2582 node2582Labels := rfl
  simpa [nodeValue2582, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = 0 := by
  exact mixedMoment_alpha B hF node2709 node2709Labels 1 permutation200
    (by decide +kernel)

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

theorem sound2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2709 node2709Labels = Sparse.eval nodeValue2709 (mixedVector B) := by
  simpa only [nodeValue2709, Sparse.eval_nil] using zero2709 B _hB _hF

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

theorem sound2861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2861 node2861Labels = Sparse.eval nodeValue2861 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2861) = mixedMoment B node2861 node2861Labels := rfl
  simpa [nodeValue2861, Sparse.eval] using hc.symm

theorem sound2867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2867 node2867Labels = Sparse.eval nodeValue2867 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2867) = mixedMoment B node2867 node2867Labels := rfl
  simpa [nodeValue2867, Sparse.eval] using hc.symm

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

theorem sound2971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2971 node2971Labels = Sparse.eval nodeValue2971 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2971) = mixedMoment B node2971 node2971Labels := rfl
  simpa [nodeValue2971, Sparse.eval] using hc.symm

theorem sound2974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2974 node2974Labels = Sparse.eval nodeValue2974 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2974) = mixedMoment B node2974 node2974Labels := rfl
  simpa [nodeValue2974, Sparse.eval] using hc.symm

theorem sound3007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3007 node3007Labels = Sparse.eval nodeValue3007 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3007) = mixedMoment B node3007 node3007Labels := rfl
  simpa [nodeValue3007, Sparse.eval] using hc.symm

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

theorem sound3010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3010 node3010Labels = Sparse.eval nodeValue3010 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3010) = mixedMoment B node3010 node3010Labels := rfl
  simpa [nodeValue3010, Sparse.eval] using hc.symm

theorem sound3036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3036 node3036Labels = Sparse.eval nodeValue3036 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3036) = mixedMoment B node3036 node3036Labels := rfl
  simpa [nodeValue3036, Sparse.eval] using hc.symm

theorem sound3038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3038 node3038Labels = Sparse.eval nodeValue3038 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3038) = mixedMoment B node3038 node3038Labels := rfl
  simpa [nodeValue3038, Sparse.eval] using hc.symm

theorem sound3040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3040 node3040Labels = Sparse.eval nodeValue3040 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3040) = mixedMoment B node3040 node3040Labels := rfl
  simpa [nodeValue3040, Sparse.eval] using hc.symm

theorem sound3051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3051 node3051Labels = Sparse.eval nodeValue3051 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3051) = mixedMoment B node3051 node3051Labels := rfl
  simpa [nodeValue3051, Sparse.eval] using hc.symm

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

theorem sound3151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3151 node3151Labels = Sparse.eval nodeValue3151 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3151) = mixedMoment B node3151 node3151Labels := rfl
  simpa [nodeValue3151, Sparse.eval] using hc.symm

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

theorem sound3375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3375 node3375Labels = Sparse.eval nodeValue3375 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3375) = mixedMoment B node3375 node3375Labels := rfl
  simpa [nodeValue3375, Sparse.eval] using hc.symm

theorem sound3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3379 node3379Labels = Sparse.eval nodeValue3379 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3379) = mixedMoment B node3379 node3379Labels := rfl
  simpa [nodeValue3379, Sparse.eval] using hc.symm

theorem sound3382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3382 node3382Labels = Sparse.eval nodeValue3382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3382) = mixedMoment B node3382 node3382Labels := rfl
  simpa [nodeValue3382, Sparse.eval] using hc.symm

theorem sound3383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3383 node3383Labels = Sparse.eval nodeValue3383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3383) = mixedMoment B node3383 node3383Labels := rfl
  simpa [nodeValue3383, Sparse.eval] using hc.symm

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

theorem sound3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3395 node3395Labels = Sparse.eval nodeValue3395 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3395) = mixedMoment B node3395 node3395Labels := rfl
  simpa [nodeValue3395, Sparse.eval] using hc.symm

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

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

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

theorem sound3800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3800 node3800Labels = Sparse.eval nodeValue3800 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3800) = mixedMoment B node3800 node3800Labels := rfl
  simpa [nodeValue3800, Sparse.eval] using hc.symm

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

theorem sound3845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3845 node3845Labels = Sparse.eval nodeValue3845 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3845) = mixedMoment B node3845 node3845Labels := rfl
  simpa [nodeValue3845, Sparse.eval] using hc.symm

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

theorem sound3871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3871 node3871Labels = Sparse.eval nodeValue3871 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3871) = mixedMoment B node3871 node3871Labels := rfl
  simpa [nodeValue3871, Sparse.eval] using hc.symm

theorem sound3901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3901 node3901Labels = Sparse.eval nodeValue3901 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3901) = mixedMoment B node3901 node3901Labels := rfl
  simpa [nodeValue3901, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources10
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm343 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA343 + difference 0 0) (sourceB343 + difference 0 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA343 + difference 0 0) (sourceB343 + difference 0 0) sourceC343) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA343 + difference 0 1) (sourceB343 + difference 1 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA343 + difference 0 1) (sourceB343 + difference 1 0) sourceC343) = raw7022 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7022; decide +kernel
    rw [ha]
    exact (canonical7022 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA343 + difference 0 2) (sourceB343 + difference 2 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA343 + difference 0 2) (sourceB343 + difference 2 0) sourceC343) = raw7023 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7023; decide +kernel
    rw [ha]
    exact (canonical7023 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA343 + difference 0 3) (sourceB343 + difference 3 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA343 + difference 0 3) (sourceB343 + difference 3 0) sourceC343) = raw7024 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7024; decide +kernel
    rw [ha]
    exact (canonical7024 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA343 + difference 0 4) (sourceB343 + difference 4 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3907) := by
    have ha : (tripleCharges (sourceA343 + difference 0 4) (sourceB343 + difference 4 0) sourceC343) = raw7025 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7025; decide +kernel
    rw [ha]
    exact (canonical7025 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA343 + difference 0 5) (sourceB343 + difference 5 0) sourceC343) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3857) := by
    have ha : (tripleCharges (sourceA343 + difference 0 5) (sourceB343 + difference 5 0) sourceC343) = raw7026 := by
      apply Matrix.ext; unfold tripleCharges sourceA343 sourceB343 sourceC343 difference raw7026; decide +kernel
    rw [ha]
    exact (canonical7026 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA343 + sourceB343) sourceC343) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA343 + sourceB343) sourceC343) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA343 sourceB343 sourceC343 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA343 sourceB343 sourceC343
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm343, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm344 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA344 + difference 0 0) (sourceB344 + difference 0 0) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA344 + difference 0 0) (sourceB344 + difference 0 0) sourceC344) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA344 + difference 1 0) (sourceB344 + difference 0 1) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA344 + difference 1 0) (sourceB344 + difference 0 1) sourceC344) = raw7028 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7028; decide +kernel
    rw [ha]
    exact (canonical7028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA344 + difference 2 0) (sourceB344 + difference 0 2) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1357) := by
    have ha : (tripleCharges (sourceA344 + difference 2 0) (sourceB344 + difference 0 2) sourceC344) = raw7029 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7029; decide +kernel
    rw [ha]
    exact (canonical7029 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA344 + difference 3 0) (sourceB344 + difference 0 3) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1422) := by
    have ha : (tripleCharges (sourceA344 + difference 3 0) (sourceB344 + difference 0 3) sourceC344) = raw7030 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7030; decide +kernel
    rw [ha]
    exact (canonical7030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA344 + difference 4 0) (sourceB344 + difference 0 4) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA344 + difference 4 0) (sourceB344 + difference 0 4) sourceC344) = raw7031 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7031; decide +kernel
    rw [ha]
    exact (canonical7031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA344 + difference 5 0) (sourceB344 + difference 0 5) sourceC344) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1359) := by
    have ha : (tripleCharges (sourceA344 + difference 5 0) (sourceB344 + difference 0 5) sourceC344) = raw7032 := by
      apply Matrix.ext; unfold tripleCharges sourceA344 sourceB344 sourceC344 difference raw7032; decide +kernel
    rw [ha]
    exact (canonical7032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA344 + sourceB344) sourceC344) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA344 + sourceB344) sourceC344) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA344 sourceB344 sourceC344 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA344 sourceB344 sourceC344
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm344, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm345 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA345 + difference 1 0) (sourceB345 + difference 0 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA345 + difference 1 0) (sourceB345 + difference 0 1) sourceC345) = raw7028 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7028; decide +kernel
    rw [ha]
    exact (canonical7028 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA345 + difference 1 1) (sourceB345 + difference 1 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA345 + difference 1 1) (sourceB345 + difference 1 1) sourceC345) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA345 + difference 1 2) (sourceB345 + difference 2 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA345 + difference 1 2) (sourceB345 + difference 2 1) sourceC345) = raw7033 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7033; decide +kernel
    rw [ha]
    exact (canonical7033 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA345 + difference 1 3) (sourceB345 + difference 3 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA345 + difference 1 3) (sourceB345 + difference 3 1) sourceC345) = raw7034 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7034; decide +kernel
    rw [ha]
    exact (canonical7034 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA345 + difference 1 4) (sourceB345 + difference 4 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3054) := by
    have ha : (tripleCharges (sourceA345 + difference 1 4) (sourceB345 + difference 4 1) sourceC345) = raw7035 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7035; decide +kernel
    rw [ha]
    exact (canonical7035 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA345 + difference 1 5) (sourceB345 + difference 5 1) sourceC345) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3051) := by
    have ha : (tripleCharges (sourceA345 + difference 1 5) (sourceB345 + difference 5 1) sourceC345) = raw7036 := by
      apply Matrix.ext; unfold tripleCharges sourceA345 sourceB345 sourceC345 difference raw7036; decide +kernel
    rw [ha]
    exact (canonical7036 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA345 + sourceB345) sourceC345) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA345 + sourceB345) sourceC345) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA345 sourceB345 sourceC345 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA345 sourceB345 sourceC345
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm345, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm346 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA346 + difference 0 1) (sourceB346 + difference 1 0) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3854) := by
    have ha : (tripleCharges (sourceA346 + difference 0 1) (sourceB346 + difference 1 0) sourceC346) = raw7022 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7022; decide +kernel
    rw [ha]
    exact (canonical7022 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA346 + difference 1 1) (sourceB346 + difference 1 1) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA346 + difference 1 1) (sourceB346 + difference 1 1) sourceC346) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA346 + difference 2 1) (sourceB346 + difference 1 2) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3007) := by
    have ha : (tripleCharges (sourceA346 + difference 2 1) (sourceB346 + difference 1 2) sourceC346) = raw7037 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7037; decide +kernel
    rw [ha]
    exact (canonical7037 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA346 + difference 3 1) (sourceB346 + difference 1 3) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2582) := by
    have ha : (tripleCharges (sourceA346 + difference 3 1) (sourceB346 + difference 1 3) sourceC346) = raw7038 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7038; decide +kernel
    rw [ha]
    exact (canonical7038 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA346 + difference 4 1) (sourceB346 + difference 1 4) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3010) := by
    have ha : (tripleCharges (sourceA346 + difference 4 1) (sourceB346 + difference 1 4) sourceC346) = raw7039 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7039; decide +kernel
    rw [ha]
    exact (canonical7039 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA346 + difference 5 1) (sourceB346 + difference 1 5) sourceC346) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2579) := by
    have ha : (tripleCharges (sourceA346 + difference 5 1) (sourceB346 + difference 1 5) sourceC346) = raw7040 := by
      apply Matrix.ext; unfold tripleCharges sourceA346 sourceB346 sourceC346 difference raw7040; decide +kernel
    rw [ha]
    exact (canonical7040 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA346 + sourceB346) sourceC346) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA346 + sourceB346) sourceC346) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA346 sourceB346 sourceC346 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA346 sourceB346 sourceC346
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm346, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm347 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA347 + difference 2 0) (sourceB347 + difference 0 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1357) := by
    have ha : (tripleCharges (sourceA347 + difference 2 0) (sourceB347 + difference 0 2) sourceC347) = raw7029 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7029; decide +kernel
    rw [ha]
    exact (canonical7029 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA347 + difference 2 1) (sourceB347 + difference 1 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3007) := by
    have ha : (tripleCharges (sourceA347 + difference 2 1) (sourceB347 + difference 1 2) sourceC347) = raw7037 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7037; decide +kernel
    rw [ha]
    exact (canonical7037 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA347 + difference 2 2) (sourceB347 + difference 2 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA347 + difference 2 2) (sourceB347 + difference 2 2) sourceC347) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA347 + difference 2 3) (sourceB347 + difference 3 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA347 + difference 2 3) (sourceB347 + difference 3 2) sourceC347) = raw7041 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7041; decide +kernel
    rw [ha]
    exact (canonical7041 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA347 + difference 2 4) (sourceB347 + difference 4 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA347 + difference 2 4) (sourceB347 + difference 4 2) sourceC347) = raw7042 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7042; decide +kernel
    rw [ha]
    exact (canonical7042 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA347 + difference 2 5) (sourceB347 + difference 5 2) sourceC347) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3036) := by
    have ha : (tripleCharges (sourceA347 + difference 2 5) (sourceB347 + difference 5 2) sourceC347) = raw7043 := by
      apply Matrix.ext; unfold tripleCharges sourceA347 sourceB347 sourceC347 difference raw7043; decide +kernel
    rw [ha]
    exact (canonical7043 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA347 + sourceB347) sourceC347) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA347 + sourceB347) sourceC347) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA347 sourceB347 sourceC347 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA347 sourceB347 sourceC347
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm347, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm348 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA348 + difference 0 2) (sourceB348 + difference 2 0) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3840) := by
    have ha : (tripleCharges (sourceA348 + difference 0 2) (sourceB348 + difference 2 0) sourceC348) = raw7023 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7023; decide +kernel
    rw [ha]
    exact (canonical7023 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA348 + difference 1 2) (sourceB348 + difference 2 1) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2974) := by
    have ha : (tripleCharges (sourceA348 + difference 1 2) (sourceB348 + difference 2 1) sourceC348) = raw7033 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7033; decide +kernel
    rw [ha]
    exact (canonical7033 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA348 + difference 2 2) (sourceB348 + difference 2 2) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA348 + difference 2 2) (sourceB348 + difference 2 2) sourceC348) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA348 + difference 3 2) (sourceB348 + difference 2 3) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2580) := by
    have ha : (tripleCharges (sourceA348 + difference 3 2) (sourceB348 + difference 2 3) sourceC348) = raw7044 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7044; decide +kernel
    rw [ha]
    exact (canonical7044 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA348 + difference 4 2) (sourceB348 + difference 2 4) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2971) := by
    have ha : (tripleCharges (sourceA348 + difference 4 2) (sourceB348 + difference 2 4) sourceC348) = raw7045 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7045; decide +kernel
    rw [ha]
    exact (canonical7045 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA348 + difference 5 2) (sourceB348 + difference 2 5) sourceC348) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2547) := by
    have ha : (tripleCharges (sourceA348 + difference 5 2) (sourceB348 + difference 2 5) sourceC348) = raw7046 := by
      apply Matrix.ext; unfold tripleCharges sourceA348 sourceB348 sourceC348 difference raw7046; decide +kernel
    rw [ha]
    exact (canonical7046 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA348 + sourceB348) sourceC348) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA348 + sourceB348) sourceC348) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA348 sourceB348 sourceC348 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA348 sourceB348 sourceC348
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm348, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm349 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA349 + difference 0 3) (sourceB349 + difference 3 0) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3845) := by
    have ha : (tripleCharges (sourceA349 + difference 0 3) (sourceB349 + difference 3 0) sourceC349) = raw7024 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7024; decide +kernel
    rw [ha]
    exact (canonical7024 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA349 + difference 1 3) (sourceB349 + difference 3 1) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA349 + difference 1 3) (sourceB349 + difference 3 1) sourceC349) = raw7034 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7034; decide +kernel
    rw [ha]
    exact (canonical7034 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA349 + difference 2 3) (sourceB349 + difference 3 2) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2861) := by
    have ha : (tripleCharges (sourceA349 + difference 2 3) (sourceB349 + difference 3 2) sourceC349) = raw7041 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7041; decide +kernel
    rw [ha]
    exact (canonical7041 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA349 + difference 3 3) (sourceB349 + difference 3 3) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA349 + difference 3 3) (sourceB349 + difference 3 3) sourceC349) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA349 + difference 4 3) (sourceB349 + difference 3 4) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA349 + difference 4 3) (sourceB349 + difference 3 4) sourceC349) = raw7047 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7047; decide +kernel
    rw [ha]
    exact (canonical7047 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA349 + difference 5 3) (sourceB349 + difference 3 5) sourceC349) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2558) := by
    have ha : (tripleCharges (sourceA349 + difference 5 3) (sourceB349 + difference 3 5) sourceC349) = raw7048 := by
      apply Matrix.ext; unfold tripleCharges sourceA349 sourceB349 sourceC349 difference raw7048; decide +kernel
    rw [ha]
    exact (canonical7048 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA349 + sourceB349) sourceC349) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA349 + sourceB349) sourceC349) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA349 sourceB349 sourceC349 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA349 sourceB349 sourceC349
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm349, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm350 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA350 + difference 4 0) (sourceB350 + difference 0 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1362) := by
    have ha : (tripleCharges (sourceA350 + difference 4 0) (sourceB350 + difference 0 4) sourceC350) = raw7031 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7031; decide +kernel
    rw [ha]
    exact (canonical7031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA350 + difference 4 1) (sourceB350 + difference 1 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3010) := by
    have ha : (tripleCharges (sourceA350 + difference 4 1) (sourceB350 + difference 1 4) sourceC350) = raw7039 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7039; decide +kernel
    rw [ha]
    exact (canonical7039 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA350 + difference 4 2) (sourceB350 + difference 2 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2971) := by
    have ha : (tripleCharges (sourceA350 + difference 4 2) (sourceB350 + difference 2 4) sourceC350) = raw7045 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7045; decide +kernel
    rw [ha]
    exact (canonical7045 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA350 + difference 4 3) (sourceB350 + difference 3 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2867) := by
    have ha : (tripleCharges (sourceA350 + difference 4 3) (sourceB350 + difference 3 4) sourceC350) = raw7047 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7047; decide +kernel
    rw [ha]
    exact (canonical7047 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA350 + difference 4 4) (sourceB350 + difference 4 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3038) := by
    have ha : (tripleCharges (sourceA350 + difference 4 4) (sourceB350 + difference 4 4) sourceC350) = raw7021 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7021; decide +kernel
    rw [ha]
    exact (canonical7021 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA350 + difference 4 5) (sourceB350 + difference 5 4) sourceC350) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3040) := by
    have ha : (tripleCharges (sourceA350 + difference 4 5) (sourceB350 + difference 5 4) sourceC350) = raw7049 := by
      apply Matrix.ext; unfold tripleCharges sourceA350 sourceB350 sourceC350 difference raw7049; decide +kernel
    rw [ha]
    exact (canonical7049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA350 + sourceB350) sourceC350) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA350 + sourceB350) sourceC350) = raw7027 := by
      apply Matrix.ext; unfold doubleCharges sourceA350 sourceB350 sourceC350 raw7027; decide +kernel
    rw [ha]
    exact (canonical7027 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA350 sourceB350 sourceC350
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm350, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources11
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm354 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA354 + difference 0 0) (sourceB354 + difference 0 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA354 + difference 0 0) (sourceB354 + difference 0 0) sourceC354) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA354 + difference 0 1) (sourceB354 + difference 1 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA354 + difference 0 1) (sourceB354 + difference 1 0) sourceC354) = raw7092 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw7092; decide +kernel
    rw [ha]
    exact (canonical7092 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA354 + difference 0 2) (sourceB354 + difference 2 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3375) := by
    have ha : (tripleCharges (sourceA354 + difference 0 2) (sourceB354 + difference 2 0) sourceC354) = raw7093 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw7093; decide +kernel
    rw [ha]
    exact (canonical7093 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA354 + difference 0 3) (sourceB354 + difference 3 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3533) := by
    have ha : (tripleCharges (sourceA354 + difference 0 3) (sourceB354 + difference 3 0) sourceC354) = raw6437 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw6437; decide +kernel
    rw [ha]
    exact (canonical6437 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA354 + difference 0 4) (sourceB354 + difference 4 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3391) := by
    have ha : (tripleCharges (sourceA354 + difference 0 4) (sourceB354 + difference 4 0) sourceC354) = raw6789 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw6789; decide +kernel
    rw [ha]
    exact (canonical6789 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA354 + difference 0 5) (sourceB354 + difference 5 0) sourceC354) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2560) := by
    have ha : (tripleCharges (sourceA354 + difference 0 5) (sourceB354 + difference 5 0) sourceC354) = raw7094 := by
      apply Matrix.ext; unfold tripleCharges sourceA354 sourceB354 sourceC354 difference raw7094; decide +kernel
    rw [ha]
    exact (canonical7094 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA354 + sourceB354) sourceC354) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA354 + sourceB354) sourceC354) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA354 sourceB354 sourceC354 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA354 sourceB354 sourceC354
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm354, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm355 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA355 + difference 0 0) (sourceB355 + difference 0 0) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA355 + difference 0 0) (sourceB355 + difference 0 0) sourceC355) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA355 + difference 1 0) (sourceB355 + difference 0 1) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA355 + difference 1 0) (sourceB355 + difference 0 1) sourceC355) = raw7095 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw7095; decide +kernel
    rw [ha]
    exact (canonical7095 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA355 + difference 2 0) (sourceB355 + difference 0 2) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA355 + difference 2 0) (sourceB355 + difference 0 2) sourceC355) = raw7096 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw7096; decide +kernel
    rw [ha]
    exact (canonical7096 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA355 + difference 3 0) (sourceB355 + difference 0 3) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2037) := by
    have ha : (tripleCharges (sourceA355 + difference 3 0) (sourceB355 + difference 0 3) sourceC355) = raw7097 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw7097; decide +kernel
    rw [ha]
    exact (canonical7097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA355 + difference 4 0) (sourceB355 + difference 0 4) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2039) := by
    have ha : (tripleCharges (sourceA355 + difference 4 0) (sourceB355 + difference 0 4) sourceC355) = raw6441 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw6441; decide +kernel
    rw [ha]
    exact (canonical6441 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA355 + difference 5 0) (sourceB355 + difference 0 5) sourceC355) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2058) := by
    have ha : (tripleCharges (sourceA355 + difference 5 0) (sourceB355 + difference 0 5) sourceC355) = raw6793 := by
      apply Matrix.ext; unfold tripleCharges sourceA355 sourceB355 sourceC355 difference raw6793; decide +kernel
    rw [ha]
    exact (canonical6793 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA355 + sourceB355) sourceC355) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA355 + sourceB355) sourceC355) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA355 sourceB355 sourceC355 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA355 sourceB355 sourceC355
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm355, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm356 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA356 + difference 0 1) (sourceB356 + difference 1 0) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3379) := by
    have ha : (tripleCharges (sourceA356 + difference 0 1) (sourceB356 + difference 1 0) sourceC356) = raw7092 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw7092; decide +kernel
    rw [ha]
    exact (canonical7092 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA356 + difference 1 1) (sourceB356 + difference 1 1) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA356 + difference 1 1) (sourceB356 + difference 1 1) sourceC356) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA356 + difference 2 1) (sourceB356 + difference 1 2) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3382) := by
    have ha : (tripleCharges (sourceA356 + difference 2 1) (sourceB356 + difference 1 2) sourceC356) = raw7098 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw7098; decide +kernel
    rw [ha]
    exact (canonical7098 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA356 + difference 3 1) (sourceB356 + difference 1 3) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3151) := by
    have ha : (tripleCharges (sourceA356 + difference 3 1) (sourceB356 + difference 1 3) sourceC356) = raw7099 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw7099; decide +kernel
    rw [ha]
    exact (canonical7099 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA356 + difference 4 1) (sourceB356 + difference 1 4) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3383) := by
    have ha : (tripleCharges (sourceA356 + difference 4 1) (sourceB356 + difference 1 4) sourceC356) = raw6448 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw6448; decide +kernel
    rw [ha]
    exact (canonical6448 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA356 + difference 5 1) (sourceB356 + difference 1 5) sourceC356) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3395) := by
    have ha : (tripleCharges (sourceA356 + difference 5 1) (sourceB356 + difference 1 5) sourceC356) = raw6801 := by
      apply Matrix.ext; unfold tripleCharges sourceA356 sourceB356 sourceC356 difference raw6801; decide +kernel
    rw [ha]
    exact (canonical6801 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA356 + sourceB356) sourceC356) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA356 + sourceB356) sourceC356) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA356 sourceB356 sourceC356 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA356 sourceB356 sourceC356
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm356, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm357 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA357 + difference 2 0) (sourceB357 + difference 0 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2034) := by
    have ha : (tripleCharges (sourceA357 + difference 2 0) (sourceB357 + difference 0 2) sourceC357) = raw7096 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw7096; decide +kernel
    rw [ha]
    exact (canonical7096 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA357 + difference 2 1) (sourceB357 + difference 1 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3382) := by
    have ha : (tripleCharges (sourceA357 + difference 2 1) (sourceB357 + difference 1 2) sourceC357) = raw7098 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw7098; decide +kernel
    rw [ha]
    exact (canonical7098 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA357 + difference 2 2) (sourceB357 + difference 2 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA357 + difference 2 2) (sourceB357 + difference 2 2) sourceC357) = raw6454 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw6454; decide +kernel
    rw [ha]
    exact (canonical6454 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA357 + difference 2 3) (sourceB357 + difference 3 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3539) := by
    have ha : (tripleCharges (sourceA357 + difference 2 3) (sourceB357 + difference 3 2) sourceC357) = raw6450 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw6450; decide +kernel
    rw [ha]
    exact (canonical6450 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA357 + difference 2 4) (sourceB357 + difference 4 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3528) := by
    have ha : (tripleCharges (sourceA357 + difference 2 4) (sourceB357 + difference 4 2) sourceC357) = raw6805 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw6805; decide +kernel
    rw [ha]
    exact (canonical6805 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA357 + difference 2 5) (sourceB357 + difference 5 2) sourceC357) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2555) := by
    have ha : (tripleCharges (sourceA357 + difference 2 5) (sourceB357 + difference 5 2) sourceC357) = raw7100 := by
      apply Matrix.ext; unfold tripleCharges sourceA357 sourceB357 sourceC357 difference raw7100; decide +kernel
    rw [ha]
    exact (canonical7100 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA357 + sourceB357) sourceC357) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA357 + sourceB357) sourceC357) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA357 sourceB357 sourceC357 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA357 sourceB357 sourceC357
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm357, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm362 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA362 + difference 0 0) (sourceB362 + difference 0 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA362 + difference 0 0) (sourceB362 + difference 0 0) sourceC362) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA362 + difference 0 1) (sourceB362 + difference 1 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3800) := by
    have ha : (tripleCharges (sourceA362 + difference 0 1) (sourceB362 + difference 1 0) sourceC362) = raw7194 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7194; decide +kernel
    rw [ha]
    exact (canonical7194 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA362 + difference 0 2) (sourceB362 + difference 2 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA362 + difference 0 2) (sourceB362 + difference 2 0) sourceC362) = raw7195 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7195; decide +kernel
    rw [ha]
    exact (canonical7195 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA362 + difference 0 3) (sourceB362 + difference 3 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3871) := by
    have ha : (tripleCharges (sourceA362 + difference 0 3) (sourceB362 + difference 3 0) sourceC362) = raw7196 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7196; decide +kernel
    rw [ha]
    exact (canonical7196 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA362 + difference 0 4) (sourceB362 + difference 4 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3902) := by
    have ha : (tripleCharges (sourceA362 + difference 0 4) (sourceB362 + difference 4 0) sourceC362) = raw7197 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7197; decide +kernel
    rw [ha]
    exact (canonical7197 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA362 + difference 0 5) (sourceB362 + difference 5 0) sourceC362) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3901) := by
    have ha : (tripleCharges (sourceA362 + difference 0 5) (sourceB362 + difference 5 0) sourceC362) = raw7198 := by
      apply Matrix.ext; unfold tripleCharges sourceA362 sourceB362 sourceC362 difference raw7198; decide +kernel
    rw [ha]
    exact (canonical7198 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA362 + sourceB362) sourceC362) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA362 + sourceB362) sourceC362) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA362 sourceB362 sourceC362 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA362 sourceB362 sourceC362
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm362, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm363 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA363 + difference 0 0) (sourceB363 + difference 0 0) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2709) := by
    have ha : (tripleCharges (sourceA363 + difference 0 0) (sourceB363 + difference 0 0) sourceC363) = raw7193 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7193; decide +kernel
    rw [ha]
    exact (canonical7193 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA363 + difference 1 0) (sourceB363 + difference 0 1) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1247) := by
    have ha : (tripleCharges (sourceA363 + difference 1 0) (sourceB363 + difference 0 1) sourceC363) = raw7200 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7200; decide +kernel
    rw [ha]
    exact (canonical7200 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA363 + difference 2 0) (sourceB363 + difference 0 2) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA363 + difference 2 0) (sourceB363 + difference 0 2) sourceC363) = raw7201 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7201; decide +kernel
    rw [ha]
    exact (canonical7201 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA363 + difference 3 0) (sourceB363 + difference 0 3) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA363 + difference 3 0) (sourceB363 + difference 0 3) sourceC363) = raw7202 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7202; decide +kernel
    rw [ha]
    exact (canonical7202 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA363 + difference 4 0) (sourceB363 + difference 0 4) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1208) := by
    have ha : (tripleCharges (sourceA363 + difference 4 0) (sourceB363 + difference 0 4) sourceC363) = raw7203 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7203; decide +kernel
    rw [ha]
    exact (canonical7203 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA363 + difference 5 0) (sourceB363 + difference 0 5) sourceC363) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1206) := by
    have ha : (tripleCharges (sourceA363 + difference 5 0) (sourceB363 + difference 0 5) sourceC363) = raw7204 := by
      apply Matrix.ext; unfold tripleCharges sourceA363 sourceB363 sourceC363 difference raw7204; decide +kernel
    rw [ha]
    exact (canonical7204 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA363 + sourceB363) sourceC363) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA363 + sourceB363) sourceC363) = raw7199 := by
      apply Matrix.ext; unfold doubleCharges sourceA363 sourceB363 sourceC363 raw7199; decide +kernel
    rw [ha]
    exact (canonical7199 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA363 sourceB363 sourceC363
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm363, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck288 : Integer.Sparse.reindex keyMap MixedData.row288 = numericRow288 := by decide +kernel

theorem numericCheck288 (x : Master → ℝ) : Integer.Sparse.eval numericRow288 x =
    (1 : ℝ) * reducedSource288 x := by
  norm_num [numericRow288, reducedSource288, Integer.Sparse.eval, Sparse.eval, nodeValue3038, nodeValue3840, nodeValue3845, nodeValue3854, nodeValue3857, nodeValue3907, nodeValue4092]

theorem reindexCheck289 : Integer.Sparse.reindex keyMap MixedData.row289 = numericRow289 := by decide +kernel

theorem numericCheck289 (x : Master → ℝ) : Integer.Sparse.eval numericRow289 x =
    (1 : ℝ) * reducedSource289 x := by
  norm_num [numericRow289, reducedSource289, Integer.Sparse.eval, Sparse.eval, nodeValue1357, nodeValue1359, nodeValue1362, nodeValue1367, nodeValue1422, nodeValue3038, nodeValue4092]

theorem reindexCheck290 : Integer.Sparse.reindex keyMap MixedData.row290 = numericRow290 := by decide +kernel

theorem numericCheck290 (x : Master → ℝ) : Integer.Sparse.eval numericRow290 x =
    (1 : ℝ) * reducedSource290 x := by
  norm_num [numericRow290, reducedSource290, Integer.Sparse.eval, Sparse.eval, nodeValue1367, nodeValue2881, nodeValue2974, nodeValue3038, nodeValue3051, nodeValue3054, nodeValue4092]

theorem reindexCheck291 : Integer.Sparse.reindex keyMap MixedData.row291 = numericRow291 := by decide +kernel

theorem numericCheck291 (x : Master → ℝ) : Integer.Sparse.eval numericRow291 x =
    (1 : ℝ) * reducedSource291 x := by
  norm_num [numericRow291, reducedSource291, Integer.Sparse.eval, Sparse.eval, nodeValue2579, nodeValue2582, nodeValue3007, nodeValue3010, nodeValue3038, nodeValue3854, nodeValue4092]

theorem reindexCheck292 : Integer.Sparse.reindex keyMap MixedData.row292 = numericRow292 := by decide +kernel

theorem numericCheck292 (x : Master → ℝ) : Integer.Sparse.eval numericRow292 x =
    (1 : ℝ) * reducedSource292 x := by
  norm_num [numericRow292, reducedSource292, Integer.Sparse.eval, Sparse.eval, nodeValue1357, nodeValue2861, nodeValue3007, nodeValue3036, nodeValue3038, nodeValue4092]

theorem reindexCheck293 : Integer.Sparse.reindex keyMap MixedData.row293 = numericRow293 := by decide +kernel

theorem numericCheck293 (x : Master → ℝ) : Integer.Sparse.eval numericRow293 x =
    (1 : ℝ) * reducedSource293 x := by
  norm_num [numericRow293, reducedSource293, Integer.Sparse.eval, Sparse.eval, nodeValue2547, nodeValue2580, nodeValue2971, nodeValue2974, nodeValue3038, nodeValue3840, nodeValue4092]

theorem reindexCheck294 : Integer.Sparse.reindex keyMap MixedData.row294 = numericRow294 := by decide +kernel

theorem numericCheck294 (x : Master → ℝ) : Integer.Sparse.eval numericRow294 x =
    (1 : ℝ) * reducedSource294 x := by
  norm_num [numericRow294, reducedSource294, Integer.Sparse.eval, Sparse.eval, nodeValue2558, nodeValue2861, nodeValue2867, nodeValue2881, nodeValue3038, nodeValue3845, nodeValue4092]

theorem reindexCheck295 : Integer.Sparse.reindex keyMap MixedData.row295 = numericRow295 := by decide +kernel

theorem numericCheck295 (x : Master → ℝ) : Integer.Sparse.eval numericRow295 x =
    (1 : ℝ) * reducedSource295 x := by
  norm_num [numericRow295, reducedSource295, Integer.Sparse.eval, Sparse.eval, nodeValue1362, nodeValue2867, nodeValue2971, nodeValue3010, nodeValue3038, nodeValue3040, nodeValue4092]

theorem reindexCheck297 : Integer.Sparse.reindex keyMap MixedData.row297 = numericRow297 := by decide +kernel

theorem numericCheck297 (x : Master → ℝ) : Integer.Sparse.eval numericRow297 x =
    (1 : ℝ) * reducedSource297 x := by
  norm_num [numericRow297, reducedSource297, Integer.Sparse.eval, Sparse.eval, nodeValue2560, nodeValue3375, nodeValue3379, nodeValue3391, nodeValue3533, nodeValue3541, nodeValue4084]

theorem reindexCheck298 : Integer.Sparse.reindex keyMap MixedData.row298 = numericRow298 := by decide +kernel

theorem numericCheck298 (x : Master → ℝ) : Integer.Sparse.eval numericRow298 x =
    (1 : ℝ) * reducedSource298 x := by
  norm_num [numericRow298, reducedSource298, Integer.Sparse.eval, Sparse.eval, nodeValue2034, nodeValue2037, nodeValue2039, nodeValue2058, nodeValue2279, nodeValue3541, nodeValue4084]

theorem reindexCheck299 : Integer.Sparse.reindex keyMap MixedData.row299 = numericRow299 := by decide +kernel

theorem numericCheck299 (x : Master → ℝ) : Integer.Sparse.eval numericRow299 x =
    (1 : ℝ) * reducedSource299 x := by
  norm_num [numericRow299, reducedSource299, Integer.Sparse.eval, Sparse.eval, nodeValue3151, nodeValue3379, nodeValue3382, nodeValue3383, nodeValue3395, nodeValue3541, nodeValue4084]

theorem reindexCheck300 : Integer.Sparse.reindex keyMap MixedData.row300 = numericRow300 := by decide +kernel

theorem numericCheck300 (x : Master → ℝ) : Integer.Sparse.eval numericRow300 x =
    (1 : ℝ) * reducedSource300 x := by
  norm_num [numericRow300, reducedSource300, Integer.Sparse.eval, Sparse.eval, nodeValue2034, nodeValue2555, nodeValue3382, nodeValue3528, nodeValue3539, nodeValue3541, nodeValue4084]

theorem reindexCheck302 : Integer.Sparse.reindex keyMap MixedData.row302 = numericRow302 := by decide +kernel

theorem numericCheck302 (x : Master → ℝ) : Integer.Sparse.eval numericRow302 x =
    (1 : ℝ) * reducedSource302 x := by
  norm_num [numericRow302, reducedSource302, Integer.Sparse.eval, Sparse.eval, nodeValue2709, nodeValue3800, nodeValue3871, nodeValue3901, nodeValue3902, nodeValue4091]

theorem reindexCheck303 : Integer.Sparse.reindex keyMap MixedData.row303 = numericRow303 := by decide +kernel

theorem numericCheck303 (x : Master → ℝ) : Integer.Sparse.eval numericRow303 x =
    (1 : ℝ) * reducedSource303 x := by
  norm_num [numericRow303, reducedSource303, Integer.Sparse.eval, Sparse.eval, nodeValue1206, nodeValue1208, nodeValue1213, nodeValue1247, nodeValue2709, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource288 (mixedVector B) = 0 := by
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h3857 : mixedVector B (Sum.inr 3857) = Sparse.eval nodeValue3857 (mixedVector B) := by
    change mixedMoment B node3857 node3857Labels = _
    exact sound3857 B hB hF
  have h3907 : mixedVector B (Sum.inr 3907) = Sparse.eval nodeValue3907 (mixedVector B) := by
    change mixedMoment B node3907 node3907Labels = _
    exact sound3907 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm343, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3038, h3840, h3845, h3854, h3857, h3907, h4092, reducedSource288] using sourceEq343 B hB

theorem rowSound288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row288 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck288, numericCheck288, reducedZero288 B hB hF, mul_zero]

theorem reducedZero289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource289 (mixedVector B) = 0 := by
  have h1357 : mixedVector B (Sum.inr 1357) = Sparse.eval nodeValue1357 (mixedVector B) := by
    change mixedMoment B node1357 node1357Labels = _
    exact sound1357 B hB hF
  have h1359 : mixedVector B (Sum.inr 1359) = Sparse.eval nodeValue1359 (mixedVector B) := by
    change mixedMoment B node1359 node1359Labels = _
    exact sound1359 B hB hF
  have h1362 : mixedVector B (Sum.inr 1362) = Sparse.eval nodeValue1362 (mixedVector B) := by
    change mixedMoment B node1362 node1362Labels = _
    exact sound1362 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h1422 : mixedVector B (Sum.inr 1422) = Sparse.eval nodeValue1422 (mixedVector B) := by
    change mixedMoment B node1422 node1422Labels = _
    exact sound1422 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm344, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1357, h1359, h1362, h1367, h1422, h3038, h4092, reducedSource289] using sourceEq344 B hB

theorem rowSound289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row289 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck289, numericCheck289, reducedZero289 B hB hF, mul_zero]

theorem reducedZero290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource290 (mixedVector B) = 0 := by
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3051 : mixedVector B (Sum.inr 3051) = Sparse.eval nodeValue3051 (mixedVector B) := by
    change mixedMoment B node3051 node3051Labels = _
    exact sound3051 B hB hF
  have h3054 : mixedVector B (Sum.inr 3054) = Sparse.eval nodeValue3054 (mixedVector B) := by
    change mixedMoment B node3054 node3054Labels = _
    exact sound3054 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm345, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1367, h2881, h2974, h3038, h3051, h3054, h4092, reducedSource290] using sourceEq345 B hB

theorem rowSound290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row290 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck290, numericCheck290, reducedZero290 B hB hF, mul_zero]

theorem reducedZero291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource291 (mixedVector B) = 0 := by
  have h2579 : mixedVector B (Sum.inr 2579) = Sparse.eval nodeValue2579 (mixedVector B) := by
    change mixedMoment B node2579 node2579Labels = _
    exact sound2579 B hB hF
  have h2582 : mixedVector B (Sum.inr 2582) = Sparse.eval nodeValue2582 (mixedVector B) := by
    change mixedMoment B node2582 node2582Labels = _
    exact sound2582 B hB hF
  have h3007 : mixedVector B (Sum.inr 3007) = Sparse.eval nodeValue3007 (mixedVector B) := by
    change mixedMoment B node3007 node3007Labels = _
    exact sound3007 B hB hF
  have h3010 : mixedVector B (Sum.inr 3010) = Sparse.eval nodeValue3010 (mixedVector B) := by
    change mixedMoment B node3010 node3010Labels = _
    exact sound3010 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3854 : mixedVector B (Sum.inr 3854) = Sparse.eval nodeValue3854 (mixedVector B) := by
    change mixedMoment B node3854 node3854Labels = _
    exact sound3854 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm346, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2579, h2582, h3007, h3010, h3038, h3854, h4092, reducedSource291] using sourceEq346 B hB

theorem rowSound291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row291 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck291, numericCheck291, reducedZero291 B hB hF, mul_zero]

theorem reducedZero292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource292 (mixedVector B) = 0 := by
  have h1357 : mixedVector B (Sum.inr 1357) = Sparse.eval nodeValue1357 (mixedVector B) := by
    change mixedMoment B node1357 node1357Labels = _
    exact sound1357 B hB hF
  have h2861 : mixedVector B (Sum.inr 2861) = Sparse.eval nodeValue2861 (mixedVector B) := by
    change mixedMoment B node2861 node2861Labels = _
    exact sound2861 B hB hF
  have h3007 : mixedVector B (Sum.inr 3007) = Sparse.eval nodeValue3007 (mixedVector B) := by
    change mixedMoment B node3007 node3007Labels = _
    exact sound3007 B hB hF
  have h3036 : mixedVector B (Sum.inr 3036) = Sparse.eval nodeValue3036 (mixedVector B) := by
    change mixedMoment B node3036 node3036Labels = _
    exact sound3036 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm347, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1357, h2861, h3007, h3036, h3038, h4092, reducedSource292] using sourceEq347 B hB

theorem rowSound292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row292 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck292, numericCheck292, reducedZero292 B hB hF, mul_zero]

theorem reducedZero293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource293 (mixedVector B) = 0 := by
  have h2547 : mixedVector B (Sum.inr 2547) = Sparse.eval nodeValue2547 (mixedVector B) := by
    change mixedMoment B node2547 node2547Labels = _
    exact sound2547 B hB hF
  have h2580 : mixedVector B (Sum.inr 2580) = Sparse.eval nodeValue2580 (mixedVector B) := by
    change mixedMoment B node2580 node2580Labels = _
    exact sound2580 B hB hF
  have h2971 : mixedVector B (Sum.inr 2971) = Sparse.eval nodeValue2971 (mixedVector B) := by
    change mixedMoment B node2971 node2971Labels = _
    exact sound2971 B hB hF
  have h2974 : mixedVector B (Sum.inr 2974) = Sparse.eval nodeValue2974 (mixedVector B) := by
    change mixedMoment B node2974 node2974Labels = _
    exact sound2974 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3840 : mixedVector B (Sum.inr 3840) = Sparse.eval nodeValue3840 (mixedVector B) := by
    change mixedMoment B node3840 node3840Labels = _
    exact sound3840 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm348, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2547, h2580, h2971, h2974, h3038, h3840, h4092, reducedSource293] using sourceEq348 B hB

theorem rowSound293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row293 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck293, numericCheck293, reducedZero293 B hB hF, mul_zero]

theorem reducedZero294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource294 (mixedVector B) = 0 := by
  have h2558 : mixedVector B (Sum.inr 2558) = Sparse.eval nodeValue2558 (mixedVector B) := by
    change mixedMoment B node2558 node2558Labels = _
    exact sound2558 B hB hF
  have h2861 : mixedVector B (Sum.inr 2861) = Sparse.eval nodeValue2861 (mixedVector B) := by
    change mixedMoment B node2861 node2861Labels = _
    exact sound2861 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3845 : mixedVector B (Sum.inr 3845) = Sparse.eval nodeValue3845 (mixedVector B) := by
    change mixedMoment B node3845 node3845Labels = _
    exact sound3845 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm349, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2558, h2861, h2867, h2881, h3038, h3845, h4092, reducedSource294] using sourceEq349 B hB

theorem rowSound294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row294 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck294, numericCheck294, reducedZero294 B hB hF, mul_zero]

theorem reducedZero295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource295 (mixedVector B) = 0 := by
  have h1362 : mixedVector B (Sum.inr 1362) = Sparse.eval nodeValue1362 (mixedVector B) := by
    change mixedMoment B node1362 node1362Labels = _
    exact sound1362 B hB hF
  have h2867 : mixedVector B (Sum.inr 2867) = Sparse.eval nodeValue2867 (mixedVector B) := by
    change mixedMoment B node2867 node2867Labels = _
    exact sound2867 B hB hF
  have h2971 : mixedVector B (Sum.inr 2971) = Sparse.eval nodeValue2971 (mixedVector B) := by
    change mixedMoment B node2971 node2971Labels = _
    exact sound2971 B hB hF
  have h3010 : mixedVector B (Sum.inr 3010) = Sparse.eval nodeValue3010 (mixedVector B) := by
    change mixedMoment B node3010 node3010Labels = _
    exact sound3010 B hB hF
  have h3038 : mixedVector B (Sum.inr 3038) = Sparse.eval nodeValue3038 (mixedVector B) := by
    change mixedMoment B node3038 node3038Labels = _
    exact sound3038 B hB hF
  have h3040 : mixedVector B (Sum.inr 3040) = Sparse.eval nodeValue3040 (mixedVector B) := by
    change mixedMoment B node3040 node3040Labels = _
    exact sound3040 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm350, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1362, h2867, h2971, h3010, h3038, h3040, h4092, reducedSource295] using sourceEq350 B hB

theorem rowSound295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row295 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck295, numericCheck295, reducedZero295 B hB hF, mul_zero]

theorem reducedZero297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource297 (mixedVector B) = 0 := by
  have h2560 : mixedVector B (Sum.inr 2560) = Sparse.eval nodeValue2560 (mixedVector B) := by
    change mixedMoment B node2560 node2560Labels = _
    exact sound2560 B hB hF
  have h3375 : mixedVector B (Sum.inr 3375) = Sparse.eval nodeValue3375 (mixedVector B) := by
    change mixedMoment B node3375 node3375Labels = _
    exact sound3375 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3391 : mixedVector B (Sum.inr 3391) = Sparse.eval nodeValue3391 (mixedVector B) := by
    change mixedMoment B node3391 node3391Labels = _
    exact sound3391 B hB hF
  have h3533 : mixedVector B (Sum.inr 3533) = Sparse.eval nodeValue3533 (mixedVector B) := by
    change mixedMoment B node3533 node3533Labels = _
    exact sound3533 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm354, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2560, h3375, h3379, h3391, h3533, h3541, h4084, reducedSource297] using sourceEq354 B hB

theorem rowSound297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row297 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck297, numericCheck297, reducedZero297 B hB hF, mul_zero]

theorem reducedZero298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource298 (mixedVector B) = 0 := by
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2037 : mixedVector B (Sum.inr 2037) = Sparse.eval nodeValue2037 (mixedVector B) := by
    change mixedMoment B node2037 node2037Labels = _
    exact sound2037 B hB hF
  have h2039 : mixedVector B (Sum.inr 2039) = Sparse.eval nodeValue2039 (mixedVector B) := by
    change mixedMoment B node2039 node2039Labels = _
    exact sound2039 B hB hF
  have h2058 : mixedVector B (Sum.inr 2058) = Sparse.eval nodeValue2058 (mixedVector B) := by
    change mixedMoment B node2058 node2058Labels = _
    exact sound2058 B hB hF
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm355, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2034, h2037, h2039, h2058, h2279, h3541, h4084, reducedSource298] using sourceEq355 B hB

theorem rowSound298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row298 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck298, numericCheck298, reducedZero298 B hB hF, mul_zero]

theorem reducedZero299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource299 (mixedVector B) = 0 := by
  have h3151 : mixedVector B (Sum.inr 3151) = Sparse.eval nodeValue3151 (mixedVector B) := by
    change mixedMoment B node3151 node3151Labels = _
    exact sound3151 B hB hF
  have h3379 : mixedVector B (Sum.inr 3379) = Sparse.eval nodeValue3379 (mixedVector B) := by
    change mixedMoment B node3379 node3379Labels = _
    exact sound3379 B hB hF
  have h3382 : mixedVector B (Sum.inr 3382) = Sparse.eval nodeValue3382 (mixedVector B) := by
    change mixedMoment B node3382 node3382Labels = _
    exact sound3382 B hB hF
  have h3383 : mixedVector B (Sum.inr 3383) = Sparse.eval nodeValue3383 (mixedVector B) := by
    change mixedMoment B node3383 node3383Labels = _
    exact sound3383 B hB hF
  have h3395 : mixedVector B (Sum.inr 3395) = Sparse.eval nodeValue3395 (mixedVector B) := by
    change mixedMoment B node3395 node3395Labels = _
    exact sound3395 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm356, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3151, h3379, h3382, h3383, h3395, h3541, h4084, reducedSource299] using sourceEq356 B hB

theorem rowSound299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row299 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck299, numericCheck299, reducedZero299 B hB hF, mul_zero]

theorem reducedZero300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource300 (mixedVector B) = 0 := by
  have h2034 : mixedVector B (Sum.inr 2034) = Sparse.eval nodeValue2034 (mixedVector B) := by
    change mixedMoment B node2034 node2034Labels = _
    exact sound2034 B hB hF
  have h2555 : mixedVector B (Sum.inr 2555) = Sparse.eval nodeValue2555 (mixedVector B) := by
    change mixedMoment B node2555 node2555Labels = _
    exact sound2555 B hB hF
  have h3382 : mixedVector B (Sum.inr 3382) = Sparse.eval nodeValue3382 (mixedVector B) := by
    change mixedMoment B node3382 node3382Labels = _
    exact sound3382 B hB hF
  have h3528 : mixedVector B (Sum.inr 3528) = Sparse.eval nodeValue3528 (mixedVector B) := by
    change mixedMoment B node3528 node3528Labels = _
    exact sound3528 B hB hF
  have h3539 : mixedVector B (Sum.inr 3539) = Sparse.eval nodeValue3539 (mixedVector B) := by
    change mixedMoment B node3539 node3539Labels = _
    exact sound3539 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm357, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2034, h2555, h3382, h3528, h3539, h3541, h4084, reducedSource300] using sourceEq357 B hB

theorem rowSound300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row300 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck300, numericCheck300, reducedZero300 B hB hF, mul_zero]

theorem reducedZero302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource302 (mixedVector B) = 0 := by
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h3800 : mixedVector B (Sum.inr 3800) = Sparse.eval nodeValue3800 (mixedVector B) := by
    change mixedMoment B node3800 node3800Labels = _
    exact sound3800 B hB hF
  have h3871 : mixedVector B (Sum.inr 3871) = Sparse.eval nodeValue3871 (mixedVector B) := by
    change mixedMoment B node3871 node3871Labels = _
    exact sound3871 B hB hF
  have h3901 : mixedVector B (Sum.inr 3901) = Sparse.eval nodeValue3901 (mixedVector B) := by
    change mixedMoment B node3901 node3901Labels = _
    exact sound3901 B hB hF
  have h3902 : mixedVector B (Sum.inr 3902) = Sparse.eval nodeValue3902 (mixedVector B) := by
    change mixedMoment B node3902 node3902Labels = _
    exact sound3902 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm362, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2709, h3800, h3871, h3901, h3902, h4091, reducedSource302] using sourceEq362 B hB

theorem rowSound302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row302 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck302, numericCheck302, reducedZero302 B hB hF, mul_zero]

theorem reducedZero303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource303 (mixedVector B) = 0 := by
  have h1206 : mixedVector B (Sum.inr 1206) = Sparse.eval nodeValue1206 (mixedVector B) := by
    change mixedMoment B node1206 node1206Labels = _
    exact sound1206 B hB hF
  have h1208 : mixedVector B (Sum.inr 1208) = Sparse.eval nodeValue1208 (mixedVector B) := by
    change mixedMoment B node1208 node1208Labels = _
    exact sound1208 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1247 : mixedVector B (Sum.inr 1247) = Sparse.eval nodeValue1247 (mixedVector B) := by
    change mixedMoment B node1247 node1247Labels = _
    exact sound1247 B hB hF
  have h2709 : mixedVector B (Sum.inr 2709) = Sparse.eval nodeValue2709 (mixedVector B) := by
    change mixedMoment B node2709 node2709Labels = _
    exact sound2709 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm363, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1206, h1208, h1213, h1247, h2709, h4091, reducedSource303] using sourceEq363 B hB

theorem rowSound303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row303 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck303, numericCheck303, reducedZero303 B hB hF, mul_zero]

theorem sourceRowsAt288 : MixedData.sourceRows (288 : Fin 2425) =
    MixedData.row288 := by decide +kernel

theorem sourceRowsAt289 : MixedData.sourceRows (289 : Fin 2425) =
    MixedData.row289 := by decide +kernel

theorem sourceRowsAt290 : MixedData.sourceRows (290 : Fin 2425) =
    MixedData.row290 := by decide +kernel

theorem sourceRowsAt291 : MixedData.sourceRows (291 : Fin 2425) =
    MixedData.row291 := by decide +kernel

theorem sourceRowsAt292 : MixedData.sourceRows (292 : Fin 2425) =
    MixedData.row292 := by decide +kernel

theorem sourceRowsAt293 : MixedData.sourceRows (293 : Fin 2425) =
    MixedData.row293 := by decide +kernel

theorem sourceRowsAt294 : MixedData.sourceRows (294 : Fin 2425) =
    MixedData.row294 := by decide +kernel

theorem sourceRowsAt295 : MixedData.sourceRows (295 : Fin 2425) =
    MixedData.row295 := by decide +kernel

theorem sourceRowsAt296 : MixedData.sourceRows (296 : Fin 2425) =
    MixedData.row296 := by decide +kernel

theorem sourceRowsAt297 : MixedData.sourceRows (297 : Fin 2425) =
    MixedData.row297 := by decide +kernel

theorem sourceRowsAt298 : MixedData.sourceRows (298 : Fin 2425) =
    MixedData.row298 := by decide +kernel

theorem sourceRowsAt299 : MixedData.sourceRows (299 : Fin 2425) =
    MixedData.row299 := by decide +kernel

theorem sourceRowsAt300 : MixedData.sourceRows (300 : Fin 2425) =
    MixedData.row300 := by decide +kernel

theorem sourceRowsAt301 : MixedData.sourceRows (301 : Fin 2425) =
    MixedData.row301 := by decide +kernel

theorem sourceRowsAt302 : MixedData.sourceRows (302 : Fin 2425) =
    MixedData.row302 := by decide +kernel

theorem sourceRowsAt303 : MixedData.sourceRows (303 : Fin 2425) =
    MixedData.row303 := by decide +kernel

theorem chunkSound18_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 18) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 288 ∨ k.val = 289 ∨ k.val = 290 ∨ k.val = 291 ∨ k.val = 292 ∨ k.val = 293 ∨ k.val = 294 ∨ k.val = 295 ∨ k.val = 296 ∨ k.val = 297 ∨ k.val = 298 ∨ k.val = 299 ∨ k.val = 300 ∨ k.val = 301 ∨ k.val = 302 ∨ k.val = 303 := by omega
  rcases heq with h288 | h289 | h290 | h291 | h292 | h293 | h294 | h295 | h296 | h297 | h298 | h299 | h300 | h301 | h302 | h303
  · have he : k = (288 : Fin 2425) := Fin.ext h288
    subst k
    rw [sourceRowsAt288]
    exact rowSound288 B hB hF
  · have he : k = (289 : Fin 2425) := Fin.ext h289
    subst k
    rw [sourceRowsAt289]
    exact rowSound289 B hB hF
  · have he : k = (290 : Fin 2425) := Fin.ext h290
    subst k
    rw [sourceRowsAt290]
    exact rowSound290 B hB hF
  · have he : k = (291 : Fin 2425) := Fin.ext h291
    subst k
    rw [sourceRowsAt291]
    exact rowSound291 B hB hF
  · have he : k = (292 : Fin 2425) := Fin.ext h292
    subst k
    rw [sourceRowsAt292]
    exact rowSound292 B hB hF
  · have he : k = (293 : Fin 2425) := Fin.ext h293
    subst k
    rw [sourceRowsAt293]
    exact rowSound293 B hB hF
  · have he : k = (294 : Fin 2425) := Fin.ext h294
    subst k
    rw [sourceRowsAt294]
    exact rowSound294 B hB hF
  · have he : k = (295 : Fin 2425) := Fin.ext h295
    subst k
    rw [sourceRowsAt295]
    exact rowSound295 B hB hF
  · have he : k = (296 : Fin 2425) := Fin.ext h296
    subst k
    rw [sourceRowsAt296]
    exact rowSound296_e B hB hF
  · have he : k = (297 : Fin 2425) := Fin.ext h297
    subst k
    rw [sourceRowsAt297]
    exact rowSound297 B hB hF
  · have he : k = (298 : Fin 2425) := Fin.ext h298
    subst k
    rw [sourceRowsAt298]
    exact rowSound298 B hB hF
  · have he : k = (299 : Fin 2425) := Fin.ext h299
    subst k
    rw [sourceRowsAt299]
    exact rowSound299 B hB hF
  · have he : k = (300 : Fin 2425) := Fin.ext h300
    subst k
    rw [sourceRowsAt300]
    exact rowSound300 B hB hF
  · have he : k = (301 : Fin 2425) := Fin.ext h301
    subst k
    rw [sourceRowsAt301]
    exact rowSound301_e B hB hF
  · have he : k = (302 : Fin 2425) := Fin.ext h302
    subst k
    rw [sourceRowsAt302]
    exact rowSound302 B hB hF
  · have he : k = (303 : Fin 2425) := Fin.ext h303
    subst k
    rw [sourceRowsAt303]
    exact rowSound303 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound18_e_oai
