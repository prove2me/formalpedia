-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:06:09.528283+00:00
-- url     : https://prove2.me/submissions/f71dd5a9-ecd7-41cb-8976-f58e4324d5dc

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
import Definitions.Def_OAIQ106E127
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound438_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound444_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound445_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound446_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound447_e

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

theorem canonical5752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5752 raw5752Labels = mixedMoment B node3576 node3576Labels := by
  calc
    mixedMoment B raw5752 raw5752Labels = mixedMoment B raw5752step0 raw5752step0Labels := by
      have ha : raw5752step0 = (fun i j => raw5752 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5752step0 raw5752; decide +kernel
      have hl : raw5752step0Labels = raw5752Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5752 raw5752Labels permutation240 permutation4
    mixedMoment B raw5752step0 raw5752step0Labels = mixedMoment B raw5752step1 raw5752step1Labels := by
      have ha : raw5752step1 = -raw5752step0 := by apply Matrix.ext; change ∀ i j, raw5752step1 i j = -(raw5752step0 i j); unfold raw5752step1 raw5752step0; decide +kernel
      have hl : raw5752step1Labels = raw5752step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3576 node3576Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5767 raw5767Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw5767 raw5767Labels = mixedMoment B raw5767step0 raw5767step0Labels := by
      have ha : raw5767step0 = (fun i j => raw5767 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5767step0 raw5767; decide +kernel
      have hl : raw5767step0Labels = raw5767Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5767 raw5767Labels permutation224 permutation4
    mixedMoment B raw5767step0 raw5767step0Labels = mixedMoment B raw5767step1 raw5767step1Labels := by
      have ha : raw5767step1 = -raw5767step0 := by apply Matrix.ext; change ∀ i j, raw5767step1 i j = -(raw5767step0 i j); unfold raw5767step1 raw5767step0; decide +kernel
      have hl : raw5767step1Labels = raw5767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2104 node2104Labels := by rfl

theorem canonical5768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5768 raw5768Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5768 raw5768Labels = mixedMoment B raw5768step0 raw5768step0Labels := by
      have hz : ∀ j, raw5768 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5768step0 = (fun i j => raw5768 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5768step0 raw5768; decide +kernel
      have hl : raw5768step0Labels = raw5768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5768 raw5768Labels permutation265 hz
    mixedMoment B raw5768step0 raw5768step0Labels = mixedMoment B raw5768step1 raw5768step1Labels := by
      have ha : raw5768step1 = (fun i j => raw5768step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5768step1 raw5768step0; decide +kernel
      have hl : raw5768step1Labels = raw5768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5768step0 raw5768step0Labels permutation44 permutation4
    mixedMoment B raw5768step1 raw5768step1Labels = mixedMoment B raw5768step2 raw5768step2Labels := by
      have ha : raw5768step2 = -raw5768step1 := by apply Matrix.ext; change ∀ i j, raw5768step2 i j = -(raw5768step1 i j); unfold raw5768step2 raw5768step1; decide +kernel
      have hl : raw5768step2Labels = raw5768step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

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

theorem canonical7277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7277 raw7277Labels = mixedMoment B node3494 node3494Labels := by
  calc
    mixedMoment B raw7277 raw7277Labels = mixedMoment B raw7277step0 raw7277step0Labels := by
      have ha : raw7277step0 = (fun i j => raw7277 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7277step0 raw7277; decide +kernel
      have hl : raw7277step0Labels = raw7277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7277 raw7277Labels permutation183 permutation2
    mixedMoment B raw7277step0 raw7277step0Labels = mixedMoment B raw7277step1 raw7277step1Labels := by
      have ha : raw7277step1 = -raw7277step0 := by apply Matrix.ext; change ∀ i j, raw7277step1 i j = -(raw7277step0 i j); unfold raw7277step1 raw7277step0; decide +kernel
      have hl : raw7277step1Labels = raw7277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3494 node3494Labels := by rfl

theorem canonical7283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7283 raw7283Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7283 raw7283Labels = mixedMoment B raw7283step0 raw7283step0Labels := by
      have hz : ∀ j, raw7283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7283step0 = (fun i j => raw7283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7283step0 raw7283; decide +kernel
      have hl : raw7283step0Labels = raw7283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7283 raw7283Labels permutation265 hz
    mixedMoment B raw7283step0 raw7283step0Labels = mixedMoment B raw7283step1 raw7283step1Labels := by
      have ha : raw7283step1 = (fun i j => raw7283step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7283step1 raw7283step0; decide +kernel
      have hl : raw7283step1Labels = raw7283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7283step0 raw7283step0Labels permutation44 permutation4
    mixedMoment B raw7283step1 raw7283step1Labels = mixedMoment B raw7283step2 raw7283step2Labels := by
      have ha : raw7283step2 = -raw7283step1 := by apply Matrix.ext; change ∀ i j, raw7283step2 i j = -(raw7283step1 i j); unfold raw7283step2 raw7283step1; decide +kernel
      have hl : raw7283step2Labels = raw7283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical7289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7289 raw7289Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw7289 raw7289Labels = mixedMoment B raw7289step0 raw7289step0Labels := by
      have ha : raw7289step0 = (fun i j => raw7289 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7289step0 raw7289; decide +kernel
      have hl : raw7289step0Labels = raw7289Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7289 raw7289Labels permutation164 permutation4
    mixedMoment B raw7289step0 raw7289step0Labels = mixedMoment B raw7289step1 raw7289step1Labels := by
      have ha : raw7289step1 = -raw7289step0 := by apply Matrix.ext; change ∀ i j, raw7289step1 i j = -(raw7289step0 i j); unfold raw7289step1 raw7289step0; decide +kernel
      have hl : raw7289step1Labels = raw7289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3502 node3502Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7959 raw7959Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw7959 raw7959Labels = mixedMoment B raw7959step0 raw7959step0Labels := by
      have hz : ∀ j, raw7959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7959step0 = (fun i j => raw7959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7959step0 raw7959; decide +kernel
      have hl : raw7959step0Labels = raw7959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959 raw7959Labels permutation346 hz
    mixedMoment B raw7959step0 raw7959step0Labels = mixedMoment B raw7959step1 raw7959step1Labels := by
      have hz : ∀ j, raw7959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7959step1 = (fun i j => raw7959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7959step1 raw7959step0; decide +kernel
      have hl : raw7959step1Labels = raw7959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7959step0 raw7959step0Labels permutation56 hz
    mixedMoment B raw7959step1 raw7959step1Labels = mixedMoment B raw7959step2 raw7959step2Labels := by
      have ha : raw7959step2 = (fun i j => raw7959step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7959step2 raw7959step1; decide +kernel
      have hl : raw7959step2Labels = raw7959step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7959step1 raw7959step1Labels permutation9 permutation2
    mixedMoment B raw7959step2 raw7959step2Labels = mixedMoment B raw7959step3 raw7959step3Labels := by
      have ha : raw7959step3 = -raw7959step2 := by apply Matrix.ext; change ∀ i j, raw7959step3 i j = -(raw7959step2 i j); unfold raw7959step3 raw7959step2; decide +kernel
      have hl : raw7959step3Labels = raw7959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical7965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7965 raw7965Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw7965 raw7965Labels = mixedMoment B raw7965step0 raw7965step0Labels := by
      have hz : ∀ j, raw7965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7965step0 = (fun i j => raw7965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7965step0 raw7965; decide +kernel
      have hl : raw7965step0Labels = raw7965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7965 raw7965Labels permutation346 hz
    mixedMoment B raw7965step0 raw7965step0Labels = mixedMoment B raw7965step1 raw7965step1Labels := by
      have ha : raw7965step1 = (fun i j => raw7965step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7965step1 raw7965step0; decide +kernel
      have hl : raw7965step1Labels = raw7965step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7965step0 raw7965step0Labels permutation44 permutation4
    mixedMoment B raw7965step1 raw7965step1Labels = mixedMoment B raw7965step2 raw7965step2Labels := by
      have ha : raw7965step2 = -raw7965step1 := by apply Matrix.ext; change ∀ i j, raw7965step2 i j = -(raw7965step1 i j); unfold raw7965step2 raw7965step1; decide +kernel
      have hl : raw7965step2Labels = raw7965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical7966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7966 raw7966Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw7966 raw7966Labels = mixedMoment B raw7966step0 raw7966step0Labels := by
      have hz : ∀ j, raw7966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7966step0 = (fun i j => raw7966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7966step0 raw7966; decide +kernel
      have hl : raw7966step0Labels = raw7966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966 raw7966Labels permutation346 hz
    mixedMoment B raw7966step0 raw7966step0Labels = mixedMoment B raw7966step1 raw7966step1Labels := by
      have hz : ∀ j, raw7966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7966step1 = (fun i j => raw7966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7966step1 raw7966step0; decide +kernel
      have hl : raw7966step1Labels = raw7966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7966step0 raw7966step0Labels permutation56 hz
    mixedMoment B raw7966step1 raw7966step1Labels = mixedMoment B raw7966step2 raw7966step2Labels := by
      have ha : raw7966step2 = (fun i j => raw7966step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7966step2 raw7966step1; decide +kernel
      have hl : raw7966step2Labels = raw7966step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7966step1 raw7966step1Labels permutation10 permutation4
    mixedMoment B raw7966step2 raw7966step2Labels = mixedMoment B raw7966step3 raw7966step3Labels := by
      have ha : raw7966step3 = -raw7966step2 := by apply Matrix.ext; change ∀ i j, raw7966step3 i j = -(raw7966step2 i j); unfold raw7966step3 raw7966step2; decide +kernel
      have hl : raw7966step3Labels = raw7966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8608 raw8608Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw8608 raw8608Labels = mixedMoment B raw8608step0 raw8608step0Labels := by
      have hz : ∀ j, raw8608 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8608step0 = (fun i j => raw8608 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8608step0 raw8608; decide +kernel
      have hl : raw8608step0Labels = raw8608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8608 raw8608Labels permutation265 hz
    mixedMoment B raw8608step0 raw8608step0Labels = mixedMoment B raw8608step1 raw8608step1Labels := by
      have ha : raw8608step1 = (fun i j => raw8608step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8608step1 raw8608step0; decide +kernel
      have hl : raw8608step1Labels = raw8608step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8608step0 raw8608step0Labels permutation45 permutation4
    mixedMoment B raw8608step1 raw8608step1Labels = mixedMoment B raw8608step2 raw8608step2Labels := by
      have ha : raw8608step2 = -raw8608step1 := by apply Matrix.ext; change ∀ i j, raw8608step2 i j = -(raw8608step1 i j); unfold raw8608step2 raw8608step1; decide +kernel
      have hl : raw8608step2Labels = raw8608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical8617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8617 raw8617Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw8617 raw8617Labels = mixedMoment B raw8617step0 raw8617step0Labels := by
      have hz : ∀ j, raw8617 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8617step0 = (fun i j => raw8617 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8617step0 raw8617; decide +kernel
      have hl : raw8617step0Labels = raw8617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8617 raw8617Labels permutation265 hz
    mixedMoment B raw8617step0 raw8617step0Labels = mixedMoment B raw8617step1 raw8617step1Labels := by
      have ha : raw8617step1 = (fun i j => raw8617step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8617step1 raw8617step0; decide +kernel
      have hl : raw8617step1Labels = raw8617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8617step0 raw8617step0Labels permutation124 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

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

theorem canonical9007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9007 raw9007Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw9007 raw9007Labels = mixedMoment B raw9007step0 raw9007step0Labels := by
      have hz : ∀ j, raw9007 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9007step0 = (fun i j => raw9007 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9007step0 raw9007; decide +kernel
      have hl : raw9007step0Labels = raw9007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9007 raw9007Labels permutation265 hz
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical9008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9008 raw9008Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw9008 raw9008Labels = mixedMoment B raw9008step0 raw9008step0Labels := by
      have ha : raw9008step0 = (fun i j => raw9008 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9008step0 raw9008; decide +kernel
      have hl : raw9008step0Labels = raw9008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9008 raw9008Labels permutation682 permutation2
    mixedMoment B raw9008step0 raw9008step0Labels = mixedMoment B raw9008step1 raw9008step1Labels := by
      have ha : raw9008step1 = -raw9008step0 := by apply Matrix.ext; change ∀ i j, raw9008step1 i j = -(raw9008step0 i j); unfold raw9008step1 raw9008step0; decide +kernel
      have hl : raw9008step1Labels = raw9008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

theorem canonical9009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9009 raw9009Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw9009 raw9009Labels = mixedMoment B raw9009step0 raw9009step0Labels := by
      have hz : ∀ j, raw9009 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9009step0 = (fun i j => raw9009 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9009step0 raw9009; decide +kernel
      have hl : raw9009step0Labels = raw9009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9009 raw9009Labels permutation265 hz
    mixedMoment B raw9009step0 raw9009step0Labels = mixedMoment B raw9009step1 raw9009step1Labels := by
      have ha : raw9009step1 = (fun i j => raw9009step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9009step1 raw9009step0; decide +kernel
      have hl : raw9009step1Labels = raw9009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9009step0 raw9009step0Labels permutation151 permutation2
    mixedMoment B raw9009step1 raw9009step1Labels = mixedMoment B raw9009step2 raw9009step2Labels := by
      have ha : raw9009step2 = -raw9009step1 := by apply Matrix.ext; change ∀ i j, raw9009step2 i j = -(raw9009step1 i j); unfold raw9009step2 raw9009step1; decide +kernel
      have hl : raw9009step2Labels = raw9009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical9011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9011 raw9011Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw9011 raw9011Labels = mixedMoment B raw9011step0 raw9011step0Labels := by
      have hz : ∀ j, raw9011 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9011step0 = (fun i j => raw9011 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9011step0 raw9011; decide +kernel
      have hl : raw9011step0Labels = raw9011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9011 raw9011Labels permutation265 hz
    mixedMoment B raw9011step0 raw9011step0Labels = mixedMoment B raw9011step1 raw9011step1Labels := by
      have ha : raw9011step1 = (fun i j => raw9011step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9011step1 raw9011step0; decide +kernel
      have hl : raw9011step1Labels = raw9011step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9011step0 raw9011step0Labels permutation108 permutation4
    mixedMoment B raw9011step1 raw9011step1Labels = mixedMoment B raw9011step2 raw9011step2Labels := by
      have ha : raw9011step2 = -raw9011step1 := by apply Matrix.ext; change ∀ i j, raw9011step2 i j = -(raw9011step1 i j); unfold raw9011step2 raw9011step1; decide +kernel
      have hl : raw9011step2Labels = raw9011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

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

theorem canonical9015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9015 raw9015Labels = mixedMoment B node1407 node1407Labels := by
  calc
    mixedMoment B raw9015 raw9015Labels = mixedMoment B raw9015step0 raw9015step0Labels := by
      have hz : ∀ j, raw9015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9015step0 = (fun i j => raw9015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9015step0 raw9015; decide +kernel
      have hl : raw9015step0Labels = raw9015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9015 raw9015Labels permutation265 hz
    mixedMoment B raw9015step0 raw9015step0Labels = mixedMoment B raw9015step1 raw9015step1Labels := by
      have ha : raw9015step1 = (fun i j => raw9015step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9015step1 raw9015step0; decide +kernel
      have hl : raw9015step1Labels = raw9015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9015step0 raw9015step0Labels permutation38 permutation2
    _ = mixedMoment B node1407 node1407Labels := by rfl

theorem canonical9017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9017 raw9017Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw9017 raw9017Labels = mixedMoment B raw9017step0 raw9017step0Labels := by
      have hz : ∀ j, raw9017 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9017step0 = (fun i j => raw9017 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9017step0 raw9017; decide +kernel
      have hl : raw9017step0Labels = raw9017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9017 raw9017Labels permutation265 hz
    mixedMoment B raw9017step0 raw9017step0Labels = mixedMoment B raw9017step1 raw9017step1Labels := by
      have ha : raw9017step1 = (fun i j => raw9017step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9017step1 raw9017step0; decide +kernel
      have hl : raw9017step1Labels = raw9017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9017step0 raw9017step0Labels permutation33 permutation2
    _ = mixedMoment B node1391 node1391Labels := by rfl

theorem canonical9018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9018 raw9018Labels = mixedMoment B node1389 node1389Labels := by
  calc
    mixedMoment B raw9018 raw9018Labels = mixedMoment B raw9018step0 raw9018step0Labels := by
      have hz : ∀ j, raw9018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9018step0 = (fun i j => raw9018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9018step0 raw9018; decide +kernel
      have hl : raw9018step0Labels = raw9018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9018 raw9018Labels permutation265 hz
    _ = mixedMoment B node1389 node1389Labels := by rfl

theorem canonical9019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9019 raw9019Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw9019 raw9019Labels = mixedMoment B raw9019step0 raw9019step0Labels := by
      have ha : raw9019step0 = (fun i j => raw9019 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9019step0 raw9019; decide +kernel
      have hl : raw9019step0Labels = raw9019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9019 raw9019Labels permutation182 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical9021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9021 raw9021Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw9021 raw9021Labels = mixedMoment B raw9021step0 raw9021step0Labels := by
      have ha : raw9021step0 = (fun i j => raw9021 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9021step0 raw9021; decide +kernel
      have hl : raw9021step0Labels = raw9021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9021 raw9021Labels permutation184 permutation2
    _ = mixedMoment B node3068 node3068Labels := by rfl

theorem canonical9023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9023 raw9023Labels = mixedMoment B node2985 node2985Labels := by
  calc
    mixedMoment B raw9023 raw9023Labels = mixedMoment B raw9023step0 raw9023step0Labels := by
      have ha : raw9023step0 = (fun i j => raw9023 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9023step0 raw9023; decide +kernel
      have hl : raw9023step0Labels = raw9023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9023 raw9023Labels permutation158 permutation2
    _ = mixedMoment B node2985 node2985Labels := by rfl

theorem canonical9024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9024 raw9024Labels = mixedMoment B node2985 node2985Labels := by
  calc
    _ = mixedMoment B node2985 node2985Labels := by rfl

theorem canonical9025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9025 raw9025Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw9025 raw9025Labels = mixedMoment B raw9025step0 raw9025step0Labels := by
      have ha : raw9025step0 = (fun i j => raw9025 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9025step0 raw9025; decide +kernel
      have hl : raw9025step0Labels = raw9025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9025 raw9025Labels permutation153 permutation2
    _ = mixedMoment B node2981 node2981Labels := by rfl

theorem canonical9026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9026 raw9026Labels = mixedMoment B node2857 node2857Labels := by
  calc
    mixedMoment B raw9026 raw9026Labels = mixedMoment B raw9026step0 raw9026step0Labels := by
      have ha : raw9026step0 = (fun i j => raw9026 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9026step0 raw9026; decide +kernel
      have hl : raw9026step0Labels = raw9026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9026 raw9026Labels permutation682 permutation2
    mixedMoment B raw9026step0 raw9026step0Labels = mixedMoment B raw9026step1 raw9026step1Labels := by
      have ha : raw9026step1 = -raw9026step0 := by apply Matrix.ext; change ∀ i j, raw9026step1 i j = -(raw9026step0 i j); unfold raw9026step1 raw9026step0; decide +kernel
      have hl : raw9026step1Labels = raw9026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2857 node2857Labels := by rfl

theorem canonical9027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9027 raw9027Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw9027 raw9027Labels = mixedMoment B raw9027step0 raw9027step0Labels := by
      have hz : ∀ j, raw9027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9027step0 = (fun i j => raw9027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9027step0 raw9027; decide +kernel
      have hl : raw9027step0Labels = raw9027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9027 raw9027Labels permutation265 hz
    mixedMoment B raw9027step0 raw9027step0Labels = mixedMoment B raw9027step1 raw9027step1Labels := by
      have ha : raw9027step1 = (fun i j => raw9027step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9027step1 raw9027step0; decide +kernel
      have hl : raw9027step1Labels = raw9027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9027step0 raw9027step0Labels permutation38 permutation2
    _ = mixedMoment B node2955 node2955Labels := by rfl

theorem canonical9028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9028 raw9028Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw9028 raw9028Labels = mixedMoment B raw9028step0 raw9028step0Labels := by
      have hz : ∀ j, raw9028 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9028step0 = (fun i j => raw9028 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9028step0 raw9028; decide +kernel
      have hl : raw9028step0Labels = raw9028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9028 raw9028Labels permutation265 hz
    mixedMoment B raw9028step0 raw9028step0Labels = mixedMoment B raw9028step1 raw9028step1Labels := by
      have ha : raw9028step1 = (fun i j => raw9028step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9028step1 raw9028step0; decide +kernel
      have hl : raw9028step1Labels = raw9028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9028step0 raw9028step0Labels permutation40 permutation2
    _ = mixedMoment B node3092 node3092Labels := by rfl

theorem canonical9029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9029 raw9029Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw9029 raw9029Labels = mixedMoment B raw9029step0 raw9029step0Labels := by
      have hz : ∀ j, raw9029 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9029step0 = (fun i j => raw9029 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9029step0 raw9029; decide +kernel
      have hl : raw9029step0Labels = raw9029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9029 raw9029Labels permutation265 hz
    mixedMoment B raw9029step0 raw9029step0Labels = mixedMoment B raw9029step1 raw9029step1Labels := by
      have ha : raw9029step1 = (fun i j => raw9029step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9029step1 raw9029step0; decide +kernel
      have hl : raw9029step1Labels = raw9029step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9029step0 raw9029step0Labels permutation39 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical9030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9030 raw9030Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw9030 raw9030Labels = mixedMoment B raw9030step0 raw9030step0Labels := by
      have hz : ∀ j, raw9030 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9030step0 = (fun i j => raw9030 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9030step0 raw9030; decide +kernel
      have hl : raw9030step0Labels = raw9030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9030 raw9030Labels permutation265 hz
    _ = mixedMoment B node2955 node2955Labels := by rfl

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

theorem canonical9032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9032 raw9032Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw9032 raw9032Labels = mixedMoment B raw9032step0 raw9032step0Labels := by
      have hz : ∀ j, raw9032 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9032step0 = (fun i j => raw9032 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9032step0 raw9032; decide +kernel
      have hl : raw9032step0Labels = raw9032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9032 raw9032Labels permutation265 hz
    mixedMoment B raw9032step0 raw9032step0Labels = mixedMoment B raw9032step1 raw9032step1Labels := by
      have ha : raw9032step1 = (fun i j => raw9032step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9032step1 raw9032step0; decide +kernel
      have hl : raw9032step1Labels = raw9032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9032step0 raw9032step0Labels permutation151 permutation2
    mixedMoment B raw9032step1 raw9032step1Labels = mixedMoment B raw9032step2 raw9032step2Labels := by
      have ha : raw9032step2 = -raw9032step1 := by apply Matrix.ext; change ∀ i j, raw9032step2 i j = -(raw9032step1 i j); unfold raw9032step2 raw9032step1; decide +kernel
      have hl : raw9032step2Labels = raw9032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical9033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9033 raw9033Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw9033 raw9033Labels = mixedMoment B raw9033step0 raw9033step0Labels := by
      have hz : ∀ j, raw9033 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9033step0 = (fun i j => raw9033 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9033step0 raw9033; decide +kernel
      have hl : raw9033step0Labels = raw9033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9033 raw9033Labels permutation265 hz
    mixedMoment B raw9033step0 raw9033step0Labels = mixedMoment B raw9033step1 raw9033step1Labels := by
      have ha : raw9033step1 = (fun i j => raw9033step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9033step1 raw9033step0; decide +kernel
      have hl : raw9033step1Labels = raw9033step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9033step0 raw9033step0Labels permutation39 permutation2
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical9034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9034 raw9034Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw9034 raw9034Labels = mixedMoment B raw9034step0 raw9034step0Labels := by
      have hz : ∀ j, raw9034 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9034step0 = (fun i j => raw9034 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9034step0 raw9034; decide +kernel
      have hl : raw9034step0Labels = raw9034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9034 raw9034Labels permutation265 hz
    mixedMoment B raw9034step0 raw9034step0Labels = mixedMoment B raw9034step1 raw9034step1Labels := by
      have ha : raw9034step1 = (fun i j => raw9034step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9034step1 raw9034step0; decide +kernel
      have hl : raw9034step1Labels = raw9034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9034step0 raw9034step0Labels permutation33 permutation2
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical9035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9035 raw9035Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw9035 raw9035Labels = mixedMoment B raw9035step0 raw9035step0Labels := by
      have hz : ∀ j, raw9035 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9035step0 = (fun i j => raw9035 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9035step0 raw9035; decide +kernel
      have hl : raw9035step0Labels = raw9035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9035 raw9035Labels permutation265 hz
    mixedMoment B raw9035step0 raw9035step0Labels = mixedMoment B raw9035step1 raw9035step1Labels := by
      have ha : raw9035step1 = (fun i j => raw9035step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9035step1 raw9035step0; decide +kernel
      have hl : raw9035step1Labels = raw9035step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9035step0 raw9035step0Labels permutation34 permutation2
    _ = mixedMoment B node3092 node3092Labels := by rfl

theorem canonical9036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9036 raw9036Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw9036 raw9036Labels = mixedMoment B raw9036step0 raw9036step0Labels := by
      have hz : ∀ j, raw9036 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9036step0 = (fun i j => raw9036 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9036step0 raw9036; decide +kernel
      have hl : raw9036step0Labels = raw9036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9036 raw9036Labels permutation265 hz
    mixedMoment B raw9036step0 raw9036step0Labels = mixedMoment B raw9036step1 raw9036step1Labels := by
      have ha : raw9036step1 = (fun i j => raw9036step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9036step1 raw9036step0; decide +kernel
      have hl : raw9036step1Labels = raw9036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9036step0 raw9036step0Labels permutation149 permutation2
    mixedMoment B raw9036step1 raw9036step1Labels = mixedMoment B raw9036step2 raw9036step2Labels := by
      have ha : raw9036step2 = -raw9036step1 := by apply Matrix.ext; change ∀ i j, raw9036step2 i j = -(raw9036step1 i j); unfold raw9036step2 raw9036step1; decide +kernel
      have hl : raw9036step2Labels = raw9036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3031 node3031Labels := by rfl

theorem canonical9037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9037 raw9037Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw9037 raw9037Labels = mixedMoment B raw9037step0 raw9037step0Labels := by
      have hz : ∀ j, raw9037 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9037step0 = (fun i j => raw9037 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9037step0 raw9037; decide +kernel
      have hl : raw9037step0Labels = raw9037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9037 raw9037Labels permutation265 hz
    mixedMoment B raw9037step0 raw9037step0Labels = mixedMoment B raw9037step1 raw9037step1Labels := by
      have ha : raw9037step1 = (fun i j => raw9037step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9037step1 raw9037step0; decide +kernel
      have hl : raw9037step1Labels = raw9037step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9037step0 raw9037step0Labels permutation149 permutation2
    mixedMoment B raw9037step1 raw9037step1Labels = mixedMoment B raw9037step2 raw9037step2Labels := by
      have ha : raw9037step2 = -raw9037step1 := by apply Matrix.ext; change ∀ i j, raw9037step2 i j = -(raw9037step1 i j); unfold raw9037step2 raw9037step1; decide +kernel
      have hl : raw9037step2Labels = raw9037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2865 node2865Labels := by rfl

theorem canonical9074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9074 raw9074Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw9074 raw9074Labels = mixedMoment B raw9074step0 raw9074step0Labels := by
      have hz : ∀ j, raw9074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9074step0 = (fun i j => raw9074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9074step0 raw9074; decide +kernel
      have hl : raw9074step0Labels = raw9074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9074 raw9074Labels permutation434 hz
    mixedMoment B raw9074step0 raw9074step0Labels = mixedMoment B raw9074step1 raw9074step1Labels := by
      have hz : ∀ j, raw9074step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9074step1 = (fun i j => raw9074step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9074step1 raw9074step0; decide +kernel
      have hl : raw9074step1Labels = raw9074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9074step0 raw9074step0Labels permutation56 hz
    mixedMoment B raw9074step1 raw9074step1Labels = mixedMoment B raw9074step2 raw9074step2Labels := by
      have ha : raw9074step2 = (fun i j => raw9074step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9074step2 raw9074step1; decide +kernel
      have hl : raw9074step2Labels = raw9074step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9074step1 raw9074step1Labels permutation9 permutation2
    mixedMoment B raw9074step2 raw9074step2Labels = mixedMoment B raw9074step3 raw9074step3Labels := by
      have ha : raw9074step3 = -raw9074step2 := by apply Matrix.ext; change ∀ i j, raw9074step3 i j = -(raw9074step2 i j); unfold raw9074step3 raw9074step2; decide +kernel
      have hl : raw9074step3Labels = raw9074step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical9075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9075 raw9075Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw9075 raw9075Labels = mixedMoment B raw9075step0 raw9075step0Labels := by
      have hz : ∀ j, raw9075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9075step0 = (fun i j => raw9075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9075step0 raw9075; decide +kernel
      have hl : raw9075step0Labels = raw9075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9075 raw9075Labels permutation265 hz
    mixedMoment B raw9075step0 raw9075step0Labels = mixedMoment B raw9075step1 raw9075step1Labels := by
      have ha : raw9075step1 = (fun i j => raw9075step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9075step1 raw9075step0; decide +kernel
      have hl : raw9075step1Labels = raw9075step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9075step0 raw9075step0Labels permutation125 permutation2
    _ = mixedMoment B node2879 node2879Labels := by rfl

theorem canonical9076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9076 raw9076Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw9076 raw9076Labels = mixedMoment B raw9076step0 raw9076step0Labels := by
      have hz : ∀ j, raw9076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9076step0 = (fun i j => raw9076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9076step0 raw9076; decide +kernel
      have hl : raw9076step0Labels = raw9076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9076 raw9076Labels permutation265 hz
    mixedMoment B raw9076step0 raw9076step0Labels = mixedMoment B raw9076step1 raw9076step1Labels := by
      have ha : raw9076step1 = -raw9076step0 := by apply Matrix.ext; change ∀ i j, raw9076step1 i j = -(raw9076step0 i j); unfold raw9076step1 raw9076step0; decide +kernel
      have hl : raw9076step1Labels = raw9076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3498 node3498Labels := by rfl

theorem canonical9077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9077 raw9077Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw9077 raw9077Labels = mixedMoment B raw9077step0 raw9077step0Labels := by
      have hz : ∀ j, raw9077 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9077step0 = (fun i j => raw9077 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9077step0 raw9077; decide +kernel
      have hl : raw9077step0Labels = raw9077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9077 raw9077Labels permutation265 hz
    mixedMoment B raw9077step0 raw9077step0Labels = mixedMoment B raw9077step1 raw9077step1Labels := by
      have ha : raw9077step1 = (fun i j => raw9077step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9077step1 raw9077step0; decide +kernel
      have hl : raw9077step1Labels = raw9077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9077step0 raw9077step0Labels permutation47 permutation4
    mixedMoment B raw9077step1 raw9077step1Labels = mixedMoment B raw9077step2 raw9077step2Labels := by
      have ha : raw9077step2 = -raw9077step1 := by apply Matrix.ext; change ∀ i j, raw9077step2 i j = -(raw9077step1 i j); unfold raw9077step2 raw9077step1; decide +kernel
      have hl : raw9077step2Labels = raw9077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical9078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9078 raw9078Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw9078 raw9078Labels = mixedMoment B raw9078step0 raw9078step0Labels := by
      have hz : ∀ j, raw9078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9078step0 = (fun i j => raw9078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9078step0 raw9078; decide +kernel
      have hl : raw9078step0Labels = raw9078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9078 raw9078Labels permutation265 hz
    mixedMoment B raw9078step0 raw9078step0Labels = mixedMoment B raw9078step1 raw9078step1Labels := by
      have ha : raw9078step1 = (fun i j => raw9078step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9078step1 raw9078step0; decide +kernel
      have hl : raw9078step1Labels = raw9078step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9078step0 raw9078step0Labels permutation44 permutation4
    mixedMoment B raw9078step1 raw9078step1Labels = mixedMoment B raw9078step2 raw9078step2Labels := by
      have ha : raw9078step2 = -raw9078step1 := by apply Matrix.ext; change ∀ i j, raw9078step2 i j = -(raw9078step1 i j); unfold raw9078step2 raw9078step1; decide +kernel
      have hl : raw9078step2Labels = raw9078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical9079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9079 raw9079Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw9079 raw9079Labels = mixedMoment B raw9079step0 raw9079step0Labels := by
      have hz : ∀ j, raw9079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9079step0 = (fun i j => raw9079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9079step0 raw9079; decide +kernel
      have hl : raw9079step0Labels = raw9079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9079 raw9079Labels permutation434 hz
    mixedMoment B raw9079step0 raw9079step0Labels = mixedMoment B raw9079step1 raw9079step1Labels := by
      have ha : raw9079step1 = (fun i j => raw9079step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9079step1 raw9079step0; decide +kernel
      have hl : raw9079step1Labels = raw9079step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9079step0 raw9079step0Labels permutation44 permutation4
    mixedMoment B raw9079step1 raw9079step1Labels = mixedMoment B raw9079step2 raw9079step2Labels := by
      have ha : raw9079step2 = -raw9079step1 := by apply Matrix.ext; change ∀ i j, raw9079step2 i j = -(raw9079step1 i j); unfold raw9079step2 raw9079step1; decide +kernel
      have hl : raw9079step2Labels = raw9079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical9080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9080 raw9080Labels = mixedMoment B node2877 node2877Labels := by
  calc
    mixedMoment B raw9080 raw9080Labels = mixedMoment B raw9080step0 raw9080step0Labels := by
      have ha : raw9080step0 = (fun i j => raw9080 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9080step0 raw9080; decide +kernel
      have hl : raw9080step0Labels = raw9080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9080 raw9080Labels permutation577 permutation2
    _ = mixedMoment B node2877 node2877Labels := by rfl

theorem canonical9081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9081 raw9081Labels = mixedMoment B node2883 node2883Labels := by
  calc
    mixedMoment B raw9081 raw9081Labels = mixedMoment B raw9081step0 raw9081step0Labels := by
      have hz : ∀ j, raw9081 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9081step0 = (fun i j => raw9081 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9081step0 raw9081; decide +kernel
      have hl : raw9081step0Labels = raw9081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9081 raw9081Labels permutation265 hz
    mixedMoment B raw9081step0 raw9081step0Labels = mixedMoment B raw9081step1 raw9081step1Labels := by
      have ha : raw9081step1 = (fun i j => raw9081step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9081step1 raw9081step0; decide +kernel
      have hl : raw9081step1Labels = raw9081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9081step0 raw9081step0Labels permutation126 permutation2
    _ = mixedMoment B node2883 node2883Labels := by rfl

theorem canonical9082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9082 raw9082Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw9082 raw9082Labels = mixedMoment B raw9082step0 raw9082step0Labels := by
      have hz : ∀ j, raw9082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9082step0 = (fun i j => raw9082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9082step0 raw9082; decide +kernel
      have hl : raw9082step0Labels = raw9082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9082 raw9082Labels permutation265 hz
    mixedMoment B raw9082step0 raw9082step0Labels = mixedMoment B raw9082step1 raw9082step1Labels := by
      have ha : raw9082step1 = (fun i j => raw9082step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9082step1 raw9082step0; decide +kernel
      have hl : raw9082step1Labels = raw9082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9082step0 raw9082step0Labels permutation125 permutation2
    _ = mixedMoment B node3050 node3050Labels := by rfl

theorem canonical9083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9083 raw9083Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw9083 raw9083Labels = mixedMoment B raw9083step0 raw9083step0Labels := by
      have hz : ∀ j, raw9083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9083step0 = (fun i j => raw9083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9083step0 raw9083; decide +kernel
      have hl : raw9083step0Labels = raw9083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9083 raw9083Labels permutation434 hz
    mixedMoment B raw9083step0 raw9083step0Labels = mixedMoment B raw9083step1 raw9083step1Labels := by
      have hz : ∀ j, raw9083step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9083step1 = (fun i j => raw9083step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9083step1 raw9083step0; decide +kernel
      have hl : raw9083step1Labels = raw9083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9083step0 raw9083step0Labels permutation56 hz
    mixedMoment B raw9083step1 raw9083step1Labels = mixedMoment B raw9083step2 raw9083step2Labels := by
      have ha : raw9083step2 = (fun i j => raw9083step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw9083step2 raw9083step1; decide +kernel
      have hl : raw9083step2Labels = raw9083step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9083step1 raw9083step1Labels permutation10 permutation4
    mixedMoment B raw9083step2 raw9083step2Labels = mixedMoment B raw9083step3 raw9083step3Labels := by
      have ha : raw9083step3 = -raw9083step2 := by apply Matrix.ext; change ∀ i j, raw9083step3 i j = -(raw9083step2 i j); unfold raw9083step3 raw9083step2; decide +kernel
      have hl : raw9083step3Labels = raw9083step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1389 node1389Labels = Sparse.eval nodeValue1389 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1389) = mixedMoment B node1389 node1389Labels := rfl
  simpa [nodeValue1389, Sparse.eval] using hc.symm

theorem sound1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1391 node1391Labels = Sparse.eval nodeValue1391 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1391) = mixedMoment B node1391 node1391Labels := rfl
  simpa [nodeValue1391, Sparse.eval] using hc.symm

theorem sound1407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1407 node1407Labels = Sparse.eval nodeValue1407 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1407) = mixedMoment B node1407 node1407Labels := rfl
  simpa [nodeValue1407, Sparse.eval] using hc.symm

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

theorem sound2104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2104 node2104Labels = Sparse.eval nodeValue2104 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2104) = mixedMoment B node2104 node2104Labels := rfl
  simpa [nodeValue2104, Sparse.eval] using hc.symm

theorem sound2106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2106 node2106Labels = Sparse.eval nodeValue2106 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2106) = mixedMoment B node2106 node2106Labels := rfl
  simpa [nodeValue2106, Sparse.eval] using hc.symm

theorem sound2108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2108 node2108Labels = Sparse.eval nodeValue2108 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2108) = mixedMoment B node2108 node2108Labels := rfl
  simpa [nodeValue2108, Sparse.eval] using hc.symm

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

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

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

theorem sound2857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2857 node2857Labels = Sparse.eval nodeValue2857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2857) = mixedMoment B node2857 node2857Labels := rfl
  simpa [nodeValue2857, Sparse.eval] using hc.symm

theorem sound2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2865 node2865Labels = Sparse.eval nodeValue2865 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2865) = mixedMoment B node2865 node2865Labels := rfl
  simpa [nodeValue2865, Sparse.eval] using hc.symm

theorem sound2877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2877 node2877Labels = Sparse.eval nodeValue2877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2877) = mixedMoment B node2877 node2877Labels := rfl
  simpa [nodeValue2877, Sparse.eval] using hc.symm

theorem sound2879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2879 node2879Labels = Sparse.eval nodeValue2879 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2879) = mixedMoment B node2879 node2879Labels := rfl
  simpa [nodeValue2879, Sparse.eval] using hc.symm

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

theorem sound2883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2883 node2883Labels = Sparse.eval nodeValue2883 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2883) = mixedMoment B node2883 node2883Labels := rfl
  simpa [nodeValue2883, Sparse.eval] using hc.symm

theorem sound2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2925 node2925Labels = Sparse.eval nodeValue2925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2925) = mixedMoment B node2925 node2925Labels := rfl
  simpa [nodeValue2925, Sparse.eval] using hc.symm

theorem sound2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2931 node2931Labels = Sparse.eval nodeValue2931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2931) = mixedMoment B node2931 node2931Labels := rfl
  simpa [nodeValue2931, Sparse.eval] using hc.symm

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

theorem sound2955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2955 node2955Labels = Sparse.eval nodeValue2955 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2955) = mixedMoment B node2955 node2955Labels := rfl
  simpa [nodeValue2955, Sparse.eval] using hc.symm

theorem sound2981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2981 node2981Labels = Sparse.eval nodeValue2981 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2981) = mixedMoment B node2981 node2981Labels := rfl
  simpa [nodeValue2981, Sparse.eval] using hc.symm

theorem sound2985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2985 node2985Labels = Sparse.eval nodeValue2985 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2985) = mixedMoment B node2985 node2985Labels := rfl
  simpa [nodeValue2985, Sparse.eval] using hc.symm

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

theorem sound3031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3031 node3031Labels = Sparse.eval nodeValue3031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3031) = mixedMoment B node3031 node3031Labels := rfl
  simpa [nodeValue3031, Sparse.eval] using hc.symm

theorem sound3050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3050 node3050Labels = Sparse.eval nodeValue3050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3050) = mixedMoment B node3050 node3050Labels := rfl
  simpa [nodeValue3050, Sparse.eval] using hc.symm

theorem sound3068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3068 node3068Labels = Sparse.eval nodeValue3068 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3068) = mixedMoment B node3068 node3068Labels := rfl
  simpa [nodeValue3068, Sparse.eval] using hc.symm

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

theorem sound3078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3078 node3078Labels = Sparse.eval nodeValue3078 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3078) = mixedMoment B node3078 node3078Labels := rfl
  simpa [nodeValue3078, Sparse.eval] using hc.symm

theorem sound3092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3092 node3092Labels = Sparse.eval nodeValue3092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3092) = mixedMoment B node3092 node3092Labels := rfl
  simpa [nodeValue3092, Sparse.eval] using hc.symm

theorem sound3097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3097 node3097Labels = Sparse.eval nodeValue3097 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3097) = mixedMoment B node3097 node3097Labels := rfl
  simpa [nodeValue3097, Sparse.eval] using hc.symm

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

theorem sound3494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3494 node3494Labels = Sparse.eval nodeValue3494 (mixedVector B) := by
  simpa only [nodeValue3494, Sparse.eval_nil] using zero3494 B _hB _hF

theorem sound3498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3498 node3498Labels = Sparse.eval nodeValue3498 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3498) = mixedMoment B node3498 node3498Labels := rfl
  simpa [nodeValue3498, Sparse.eval] using hc.symm

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

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3576 node3576Labels = Sparse.eval nodeValue3576 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3576) = mixedMoment B node3576 node3576Labels := rfl
  simpa [nodeValue3576, Sparse.eval] using hc.symm

theorem sound3580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3580 node3580Labels = Sparse.eval nodeValue3580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3580) = mixedMoment B node3580 node3580Labels := rfl
  simpa [nodeValue3580, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound3885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3885 node3885Labels = Sparse.eval nodeValue3885 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3885) = mixedMoment B node3885 node3885Labels := rfl
  simpa [nodeValue3885, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = 0 := by
  exact mixedMoment_alpha B hF node3953 node3953Labels 1 permutation200
    (by decide +kernel)

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

theorem sound3953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3953 node3953Labels = Sparse.eval nodeValue3953 (mixedVector B) := by
  simpa only [nodeValue3953, Sparse.eval_nil] using zero3953 B _hB _hF

theorem sound3958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3958 node3958Labels = Sparse.eval nodeValue3958 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3958) = mixedMoment B node3958 node3958Labels := rfl
  simpa [nodeValue3958, Sparse.eval] using hc.symm

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources16
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm516 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA516 + difference 0 1) (sourceB516 + difference 1 0) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3953) := by
    have ha : (tripleCharges (sourceA516 + difference 0 1) (sourceB516 + difference 1 0) sourceC516) = raw9008 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9008; decide +kernel
    rw [ha]
    exact (canonical9008 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA516 + difference 1 1) (sourceB516 + difference 1 1) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA516 + difference 1 1) (sourceB516 + difference 1 1) sourceC516) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA516 + difference 2 1) (sourceB516 + difference 1 2) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA516 + difference 2 1) (sourceB516 + difference 1 2) sourceC516) = raw9023 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9023; decide +kernel
    rw [ha]
    exact (canonical9023 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA516 + difference 3 1) (sourceB516 + difference 1 3) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA516 + difference 3 1) (sourceB516 + difference 1 3) sourceC516) = raw9024 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9024; decide +kernel
    rw [ha]
    exact (canonical9024 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA516 + difference 4 1) (sourceB516 + difference 1 4) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA516 + difference 4 1) (sourceB516 + difference 1 4) sourceC516) = raw9025 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9025; decide +kernel
    rw [ha]
    exact (canonical9025 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA516 + difference 5 1) (sourceB516 + difference 1 5) sourceC516) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2857) := by
    have ha : (tripleCharges (sourceA516 + difference 5 1) (sourceB516 + difference 1 5) sourceC516) = raw9026 := by
      apply Matrix.ext; unfold tripleCharges sourceA516 sourceB516 sourceC516 difference raw9026; decide +kernel
    rw [ha]
    exact (canonical9026 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA516 + sourceB516) sourceC516) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA516 + sourceB516) sourceC516) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA516 sourceB516 sourceC516 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA516 sourceB516 sourceC516
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm516, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm517 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA517 + difference 2 0) (sourceB517 + difference 0 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1407) := by
    have ha : (tripleCharges (sourceA517 + difference 2 0) (sourceB517 + difference 0 2) sourceC517) = raw9015 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9015; decide +kernel
    rw [ha]
    exact (canonical9015 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA517 + difference 2 1) (sourceB517 + difference 1 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2985) := by
    have ha : (tripleCharges (sourceA517 + difference 2 1) (sourceB517 + difference 1 2) sourceC517) = raw9023 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9023; decide +kernel
    rw [ha]
    exact (canonical9023 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA517 + difference 2 2) (sourceB517 + difference 2 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA517 + difference 2 2) (sourceB517 + difference 2 2) sourceC517) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA517 + difference 2 3) (sourceB517 + difference 3 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA517 + difference 2 3) (sourceB517 + difference 3 2) sourceC517) = raw9027 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9027; decide +kernel
    rw [ha]
    exact (canonical9027 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA517 + difference 2 4) (sourceB517 + difference 4 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA517 + difference 2 4) (sourceB517 + difference 4 2) sourceC517) = raw9028 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9028; decide +kernel
    rw [ha]
    exact (canonical9028 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA517 + difference 2 5) (sourceB517 + difference 5 2) sourceC517) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3097) := by
    have ha : (tripleCharges (sourceA517 + difference 2 5) (sourceB517 + difference 5 2) sourceC517) = raw9029 := by
      apply Matrix.ext; unfold tripleCharges sourceA517 sourceB517 sourceC517 difference raw9029; decide +kernel
    rw [ha]
    exact (canonical9029 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA517 + sourceB517) sourceC517) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA517 + sourceB517) sourceC517) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA517 sourceB517 sourceC517 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA517 sourceB517 sourceC517
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm517, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm518 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA518 + difference 0 2) (sourceB518 + difference 2 0) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3958) := by
    have ha : (tripleCharges (sourceA518 + difference 0 2) (sourceB518 + difference 2 0) sourceC518) = raw9009 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9009; decide +kernel
    rw [ha]
    exact (canonical9009 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA518 + difference 1 2) (sourceB518 + difference 2 1) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2925) := by
    have ha : (tripleCharges (sourceA518 + difference 1 2) (sourceB518 + difference 2 1) sourceC518) = raw9019 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9019; decide +kernel
    rw [ha]
    exact (canonical9019 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA518 + difference 2 2) (sourceB518 + difference 2 2) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA518 + difference 2 2) (sourceB518 + difference 2 2) sourceC518) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA518 + difference 3 2) (sourceB518 + difference 2 3) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2955) := by
    have ha : (tripleCharges (sourceA518 + difference 3 2) (sourceB518 + difference 2 3) sourceC518) = raw9030 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9030; decide +kernel
    rw [ha]
    exact (canonical9030 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA518 + difference 4 2) (sourceB518 + difference 2 4) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA518 + difference 4 2) (sourceB518 + difference 2 4) sourceC518) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA518 + difference 5 2) (sourceB518 + difference 2 5) sourceC518) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA518 + difference 5 2) (sourceB518 + difference 2 5) sourceC518) = raw9032 := by
      apply Matrix.ext; unfold tripleCharges sourceA518 sourceB518 sourceC518 difference raw9032; decide +kernel
    rw [ha]
    exact (canonical9032 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA518 + sourceB518) sourceC518) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA518 + sourceB518) sourceC518) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA518 sourceB518 sourceC518 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA518 sourceB518 sourceC518
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm518, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm519 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA519 + difference 4 0) (sourceB519 + difference 0 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1391) := by
    have ha : (tripleCharges (sourceA519 + difference 4 0) (sourceB519 + difference 0 4) sourceC519) = raw9017 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9017; decide +kernel
    rw [ha]
    exact (canonical9017 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA519 + difference 4 1) (sourceB519 + difference 1 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2981) := by
    have ha : (tripleCharges (sourceA519 + difference 4 1) (sourceB519 + difference 1 4) sourceC519) = raw9025 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9025; decide +kernel
    rw [ha]
    exact (canonical9025 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA519 + difference 4 2) (sourceB519 + difference 2 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA519 + difference 4 2) (sourceB519 + difference 2 4) sourceC519) = raw9031 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9031; decide +kernel
    rw [ha]
    exact (canonical9031 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA519 + difference 4 3) (sourceB519 + difference 3 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2931) := by
    have ha : (tripleCharges (sourceA519 + difference 4 3) (sourceB519 + difference 3 4) sourceC519) = raw9033 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9033; decide +kernel
    rw [ha]
    exact (canonical9033 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA519 + difference 4 4) (sourceB519 + difference 4 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA519 + difference 4 4) (sourceB519 + difference 4 4) sourceC519) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA519 + difference 4 5) (sourceB519 + difference 5 4) sourceC519) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3077) := by
    have ha : (tripleCharges (sourceA519 + difference 4 5) (sourceB519 + difference 5 4) sourceC519) = raw9034 := by
      apply Matrix.ext; unfold tripleCharges sourceA519 sourceB519 sourceC519 difference raw9034; decide +kernel
    rw [ha]
    exact (canonical9034 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA519 + sourceB519) sourceC519) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA519 + sourceB519) sourceC519) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA519 sourceB519 sourceC519 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA519 sourceB519 sourceC519
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm519, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm520 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA520 + difference 0 4) (sourceB520 + difference 4 0) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3885) := by
    have ha : (tripleCharges (sourceA520 + difference 0 4) (sourceB520 + difference 4 0) sourceC520) = raw9011 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9011; decide +kernel
    rw [ha]
    exact (canonical9011 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA520 + difference 1 4) (sourceB520 + difference 4 1) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3068) := by
    have ha : (tripleCharges (sourceA520 + difference 1 4) (sourceB520 + difference 4 1) sourceC520) = raw9021 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9021; decide +kernel
    rw [ha]
    exact (canonical9021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA520 + difference 2 4) (sourceB520 + difference 4 2) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA520 + difference 2 4) (sourceB520 + difference 4 2) sourceC520) = raw9028 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9028; decide +kernel
    rw [ha]
    exact (canonical9028 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA520 + difference 3 4) (sourceB520 + difference 4 3) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3092) := by
    have ha : (tripleCharges (sourceA520 + difference 3 4) (sourceB520 + difference 4 3) sourceC520) = raw9035 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9035; decide +kernel
    rw [ha]
    exact (canonical9035 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA520 + difference 4 4) (sourceB520 + difference 4 4) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA520 + difference 4 4) (sourceB520 + difference 4 4) sourceC520) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA520 + difference 5 4) (sourceB520 + difference 4 5) sourceC520) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA520 + difference 5 4) (sourceB520 + difference 4 5) sourceC520) = raw9036 := by
      apply Matrix.ext; unfold tripleCharges sourceA520 sourceB520 sourceC520 difference raw9036; decide +kernel
    rw [ha]
    exact (canonical9036 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA520 + sourceB520) sourceC520) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA520 + sourceB520) sourceC520) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA520 sourceB520 sourceC520 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA520 sourceB520 sourceC520
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm520, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm521 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA521 + difference 5 0) (sourceB521 + difference 0 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1389) := by
    have ha : (tripleCharges (sourceA521 + difference 5 0) (sourceB521 + difference 0 5) sourceC521) = raw9018 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9018; decide +kernel
    rw [ha]
    exact (canonical9018 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA521 + difference 5 1) (sourceB521 + difference 1 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2857) := by
    have ha : (tripleCharges (sourceA521 + difference 5 1) (sourceB521 + difference 1 5) sourceC521) = raw9026 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9026; decide +kernel
    rw [ha]
    exact (canonical9026 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA521 + difference 5 2) (sourceB521 + difference 2 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA521 + difference 5 2) (sourceB521 + difference 2 5) sourceC521) = raw9032 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9032; decide +kernel
    rw [ha]
    exact (canonical9032 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA521 + difference 5 3) (sourceB521 + difference 3 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2865) := by
    have ha : (tripleCharges (sourceA521 + difference 5 3) (sourceB521 + difference 3 5) sourceC521) = raw9037 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9037; decide +kernel
    rw [ha]
    exact (canonical9037 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA521 + difference 5 4) (sourceB521 + difference 4 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3031) := by
    have ha : (tripleCharges (sourceA521 + difference 5 4) (sourceB521 + difference 4 5) sourceC521) = raw9036 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9036; decide +kernel
    rw [ha]
    exact (canonical9036 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA521 + difference 5 5) (sourceB521 + difference 5 5) sourceC521) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3078) := by
    have ha : (tripleCharges (sourceA521 + difference 5 5) (sourceB521 + difference 5 5) sourceC521) = raw9007 := by
      apply Matrix.ext; unfold tripleCharges sourceA521 sourceB521 sourceC521 difference raw9007; decide +kernel
    rw [ha]
    exact (canonical9007 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA521 + sourceB521) sourceC521) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA521 + sourceB521) sourceC521) = raw9013 := by
      apply Matrix.ext; unfold doubleCharges sourceA521 sourceB521 sourceC521 raw9013; decide +kernel
    rw [ha]
    exact (canonical9013 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA521 sourceB521 sourceC521
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm521, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm525 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA525 + difference 0 0) (sourceB525 + difference 0 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA525 + difference 0 0) (sourceB525 + difference 0 0) sourceC525) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA525 + difference 0 1) (sourceB525 + difference 1 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3494) := by
    have ha : (tripleCharges (sourceA525 + difference 0 1) (sourceB525 + difference 1 0) sourceC525) = raw7277 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw7277; decide +kernel
    rw [ha]
    exact (canonical7277 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA525 + difference 0 2) (sourceB525 + difference 2 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA525 + difference 0 2) (sourceB525 + difference 2 0) sourceC525) = raw7959 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw7959; decide +kernel
    rw [ha]
    exact (canonical7959 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA525 + difference 0 3) (sourceB525 + difference 3 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA525 + difference 0 3) (sourceB525 + difference 3 0) sourceC525) = raw9074 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw9074; decide +kernel
    rw [ha]
    exact (canonical9074 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA525 + difference 0 4) (sourceB525 + difference 4 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA525 + difference 0 4) (sourceB525 + difference 4 0) sourceC525) = raw9075 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw9075; decide +kernel
    rw [ha]
    exact (canonical9075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA525 + difference 0 5) (sourceB525 + difference 5 0) sourceC525) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3498) := by
    have ha : (tripleCharges (sourceA525 + difference 0 5) (sourceB525 + difference 5 0) sourceC525) = raw9076 := by
      apply Matrix.ext; unfold tripleCharges sourceA525 sourceB525 sourceC525 difference raw9076; decide +kernel
    rw [ha]
    exact (canonical9076 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA525 + sourceB525) sourceC525) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA525 + sourceB525) sourceC525) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA525 sourceB525 sourceC525 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA525 sourceB525 sourceC525
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm525, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm526 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA526 + difference 0 0) (sourceB526 + difference 0 0) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA526 + difference 0 0) (sourceB526 + difference 0 0) sourceC526) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA526 + difference 1 0) (sourceB526 + difference 0 1) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA526 + difference 1 0) (sourceB526 + difference 0 1) sourceC526) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA526 + difference 2 0) (sourceB526 + difference 0 2) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA526 + difference 2 0) (sourceB526 + difference 0 2) sourceC526) = raw9077 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw9077; decide +kernel
    rw [ha]
    exact (canonical9077 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA526 + difference 3 0) (sourceB526 + difference 0 3) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2108) := by
    have ha : (tripleCharges (sourceA526 + difference 3 0) (sourceB526 + difference 0 3) sourceC526) = raw8608 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw8608; decide +kernel
    rw [ha]
    exact (canonical8608 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA526 + difference 4 0) (sourceB526 + difference 0 4) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA526 + difference 4 0) (sourceB526 + difference 0 4) sourceC526) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA526 + difference 5 0) (sourceB526 + difference 0 5) sourceC526) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA526 + difference 5 0) (sourceB526 + difference 0 5) sourceC526) = raw9078 := by
      apply Matrix.ext; unfold tripleCharges sourceA526 sourceB526 sourceC526 difference raw9078; decide +kernel
    rw [ha]
    exact (canonical9078 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA526 + sourceB526) sourceC526) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA526 + sourceB526) sourceC526) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA526 sourceB526 sourceC526 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA526 sourceB526 sourceC526
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm526, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm527 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA527 + difference 1 0) (sourceB527 + difference 0 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA527 + difference 1 0) (sourceB527 + difference 0 1) sourceC527) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA527 + difference 1 1) (sourceB527 + difference 1 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA527 + difference 1 1) (sourceB527 + difference 1 1) sourceC527) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA527 + difference 1 2) (sourceB527 + difference 2 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA527 + difference 1 2) (sourceB527 + difference 2 1) sourceC527) = raw7965 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw7965; decide +kernel
    rw [ha]
    exact (canonical7965 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA527 + difference 1 3) (sourceB527 + difference 3 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA527 + difference 1 3) (sourceB527 + difference 3 1) sourceC527) = raw9079 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw9079; decide +kernel
    rw [ha]
    exact (canonical9079 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA527 + difference 1 4) (sourceB527 + difference 4 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2877) := by
    have ha : (tripleCharges (sourceA527 + difference 1 4) (sourceB527 + difference 4 1) sourceC527) = raw9080 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw9080; decide +kernel
    rw [ha]
    exact (canonical9080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA527 + difference 1 5) (sourceB527 + difference 5 1) sourceC527) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA527 + difference 1 5) (sourceB527 + difference 5 1) sourceC527) = raw5752 := by
      apply Matrix.ext; unfold tripleCharges sourceA527 sourceB527 sourceC527 difference raw5752; decide +kernel
    rw [ha]
    exact (canonical5752 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA527 + sourceB527) sourceC527) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA527 + sourceB527) sourceC527) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA527 sourceB527 sourceC527 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA527 sourceB527 sourceC527
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm527, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq528 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm528 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA528 + difference 0 4) (sourceB528 + difference 4 0) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA528 + difference 0 4) (sourceB528 + difference 4 0) sourceC528) = raw9075 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9075; decide +kernel
    rw [ha]
    exact (canonical9075 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA528 + difference 1 4) (sourceB528 + difference 4 1) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2877) := by
    have ha : (tripleCharges (sourceA528 + difference 1 4) (sourceB528 + difference 4 1) sourceC528) = raw9080 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9080; decide +kernel
    rw [ha]
    exact (canonical9080 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA528 + difference 2 4) (sourceB528 + difference 4 2) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA528 + difference 2 4) (sourceB528 + difference 4 2) sourceC528) = raw9081 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9081; decide +kernel
    rw [ha]
    exact (canonical9081 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA528 + difference 3 4) (sourceB528 + difference 4 3) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2883) := by
    have ha : (tripleCharges (sourceA528 + difference 3 4) (sourceB528 + difference 4 3) sourceC528) = raw8617 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw8617; decide +kernel
    rw [ha]
    exact (canonical8617 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA528 + difference 4 4) (sourceB528 + difference 4 4) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA528 + difference 4 4) (sourceB528 + difference 4 4) sourceC528) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA528 + difference 5 4) (sourceB528 + difference 4 5) sourceC528) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA528 + difference 5 4) (sourceB528 + difference 4 5) sourceC528) = raw9082 := by
      apply Matrix.ext; unfold tripleCharges sourceA528 sourceB528 sourceC528 difference raw9082; decide +kernel
    rw [ha]
    exact (canonical9082 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA528 + sourceB528) sourceC528) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA528 + sourceB528) sourceC528) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA528 sourceB528 sourceC528 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA528 sourceB528 sourceC528
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm528, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq529 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm529 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA529 + difference 5 0) (sourceB529 + difference 0 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2106) := by
    have ha : (tripleCharges (sourceA529 + difference 5 0) (sourceB529 + difference 0 5) sourceC529) = raw9078 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw9078; decide +kernel
    rw [ha]
    exact (canonical9078 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA529 + difference 5 1) (sourceB529 + difference 1 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3502) := by
    have ha : (tripleCharges (sourceA529 + difference 5 1) (sourceB529 + difference 1 5) sourceC529) = raw7289 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw7289; decide +kernel
    rw [ha]
    exact (canonical7289 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA529 + difference 5 2) (sourceB529 + difference 2 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA529 + difference 5 2) (sourceB529 + difference 2 5) sourceC529) = raw7966 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw7966; decide +kernel
    rw [ha]
    exact (canonical7966 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA529 + difference 5 3) (sourceB529 + difference 3 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA529 + difference 5 3) (sourceB529 + difference 3 5) sourceC529) = raw9083 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw9083; decide +kernel
    rw [ha]
    exact (canonical9083 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA529 + difference 5 4) (sourceB529 + difference 4 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA529 + difference 5 4) (sourceB529 + difference 4 5) sourceC529) = raw9082 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw9082; decide +kernel
    rw [ha]
    exact (canonical9082 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA529 + difference 5 5) (sourceB529 + difference 5 5) sourceC529) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3580) := by
    have ha : (tripleCharges (sourceA529 + difference 5 5) (sourceB529 + difference 5 5) sourceC529) = raw7283 := by
      apply Matrix.ext; unfold tripleCharges sourceA529 sourceB529 sourceC529 difference raw7283; decide +kernel
    rw [ha]
    exact (canonical7283 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA529 + sourceB529) sourceC529) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA529 + sourceB529) sourceC529) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA529 sourceB529 sourceC529 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA529 sourceB529 sourceC529
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm529, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck432 : Integer.Sparse.reindex keyMap MixedData.row432 = numericRow432 := by decide +kernel

theorem numericCheck432 (x : Master → ℝ) : Integer.Sparse.eval numericRow432 x =
    (1 : ℝ) * reducedSource432 x := by
  norm_num [numericRow432, reducedSource432, Integer.Sparse.eval, Sparse.eval, nodeValue2857, nodeValue2981, nodeValue2985, nodeValue3078, nodeValue3953, nodeValue4091]

theorem reindexCheck433 : Integer.Sparse.reindex keyMap MixedData.row433 = numericRow433 := by decide +kernel

theorem numericCheck433 (x : Master → ℝ) : Integer.Sparse.eval numericRow433 x =
    (1 : ℝ) * reducedSource433 x := by
  norm_num [numericRow433, reducedSource433, Integer.Sparse.eval, Sparse.eval, nodeValue1407, nodeValue2955, nodeValue2985, nodeValue3078, nodeValue3092, nodeValue3097, nodeValue4091]

theorem reindexCheck434 : Integer.Sparse.reindex keyMap MixedData.row434 = numericRow434 := by decide +kernel

theorem numericCheck434 (x : Master → ℝ) : Integer.Sparse.eval numericRow434 x =
    (1 : ℝ) * reducedSource434 x := by
  norm_num [numericRow434, reducedSource434, Integer.Sparse.eval, Sparse.eval, nodeValue2865, nodeValue2925, nodeValue2931, nodeValue2955, nodeValue3078, nodeValue3958, nodeValue4091]

theorem reindexCheck435 : Integer.Sparse.reindex keyMap MixedData.row435 = numericRow435 := by decide +kernel

theorem numericCheck435 (x : Master → ℝ) : Integer.Sparse.eval numericRow435 x =
    (1 : ℝ) * reducedSource435 x := by
  norm_num [numericRow435, reducedSource435, Integer.Sparse.eval, Sparse.eval, nodeValue1391, nodeValue2931, nodeValue2981, nodeValue3077, nodeValue3078, nodeValue4091]

theorem reindexCheck436 : Integer.Sparse.reindex keyMap MixedData.row436 = numericRow436 := by decide +kernel

theorem numericCheck436 (x : Master → ℝ) : Integer.Sparse.eval numericRow436 x =
    (1 : ℝ) * reducedSource436 x := by
  norm_num [numericRow436, reducedSource436, Integer.Sparse.eval, Sparse.eval, nodeValue3031, nodeValue3068, nodeValue3078, nodeValue3092, nodeValue3885, nodeValue4091]

theorem reindexCheck437 : Integer.Sparse.reindex keyMap MixedData.row437 = numericRow437 := by decide +kernel

theorem numericCheck437 (x : Master → ℝ) : Integer.Sparse.eval numericRow437 x =
    (1 : ℝ) * reducedSource437 x := by
  norm_num [numericRow437, reducedSource437, Integer.Sparse.eval, Sparse.eval, nodeValue1389, nodeValue2857, nodeValue2865, nodeValue3031, nodeValue3078, nodeValue4091]

theorem reindexCheck439 : Integer.Sparse.reindex keyMap MixedData.row439 = numericRow439 := by decide +kernel

theorem numericCheck439 (x : Master → ℝ) : Integer.Sparse.eval numericRow439 x =
    (1 : ℝ) * reducedSource439 x := by
  norm_num [numericRow439, reducedSource439, Integer.Sparse.eval, Sparse.eval, nodeValue2879, nodeValue3494, nodeValue3498, nodeValue3548, nodeValue3580, nodeValue4084]

theorem reindexCheck440 : Integer.Sparse.reindex keyMap MixedData.row440 = numericRow440 := by decide +kernel

theorem numericCheck440 (x : Master → ℝ) : Integer.Sparse.eval numericRow440 x =
    (1 : ℝ) * reducedSource440 x := by
  norm_num [numericRow440, reducedSource440, Integer.Sparse.eval, Sparse.eval, nodeValue2104, nodeValue2106, nodeValue2108, nodeValue2262, nodeValue3580, nodeValue4084]

theorem reindexCheck441 : Integer.Sparse.reindex keyMap MixedData.row441 = numericRow441 := by decide +kernel

theorem numericCheck441 (x : Master → ℝ) : Integer.Sparse.eval numericRow441 x =
    (1 : ℝ) * reducedSource441 x := by
  norm_num [numericRow441, reducedSource441, Integer.Sparse.eval, Sparse.eval, nodeValue2104, nodeValue2877, nodeValue3576, nodeValue3580, nodeValue4084]

theorem reindexCheck442 : Integer.Sparse.reindex keyMap MixedData.row442 = numericRow442 := by decide +kernel

theorem numericCheck442 (x : Master → ℝ) : Integer.Sparse.eval numericRow442 x =
    (1 : ℝ) * reducedSource442 x := by
  norm_num [numericRow442, reducedSource442, Integer.Sparse.eval, Sparse.eval, nodeValue2877, nodeValue2879, nodeValue2883, nodeValue3050, nodeValue3580, nodeValue4084]

theorem reindexCheck443 : Integer.Sparse.reindex keyMap MixedData.row443 = numericRow443 := by decide +kernel

theorem numericCheck443 (x : Master → ℝ) : Integer.Sparse.eval numericRow443 x =
    (1 : ℝ) * reducedSource443 x := by
  norm_num [numericRow443, reducedSource443, Integer.Sparse.eval, Sparse.eval, nodeValue2106, nodeValue3050, nodeValue3502, nodeValue3580, nodeValue3582, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource432 (mixedVector B) = 0 := by
  have h2857 : mixedVector B (Sum.inr 2857) = Sparse.eval nodeValue2857 (mixedVector B) := by
    change mixedMoment B node2857 node2857Labels = _
    exact sound2857 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h2985 : mixedVector B (Sum.inr 2985) = Sparse.eval nodeValue2985 (mixedVector B) := by
    change mixedMoment B node2985 node2985Labels = _
    exact sound2985 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3953 : mixedVector B (Sum.inr 3953) = Sparse.eval nodeValue3953 (mixedVector B) := by
    change mixedMoment B node3953 node3953Labels = _
    exact sound3953 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm516, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2857, h2981, h2985, h3078, h3953, h4091, reducedSource432] using sourceEq516 B hB

theorem rowSound432 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row432 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck432, numericCheck432, reducedZero432 B hB hF, mul_zero]

theorem reducedZero433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource433 (mixedVector B) = 0 := by
  have h1407 : mixedVector B (Sum.inr 1407) = Sparse.eval nodeValue1407 (mixedVector B) := by
    change mixedMoment B node1407 node1407Labels = _
    exact sound1407 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h2985 : mixedVector B (Sum.inr 2985) = Sparse.eval nodeValue2985 (mixedVector B) := by
    change mixedMoment B node2985 node2985Labels = _
    exact sound2985 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3097 : mixedVector B (Sum.inr 3097) = Sparse.eval nodeValue3097 (mixedVector B) := by
    change mixedMoment B node3097 node3097Labels = _
    exact sound3097 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm517, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1407, h2955, h2985, h3078, h3092, h3097, h4091, reducedSource433] using sourceEq517 B hB

theorem rowSound433 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row433 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck433, numericCheck433, reducedZero433 B hB hF, mul_zero]

theorem reducedZero434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource434 (mixedVector B) = 0 := by
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h2925 : mixedVector B (Sum.inr 2925) = Sparse.eval nodeValue2925 (mixedVector B) := by
    change mixedMoment B node2925 node2925Labels = _
    exact sound2925 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2955 : mixedVector B (Sum.inr 2955) = Sparse.eval nodeValue2955 (mixedVector B) := by
    change mixedMoment B node2955 node2955Labels = _
    exact sound2955 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3958 : mixedVector B (Sum.inr 3958) = Sparse.eval nodeValue3958 (mixedVector B) := by
    change mixedMoment B node3958 node3958Labels = _
    exact sound3958 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm518, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2865, h2925, h2931, h2955, h3078, h3958, h4091, reducedSource434] using sourceEq518 B hB

theorem rowSound434 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row434 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck434, numericCheck434, reducedZero434 B hB hF, mul_zero]

theorem reducedZero435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource435 (mixedVector B) = 0 := by
  have h1391 : mixedVector B (Sum.inr 1391) = Sparse.eval nodeValue1391 (mixedVector B) := by
    change mixedMoment B node1391 node1391Labels = _
    exact sound1391 B hB hF
  have h2931 : mixedVector B (Sum.inr 2931) = Sparse.eval nodeValue2931 (mixedVector B) := by
    change mixedMoment B node2931 node2931Labels = _
    exact sound2931 B hB hF
  have h2981 : mixedVector B (Sum.inr 2981) = Sparse.eval nodeValue2981 (mixedVector B) := by
    change mixedMoment B node2981 node2981Labels = _
    exact sound2981 B hB hF
  have h3077 : mixedVector B (Sum.inr 3077) = Sparse.eval nodeValue3077 (mixedVector B) := by
    change mixedMoment B node3077 node3077Labels = _
    exact sound3077 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm519, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1391, h2931, h2981, h3077, h3078, h4091, reducedSource435] using sourceEq519 B hB

theorem rowSound435 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row435 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck435, numericCheck435, reducedZero435 B hB hF, mul_zero]

theorem reducedZero436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource436 (mixedVector B) = 0 := by
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3068 : mixedVector B (Sum.inr 3068) = Sparse.eval nodeValue3068 (mixedVector B) := by
    change mixedMoment B node3068 node3068Labels = _
    exact sound3068 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h3092 : mixedVector B (Sum.inr 3092) = Sparse.eval nodeValue3092 (mixedVector B) := by
    change mixedMoment B node3092 node3092Labels = _
    exact sound3092 B hB hF
  have h3885 : mixedVector B (Sum.inr 3885) = Sparse.eval nodeValue3885 (mixedVector B) := by
    change mixedMoment B node3885 node3885Labels = _
    exact sound3885 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm520, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3031, h3068, h3078, h3092, h3885, h4091, reducedSource436] using sourceEq520 B hB

theorem rowSound436 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row436 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck436, numericCheck436, reducedZero436 B hB hF, mul_zero]

theorem reducedZero437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource437 (mixedVector B) = 0 := by
  have h1389 : mixedVector B (Sum.inr 1389) = Sparse.eval nodeValue1389 (mixedVector B) := by
    change mixedMoment B node1389 node1389Labels = _
    exact sound1389 B hB hF
  have h2857 : mixedVector B (Sum.inr 2857) = Sparse.eval nodeValue2857 (mixedVector B) := by
    change mixedMoment B node2857 node2857Labels = _
    exact sound2857 B hB hF
  have h2865 : mixedVector B (Sum.inr 2865) = Sparse.eval nodeValue2865 (mixedVector B) := by
    change mixedMoment B node2865 node2865Labels = _
    exact sound2865 B hB hF
  have h3031 : mixedVector B (Sum.inr 3031) = Sparse.eval nodeValue3031 (mixedVector B) := by
    change mixedMoment B node3031 node3031Labels = _
    exact sound3031 B hB hF
  have h3078 : mixedVector B (Sum.inr 3078) = Sparse.eval nodeValue3078 (mixedVector B) := by
    change mixedMoment B node3078 node3078Labels = _
    exact sound3078 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm521, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1389, h2857, h2865, h3031, h3078, h4091, reducedSource437] using sourceEq521 B hB

theorem rowSound437 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row437 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck437, numericCheck437, reducedZero437 B hB hF, mul_zero]

theorem reducedZero439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource439 (mixedVector B) = 0 := by
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h3494 : mixedVector B (Sum.inr 3494) = Sparse.eval nodeValue3494 (mixedVector B) := by
    change mixedMoment B node3494 node3494Labels = _
    exact sound3494 B hB hF
  have h3498 : mixedVector B (Sum.inr 3498) = Sparse.eval nodeValue3498 (mixedVector B) := by
    change mixedMoment B node3498 node3498Labels = _
    exact sound3498 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm525, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2879, h3494, h3498, h3548, h3580, h4084, reducedSource439] using sourceEq525 B hB

theorem rowSound439 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row439 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck439, numericCheck439, reducedZero439 B hB hF, mul_zero]

theorem reducedZero440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource440 (mixedVector B) = 0 := by
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h2108 : mixedVector B (Sum.inr 2108) = Sparse.eval nodeValue2108 (mixedVector B) := by
    change mixedMoment B node2108 node2108Labels = _
    exact sound2108 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm526, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2104, h2106, h2108, h2262, h3580, h4084, reducedSource440] using sourceEq526 B hB

theorem rowSound440 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row440 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck440, numericCheck440, reducedZero440 B hB hF, mul_zero]

theorem reducedZero441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource441 (mixedVector B) = 0 := by
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2877 : mixedVector B (Sum.inr 2877) = Sparse.eval nodeValue2877 (mixedVector B) := by
    change mixedMoment B node2877 node2877Labels = _
    exact sound2877 B hB hF
  have h3576 : mixedVector B (Sum.inr 3576) = Sparse.eval nodeValue3576 (mixedVector B) := by
    change mixedMoment B node3576 node3576Labels = _
    exact sound3576 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm527, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2104, h2877, h3576, h3580, h4084, reducedSource441] using sourceEq527 B hB

theorem rowSound441 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row441 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck441, numericCheck441, reducedZero441 B hB hF, mul_zero]

theorem reducedZero442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource442 (mixedVector B) = 0 := by
  have h2877 : mixedVector B (Sum.inr 2877) = Sparse.eval nodeValue2877 (mixedVector B) := by
    change mixedMoment B node2877 node2877Labels = _
    exact sound2877 B hB hF
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h2883 : mixedVector B (Sum.inr 2883) = Sparse.eval nodeValue2883 (mixedVector B) := by
    change mixedMoment B node2883 node2883Labels = _
    exact sound2883 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm528, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2877, h2879, h2883, h3050, h3580, h4084, reducedSource442] using sourceEq528 B hB

theorem rowSound442 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row442 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck442, numericCheck442, reducedZero442 B hB hF, mul_zero]

theorem reducedZero443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource443 (mixedVector B) = 0 := by
  have h2106 : mixedVector B (Sum.inr 2106) = Sparse.eval nodeValue2106 (mixedVector B) := by
    change mixedMoment B node2106 node2106Labels = _
    exact sound2106 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h3502 : mixedVector B (Sum.inr 3502) = Sparse.eval nodeValue3502 (mixedVector B) := by
    change mixedMoment B node3502 node3502Labels = _
    exact sound3502 B hB hF
  have h3580 : mixedVector B (Sum.inr 3580) = Sparse.eval nodeValue3580 (mixedVector B) := by
    change mixedMoment B node3580 node3580Labels = _
    exact sound3580 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm529, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2106, h3050, h3502, h3580, h3582, h4084, reducedSource443] using sourceEq529 B hB

theorem rowSound443 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row443 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck443, numericCheck443, reducedZero443 B hB hF, mul_zero]

theorem sourceRowsAt432 : MixedData.sourceRows (432 : Fin 2425) =
    MixedData.row432 := by decide +kernel

theorem sourceRowsAt433 : MixedData.sourceRows (433 : Fin 2425) =
    MixedData.row433 := by decide +kernel

theorem sourceRowsAt434 : MixedData.sourceRows (434 : Fin 2425) =
    MixedData.row434 := by decide +kernel

theorem sourceRowsAt435 : MixedData.sourceRows (435 : Fin 2425) =
    MixedData.row435 := by decide +kernel

theorem sourceRowsAt436 : MixedData.sourceRows (436 : Fin 2425) =
    MixedData.row436 := by decide +kernel

theorem sourceRowsAt437 : MixedData.sourceRows (437 : Fin 2425) =
    MixedData.row437 := by decide +kernel

theorem sourceRowsAt438 : MixedData.sourceRows (438 : Fin 2425) =
    MixedData.row438 := by decide +kernel

theorem sourceRowsAt439 : MixedData.sourceRows (439 : Fin 2425) =
    MixedData.row439 := by decide +kernel

theorem sourceRowsAt440 : MixedData.sourceRows (440 : Fin 2425) =
    MixedData.row440 := by decide +kernel

theorem sourceRowsAt441 : MixedData.sourceRows (441 : Fin 2425) =
    MixedData.row441 := by decide +kernel

theorem sourceRowsAt442 : MixedData.sourceRows (442 : Fin 2425) =
    MixedData.row442 := by decide +kernel

theorem sourceRowsAt443 : MixedData.sourceRows (443 : Fin 2425) =
    MixedData.row443 := by decide +kernel

theorem sourceRowsAt444 : MixedData.sourceRows (444 : Fin 2425) =
    MixedData.row444 := by decide +kernel

theorem sourceRowsAt445 : MixedData.sourceRows (445 : Fin 2425) =
    MixedData.row445 := by decide +kernel

theorem sourceRowsAt446 : MixedData.sourceRows (446 : Fin 2425) =
    MixedData.row446 := by decide +kernel

theorem sourceRowsAt447 : MixedData.sourceRows (447 : Fin 2425) =
    MixedData.row447 := by decide +kernel

theorem chunkSound27_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 27) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 432 ∨ k.val = 433 ∨ k.val = 434 ∨ k.val = 435 ∨ k.val = 436 ∨ k.val = 437 ∨ k.val = 438 ∨ k.val = 439 ∨ k.val = 440 ∨ k.val = 441 ∨ k.val = 442 ∨ k.val = 443 ∨ k.val = 444 ∨ k.val = 445 ∨ k.val = 446 ∨ k.val = 447 := by omega
  rcases heq with h432 | h433 | h434 | h435 | h436 | h437 | h438 | h439 | h440 | h441 | h442 | h443 | h444 | h445 | h446 | h447
  · have he : k = (432 : Fin 2425) := Fin.ext h432
    subst k
    rw [sourceRowsAt432]
    exact rowSound432 B hB hF
  · have he : k = (433 : Fin 2425) := Fin.ext h433
    subst k
    rw [sourceRowsAt433]
    exact rowSound433 B hB hF
  · have he : k = (434 : Fin 2425) := Fin.ext h434
    subst k
    rw [sourceRowsAt434]
    exact rowSound434 B hB hF
  · have he : k = (435 : Fin 2425) := Fin.ext h435
    subst k
    rw [sourceRowsAt435]
    exact rowSound435 B hB hF
  · have he : k = (436 : Fin 2425) := Fin.ext h436
    subst k
    rw [sourceRowsAt436]
    exact rowSound436 B hB hF
  · have he : k = (437 : Fin 2425) := Fin.ext h437
    subst k
    rw [sourceRowsAt437]
    exact rowSound437 B hB hF
  · have he : k = (438 : Fin 2425) := Fin.ext h438
    subst k
    rw [sourceRowsAt438]
    exact rowSound438_e B hB hF
  · have he : k = (439 : Fin 2425) := Fin.ext h439
    subst k
    rw [sourceRowsAt439]
    exact rowSound439 B hB hF
  · have he : k = (440 : Fin 2425) := Fin.ext h440
    subst k
    rw [sourceRowsAt440]
    exact rowSound440 B hB hF
  · have he : k = (441 : Fin 2425) := Fin.ext h441
    subst k
    rw [sourceRowsAt441]
    exact rowSound441 B hB hF
  · have he : k = (442 : Fin 2425) := Fin.ext h442
    subst k
    rw [sourceRowsAt442]
    exact rowSound442 B hB hF
  · have he : k = (443 : Fin 2425) := Fin.ext h443
    subst k
    rw [sourceRowsAt443]
    exact rowSound443 B hB hF
  · have he : k = (444 : Fin 2425) := Fin.ext h444
    subst k
    rw [sourceRowsAt444]
    exact rowSound444_e B hB hF
  · have he : k = (445 : Fin 2425) := Fin.ext h445
    subst k
    rw [sourceRowsAt445]
    exact rowSound445_e B hB hF
  · have he : k = (446 : Fin 2425) := Fin.ext h446
    subst k
    rw [sourceRowsAt446]
    exact rowSound446_e B hB hF
  · have he : k = (447 : Fin 2425) := Fin.ext h447
    subst k
    rw [sourceRowsAt447]
    exact rowSound447_e B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound27_e_oai
