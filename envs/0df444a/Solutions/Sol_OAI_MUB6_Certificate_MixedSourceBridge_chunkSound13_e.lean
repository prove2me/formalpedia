-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:47:26.996426+00:00
-- url     : https://prove2.me/submissions/b362db8a-df70-43d8-bb62-8f13c08aa856

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
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound213_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound214_e

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

theorem canonical6100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6100 raw6100Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw6100 raw6100Labels = mixedMoment B raw6100step0 raw6100step0Labels := by
      have hz : ∀ j, raw6100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6100step0 = (fun i j => raw6100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6100step0 raw6100; decide +kernel
      have hl : raw6100step0Labels = raw6100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6100 raw6100Labels permutation434 hz
    mixedMoment B raw6100step0 raw6100step0Labels = mixedMoment B raw6100step1 raw6100step1Labels := by
      have hz : ∀ j, raw6100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6100step1 = (fun i j => raw6100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6100step1 raw6100step0; decide +kernel
      have hl : raw6100step1Labels = raw6100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6100step0 raw6100step0Labels permutation80 hz
    mixedMoment B raw6100step1 raw6100step1Labels = mixedMoment B raw6100step2 raw6100step2Labels := by
      have ha : raw6100step2 = (fun i j => raw6100step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6100step2 raw6100step1; decide +kernel
      have hl : raw6100step2Labels = raw6100step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6100step1 raw6100step1Labels permutation25 permutation4
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical6101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6101 raw6101Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw6101 raw6101Labels = mixedMoment B raw6101step0 raw6101step0Labels := by
      have hz : ∀ j, raw6101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6101step0 = (fun i j => raw6101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6101step0 raw6101; decide +kernel
      have hl : raw6101step0Labels = raw6101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6101 raw6101Labels permutation434 hz
    mixedMoment B raw6101step0 raw6101step0Labels = mixedMoment B raw6101step1 raw6101step1Labels := by
      have hz : ∀ j, raw6101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6101step1 = (fun i j => raw6101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6101step1 raw6101step0; decide +kernel
      have hl : raw6101step1Labels = raw6101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6101step0 raw6101step0Labels permutation80 hz
    mixedMoment B raw6101step1 raw6101step1Labels = mixedMoment B raw6101step2 raw6101step2Labels := by
      have ha : raw6101step2 = (fun i j => raw6101step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6101step2 raw6101step1; decide +kernel
      have hl : raw6101step2Labels = raw6101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6101step1 raw6101step1Labels permutation24 permutation4
    _ = mixedMoment B node3056 node3056Labels := by rfl

theorem canonical6102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6102 raw6102Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw6102 raw6102Labels = mixedMoment B raw6102step0 raw6102step0Labels := by
      have hz : ∀ j, raw6102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6102step0 = (fun i j => raw6102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6102step0 raw6102; decide +kernel
      have hl : raw6102step0Labels = raw6102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6102 raw6102Labels permutation434 hz
    mixedMoment B raw6102step0 raw6102step0Labels = mixedMoment B raw6102step1 raw6102step1Labels := by
      have ha : raw6102step1 = (fun i j => raw6102step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6102step1 raw6102step0; decide +kernel
      have hl : raw6102step1Labels = raw6102step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6102step0 raw6102step0Labels permutation125 permutation4
    _ = mixedMoment B node3050 node3050Labels := by rfl

theorem canonical6103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6103 raw6103Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw6103 raw6103Labels = mixedMoment B raw6103step0 raw6103step0Labels := by
      have hz : ∀ j, raw6103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6103step0 = (fun i j => raw6103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6103step0 raw6103; decide +kernel
      have hl : raw6103step0Labels = raw6103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6103 raw6103Labels permutation346 hz
    mixedMoment B raw6103step0 raw6103step0Labels = mixedMoment B raw6103step1 raw6103step1Labels := by
      have ha : raw6103step1 = (fun i j => raw6103step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6103step1 raw6103step0; decide +kernel
      have hl : raw6103step1Labels = raw6103step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6103step0 raw6103step0Labels permutation125 permutation4
    _ = mixedMoment B node3050 node3050Labels := by rfl

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

theorem canonical6105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6105 raw6105Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw6105 raw6105Labels = mixedMoment B raw6105step0 raw6105step0Labels := by
      have hz : ∀ j, raw6105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6105step0 = (fun i j => raw6105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6105step0 raw6105; decide +kernel
      have hl : raw6105step0Labels = raw6105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6105 raw6105Labels permutation434 hz
    mixedMoment B raw6105step0 raw6105step0Labels = mixedMoment B raw6105step1 raw6105step1Labels := by
      have hz : ∀ j, raw6105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6105step1 = (fun i j => raw6105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6105step1 raw6105step0; decide +kernel
      have hl : raw6105step1Labels = raw6105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6105step0 raw6105step0Labels permutation80 hz
    mixedMoment B raw6105step1 raw6105step1Labels = mixedMoment B raw6105step2 raw6105step2Labels := by
      have ha : raw6105step2 = (fun i j => raw6105step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6105step2 raw6105step1; decide +kernel
      have hl : raw6105step2Labels = raw6105step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6105step1 raw6105step1Labels permutation29 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

theorem canonical6106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6106 raw6106Labels = mixedMoment B node2978 node2978Labels := by
  calc
    mixedMoment B raw6106 raw6106Labels = mixedMoment B raw6106step0 raw6106step0Labels := by
      have hz : ∀ j, raw6106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6106step0 = (fun i j => raw6106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6106step0 raw6106; decide +kernel
      have hl : raw6106step0Labels = raw6106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6106 raw6106Labels permutation434 hz
    mixedMoment B raw6106step0 raw6106step0Labels = mixedMoment B raw6106step1 raw6106step1Labels := by
      have ha : raw6106step1 = (fun i j => raw6106step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6106step1 raw6106step0; decide +kernel
      have hl : raw6106step1Labels = raw6106step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6106step0 raw6106step0Labels permutation121 permutation4
    _ = mixedMoment B node2978 node2978Labels := by rfl

theorem canonical6107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6107 raw6107Labels = mixedMoment B node2978 node2978Labels := by
  calc
    mixedMoment B raw6107 raw6107Labels = mixedMoment B raw6107step0 raw6107step0Labels := by
      have hz : ∀ j, raw6107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6107step0 = (fun i j => raw6107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6107step0 raw6107; decide +kernel
      have hl : raw6107step0Labels = raw6107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6107 raw6107Labels permutation346 hz
    mixedMoment B raw6107step0 raw6107step0Labels = mixedMoment B raw6107step1 raw6107step1Labels := by
      have ha : raw6107step1 = (fun i j => raw6107step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6107step1 raw6107step0; decide +kernel
      have hl : raw6107step1Labels = raw6107step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6107step0 raw6107step0Labels permutation121 permutation4
    _ = mixedMoment B node2978 node2978Labels := by rfl

theorem canonical6108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6108 raw6108Labels = mixedMoment B node1374 node1374Labels := by
  calc
    mixedMoment B raw6108 raw6108Labels = mixedMoment B raw6108step0 raw6108step0Labels := by
      have hz : ∀ j, raw6108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6108step0 = (fun i j => raw6108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6108step0 raw6108; decide +kernel
      have hl : raw6108step0Labels = raw6108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6108 raw6108Labels permutation434 hz
    mixedMoment B raw6108step0 raw6108step0Labels = mixedMoment B raw6108step1 raw6108step1Labels := by
      have hz : ∀ j, raw6108step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6108step1 = (fun i j => raw6108step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6108step1 raw6108step0; decide +kernel
      have hl : raw6108step1Labels = raw6108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6108step0 raw6108step0Labels permutation80 hz
    mixedMoment B raw6108step1 raw6108step1Labels = mixedMoment B raw6108step2 raw6108step2Labels := by
      have ha : raw6108step2 = (fun i j => raw6108step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6108step2 raw6108step1; decide +kernel
      have hl : raw6108step2Labels = raw6108step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6108step1 raw6108step1Labels permutation25 permutation4
    _ = mixedMoment B node1374 node1374Labels := by rfl

theorem canonical6109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6109 raw6109Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw6109 raw6109Labels = mixedMoment B raw6109step0 raw6109step0Labels := by
      have hz : ∀ j, raw6109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6109step0 = (fun i j => raw6109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6109step0 raw6109; decide +kernel
      have hl : raw6109step0Labels = raw6109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6109 raw6109Labels permutation434 hz
    mixedMoment B raw6109step0 raw6109step0Labels = mixedMoment B raw6109step1 raw6109step1Labels := by
      have hz : ∀ j, raw6109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6109step1 = (fun i j => raw6109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6109step1 raw6109step0; decide +kernel
      have hl : raw6109step1Labels = raw6109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6109step0 raw6109step0Labels permutation80 hz
    mixedMoment B raw6109step1 raw6109step1Labels = mixedMoment B raw6109step2 raw6109step2Labels := by
      have ha : raw6109step2 = (fun i j => raw6109step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6109step2 raw6109step1; decide +kernel
      have hl : raw6109step2Labels = raw6109step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6109step1 raw6109step1Labels permutation25 permutation4
    _ = mixedMoment B node2888 node2888Labels := by rfl

theorem canonical6110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6110 raw6110Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw6110 raw6110Labels = mixedMoment B raw6110step0 raw6110step0Labels := by
      have hz : ∀ j, raw6110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6110step0 = (fun i j => raw6110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6110step0 raw6110; decide +kernel
      have hl : raw6110step0Labels = raw6110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6110 raw6110Labels permutation434 hz
    mixedMoment B raw6110step0 raw6110step0Labels = mixedMoment B raw6110step1 raw6110step1Labels := by
      have ha : raw6110step1 = (fun i j => raw6110step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6110step1 raw6110step0; decide +kernel
      have hl : raw6110step1Labels = raw6110step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6110step0 raw6110step0Labels permutation36 permutation4
    mixedMoment B raw6110step1 raw6110step1Labels = mixedMoment B raw6110step2 raw6110step2Labels := by
      have ha : raw6110step2 = -raw6110step1 := by apply Matrix.ext; change ∀ i j, raw6110step2 i j = -(raw6110step1 i j); unfold raw6110step2 raw6110step1; decide +kernel
      have hl : raw6110step2Labels = raw6110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

theorem canonical6111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6111 raw6111Labels = mixedMoment B node2973 node2973Labels := by
  calc
    mixedMoment B raw6111 raw6111Labels = mixedMoment B raw6111step0 raw6111step0Labels := by
      have ha : raw6111step0 = (fun i j => raw6111 (permutation550 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6111step0 raw6111; decide +kernel
      have hl : raw6111step0Labels = raw6111Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6111 raw6111Labels permutation550 permutation4
    _ = mixedMoment B node2973 node2973Labels := by rfl

theorem canonical6112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6112 raw6112Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6112 raw6112Labels = mixedMoment B raw6112step0 raw6112step0Labels := by
      have hz : ∀ j, raw6112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6112step0 = (fun i j => raw6112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6112step0 raw6112; decide +kernel
      have hl : raw6112step0Labels = raw6112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6112 raw6112Labels permutation434 hz
    mixedMoment B raw6112step0 raw6112step0Labels = mixedMoment B raw6112step1 raw6112step1Labels := by
      have ha : raw6112step1 = (fun i j => raw6112step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6112step1 raw6112step0; decide +kernel
      have hl : raw6112step1Labels = raw6112step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6112step0 raw6112step0Labels permutation36 permutation4
    mixedMoment B raw6112step1 raw6112step1Labels = mixedMoment B raw6112step2 raw6112step2Labels := by
      have ha : raw6112step2 = -raw6112step1 := by apply Matrix.ext; change ∀ i j, raw6112step2 i j = -(raw6112step1 i j); unfold raw6112step2 raw6112step1; decide +kernel
      have hl : raw6112step2Labels = raw6112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical6113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6113 raw6113Labels = mixedMoment B node2597 node2597Labels := by
  calc
    mixedMoment B raw6113 raw6113Labels = mixedMoment B raw6113step0 raw6113step0Labels := by
      have hz : ∀ j, raw6113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6113step0 = (fun i j => raw6113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6113step0 raw6113; decide +kernel
      have hl : raw6113step0Labels = raw6113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6113 raw6113Labels permutation434 hz
    mixedMoment B raw6113step0 raw6113step0Labels = mixedMoment B raw6113step1 raw6113step1Labels := by
      have ha : raw6113step1 = (fun i j => raw6113step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6113step1 raw6113step0; decide +kernel
      have hl : raw6113step1Labels = raw6113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6113step0 raw6113step0Labels permutation136 permutation2
    _ = mixedMoment B node2597 node2597Labels := by rfl

theorem canonical6117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6117 raw6117Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw6117 raw6117Labels = mixedMoment B raw6117step0 raw6117step0Labels := by
      have hz : ∀ j, raw6117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6117step0 = (fun i j => raw6117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6117step0 raw6117; decide +kernel
      have hl : raw6117step0Labels = raw6117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6117 raw6117Labels permutation434 hz
    mixedMoment B raw6117step0 raw6117step0Labels = mixedMoment B raw6117step1 raw6117step1Labels := by
      have ha : raw6117step1 = (fun i j => raw6117step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6117step1 raw6117step0; decide +kernel
      have hl : raw6117step1Labels = raw6117step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6117step0 raw6117step0Labels permutation125 permutation4
    _ = mixedMoment B node2879 node2879Labels := by rfl

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

theorem canonical6124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6124 raw6124Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw6124 raw6124Labels = mixedMoment B raw6124step0 raw6124step0Labels := by
      have hz : ∀ j, raw6124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6124step0 = (fun i j => raw6124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6124step0 raw6124; decide +kernel
      have hl : raw6124step0Labels = raw6124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6124 raw6124Labels permutation434 hz
    mixedMoment B raw6124step0 raw6124step0Labels = mixedMoment B raw6124step1 raw6124step1Labels := by
      have hz : ∀ j, raw6124step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6124step1 = (fun i j => raw6124step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6124step1 raw6124step0; decide +kernel
      have hl : raw6124step1Labels = raw6124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6124step0 raw6124step0Labels permutation80 hz
    mixedMoment B raw6124step1 raw6124step1Labels = mixedMoment B raw6124step2 raw6124step2Labels := by
      have ha : raw6124step2 = (fun i j => raw6124step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6124step2 raw6124step1; decide +kernel
      have hl : raw6124step2Labels = raw6124step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6124step1 raw6124step1Labels permutation9 permutation4
    mixedMoment B raw6124step2 raw6124step2Labels = mixedMoment B raw6124step3 raw6124step3Labels := by
      have ha : raw6124step3 = -raw6124step2 := by apply Matrix.ext; change ∀ i j, raw6124step3 i j = -(raw6124step2 i j); unfold raw6124step3 raw6124step2; decide +kernel
      have hl : raw6124step3Labels = raw6124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical6125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6125 raw6125Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw6125 raw6125Labels = mixedMoment B raw6125step0 raw6125step0Labels := by
      have hz : ∀ j, raw6125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6125step0 = (fun i j => raw6125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6125step0 raw6125; decide +kernel
      have hl : raw6125step0Labels = raw6125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6125 raw6125Labels permutation346 hz
    mixedMoment B raw6125step0 raw6125step0Labels = mixedMoment B raw6125step1 raw6125step1Labels := by
      have ha : raw6125step1 = (fun i j => raw6125step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6125step1 raw6125step0; decide +kernel
      have hl : raw6125step1Labels = raw6125step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6125step0 raw6125step0Labels permutation125 permutation4
    _ = mixedMoment B node2879 node2879Labels := by rfl

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

theorem canonical6217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6217 raw6217Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw6217 raw6217Labels = mixedMoment B raw6217step0 raw6217step0Labels := by
      have hz : ∀ j, raw6217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6217step0 = (fun i j => raw6217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6217step0 raw6217; decide +kernel
      have hl : raw6217step0Labels = raw6217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6217 raw6217Labels permutation346 hz
    _ = mixedMoment B node3809 node3809Labels := by rfl

theorem canonical6218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6218 raw6218Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw6218 raw6218Labels = mixedMoment B raw6218step0 raw6218step0Labels := by
      have ha : raw6218step0 = (fun i j => raw6218 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6218step0 raw6218; decide +kernel
      have hl : raw6218step0Labels = raw6218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6218 raw6218Labels permutation176 permutation2
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical6219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6219 raw6219Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw6219 raw6219Labels = mixedMoment B raw6219step0 raw6219step0Labels := by
      have hz : ∀ j, raw6219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6219step0 = (fun i j => raw6219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6219step0 raw6219; decide +kernel
      have hl : raw6219step0Labels = raw6219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6219 raw6219Labels permutation346 hz
    mixedMoment B raw6219step0 raw6219step0Labels = mixedMoment B raw6219step1 raw6219step1Labels := by
      have ha : raw6219step1 = (fun i j => raw6219step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6219step1 raw6219step0; decide +kernel
      have hl : raw6219step1Labels = raw6219step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6219step0 raw6219step0Labels permutation38 permutation2
    _ = mixedMoment B node3877 node3877Labels := by rfl

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

theorem canonical6221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6221 raw6221Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw6221 raw6221Labels = mixedMoment B raw6221step0 raw6221step0Labels := by
      have hz : ∀ j, raw6221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6221step0 = (fun i j => raw6221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6221step0 raw6221; decide +kernel
      have hl : raw6221step0Labels = raw6221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6221 raw6221Labels permutation346 hz
    mixedMoment B raw6221step0 raw6221step0Labels = mixedMoment B raw6221step1 raw6221step1Labels := by
      have ha : raw6221step1 = (fun i j => raw6221step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6221step1 raw6221step0; decide +kernel
      have hl : raw6221step1Labels = raw6221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6221step0 raw6221step0Labels permutation33 permutation2
    _ = mixedMoment B node3903 node3903Labels := by rfl

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

theorem canonical6223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6223 raw6223Labels = mixedMoment B node1263 node1263Labels := by
  calc
    mixedMoment B raw6223 raw6223Labels = mixedMoment B raw6223step0 raw6223step0Labels := by
      have hz : ∀ j, raw6223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6223step0 = (fun i j => raw6223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6223step0 raw6223; decide +kernel
      have hl : raw6223step0Labels = raw6223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6223 raw6223Labels permutation346 hz
    mixedMoment B raw6223step0 raw6223step0Labels = mixedMoment B raw6223step1 raw6223step1Labels := by
      have ha : raw6223step1 = (fun i j => raw6223step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6223step1 raw6223step0; decide +kernel
      have hl : raw6223step1Labels = raw6223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6223step0 raw6223step0Labels permutation38 permutation2
    _ = mixedMoment B node1263 node1263Labels := by rfl

theorem canonical6224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6224 raw6224Labels = mixedMoment B node1214 node1214Labels := by
  calc
    mixedMoment B raw6224 raw6224Labels = mixedMoment B raw6224step0 raw6224step0Labels := by
      have ha : raw6224step0 = (fun i j => raw6224 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6224step0 raw6224; decide +kernel
      have hl : raw6224step0Labels = raw6224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6224 raw6224Labels permutation158 permutation2
    _ = mixedMoment B node1214 node1214Labels := by rfl

theorem canonical6225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6225 raw6225Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw6225 raw6225Labels = mixedMoment B raw6225step0 raw6225step0Labels := by
      have hz : ∀ j, raw6225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6225step0 = (fun i j => raw6225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6225step0 raw6225; decide +kernel
      have hl : raw6225step0Labels = raw6225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6225 raw6225Labels permutation346 hz
    _ = mixedMoment B node1241 node1241Labels := by rfl

theorem canonical6226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6226 raw6226Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw6226 raw6226Labels = mixedMoment B raw6226step0 raw6226step0Labels := by
      have hz : ∀ j, raw6226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6226step0 = (fun i j => raw6226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6226step0 raw6226; decide +kernel
      have hl : raw6226step0Labels = raw6226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6226 raw6226Labels permutation346 hz
    mixedMoment B raw6226step0 raw6226step0Labels = mixedMoment B raw6226step1 raw6226step1Labels := by
      have ha : raw6226step1 = (fun i j => raw6226step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6226step1 raw6226step0; decide +kernel
      have hl : raw6226step1Labels = raw6226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6226step0 raw6226step0Labels permutation33 permutation2
    _ = mixedMoment B node1219 node1219Labels := by rfl

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

theorem canonical6228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6228 raw6228Labels = mixedMoment B node2568 node2568Labels := by
  calc
    mixedMoment B raw6228 raw6228Labels = mixedMoment B raw6228step0 raw6228step0Labels := by
      have ha : raw6228step0 = (fun i j => raw6228 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6228step0 raw6228; decide +kernel
      have hl : raw6228step0Labels = raw6228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6228 raw6228Labels permutation182 permutation2
    _ = mixedMoment B node2568 node2568Labels := by rfl

theorem canonical6229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6229 raw6229Labels = mixedMoment B node2634 node2634Labels := by
  calc
    mixedMoment B raw6229 raw6229Labels = mixedMoment B raw6229step0 raw6229step0Labels := by
      have hz : ∀ j, raw6229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6229step0 = (fun i j => raw6229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6229step0 raw6229; decide +kernel
      have hl : raw6229step0Labels = raw6229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6229 raw6229Labels permutation346 hz
    mixedMoment B raw6229step0 raw6229step0Labels = mixedMoment B raw6229step1 raw6229step1Labels := by
      have ha : raw6229step1 = (fun i j => raw6229step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6229step1 raw6229step0; decide +kernel
      have hl : raw6229step1Labels = raw6229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6229step0 raw6229step0Labels permutation38 permutation2
    _ = mixedMoment B node2634 node2634Labels := by rfl

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

theorem canonical6231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6231 raw6231Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw6231 raw6231Labels = mixedMoment B raw6231step0 raw6231step0Labels := by
      have hz : ∀ j, raw6231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6231step0 = (fun i j => raw6231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6231step0 raw6231; decide +kernel
      have hl : raw6231step0Labels = raw6231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6231 raw6231Labels permutation346 hz
    mixedMoment B raw6231step0 raw6231step0Labels = mixedMoment B raw6231step1 raw6231step1Labels := by
      have ha : raw6231step1 = (fun i j => raw6231step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6231step1 raw6231step0; decide +kernel
      have hl : raw6231step1Labels = raw6231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6231step0 raw6231step0Labels permutation39 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

theorem canonical6232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6232 raw6232Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw6232 raw6232Labels = mixedMoment B raw6232step0 raw6232step0Labels := by
      have ha : raw6232step0 = (fun i j => raw6232 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6232step0 raw6232; decide +kernel
      have hl : raw6232step0Labels = raw6232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6232 raw6232Labels permutation158 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

theorem canonical6233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6233 raw6233Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw6233 raw6233Labels = mixedMoment B raw6233step0 raw6233step0Labels := by
      have hz : ∀ j, raw6233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6233step0 = (fun i j => raw6233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6233step0 raw6233; decide +kernel
      have hl : raw6233step0Labels = raw6233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6233 raw6233Labels permutation346 hz
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical6234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6234 raw6234Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw6234 raw6234Labels = mixedMoment B raw6234step0 raw6234step0Labels := by
      have hz : ∀ j, raw6234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6234step0 = (fun i j => raw6234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6234step0 raw6234; decide +kernel
      have hl : raw6234step0Labels = raw6234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6234 raw6234Labels permutation346 hz
    mixedMoment B raw6234step0 raw6234step0Labels = mixedMoment B raw6234step1 raw6234step1Labels := by
      have ha : raw6234step1 = (fun i j => raw6234step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6234step1 raw6234step0; decide +kernel
      have hl : raw6234step1Labels = raw6234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6234step0 raw6234step0Labels permutation33 permutation2
    _ = mixedMoment B node2488 node2488Labels := by rfl

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

theorem canonical6236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6236 raw6236Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw6236 raw6236Labels = mixedMoment B raw6236step0 raw6236step0Labels := by
      have ha : raw6236step0 = (fun i j => raw6236 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6236step0 raw6236; decide +kernel
      have hl : raw6236step0Labels = raw6236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6236 raw6236Labels permutation200 permutation2
    _ = mixedMoment B node2616 node2616Labels := by rfl

theorem canonical6237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6237 raw6237Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw6237 raw6237Labels = mixedMoment B raw6237step0 raw6237step0Labels := by
      have ha : raw6237step0 = (fun i j => raw6237 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6237step0 raw6237; decide +kernel
      have hl : raw6237step0Labels = raw6237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6237 raw6237Labels permutation160 permutation2
    _ = mixedMoment B node2714 node2714Labels := by rfl

theorem canonical6238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6238 raw6238Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw6238 raw6238Labels = mixedMoment B raw6238step0 raw6238step0Labels := by
      have ha : raw6238step0 = (fun i j => raw6238 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6238step0 raw6238; decide +kernel
      have hl : raw6238step0Labels = raw6238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6238 raw6238Labels permutation159 permutation2
    _ = mixedMoment B node2720 node2720Labels := by rfl

theorem canonical6239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6239 raw6239Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw6239 raw6239Labels = mixedMoment B raw6239step0 raw6239step0Labels := by
      have ha : raw6239step0 = (fun i j => raw6239 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6239step0 raw6239; decide +kernel
      have hl : raw6239step0Labels = raw6239Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6239 raw6239Labels permutation176 permutation2
    _ = mixedMoment B node2557 node2557Labels := by rfl

theorem canonical6240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6240 raw6240Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw6240 raw6240Labels = mixedMoment B raw6240step0 raw6240step0Labels := by
      have ha : raw6240step0 = (fun i j => raw6240 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6240step0 raw6240; decide +kernel
      have hl : raw6240step0Labels = raw6240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6240 raw6240Labels permutation177 permutation2
    _ = mixedMoment B node2545 node2545Labels := by rfl

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

theorem canonical6243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6243 raw6243Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw6243 raw6243Labels = mixedMoment B raw6243step0 raw6243step0Labels := by
      have hz : ∀ j, raw6243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6243step0 = (fun i j => raw6243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6243step0 raw6243; decide +kernel
      have hl : raw6243step0Labels = raw6243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6243 raw6243Labels permutation346 hz
    mixedMoment B raw6243step0 raw6243step0Labels = mixedMoment B raw6243step1 raw6243step1Labels := by
      have ha : raw6243step1 = (fun i j => raw6243step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6243step1 raw6243step0; decide +kernel
      have hl : raw6243step1Labels = raw6243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6243step0 raw6243step0Labels permutation36 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical6244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6244 raw6244Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw6244 raw6244Labels = mixedMoment B raw6244step0 raw6244step0Labels := by
      have hz : ∀ j, raw6244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6244step0 = (fun i j => raw6244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6244step0 raw6244; decide +kernel
      have hl : raw6244step0Labels = raw6244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6244 raw6244Labels permutation346 hz
    mixedMoment B raw6244step0 raw6244step0Labels = mixedMoment B raw6244step1 raw6244step1Labels := by
      have ha : raw6244step1 = (fun i j => raw6244step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6244step1 raw6244step0; decide +kernel
      have hl : raw6244step1Labels = raw6244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6244step0 raw6244step0Labels permutation39 permutation2
    _ = mixedMoment B node2620 node2620Labels := by rfl

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

theorem canonical6246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6246 raw6246Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw6246 raw6246Labels = mixedMoment B raw6246step0 raw6246step0Labels := by
      have hz : ∀ j, raw6246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6246step0 = (fun i j => raw6246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6246step0 raw6246; decide +kernel
      have hl : raw6246step0Labels = raw6246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6246 raw6246Labels permutation346 hz
    mixedMoment B raw6246step0 raw6246step0Labels = mixedMoment B raw6246step1 raw6246step1Labels := by
      have ha : raw6246step1 = (fun i j => raw6246step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6246step1 raw6246step0; decide +kernel
      have hl : raw6246step1Labels = raw6246step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6246step0 raw6246step0Labels permutation33 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1214 node1214Labels = Sparse.eval nodeValue1214 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1214) = mixedMoment B node1214 node1214Labels := rfl
  simpa [nodeValue1214, Sparse.eval] using hc.symm

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

theorem sound1219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1219 node1219Labels = Sparse.eval nodeValue1219 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1219) = mixedMoment B node1219 node1219Labels := rfl
  simpa [nodeValue1219, Sparse.eval] using hc.symm

theorem sound1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1241 node1241Labels = Sparse.eval nodeValue1241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1241) = mixedMoment B node1241 node1241Labels := rfl
  simpa [nodeValue1241, Sparse.eval] using hc.symm

theorem sound1263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1263 node1263Labels = Sparse.eval nodeValue1263 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1263) = mixedMoment B node1263 node1263Labels := rfl
  simpa [nodeValue1263, Sparse.eval] using hc.symm

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

theorem sound1374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1374 node1374Labels = Sparse.eval nodeValue1374 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1374) = mixedMoment B node1374 node1374Labels := rfl
  simpa [nodeValue1374, Sparse.eval] using hc.symm

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

theorem sound2035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2035 node2035Labels = Sparse.eval nodeValue2035 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2035) = mixedMoment B node2035 node2035Labels := rfl
  simpa [nodeValue2035, Sparse.eval] using hc.symm

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

theorem sound2062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2062 node2062Labels = Sparse.eval nodeValue2062 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2062) = mixedMoment B node2062 node2062Labels := rfl
  simpa [nodeValue2062, Sparse.eval] using hc.symm

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

theorem sound2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2481 node2481Labels = Sparse.eval nodeValue2481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2481) = mixedMoment B node2481 node2481Labels := rfl
  simpa [nodeValue2481, Sparse.eval] using hc.symm

theorem sound2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2486 node2486Labels = Sparse.eval nodeValue2486 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2486) = mixedMoment B node2486 node2486Labels := rfl
  simpa [nodeValue2486, Sparse.eval] using hc.symm

theorem sound2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2488 node2488Labels = Sparse.eval nodeValue2488 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2488) = mixedMoment B node2488 node2488Labels := rfl
  simpa [nodeValue2488, Sparse.eval] using hc.symm

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

theorem sound2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2515 node2515Labels = Sparse.eval nodeValue2515 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2515) = mixedMoment B node2515 node2515Labels := rfl
  simpa [nodeValue2515, Sparse.eval] using hc.symm

theorem sound2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2544 node2544Labels = Sparse.eval nodeValue2544 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2544) = mixedMoment B node2544 node2544Labels := rfl
  simpa [nodeValue2544, Sparse.eval] using hc.symm

theorem sound2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2545 node2545Labels = Sparse.eval nodeValue2545 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2545) = mixedMoment B node2545 node2545Labels := rfl
  simpa [nodeValue2545, Sparse.eval] using hc.symm

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

theorem sound2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2568 node2568Labels = Sparse.eval nodeValue2568 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2568) = mixedMoment B node2568 node2568Labels := rfl
  simpa [nodeValue2568, Sparse.eval] using hc.symm

theorem sound2597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2597 node2597Labels = Sparse.eval nodeValue2597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2597) = mixedMoment B node2597 node2597Labels := rfl
  simpa [nodeValue2597, Sparse.eval] using hc.symm

theorem sound2603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2603 node2603Labels = Sparse.eval nodeValue2603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2603) = mixedMoment B node2603 node2603Labels := rfl
  simpa [nodeValue2603, Sparse.eval] using hc.symm

theorem sound2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2616 node2616Labels = Sparse.eval nodeValue2616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2616) = mixedMoment B node2616 node2616Labels := rfl
  simpa [nodeValue2616, Sparse.eval] using hc.symm

theorem sound2619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2619 node2619Labels = Sparse.eval nodeValue2619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2619) = mixedMoment B node2619 node2619Labels := rfl
  simpa [nodeValue2619, Sparse.eval] using hc.symm

theorem sound2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2620 node2620Labels = Sparse.eval nodeValue2620 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2620) = mixedMoment B node2620 node2620Labels := rfl
  simpa [nodeValue2620, Sparse.eval] using hc.symm

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

theorem sound2634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2634 node2634Labels = Sparse.eval nodeValue2634 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2634) = mixedMoment B node2634 node2634Labels := rfl
  simpa [nodeValue2634, Sparse.eval] using hc.symm

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

theorem zero2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = 0 := by
  exact mixedMoment_alpha B hF node2720 node2720Labels 1 permutation203
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

theorem sound2714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2714 node2714Labels = Sparse.eval nodeValue2714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2714) = mixedMoment B node2714 node2714Labels := rfl
  simpa [nodeValue2714, Sparse.eval] using hc.symm

theorem sound2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2720 node2720Labels = Sparse.eval nodeValue2720 (mixedVector B) := by
  simpa only [nodeValue2720, Sparse.eval_nil] using zero2720 B _hB _hF

theorem sound2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2722 node2722Labels = Sparse.eval nodeValue2722 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2722) = mixedMoment B node2722 node2722Labels := rfl
  simpa [nodeValue2722, Sparse.eval] using hc.symm

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

theorem sound2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2739 node2739Labels = Sparse.eval nodeValue2739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2739) = mixedMoment B node2739 node2739Labels := rfl
  simpa [nodeValue2739, Sparse.eval] using hc.symm

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

theorem sound2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2763 node2763Labels = Sparse.eval nodeValue2763 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2763) = mixedMoment B node2763 node2763Labels := rfl
  simpa [nodeValue2763, Sparse.eval] using hc.symm

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

theorem sound2888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2888 node2888Labels = Sparse.eval nodeValue2888 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2888) = mixedMoment B node2888 node2888Labels := rfl
  simpa [nodeValue2888, Sparse.eval] using hc.symm

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

theorem sound2978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2978 node2978Labels = Sparse.eval nodeValue2978 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2978) = mixedMoment B node2978 node2978Labels := rfl
  simpa [nodeValue2978, Sparse.eval] using hc.symm

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

theorem sound3050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3050 node3050Labels = Sparse.eval nodeValue3050 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3050) = mixedMoment B node3050 node3050Labels := rfl
  simpa [nodeValue3050, Sparse.eval] using hc.symm

theorem sound3052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3052 node3052Labels = Sparse.eval nodeValue3052 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3052) = mixedMoment B node3052 node3052Labels := rfl
  simpa [nodeValue3052, Sparse.eval] using hc.symm

theorem sound3056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3056 node3056Labels = Sparse.eval nodeValue3056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3056) = mixedMoment B node3056 node3056Labels := rfl
  simpa [nodeValue3056, Sparse.eval] using hc.symm

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

theorem sound3540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3540 node3540Labels = Sparse.eval nodeValue3540 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3540) = mixedMoment B node3540 node3540Labels := rfl
  simpa [nodeValue3540, Sparse.eval] using hc.symm

theorem sound3548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3548 node3548Labels = Sparse.eval nodeValue3548 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3548) = mixedMoment B node3548 node3548Labels := rfl
  simpa [nodeValue3548, Sparse.eval] using hc.symm

theorem sound3582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3582 node3582Labels = Sparse.eval nodeValue3582 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3582) = mixedMoment B node3582 node3582Labels := rfl
  simpa [nodeValue3582, Sparse.eval] using hc.symm

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

theorem sound3809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3809 node3809Labels = Sparse.eval nodeValue3809 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3809) = mixedMoment B node3809 node3809Labels := rfl
  simpa [nodeValue3809, Sparse.eval] using hc.symm

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

theorem sound3877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3877 node3877Labels = Sparse.eval nodeValue3877 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3877) = mixedMoment B node3877 node3877Labels := rfl
  simpa [nodeValue3877, Sparse.eval] using hc.symm

theorem sound3903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3903 node3903Labels = Sparse.eval nodeValue3903 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3903) = mixedMoment B node3903 node3903Labels := rfl
  simpa [nodeValue3903, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources7
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm245 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA245 + difference 0 0) (sourceB245 + difference 0 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA245 + difference 0 0) (sourceB245 + difference 0 0) sourceC245) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA245 + difference 0 1) (sourceB245 + difference 1 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA245 + difference 0 1) (sourceB245 + difference 1 0) sourceC245) = raw6101 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6101; decide +kernel
    rw [ha]
    exact (canonical6101 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA245 + difference 0 2) (sourceB245 + difference 2 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA245 + difference 0 2) (sourceB245 + difference 2 0) sourceC245) = raw6102 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6102; decide +kernel
    rw [ha]
    exact (canonical6102 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA245 + difference 0 3) (sourceB245 + difference 3 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3050) := by
    have ha : (tripleCharges (sourceA245 + difference 0 3) (sourceB245 + difference 3 0) sourceC245) = raw6103 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6103; decide +kernel
    rw [ha]
    exact (canonical6103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA245 + difference 0 4) (sourceB245 + difference 4 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA245 + difference 0 4) (sourceB245 + difference 4 0) sourceC245) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA245 + difference 0 5) (sourceB245 + difference 5 0) sourceC245) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2603) := by
    have ha : (tripleCharges (sourceA245 + difference 0 5) (sourceB245 + difference 5 0) sourceC245) = raw6105 := by
      apply Matrix.ext; unfold tripleCharges sourceA245 sourceB245 sourceC245 difference raw6105; decide +kernel
    rw [ha]
    exact (canonical6105 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA245 + sourceB245) sourceC245) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA245 + sourceB245) sourceC245) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA245 sourceB245 sourceC245 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA245 sourceB245 sourceC245
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm245, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm246 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA246 + difference 0 1) (sourceB246 + difference 1 0) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3056) := by
    have ha : (tripleCharges (sourceA246 + difference 0 1) (sourceB246 + difference 1 0) sourceC246) = raw6101 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6101; decide +kernel
    rw [ha]
    exact (canonical6101 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA246 + difference 1 1) (sourceB246 + difference 1 1) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA246 + difference 1 1) (sourceB246 + difference 1 1) sourceC246) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA246 + difference 2 1) (sourceB246 + difference 1 2) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA246 + difference 2 1) (sourceB246 + difference 1 2) sourceC246) = raw6106 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6106; decide +kernel
    rw [ha]
    exact (canonical6106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA246 + difference 3 1) (sourceB246 + difference 1 3) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA246 + difference 3 1) (sourceB246 + difference 1 3) sourceC246) = raw6107 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6107; decide +kernel
    rw [ha]
    exact (canonical6107 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA246 + difference 4 1) (sourceB246 + difference 1 4) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1374) := by
    have ha : (tripleCharges (sourceA246 + difference 4 1) (sourceB246 + difference 1 4) sourceC246) = raw6108 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6108; decide +kernel
    rw [ha]
    exact (canonical6108 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA246 + difference 5 1) (sourceB246 + difference 1 5) sourceC246) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA246 + difference 5 1) (sourceB246 + difference 1 5) sourceC246) = raw6109 := by
      apply Matrix.ext; unfold tripleCharges sourceA246 sourceB246 sourceC246 difference raw6109; decide +kernel
    rw [ha]
    exact (canonical6109 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA246 + sourceB246) sourceC246) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA246 + sourceB246) sourceC246) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA246 sourceB246 sourceC246 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA246 sourceB246 sourceC246
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm246, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm247 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA247 + difference 2 0) (sourceB247 + difference 0 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2035) := by
    have ha : (tripleCharges (sourceA247 + difference 2 0) (sourceB247 + difference 0 2) sourceC247) = raw6110 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6110; decide +kernel
    rw [ha]
    exact (canonical6110 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA247 + difference 2 1) (sourceB247 + difference 1 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2978) := by
    have ha : (tripleCharges (sourceA247 + difference 2 1) (sourceB247 + difference 1 2) sourceC247) = raw6106 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6106; decide +kernel
    rw [ha]
    exact (canonical6106 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA247 + difference 2 2) (sourceB247 + difference 2 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA247 + difference 2 2) (sourceB247 + difference 2 2) sourceC247) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA247 + difference 2 3) (sourceB247 + difference 3 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2973) := by
    have ha : (tripleCharges (sourceA247 + difference 2 3) (sourceB247 + difference 3 2) sourceC247) = raw6111 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6111; decide +kernel
    rw [ha]
    exact (canonical6111 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA247 + difference 2 4) (sourceB247 + difference 4 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA247 + difference 2 4) (sourceB247 + difference 4 2) sourceC247) = raw6112 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6112; decide +kernel
    rw [ha]
    exact (canonical6112 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA247 + difference 2 5) (sourceB247 + difference 5 2) sourceC247) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2597) := by
    have ha : (tripleCharges (sourceA247 + difference 2 5) (sourceB247 + difference 5 2) sourceC247) = raw6113 := by
      apply Matrix.ext; unfold tripleCharges sourceA247 sourceB247 sourceC247 difference raw6113; decide +kernel
    rw [ha]
    exact (canonical6113 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA247 + sourceB247) sourceC247) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA247 + sourceB247) sourceC247) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA247 sourceB247 sourceC247 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA247 sourceB247 sourceC247
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm247, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm250 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA250 + difference 0 4) (sourceB250 + difference 4 0) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3582) := by
    have ha : (tripleCharges (sourceA250 + difference 0 4) (sourceB250 + difference 4 0) sourceC250) = raw6104 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6104; decide +kernel
    rw [ha]
    exact (canonical6104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA250 + difference 1 4) (sourceB250 + difference 4 1) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3633) := by
    have ha : (tripleCharges (sourceA250 + difference 1 4) (sourceB250 + difference 4 1) sourceC250) = raw6121 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6121; decide +kernel
    rw [ha]
    exact (canonical6121 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA250 + difference 2 4) (sourceB250 + difference 4 2) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA250 + difference 2 4) (sourceB250 + difference 4 2) sourceC250) = raw6112 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6112; decide +kernel
    rw [ha]
    exact (canonical6112 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA250 + difference 3 4) (sourceB250 + difference 4 3) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3540) := by
    have ha : (tripleCharges (sourceA250 + difference 3 4) (sourceB250 + difference 4 3) sourceC250) = raw6122 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6122; decide +kernel
    rw [ha]
    exact (canonical6122 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA250 + difference 4 4) (sourceB250 + difference 4 4) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA250 + difference 4 4) (sourceB250 + difference 4 4) sourceC250) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA250 + difference 5 4) (sourceB250 + difference 4 5) sourceC250) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA250 + difference 5 4) (sourceB250 + difference 4 5) sourceC250) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA250 sourceB250 sourceC250 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA250 + sourceB250) sourceC250) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA250 + sourceB250) sourceC250) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA250 sourceB250 sourceC250 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA250 sourceB250 sourceC250
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm250, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm251 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA251 + difference 5 0) (sourceB251 + difference 0 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA251 + difference 5 0) (sourceB251 + difference 0 5) sourceC251) = raw6124 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6124; decide +kernel
    rw [ha]
    exact (canonical6124 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA251 + difference 5 1) (sourceB251 + difference 1 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2888) := by
    have ha : (tripleCharges (sourceA251 + difference 5 1) (sourceB251 + difference 1 5) sourceC251) = raw6109 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6109; decide +kernel
    rw [ha]
    exact (canonical6109 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA251 + difference 5 2) (sourceB251 + difference 2 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA251 + difference 5 2) (sourceB251 + difference 2 5) sourceC251) = raw6117 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6117; decide +kernel
    rw [ha]
    exact (canonical6117 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA251 + difference 5 3) (sourceB251 + difference 3 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2879) := by
    have ha : (tripleCharges (sourceA251 + difference 5 3) (sourceB251 + difference 3 5) sourceC251) = raw6125 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6125; decide +kernel
    rw [ha]
    exact (canonical6125 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA251 + difference 5 4) (sourceB251 + difference 4 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3548) := by
    have ha : (tripleCharges (sourceA251 + difference 5 4) (sourceB251 + difference 4 5) sourceC251) = raw6123 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6123; decide +kernel
    rw [ha]
    exact (canonical6123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA251 + difference 5 5) (sourceB251 + difference 5 5) sourceC251) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3052) := by
    have ha : (tripleCharges (sourceA251 + difference 5 5) (sourceB251 + difference 5 5) sourceC251) = raw6100 := by
      apply Matrix.ext; unfold tripleCharges sourceA251 sourceB251 sourceC251 difference raw6100; decide +kernel
    rw [ha]
    exact (canonical6100 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA251 + sourceB251) sourceC251) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA251 + sourceB251) sourceC251) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA251 sourceB251 sourceC251 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA251 sourceB251 sourceC251
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm251, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm255 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA255 + difference 0 0) (sourceB255 + difference 0 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA255 + difference 0 0) (sourceB255 + difference 0 0) sourceC255) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA255 + difference 0 1) (sourceB255 + difference 1 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA255 + difference 0 1) (sourceB255 + difference 1 0) sourceC255) = raw6217 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6217; decide +kernel
    rw [ha]
    exact (canonical6217 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA255 + difference 0 2) (sourceB255 + difference 2 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA255 + difference 0 2) (sourceB255 + difference 2 0) sourceC255) = raw6218 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6218; decide +kernel
    rw [ha]
    exact (canonical6218 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA255 + difference 0 3) (sourceB255 + difference 3 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA255 + difference 0 3) (sourceB255 + difference 3 0) sourceC255) = raw6219 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6219; decide +kernel
    rw [ha]
    exact (canonical6219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA255 + difference 0 4) (sourceB255 + difference 4 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3814) := by
    have ha : (tripleCharges (sourceA255 + difference 0 4) (sourceB255 + difference 4 0) sourceC255) = raw6220 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6220; decide +kernel
    rw [ha]
    exact (canonical6220 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA255 + difference 0 5) (sourceB255 + difference 5 0) sourceC255) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3903) := by
    have ha : (tripleCharges (sourceA255 + difference 0 5) (sourceB255 + difference 5 0) sourceC255) = raw6221 := by
      apply Matrix.ext; unfold tripleCharges sourceA255 sourceB255 sourceC255 difference raw6221; decide +kernel
    rw [ha]
    exact (canonical6221 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA255 + sourceB255) sourceC255) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA255 + sourceB255) sourceC255) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA255 sourceB255 sourceC255 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA255 sourceB255 sourceC255
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm255, Integer.Sparse.eval]
  linarith only [hs]

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

theorem sourceEq256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm256 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA256 + difference 0 0) (sourceB256 + difference 0 0) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA256 + difference 0 0) (sourceB256 + difference 0 0) sourceC256) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA256 + difference 1 0) (sourceB256 + difference 0 1) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1263) := by
    have ha : (tripleCharges (sourceA256 + difference 1 0) (sourceB256 + difference 0 1) sourceC256) = raw6223 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6223; decide +kernel
    rw [ha]
    exact (canonical6223 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA256 + difference 2 0) (sourceB256 + difference 0 2) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA256 + difference 2 0) (sourceB256 + difference 0 2) sourceC256) = raw6224 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6224; decide +kernel
    rw [ha]
    exact (canonical6224 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA256 + difference 3 0) (sourceB256 + difference 0 3) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA256 + difference 3 0) (sourceB256 + difference 0 3) sourceC256) = raw6225 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6225; decide +kernel
    rw [ha]
    exact (canonical6225 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA256 + difference 4 0) (sourceB256 + difference 0 4) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA256 + difference 4 0) (sourceB256 + difference 0 4) sourceC256) = raw6226 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6226; decide +kernel
    rw [ha]
    exact (canonical6226 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA256 + difference 5 0) (sourceB256 + difference 0 5) sourceC256) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1218) := by
    have ha : (tripleCharges (sourceA256 + difference 5 0) (sourceB256 + difference 0 5) sourceC256) = raw6227 := by
      apply Matrix.ext; unfold tripleCharges sourceA256 sourceB256 sourceC256 difference raw6227; decide +kernel
    rw [ha]
    exact (canonical6227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA256 + sourceB256) sourceC256) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA256 + sourceB256) sourceC256) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA256 sourceB256 sourceC256 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA256 sourceB256 sourceC256
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm256, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm257 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA257 + difference 1 0) (sourceB257 + difference 0 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1263) := by
    have ha : (tripleCharges (sourceA257 + difference 1 0) (sourceB257 + difference 0 1) sourceC257) = raw6223 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6223; decide +kernel
    rw [ha]
    exact (canonical6223 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA257 + difference 1 1) (sourceB257 + difference 1 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA257 + difference 1 1) (sourceB257 + difference 1 1) sourceC257) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA257 + difference 1 2) (sourceB257 + difference 2 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA257 + difference 1 2) (sourceB257 + difference 2 1) sourceC257) = raw6228 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6228; decide +kernel
    rw [ha]
    exact (canonical6228 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA257 + difference 1 3) (sourceB257 + difference 3 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA257 + difference 1 3) (sourceB257 + difference 3 1) sourceC257) = raw6229 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6229; decide +kernel
    rw [ha]
    exact (canonical6229 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA257 + difference 1 4) (sourceB257 + difference 4 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2758) := by
    have ha : (tripleCharges (sourceA257 + difference 1 4) (sourceB257 + difference 4 1) sourceC257) = raw6230 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6230; decide +kernel
    rw [ha]
    exact (canonical6230 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA257 + difference 1 5) (sourceB257 + difference 5 1) sourceC257) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2763) := by
    have ha : (tripleCharges (sourceA257 + difference 1 5) (sourceB257 + difference 5 1) sourceC257) = raw6231 := by
      apply Matrix.ext; unfold tripleCharges sourceA257 sourceB257 sourceC257 difference raw6231; decide +kernel
    rw [ha]
    exact (canonical6231 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA257 + sourceB257) sourceC257) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA257 + sourceB257) sourceC257) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA257 sourceB257 sourceC257 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA257 sourceB257 sourceC257
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm257, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm258 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA258 + difference 0 1) (sourceB258 + difference 1 0) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3809) := by
    have ha : (tripleCharges (sourceA258 + difference 0 1) (sourceB258 + difference 1 0) sourceC258) = raw6217 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6217; decide +kernel
    rw [ha]
    exact (canonical6217 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA258 + difference 1 1) (sourceB258 + difference 1 1) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA258 + difference 1 1) (sourceB258 + difference 1 1) sourceC258) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA258 + difference 2 1) (sourceB258 + difference 1 2) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA258 + difference 2 1) (sourceB258 + difference 1 2) sourceC258) = raw6232 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6232; decide +kernel
    rw [ha]
    exact (canonical6232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA258 + difference 3 1) (sourceB258 + difference 1 3) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA258 + difference 3 1) (sourceB258 + difference 1 3) sourceC258) = raw6233 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6233; decide +kernel
    rw [ha]
    exact (canonical6233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA258 + difference 4 1) (sourceB258 + difference 1 4) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA258 + difference 4 1) (sourceB258 + difference 1 4) sourceC258) = raw6234 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6234; decide +kernel
    rw [ha]
    exact (canonical6234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA258 + difference 5 1) (sourceB258 + difference 1 5) sourceC258) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2486) := by
    have ha : (tripleCharges (sourceA258 + difference 5 1) (sourceB258 + difference 1 5) sourceC258) = raw6235 := by
      apply Matrix.ext; unfold tripleCharges sourceA258 sourceB258 sourceC258 difference raw6235; decide +kernel
    rw [ha]
    exact (canonical6235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA258 + sourceB258) sourceC258) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA258 + sourceB258) sourceC258) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA258 sourceB258 sourceC258 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA258 sourceB258 sourceC258
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm258, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm259 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA259 + difference 2 0) (sourceB259 + difference 0 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1214) := by
    have ha : (tripleCharges (sourceA259 + difference 2 0) (sourceB259 + difference 0 2) sourceC259) = raw6224 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6224; decide +kernel
    rw [ha]
    exact (canonical6224 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA259 + difference 2 1) (sourceB259 + difference 1 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2481) := by
    have ha : (tripleCharges (sourceA259 + difference 2 1) (sourceB259 + difference 1 2) sourceC259) = raw6232 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6232; decide +kernel
    rw [ha]
    exact (canonical6232 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA259 + difference 2 2) (sourceB259 + difference 2 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA259 + difference 2 2) (sourceB259 + difference 2 2) sourceC259) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA259 + difference 2 3) (sourceB259 + difference 3 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA259 + difference 2 3) (sourceB259 + difference 3 2) sourceC259) = raw6236 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6236; decide +kernel
    rw [ha]
    exact (canonical6236 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA259 + difference 2 4) (sourceB259 + difference 4 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2714) := by
    have ha : (tripleCharges (sourceA259 + difference 2 4) (sourceB259 + difference 4 2) sourceC259) = raw6237 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6237; decide +kernel
    rw [ha]
    exact (canonical6237 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA259 + difference 2 5) (sourceB259 + difference 5 2) sourceC259) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2720) := by
    have ha : (tripleCharges (sourceA259 + difference 2 5) (sourceB259 + difference 5 2) sourceC259) = raw6238 := by
      apply Matrix.ext; unfold tripleCharges sourceA259 sourceB259 sourceC259 difference raw6238; decide +kernel
    rw [ha]
    exact (canonical6238 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA259 + sourceB259) sourceC259) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA259 + sourceB259) sourceC259) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA259 sourceB259 sourceC259 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA259 sourceB259 sourceC259
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm259, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm260 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA260 + difference 0 2) (sourceB260 + difference 2 0) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3839) := by
    have ha : (tripleCharges (sourceA260 + difference 0 2) (sourceB260 + difference 2 0) sourceC260) = raw6218 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6218; decide +kernel
    rw [ha]
    exact (canonical6218 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA260 + difference 1 2) (sourceB260 + difference 2 1) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2568) := by
    have ha : (tripleCharges (sourceA260 + difference 1 2) (sourceB260 + difference 2 1) sourceC260) = raw6228 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6228; decide +kernel
    rw [ha]
    exact (canonical6228 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA260 + difference 2 2) (sourceB260 + difference 2 2) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA260 + difference 2 2) (sourceB260 + difference 2 2) sourceC260) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA260 + difference 3 2) (sourceB260 + difference 2 3) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA260 + difference 3 2) (sourceB260 + difference 2 3) sourceC260) = raw6239 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6239; decide +kernel
    rw [ha]
    exact (canonical6239 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA260 + difference 4 2) (sourceB260 + difference 2 4) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA260 + difference 4 2) (sourceB260 + difference 2 4) sourceC260) = raw6240 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6240; decide +kernel
    rw [ha]
    exact (canonical6240 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA260 + difference 5 2) (sourceB260 + difference 2 5) sourceC260) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2544) := by
    have ha : (tripleCharges (sourceA260 + difference 5 2) (sourceB260 + difference 2 5) sourceC260) = raw6241 := by
      apply Matrix.ext; unfold tripleCharges sourceA260 sourceB260 sourceC260 difference raw6241; decide +kernel
    rw [ha]
    exact (canonical6241 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA260 + sourceB260) sourceC260) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA260 + sourceB260) sourceC260) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA260 sourceB260 sourceC260 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA260 sourceB260 sourceC260
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm260, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm261 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA261 + difference 3 0) (sourceB261 + difference 0 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA261 + difference 3 0) (sourceB261 + difference 0 3) sourceC261) = raw6225 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6225; decide +kernel
    rw [ha]
    exact (canonical6225 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA261 + difference 3 1) (sourceB261 + difference 1 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA261 + difference 3 1) (sourceB261 + difference 1 3) sourceC261) = raw6233 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6233; decide +kernel
    rw [ha]
    exact (canonical6233 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA261 + difference 3 2) (sourceB261 + difference 2 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2557) := by
    have ha : (tripleCharges (sourceA261 + difference 3 2) (sourceB261 + difference 2 3) sourceC261) = raw6239 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6239; decide +kernel
    rw [ha]
    exact (canonical6239 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA261 + difference 3 3) (sourceB261 + difference 3 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA261 + difference 3 3) (sourceB261 + difference 3 3) sourceC261) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA261 + difference 3 4) (sourceB261 + difference 4 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2732) := by
    have ha : (tripleCharges (sourceA261 + difference 3 4) (sourceB261 + difference 4 3) sourceC261) = raw6242 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6242; decide +kernel
    rw [ha]
    exact (canonical6242 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA261 + difference 3 5) (sourceB261 + difference 5 3) sourceC261) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2739) := by
    have ha : (tripleCharges (sourceA261 + difference 3 5) (sourceB261 + difference 5 3) sourceC261) = raw6243 := by
      apply Matrix.ext; unfold tripleCharges sourceA261 sourceB261 sourceC261 difference raw6243; decide +kernel
    rw [ha]
    exact (canonical6243 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA261 + sourceB261) sourceC261) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA261 + sourceB261) sourceC261) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA261 sourceB261 sourceC261 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA261 sourceB261 sourceC261
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm261, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm262 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA262 + difference 0 3) (sourceB262 + difference 3 0) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3877) := by
    have ha : (tripleCharges (sourceA262 + difference 0 3) (sourceB262 + difference 3 0) sourceC262) = raw6219 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6219; decide +kernel
    rw [ha]
    exact (canonical6219 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA262 + difference 1 3) (sourceB262 + difference 3 1) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2634) := by
    have ha : (tripleCharges (sourceA262 + difference 1 3) (sourceB262 + difference 3 1) sourceC262) = raw6229 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6229; decide +kernel
    rw [ha]
    exact (canonical6229 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA262 + difference 2 3) (sourceB262 + difference 3 2) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2616) := by
    have ha : (tripleCharges (sourceA262 + difference 2 3) (sourceB262 + difference 3 2) sourceC262) = raw6236 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6236; decide +kernel
    rw [ha]
    exact (canonical6236 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA262 + difference 3 3) (sourceB262 + difference 3 3) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA262 + difference 3 3) (sourceB262 + difference 3 3) sourceC262) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA262 + difference 4 3) (sourceB262 + difference 3 4) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA262 + difference 4 3) (sourceB262 + difference 3 4) sourceC262) = raw6244 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6244; decide +kernel
    rw [ha]
    exact (canonical6244 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA262 + difference 5 3) (sourceB262 + difference 3 5) sourceC262) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2619) := by
    have ha : (tripleCharges (sourceA262 + difference 5 3) (sourceB262 + difference 3 5) sourceC262) = raw6245 := by
      apply Matrix.ext; unfold tripleCharges sourceA262 sourceB262 sourceC262 difference raw6245; decide +kernel
    rw [ha]
    exact (canonical6245 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA262 + sourceB262) sourceC262) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA262 + sourceB262) sourceC262) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA262 sourceB262 sourceC262 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA262 sourceB262 sourceC262
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm262, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm263 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA263 + difference 4 0) (sourceB263 + difference 0 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1219) := by
    have ha : (tripleCharges (sourceA263 + difference 4 0) (sourceB263 + difference 0 4) sourceC263) = raw6226 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6226; decide +kernel
    rw [ha]
    exact (canonical6226 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA263 + difference 4 1) (sourceB263 + difference 1 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2488) := by
    have ha : (tripleCharges (sourceA263 + difference 4 1) (sourceB263 + difference 1 4) sourceC263) = raw6234 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6234; decide +kernel
    rw [ha]
    exact (canonical6234 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA263 + difference 4 2) (sourceB263 + difference 2 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2545) := by
    have ha : (tripleCharges (sourceA263 + difference 4 2) (sourceB263 + difference 2 4) sourceC263) = raw6240 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6240; decide +kernel
    rw [ha]
    exact (canonical6240 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA263 + difference 4 3) (sourceB263 + difference 3 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2620) := by
    have ha : (tripleCharges (sourceA263 + difference 4 3) (sourceB263 + difference 3 4) sourceC263) = raw6244 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6244; decide +kernel
    rw [ha]
    exact (canonical6244 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA263 + difference 4 4) (sourceB263 + difference 4 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2724) := by
    have ha : (tripleCharges (sourceA263 + difference 4 4) (sourceB263 + difference 4 4) sourceC263) = raw6216 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6216; decide +kernel
    rw [ha]
    exact (canonical6216 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA263 + difference 4 5) (sourceB263 + difference 5 4) sourceC263) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2722) := by
    have ha : (tripleCharges (sourceA263 + difference 4 5) (sourceB263 + difference 5 4) sourceC263) = raw6246 := by
      apply Matrix.ext; unfold tripleCharges sourceA263 sourceB263 sourceC263 difference raw6246; decide +kernel
    rw [ha]
    exact (canonical6246 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA263 + sourceB263) sourceC263) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA263 + sourceB263) sourceC263) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA263 sourceB263 sourceC263 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA263 sourceB263 sourceC263
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm263, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck208 : Integer.Sparse.reindex keyMap MixedData.row208 = numericRow208 := by decide +kernel

theorem numericCheck208 (x : Master → ℝ) : Integer.Sparse.eval numericRow208 x =
    (1 : ℝ) * reducedSource208 x := by
  norm_num [numericRow208, reducedSource208, Integer.Sparse.eval, Sparse.eval, nodeValue2603, nodeValue3050, nodeValue3052, nodeValue3056, nodeValue3582, nodeValue4084]

theorem reindexCheck209 : Integer.Sparse.reindex keyMap MixedData.row209 = numericRow209 := by decide +kernel

theorem numericCheck209 (x : Master → ℝ) : Integer.Sparse.eval numericRow209 x =
    (1 : ℝ) * reducedSource209 x := by
  norm_num [numericRow209, reducedSource209, Integer.Sparse.eval, Sparse.eval, nodeValue1374, nodeValue2888, nodeValue2978, nodeValue3052, nodeValue3056, nodeValue4084]

theorem reindexCheck210 : Integer.Sparse.reindex keyMap MixedData.row210 = numericRow210 := by decide +kernel

theorem numericCheck210 (x : Master → ℝ) : Integer.Sparse.eval numericRow210 x =
    (1 : ℝ) * reducedSource210 x := by
  norm_num [numericRow210, reducedSource210, Integer.Sparse.eval, Sparse.eval, nodeValue2035, nodeValue2597, nodeValue2973, nodeValue2978, nodeValue3052, nodeValue3540, nodeValue4084]

theorem reindexCheck211 : Integer.Sparse.reindex keyMap MixedData.row211 = numericRow211 := by decide +kernel

theorem numericCheck211 (x : Master → ℝ) : Integer.Sparse.eval numericRow211 x =
    (1 : ℝ) * reducedSource211 x := by
  norm_num [numericRow211, reducedSource211, Integer.Sparse.eval, Sparse.eval, nodeValue3052, nodeValue3540, nodeValue3548, nodeValue3582, nodeValue3633, nodeValue4084]

theorem reindexCheck212 : Integer.Sparse.reindex keyMap MixedData.row212 = numericRow212 := by decide +kernel

theorem numericCheck212 (x : Master → ℝ) : Integer.Sparse.eval numericRow212 x =
    (1 : ℝ) * reducedSource212 x := by
  norm_num [numericRow212, reducedSource212, Integer.Sparse.eval, Sparse.eval, nodeValue2062, nodeValue2879, nodeValue2888, nodeValue3052, nodeValue3548, nodeValue4084]

theorem reindexCheck215 : Integer.Sparse.reindex keyMap MixedData.row215 = numericRow215 := by decide +kernel

theorem numericCheck215 (x : Master → ℝ) : Integer.Sparse.eval numericRow215 x =
    (1 : ℝ) * reducedSource215 x := by
  norm_num [numericRow215, reducedSource215, Integer.Sparse.eval, Sparse.eval, nodeValue2724, nodeValue3809, nodeValue3814, nodeValue3839, nodeValue3877, nodeValue3903, nodeValue4092]

theorem reindexCheck216 : Integer.Sparse.reindex keyMap MixedData.row216 = numericRow216 := by decide +kernel

theorem numericCheck216 (x : Master → ℝ) : Integer.Sparse.eval numericRow216 x =
    (1 : ℝ) * reducedSource216 x := by
  norm_num [numericRow216, reducedSource216, Integer.Sparse.eval, Sparse.eval, nodeValue1214, nodeValue1218, nodeValue1219, nodeValue1241, nodeValue1263, nodeValue2724, nodeValue4092]

theorem reindexCheck217 : Integer.Sparse.reindex keyMap MixedData.row217 = numericRow217 := by decide +kernel

theorem numericCheck217 (x : Master → ℝ) : Integer.Sparse.eval numericRow217 x =
    (1 : ℝ) * reducedSource217 x := by
  norm_num [numericRow217, reducedSource217, Integer.Sparse.eval, Sparse.eval, nodeValue1263, nodeValue2568, nodeValue2634, nodeValue2724, nodeValue2758, nodeValue2763, nodeValue4092]

theorem reindexCheck218 : Integer.Sparse.reindex keyMap MixedData.row218 = numericRow218 := by decide +kernel

theorem numericCheck218 (x : Master → ℝ) : Integer.Sparse.eval numericRow218 x =
    (1 : ℝ) * reducedSource218 x := by
  norm_num [numericRow218, reducedSource218, Integer.Sparse.eval, Sparse.eval, nodeValue2481, nodeValue2486, nodeValue2488, nodeValue2515, nodeValue2724, nodeValue3809, nodeValue4092]

theorem reindexCheck219 : Integer.Sparse.reindex keyMap MixedData.row219 = numericRow219 := by decide +kernel

theorem numericCheck219 (x : Master → ℝ) : Integer.Sparse.eval numericRow219 x =
    (1 : ℝ) * reducedSource219 x := by
  norm_num [numericRow219, reducedSource219, Integer.Sparse.eval, Sparse.eval, nodeValue1214, nodeValue2481, nodeValue2616, nodeValue2714, nodeValue2720, nodeValue2724, nodeValue4092]

theorem reindexCheck220 : Integer.Sparse.reindex keyMap MixedData.row220 = numericRow220 := by decide +kernel

theorem numericCheck220 (x : Master → ℝ) : Integer.Sparse.eval numericRow220 x =
    (1 : ℝ) * reducedSource220 x := by
  norm_num [numericRow220, reducedSource220, Integer.Sparse.eval, Sparse.eval, nodeValue2544, nodeValue2545, nodeValue2557, nodeValue2568, nodeValue2724, nodeValue3839, nodeValue4092]

theorem reindexCheck221 : Integer.Sparse.reindex keyMap MixedData.row221 = numericRow221 := by decide +kernel

theorem numericCheck221 (x : Master → ℝ) : Integer.Sparse.eval numericRow221 x =
    (1 : ℝ) * reducedSource221 x := by
  norm_num [numericRow221, reducedSource221, Integer.Sparse.eval, Sparse.eval, nodeValue1241, nodeValue2515, nodeValue2557, nodeValue2724, nodeValue2732, nodeValue2739, nodeValue4092]

theorem reindexCheck222 : Integer.Sparse.reindex keyMap MixedData.row222 = numericRow222 := by decide +kernel

theorem numericCheck222 (x : Master → ℝ) : Integer.Sparse.eval numericRow222 x =
    (1 : ℝ) * reducedSource222 x := by
  norm_num [numericRow222, reducedSource222, Integer.Sparse.eval, Sparse.eval, nodeValue2616, nodeValue2619, nodeValue2620, nodeValue2634, nodeValue2724, nodeValue3877, nodeValue4092]

theorem reindexCheck223 : Integer.Sparse.reindex keyMap MixedData.row223 = numericRow223 := by decide +kernel

theorem numericCheck223 (x : Master → ℝ) : Integer.Sparse.eval numericRow223 x =
    (1 : ℝ) * reducedSource223 x := by
  norm_num [numericRow223, reducedSource223, Integer.Sparse.eval, Sparse.eval, nodeValue1219, nodeValue2488, nodeValue2545, nodeValue2620, nodeValue2722, nodeValue2724, nodeValue4092]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource208 (mixedVector B) = 0 := by
  have h2603 : mixedVector B (Sum.inr 2603) = Sparse.eval nodeValue2603 (mixedVector B) := by
    change mixedMoment B node2603 node2603Labels = _
    exact sound2603 B hB hF
  have h3050 : mixedVector B (Sum.inr 3050) = Sparse.eval nodeValue3050 (mixedVector B) := by
    change mixedMoment B node3050 node3050Labels = _
    exact sound3050 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm245, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2603, h3050, h3052, h3056, h3582, h4084, reducedSource208] using sourceEq245 B hB

theorem rowSound208 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row208 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck208, numericCheck208, reducedZero208 B hB hF, mul_zero]

theorem reducedZero209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource209 (mixedVector B) = 0 := by
  have h1374 : mixedVector B (Sum.inr 1374) = Sparse.eval nodeValue1374 (mixedVector B) := by
    change mixedMoment B node1374 node1374Labels = _
    exact sound1374 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h2978 : mixedVector B (Sum.inr 2978) = Sparse.eval nodeValue2978 (mixedVector B) := by
    change mixedMoment B node2978 node2978Labels = _
    exact sound2978 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3056 : mixedVector B (Sum.inr 3056) = Sparse.eval nodeValue3056 (mixedVector B) := by
    change mixedMoment B node3056 node3056Labels = _
    exact sound3056 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm246, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1374, h2888, h2978, h3052, h3056, h4084, reducedSource209] using sourceEq246 B hB

theorem rowSound209 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row209 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck209, numericCheck209, reducedZero209 B hB hF, mul_zero]

theorem reducedZero210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource210 (mixedVector B) = 0 := by
  have h2035 : mixedVector B (Sum.inr 2035) = Sparse.eval nodeValue2035 (mixedVector B) := by
    change mixedMoment B node2035 node2035Labels = _
    exact sound2035 B hB hF
  have h2597 : mixedVector B (Sum.inr 2597) = Sparse.eval nodeValue2597 (mixedVector B) := by
    change mixedMoment B node2597 node2597Labels = _
    exact sound2597 B hB hF
  have h2973 : mixedVector B (Sum.inr 2973) = Sparse.eval nodeValue2973 (mixedVector B) := by
    change mixedMoment B node2973 node2973Labels = _
    exact sound2973 B hB hF
  have h2978 : mixedVector B (Sum.inr 2978) = Sparse.eval nodeValue2978 (mixedVector B) := by
    change mixedMoment B node2978 node2978Labels = _
    exact sound2978 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm247, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2035, h2597, h2973, h2978, h3052, h3540, h4084, reducedSource210] using sourceEq247 B hB

theorem rowSound210 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row210 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck210, numericCheck210, reducedZero210 B hB hF, mul_zero]

theorem reducedZero211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource211 (mixedVector B) = 0 := by
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3540 : mixedVector B (Sum.inr 3540) = Sparse.eval nodeValue3540 (mixedVector B) := by
    change mixedMoment B node3540 node3540Labels = _
    exact sound3540 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h3582 : mixedVector B (Sum.inr 3582) = Sparse.eval nodeValue3582 (mixedVector B) := by
    change mixedMoment B node3582 node3582Labels = _
    exact sound3582 B hB hF
  have h3633 : mixedVector B (Sum.inr 3633) = Sparse.eval nodeValue3633 (mixedVector B) := by
    change mixedMoment B node3633 node3633Labels = _
    exact sound3633 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm250, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3052, h3540, h3548, h3582, h3633, h4084, reducedSource211] using sourceEq250 B hB

theorem rowSound211 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row211 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck211, numericCheck211, reducedZero211 B hB hF, mul_zero]

theorem reducedZero212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource212 (mixedVector B) = 0 := by
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h2879 : mixedVector B (Sum.inr 2879) = Sparse.eval nodeValue2879 (mixedVector B) := by
    change mixedMoment B node2879 node2879Labels = _
    exact sound2879 B hB hF
  have h2888 : mixedVector B (Sum.inr 2888) = Sparse.eval nodeValue2888 (mixedVector B) := by
    change mixedMoment B node2888 node2888Labels = _
    exact sound2888 B hB hF
  have h3052 : mixedVector B (Sum.inr 3052) = Sparse.eval nodeValue3052 (mixedVector B) := by
    change mixedMoment B node3052 node3052Labels = _
    exact sound3052 B hB hF
  have h3548 : mixedVector B (Sum.inr 3548) = Sparse.eval nodeValue3548 (mixedVector B) := by
    change mixedMoment B node3548 node3548Labels = _
    exact sound3548 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm251, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2062, h2879, h2888, h3052, h3548, h4084, reducedSource212] using sourceEq251 B hB

theorem rowSound212 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row212 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck212, numericCheck212, reducedZero212 B hB hF, mul_zero]

theorem reducedZero215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource215 (mixedVector B) = 0 := by
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h3814 : mixedVector B (Sum.inr 3814) = Sparse.eval nodeValue3814 (mixedVector B) := by
    change mixedMoment B node3814 node3814Labels = _
    exact sound3814 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h3903 : mixedVector B (Sum.inr 3903) = Sparse.eval nodeValue3903 (mixedVector B) := by
    change mixedMoment B node3903 node3903Labels = _
    exact sound3903 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm255, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2724, h3809, h3814, h3839, h3877, h3903, h4092, reducedSource215] using sourceEq255 B hB

theorem rowSound215 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row215 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck215, numericCheck215, reducedZero215 B hB hF, mul_zero]

theorem reducedZero216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource216 (mixedVector B) = 0 := by
  have h1214 : mixedVector B (Sum.inr 1214) = Sparse.eval nodeValue1214 (mixedVector B) := by
    change mixedMoment B node1214 node1214Labels = _
    exact sound1214 B hB hF
  have h1218 : mixedVector B (Sum.inr 1218) = Sparse.eval nodeValue1218 (mixedVector B) := by
    change mixedMoment B node1218 node1218Labels = _
    exact sound1218 B hB hF
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h1263 : mixedVector B (Sum.inr 1263) = Sparse.eval nodeValue1263 (mixedVector B) := by
    change mixedMoment B node1263 node1263Labels = _
    exact sound1263 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm256, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1214, h1218, h1219, h1241, h1263, h2724, h4092, reducedSource216] using sourceEq256 B hB

theorem rowSound216 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row216 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck216, numericCheck216, reducedZero216 B hB hF, mul_zero]

theorem reducedZero217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource217 (mixedVector B) = 0 := by
  have h1263 : mixedVector B (Sum.inr 1263) = Sparse.eval nodeValue1263 (mixedVector B) := by
    change mixedMoment B node1263 node1263Labels = _
    exact sound1263 B hB hF
  have h2568 : mixedVector B (Sum.inr 2568) = Sparse.eval nodeValue2568 (mixedVector B) := by
    change mixedMoment B node2568 node2568Labels = _
    exact sound2568 B hB hF
  have h2634 : mixedVector B (Sum.inr 2634) = Sparse.eval nodeValue2634 (mixedVector B) := by
    change mixedMoment B node2634 node2634Labels = _
    exact sound2634 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2758 : mixedVector B (Sum.inr 2758) = Sparse.eval nodeValue2758 (mixedVector B) := by
    change mixedMoment B node2758 node2758Labels = _
    exact sound2758 B hB hF
  have h2763 : mixedVector B (Sum.inr 2763) = Sparse.eval nodeValue2763 (mixedVector B) := by
    change mixedMoment B node2763 node2763Labels = _
    exact sound2763 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm257, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1263, h2568, h2634, h2724, h2758, h2763, h4092, reducedSource217] using sourceEq257 B hB

theorem rowSound217 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row217 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck217, numericCheck217, reducedZero217 B hB hF, mul_zero]

theorem reducedZero218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource218 (mixedVector B) = 0 := by
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2486 : mixedVector B (Sum.inr 2486) = Sparse.eval nodeValue2486 (mixedVector B) := by
    change mixedMoment B node2486 node2486Labels = _
    exact sound2486 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h3809 : mixedVector B (Sum.inr 3809) = Sparse.eval nodeValue3809 (mixedVector B) := by
    change mixedMoment B node3809 node3809Labels = _
    exact sound3809 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm258, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2481, h2486, h2488, h2515, h2724, h3809, h4092, reducedSource218] using sourceEq258 B hB

theorem rowSound218 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row218 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck218, numericCheck218, reducedZero218 B hB hF, mul_zero]

theorem reducedZero219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource219 (mixedVector B) = 0 := by
  have h1214 : mixedVector B (Sum.inr 1214) = Sparse.eval nodeValue1214 (mixedVector B) := by
    change mixedMoment B node1214 node1214Labels = _
    exact sound1214 B hB hF
  have h2481 : mixedVector B (Sum.inr 2481) = Sparse.eval nodeValue2481 (mixedVector B) := by
    change mixedMoment B node2481 node2481Labels = _
    exact sound2481 B hB hF
  have h2616 : mixedVector B (Sum.inr 2616) = Sparse.eval nodeValue2616 (mixedVector B) := by
    change mixedMoment B node2616 node2616Labels = _
    exact sound2616 B hB hF
  have h2714 : mixedVector B (Sum.inr 2714) = Sparse.eval nodeValue2714 (mixedVector B) := by
    change mixedMoment B node2714 node2714Labels = _
    exact sound2714 B hB hF
  have h2720 : mixedVector B (Sum.inr 2720) = Sparse.eval nodeValue2720 (mixedVector B) := by
    change mixedMoment B node2720 node2720Labels = _
    exact sound2720 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm259, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1214, h2481, h2616, h2714, h2720, h2724, h4092, reducedSource219] using sourceEq259 B hB

theorem rowSound219 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row219 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck219, numericCheck219, reducedZero219 B hB hF, mul_zero]

theorem reducedZero220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource220 (mixedVector B) = 0 := by
  have h2544 : mixedVector B (Sum.inr 2544) = Sparse.eval nodeValue2544 (mixedVector B) := by
    change mixedMoment B node2544 node2544Labels = _
    exact sound2544 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h2568 : mixedVector B (Sum.inr 2568) = Sparse.eval nodeValue2568 (mixedVector B) := by
    change mixedMoment B node2568 node2568Labels = _
    exact sound2568 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h3839 : mixedVector B (Sum.inr 3839) = Sparse.eval nodeValue3839 (mixedVector B) := by
    change mixedMoment B node3839 node3839Labels = _
    exact sound3839 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm260, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2544, h2545, h2557, h2568, h2724, h3839, h4092, reducedSource220] using sourceEq260 B hB

theorem rowSound220 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row220 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck220, numericCheck220, reducedZero220 B hB hF, mul_zero]

theorem reducedZero221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource221 (mixedVector B) = 0 := by
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h2557 : mixedVector B (Sum.inr 2557) = Sparse.eval nodeValue2557 (mixedVector B) := by
    change mixedMoment B node2557 node2557Labels = _
    exact sound2557 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h2732 : mixedVector B (Sum.inr 2732) = Sparse.eval nodeValue2732 (mixedVector B) := by
    change mixedMoment B node2732 node2732Labels = _
    exact sound2732 B hB hF
  have h2739 : mixedVector B (Sum.inr 2739) = Sparse.eval nodeValue2739 (mixedVector B) := by
    change mixedMoment B node2739 node2739Labels = _
    exact sound2739 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm261, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1241, h2515, h2557, h2724, h2732, h2739, h4092, reducedSource221] using sourceEq261 B hB

theorem rowSound221 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row221 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck221, numericCheck221, reducedZero221 B hB hF, mul_zero]

theorem reducedZero222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource222 (mixedVector B) = 0 := by
  have h2616 : mixedVector B (Sum.inr 2616) = Sparse.eval nodeValue2616 (mixedVector B) := by
    change mixedMoment B node2616 node2616Labels = _
    exact sound2616 B hB hF
  have h2619 : mixedVector B (Sum.inr 2619) = Sparse.eval nodeValue2619 (mixedVector B) := by
    change mixedMoment B node2619 node2619Labels = _
    exact sound2619 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2634 : mixedVector B (Sum.inr 2634) = Sparse.eval nodeValue2634 (mixedVector B) := by
    change mixedMoment B node2634 node2634Labels = _
    exact sound2634 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h3877 : mixedVector B (Sum.inr 3877) = Sparse.eval nodeValue3877 (mixedVector B) := by
    change mixedMoment B node3877 node3877Labels = _
    exact sound3877 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm262, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2616, h2619, h2620, h2634, h2724, h3877, h4092, reducedSource222] using sourceEq262 B hB

theorem rowSound222 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row222 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck222, numericCheck222, reducedZero222 B hB hF, mul_zero]

theorem reducedZero223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource223 (mixedVector B) = 0 := by
  have h1219 : mixedVector B (Sum.inr 1219) = Sparse.eval nodeValue1219 (mixedVector B) := by
    change mixedMoment B node1219 node1219Labels = _
    exact sound1219 B hB hF
  have h2488 : mixedVector B (Sum.inr 2488) = Sparse.eval nodeValue2488 (mixedVector B) := by
    change mixedMoment B node2488 node2488Labels = _
    exact sound2488 B hB hF
  have h2545 : mixedVector B (Sum.inr 2545) = Sparse.eval nodeValue2545 (mixedVector B) := by
    change mixedMoment B node2545 node2545Labels = _
    exact sound2545 B hB hF
  have h2620 : mixedVector B (Sum.inr 2620) = Sparse.eval nodeValue2620 (mixedVector B) := by
    change mixedMoment B node2620 node2620Labels = _
    exact sound2620 B hB hF
  have h2722 : mixedVector B (Sum.inr 2722) = Sparse.eval nodeValue2722 (mixedVector B) := by
    change mixedMoment B node2722 node2722Labels = _
    exact sound2722 B hB hF
  have h2724 : mixedVector B (Sum.inr 2724) = Sparse.eval nodeValue2724 (mixedVector B) := by
    change mixedMoment B node2724 node2724Labels = _
    exact sound2724 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm263, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1219, h2488, h2545, h2620, h2722, h2724, h4092, reducedSource223] using sourceEq263 B hB

theorem rowSound223 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row223 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck223, numericCheck223, reducedZero223 B hB hF, mul_zero]

theorem sourceRowsAt208 : MixedData.sourceRows (208 : Fin 2425) =
    MixedData.row208 := by decide +kernel

theorem sourceRowsAt209 : MixedData.sourceRows (209 : Fin 2425) =
    MixedData.row209 := by decide +kernel

theorem sourceRowsAt210 : MixedData.sourceRows (210 : Fin 2425) =
    MixedData.row210 := by decide +kernel

theorem sourceRowsAt211 : MixedData.sourceRows (211 : Fin 2425) =
    MixedData.row211 := by decide +kernel

theorem sourceRowsAt212 : MixedData.sourceRows (212 : Fin 2425) =
    MixedData.row212 := by decide +kernel

theorem sourceRowsAt213 : MixedData.sourceRows (213 : Fin 2425) =
    MixedData.row213 := by decide +kernel

theorem sourceRowsAt214 : MixedData.sourceRows (214 : Fin 2425) =
    MixedData.row214 := by decide +kernel

theorem sourceRowsAt215 : MixedData.sourceRows (215 : Fin 2425) =
    MixedData.row215 := by decide +kernel

theorem sourceRowsAt216 : MixedData.sourceRows (216 : Fin 2425) =
    MixedData.row216 := by decide +kernel

theorem sourceRowsAt217 : MixedData.sourceRows (217 : Fin 2425) =
    MixedData.row217 := by decide +kernel

theorem sourceRowsAt218 : MixedData.sourceRows (218 : Fin 2425) =
    MixedData.row218 := by decide +kernel

theorem sourceRowsAt219 : MixedData.sourceRows (219 : Fin 2425) =
    MixedData.row219 := by decide +kernel

theorem sourceRowsAt220 : MixedData.sourceRows (220 : Fin 2425) =
    MixedData.row220 := by decide +kernel

theorem sourceRowsAt221 : MixedData.sourceRows (221 : Fin 2425) =
    MixedData.row221 := by decide +kernel

theorem sourceRowsAt222 : MixedData.sourceRows (222 : Fin 2425) =
    MixedData.row222 := by decide +kernel

theorem sourceRowsAt223 : MixedData.sourceRows (223 : Fin 2425) =
    MixedData.row223 := by decide +kernel

theorem chunkSound13_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 13) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 208 ∨ k.val = 209 ∨ k.val = 210 ∨ k.val = 211 ∨ k.val = 212 ∨ k.val = 213 ∨ k.val = 214 ∨ k.val = 215 ∨ k.val = 216 ∨ k.val = 217 ∨ k.val = 218 ∨ k.val = 219 ∨ k.val = 220 ∨ k.val = 221 ∨ k.val = 222 ∨ k.val = 223 := by omega
  rcases heq with h208 | h209 | h210 | h211 | h212 | h213 | h214 | h215 | h216 | h217 | h218 | h219 | h220 | h221 | h222 | h223
  · have he : k = (208 : Fin 2425) := Fin.ext h208
    subst k
    rw [sourceRowsAt208]
    exact rowSound208 B hB hF
  · have he : k = (209 : Fin 2425) := Fin.ext h209
    subst k
    rw [sourceRowsAt209]
    exact rowSound209 B hB hF
  · have he : k = (210 : Fin 2425) := Fin.ext h210
    subst k
    rw [sourceRowsAt210]
    exact rowSound210 B hB hF
  · have he : k = (211 : Fin 2425) := Fin.ext h211
    subst k
    rw [sourceRowsAt211]
    exact rowSound211 B hB hF
  · have he : k = (212 : Fin 2425) := Fin.ext h212
    subst k
    rw [sourceRowsAt212]
    exact rowSound212 B hB hF
  · have he : k = (213 : Fin 2425) := Fin.ext h213
    subst k
    rw [sourceRowsAt213]
    exact rowSound213_e B hB hF
  · have he : k = (214 : Fin 2425) := Fin.ext h214
    subst k
    rw [sourceRowsAt214]
    exact rowSound214_e B hB hF
  · have he : k = (215 : Fin 2425) := Fin.ext h215
    subst k
    rw [sourceRowsAt215]
    exact rowSound215 B hB hF
  · have he : k = (216 : Fin 2425) := Fin.ext h216
    subst k
    rw [sourceRowsAt216]
    exact rowSound216 B hB hF
  · have he : k = (217 : Fin 2425) := Fin.ext h217
    subst k
    rw [sourceRowsAt217]
    exact rowSound217 B hB hF
  · have he : k = (218 : Fin 2425) := Fin.ext h218
    subst k
    rw [sourceRowsAt218]
    exact rowSound218 B hB hF
  · have he : k = (219 : Fin 2425) := Fin.ext h219
    subst k
    rw [sourceRowsAt219]
    exact rowSound219 B hB hF
  · have he : k = (220 : Fin 2425) := Fin.ext h220
    subst k
    rw [sourceRowsAt220]
    exact rowSound220 B hB hF
  · have he : k = (221 : Fin 2425) := Fin.ext h221
    subst k
    rw [sourceRowsAt221]
    exact rowSound221 B hB hF
  · have he : k = (222 : Fin 2425) := Fin.ext h222
    subst k
    rw [sourceRowsAt222]
    exact rowSound222 B hB hF
  · have he : k = (223 : Fin 2425) := Fin.ext h223
    subst k
    rw [sourceRowsAt223]
    exact rowSound223 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound13_e_oai
