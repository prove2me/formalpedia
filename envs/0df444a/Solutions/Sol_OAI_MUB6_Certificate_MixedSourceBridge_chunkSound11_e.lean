-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:36:30.359418+00:00
-- url     : https://prove2.me/submissions/c5fc1677-3be7-4c4c-b808-aec1dcd7e87f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound176_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound184_e
import Theorems.Thm_OAI_MUB6_Certificate_MixedSourceBridge_rowSound188_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5630 raw5630Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw5630 raw5630Labels = mixedMoment B raw5630step0 raw5630step0Labels := by
      have ha : raw5630step0 = (fun i j => raw5630 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5630step0 raw5630; decide +kernel
      have hl : raw5630step0Labels = raw5630Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5630 raw5630Labels permutation260 permutation4
    mixedMoment B raw5630step0 raw5630step0Labels = mixedMoment B raw5630step1 raw5630step1Labels := by
      have ha : raw5630step1 = -raw5630step0 := by apply Matrix.ext; change ∀ i j, raw5630step1 i j = -(raw5630step0 i j); unfold raw5630step1 raw5630step0; decide +kernel
      have hl : raw5630step1Labels = raw5630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical5631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5631 raw5631Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw5631 raw5631Labels = mixedMoment B raw5631step0 raw5631step0Labels := by
      have ha : raw5631step0 = (fun i j => raw5631 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5631step0 raw5631; decide +kernel
      have hl : raw5631step0Labels = raw5631Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5631 raw5631Labels permutation682 permutation2
    mixedMoment B raw5631step0 raw5631step0Labels = mixedMoment B raw5631step1 raw5631step1Labels := by
      have ha : raw5631step1 = -raw5631step0 := by apply Matrix.ext; change ∀ i j, raw5631step1 i j = -(raw5631step0 i j); unfold raw5631step1 raw5631step0; decide +kernel
      have hl : raw5631step1Labels = raw5631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

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

theorem canonical5632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5632 raw5632Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw5632 raw5632Labels = mixedMoment B raw5632step0 raw5632step0Labels := by
      have ha : raw5632step0 = (fun i j => raw5632 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5632step0 raw5632; decide +kernel
      have hl : raw5632step0Labels = raw5632Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5632 raw5632Labels permutation676 permutation2
    mixedMoment B raw5632step0 raw5632step0Labels = mixedMoment B raw5632step1 raw5632step1Labels := by
      have ha : raw5632step1 = -raw5632step0 := by apply Matrix.ext; change ∀ i j, raw5632step1 i j = -(raw5632step0 i j); unfold raw5632step1 raw5632step0; decide +kernel
      have hl : raw5632step1Labels = raw5632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical5633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5633 raw5633Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw5633 raw5633Labels = mixedMoment B raw5633step0 raw5633step0Labels := by
      have ha : raw5633step0 = (fun i j => raw5633 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5633step0 raw5633; decide +kernel
      have hl : raw5633step0Labels = raw5633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5633 raw5633Labels permutation674 permutation2
    mixedMoment B raw5633step0 raw5633step0Labels = mixedMoment B raw5633step1 raw5633step1Labels := by
      have ha : raw5633step1 = -raw5633step0 := by apply Matrix.ext; change ∀ i j, raw5633step1 i j = -(raw5633step0 i j); unfold raw5633step1 raw5633step0; decide +kernel
      have hl : raw5633step1Labels = raw5633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

theorem canonical5634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5634 raw5634Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw5634 raw5634Labels = mixedMoment B raw5634step0 raw5634step0Labels := by
      have ha : raw5634step0 = (fun i j => raw5634 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5634step0 raw5634; decide +kernel
      have hl : raw5634step0Labels = raw5634Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5634 raw5634Labels permutation674 permutation2
    mixedMoment B raw5634step0 raw5634step0Labels = mixedMoment B raw5634step1 raw5634step1Labels := by
      have ha : raw5634step1 = -raw5634step0 := by apply Matrix.ext; change ∀ i j, raw5634step1 i j = -(raw5634step0 i j); unfold raw5634step1 raw5634step0; decide +kernel
      have hl : raw5634step1Labels = raw5634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical5635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5635 raw5635Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw5635 raw5635Labels = mixedMoment B raw5635step0 raw5635step0Labels := by
      have ha : raw5635step0 = (fun i j => raw5635 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5635step0 raw5635; decide +kernel
      have hl : raw5635step0Labels = raw5635Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5635 raw5635Labels permutation260 permutation4
    mixedMoment B raw5635step0 raw5635step0Labels = mixedMoment B raw5635step1 raw5635step1Labels := by
      have ha : raw5635step1 = -raw5635step0 := by apply Matrix.ext; change ∀ i j, raw5635step1 i j = -(raw5635step0 i j); unfold raw5635step1 raw5635step0; decide +kernel
      have hl : raw5635step1Labels = raw5635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

theorem canonical5636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5636 raw5636Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw5636 raw5636Labels = mixedMoment B raw5636step0 raw5636step0Labels := by
      have hz : ∀ j, raw5636 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw5636step0 = (fun i j => raw5636 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw5636step0 raw5636; decide +kernel
      have hl : raw5636step0Labels = raw5636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5636 raw5636Labels permutation152 hz
    mixedMoment B raw5636step0 raw5636step0Labels = mixedMoment B raw5636step1 raw5636step1Labels := by
      have ha : raw5636step1 = (fun i j => raw5636step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5636step1 raw5636step0; decide +kernel
      have hl : raw5636step1Labels = raw5636step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5636step0 raw5636step0Labels permutation146 permutation0
    mixedMoment B raw5636step1 raw5636step1Labels = mixedMoment B raw5636step2 raw5636step2Labels := by
      have ha : raw5636step2 = -raw5636step1 := by apply Matrix.ext; change ∀ i j, raw5636step2 i j = -(raw5636step1 i j); unfold raw5636step2 raw5636step1; decide +kernel
      have hl : raw5636step2Labels = raw5636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical5637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5637 raw5637Labels = mixedMoment B node1464 node1464Labels := by
  calc
    mixedMoment B raw5637 raw5637Labels = mixedMoment B raw5637step0 raw5637step0Labels := by
      have ha : raw5637step0 = (fun i j => raw5637 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5637step0 raw5637; decide +kernel
      have hl : raw5637step0Labels = raw5637Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5637 raw5637Labels permutation263 permutation4
    mixedMoment B raw5637step0 raw5637step0Labels = mixedMoment B raw5637step1 raw5637step1Labels := by
      have ha : raw5637step1 = -raw5637step0 := by apply Matrix.ext; change ∀ i j, raw5637step1 i j = -(raw5637step0 i j); unfold raw5637step1 raw5637step0; decide +kernel
      have hl : raw5637step1Labels = raw5637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1464 node1464Labels := by rfl

theorem canonical5638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5638 raw5638Labels = mixedMoment B node1464 node1464Labels := by
  calc
    mixedMoment B raw5638 raw5638Labels = mixedMoment B raw5638step0 raw5638step0Labels := by
      have ha : raw5638step0 = (fun i j => raw5638 (permutation261 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5638step0 raw5638; decide +kernel
      have hl : raw5638step0Labels = raw5638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5638 raw5638Labels permutation261 permutation4
    mixedMoment B raw5638step0 raw5638step0Labels = mixedMoment B raw5638step1 raw5638step1Labels := by
      have ha : raw5638step1 = -raw5638step0 := by apply Matrix.ext; change ∀ i j, raw5638step1 i j = -(raw5638step0 i j); unfold raw5638step1 raw5638step0; decide +kernel
      have hl : raw5638step1Labels = raw5638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1464 node1464Labels := by rfl

theorem canonical5639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5639 raw5639Labels = mixedMoment B node1464 node1464Labels := by
  calc
    mixedMoment B raw5639 raw5639Labels = mixedMoment B raw5639step0 raw5639step0Labels := by
      have ha : raw5639step0 = (fun i j => raw5639 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5639step0 raw5639; decide +kernel
      have hl : raw5639step0Labels = raw5639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5639 raw5639Labels permutation260 permutation4
    mixedMoment B raw5639step0 raw5639step0Labels = mixedMoment B raw5639step1 raw5639step1Labels := by
      have ha : raw5639step1 = -raw5639step0 := by apply Matrix.ext; change ∀ i j, raw5639step1 i j = -(raw5639step0 i j); unfold raw5639step1 raw5639step0; decide +kernel
      have hl : raw5639step1Labels = raw5639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1464 node1464Labels := by rfl

theorem canonical5640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5640 raw5640Labels = mixedMoment B node1467 node1467Labels := by
  calc
    mixedMoment B raw5640 raw5640Labels = mixedMoment B raw5640step0 raw5640step0Labels := by
      have ha : raw5640step0 = (fun i j => raw5640 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5640step0 raw5640; decide +kernel
      have hl : raw5640step0Labels = raw5640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5640 raw5640Labels permutation260 permutation4
    mixedMoment B raw5640step0 raw5640step0Labels = mixedMoment B raw5640step1 raw5640step1Labels := by
      have ha : raw5640step1 = -raw5640step0 := by apply Matrix.ext; change ∀ i j, raw5640step1 i j = -(raw5640step0 i j); unfold raw5640step1 raw5640step0; decide +kernel
      have hl : raw5640step1Labels = raw5640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1467 node1467Labels := by rfl

theorem canonical5641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5641 raw5641Labels = mixedMoment B node1474 node1474Labels := by
  calc
    _ = mixedMoment B node1474 node1474Labels := by rfl

theorem canonical5642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5642 raw5642Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5642 raw5642Labels = mixedMoment B raw5642step0 raw5642step0Labels := by
      have ha : raw5642step0 = (fun i j => raw5642 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5642step0 raw5642; decide +kernel
      have hl : raw5642step0Labels = raw5642Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5642 raw5642Labels permutation182 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical5643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5643 raw5643Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5643 raw5643Labels = mixedMoment B raw5643step0 raw5643step0Labels := by
      have ha : raw5643step0 = (fun i j => raw5643 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5643step0 raw5643; decide +kernel
      have hl : raw5643step0Labels = raw5643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5643 raw5643Labels permutation206 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical5644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5644 raw5644Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw5644 raw5644Labels = mixedMoment B raw5644step0 raw5644step0Labels := by
      have ha : raw5644step0 = (fun i j => raw5644 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5644step0 raw5644; decide +kernel
      have hl : raw5644step0Labels = raw5644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5644 raw5644Labels permutation243 permutation4
    mixedMoment B raw5644step0 raw5644step0Labels = mixedMoment B raw5644step1 raw5644step1Labels := by
      have ha : raw5644step1 = -raw5644step0 := by apply Matrix.ext; change ∀ i j, raw5644step1 i j = -(raw5644step0 i j); unfold raw5644step1 raw5644step0; decide +kernel
      have hl : raw5644step1Labels = raw5644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

theorem canonical5645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5645 raw5645Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw5645 raw5645Labels = mixedMoment B raw5645step0 raw5645step0Labels := by
      have ha : raw5645step0 = (fun i j => raw5645 (permutation263 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5645step0 raw5645; decide +kernel
      have hl : raw5645step0Labels = raw5645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5645 raw5645Labels permutation263 permutation4
    mixedMoment B raw5645step0 raw5645step0Labels = mixedMoment B raw5645step1 raw5645step1Labels := by
      have ha : raw5645step1 = -raw5645step0 := by apply Matrix.ext; change ∀ i j, raw5645step1 i j = -(raw5645step0 i j); unfold raw5645step1 raw5645step0; decide +kernel
      have hl : raw5645step1Labels = raw5645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3172 node3172Labels := by rfl

theorem canonical5646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5646 raw5646Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5646 raw5646Labels = mixedMoment B raw5646step0 raw5646step0Labels := by
      have ha : raw5646step0 = (fun i j => raw5646 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5646step0 raw5646; decide +kernel
      have hl : raw5646step0Labels = raw5646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5646 raw5646Labels permutation158 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical5647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5647 raw5647Labels = mixedMoment B node3202 node3202Labels := by
  calc
    _ = mixedMoment B node3202 node3202Labels := by rfl

theorem canonical5648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5648 raw5648Labels = mixedMoment B node3199 node3199Labels := by
  calc
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical5649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5649 raw5649Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5649 raw5649Labels = mixedMoment B raw5649step0 raw5649step0Labels := by
      have ha : raw5649step0 = (fun i j => raw5649 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5649step0 raw5649; decide +kernel
      have hl : raw5649step0Labels = raw5649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5649 raw5649Labels permutation682 permutation2
    mixedMoment B raw5649step0 raw5649step0Labels = mixedMoment B raw5649step1 raw5649step1Labels := by
      have ha : raw5649step1 = -raw5649step0 := by apply Matrix.ext; change ∀ i j, raw5649step1 i j = -(raw5649step0 i j); unfold raw5649step1 raw5649step0; decide +kernel
      have hl : raw5649step1Labels = raw5649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

theorem canonical5650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5650 raw5650Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw5650 raw5650Labels = mixedMoment B raw5650step0 raw5650step0Labels := by
      have ha : raw5650step0 = (fun i j => raw5650 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5650step0 raw5650; decide +kernel
      have hl : raw5650step0Labels = raw5650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5650 raw5650Labels permutation176 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical5651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5651 raw5651Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw5651 raw5651Labels = mixedMoment B raw5651step0 raw5651step0Labels := by
      have ha : raw5651step0 = (fun i j => raw5651 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5651step0 raw5651; decide +kernel
      have hl : raw5651step0Labels = raw5651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5651 raw5651Labels permutation200 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical5652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5652 raw5652Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw5652 raw5652Labels = mixedMoment B raw5652step0 raw5652step0Labels := by
      have ha : raw5652step0 = (fun i j => raw5652 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5652step0 raw5652; decide +kernel
      have hl : raw5652step0Labels = raw5652Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5652 raw5652Labels permutation260 permutation4
    mixedMoment B raw5652step0 raw5652step0Labels = mixedMoment B raw5652step1 raw5652step1Labels := by
      have ha : raw5652step1 = -raw5652step0 := by apply Matrix.ext; change ∀ i j, raw5652step1 i j = -(raw5652step0 i j); unfold raw5652step1 raw5652step0; decide +kernel
      have hl : raw5652step1Labels = raw5652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3179 node3179Labels := by rfl

theorem canonical5653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5653 raw5653Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw5653 raw5653Labels = mixedMoment B raw5653step0 raw5653step0Labels := by
      have ha : raw5653step0 = (fun i j => raw5653 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5653step0 raw5653; decide +kernel
      have hl : raw5653step0Labels = raw5653Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5653 raw5653Labels permutation241 permutation4
    mixedMoment B raw5653step0 raw5653step0Labels = mixedMoment B raw5653step1 raw5653step1Labels := by
      have ha : raw5653step1 = -raw5653step0 := by apply Matrix.ext; change ∀ i j, raw5653step1 i j = -(raw5653step0 i j); unfold raw5653step1 raw5653step0; decide +kernel
      have hl : raw5653step1Labels = raw5653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

theorem canonical5654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5654 raw5654Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw5654 raw5654Labels = mixedMoment B raw5654step0 raw5654step0Labels := by
      have ha : raw5654step0 = (fun i j => raw5654 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5654step0 raw5654; decide +kernel
      have hl : raw5654step0Labels = raw5654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5654 raw5654Labels permutation240 permutation4
    mixedMoment B raw5654step0 raw5654step0Labels = mixedMoment B raw5654step1 raw5654step1Labels := by
      have ha : raw5654step1 = -raw5654step0 := by apply Matrix.ext; change ∀ i j, raw5654step1 i j = -(raw5654step0 i j); unfold raw5654step1 raw5654step0; decide +kernel
      have hl : raw5654step1Labels = raw5654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

theorem canonical5655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5655 raw5655Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw5655 raw5655Labels = mixedMoment B raw5655step0 raw5655step0Labels := by
      have ha : raw5655step0 = (fun i j => raw5655 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5655step0 raw5655; decide +kernel
      have hl : raw5655step0Labels = raw5655Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5655 raw5655Labels permutation674 permutation2
    mixedMoment B raw5655step0 raw5655step0Labels = mixedMoment B raw5655step1 raw5655step1Labels := by
      have ha : raw5655step1 = -raw5655step0 := by apply Matrix.ext; change ∀ i j, raw5655step1 i j = -(raw5655step0 i j); unfold raw5655step1 raw5655step0; decide +kernel
      have hl : raw5655step1Labels = raw5655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2707 node2707Labels := by rfl

theorem canonical5656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5656 raw5656Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5656 raw5656Labels = mixedMoment B raw5656step0 raw5656step0Labels := by
      have ha : raw5656step0 = (fun i j => raw5656 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5656step0 raw5656; decide +kernel
      have hl : raw5656step0Labels = raw5656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5656 raw5656Labels permutation676 permutation2
    mixedMoment B raw5656step0 raw5656step0Labels = mixedMoment B raw5656step1 raw5656step1Labels := by
      have ha : raw5656step1 = -raw5656step0 := by apply Matrix.ext; change ∀ i j, raw5656step1 i j = -(raw5656step0 i j); unfold raw5656step1 raw5656step0; decide +kernel
      have hl : raw5656step1Labels = raw5656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

theorem canonical5657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5657 raw5657Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw5657 raw5657Labels = mixedMoment B raw5657step0 raw5657step0Labels := by
      have ha : raw5657step0 = (fun i j => raw5657 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5657step0 raw5657; decide +kernel
      have hl : raw5657step0Labels = raw5657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5657 raw5657Labels permutation674 permutation2
    mixedMoment B raw5657step0 raw5657step0Labels = mixedMoment B raw5657step1 raw5657step1Labels := by
      have ha : raw5657step1 = -raw5657step0 := by apply Matrix.ext; change ∀ i j, raw5657step1 i j = -(raw5657step0 i j); unfold raw5657step1 raw5657step0; decide +kernel
      have hl : raw5657step1Labels = raw5657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2471 node2471Labels := by rfl

theorem canonical5748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5748 raw5748Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw5748 raw5748Labels = mixedMoment B raw5748step0 raw5748step0Labels := by
      have ha : raw5748step0 = (fun i j => raw5748 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5748step0 raw5748; decide +kernel
      have hl : raw5748step0Labels = raw5748Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5748 raw5748Labels permutation240 permutation4
    mixedMoment B raw5748step0 raw5748step0Labels = mixedMoment B raw5748step1 raw5748step1Labels := by
      have ha : raw5748step1 = -raw5748step0 := by apply Matrix.ext; change ∀ i j, raw5748step1 i j = -(raw5748step0 i j); unfold raw5748step1 raw5748step0; decide +kernel
      have hl : raw5748step1Labels = raw5748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical5749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5749 raw5749Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5749 raw5749Labels = mixedMoment B raw5749step0 raw5749step0Labels := by
      have hz : ∀ j, raw5749 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5749step0 = (fun i j => raw5749 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5749step0 raw5749; decide +kernel
      have hl : raw5749step0Labels = raw5749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5749 raw5749Labels permutation265 hz
    mixedMoment B raw5749step0 raw5749step0Labels = mixedMoment B raw5749step1 raw5749step1Labels := by
      have ha : raw5749step1 = (fun i j => raw5749step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5749step1 raw5749step0; decide +kernel
      have hl : raw5749step1Labels = raw5749step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5749step0 raw5749step0Labels permutation48 permutation4
    mixedMoment B raw5749step1 raw5749step1Labels = mixedMoment B raw5749step2 raw5749step2Labels := by
      have ha : raw5749step2 = -raw5749step1 := by apply Matrix.ext; change ∀ i j, raw5749step2 i j = -(raw5749step1 i j); unfold raw5749step2 raw5749step1; decide +kernel
      have hl : raw5749step2Labels = raw5749step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical5750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5750 raw5750Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5750 raw5750Labels = mixedMoment B raw5750step0 raw5750step0Labels := by
      have hz : ∀ j, raw5750 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5750step0 = (fun i j => raw5750 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5750step0 raw5750; decide +kernel
      have hl : raw5750step0Labels = raw5750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5750 raw5750Labels permutation346 hz
    mixedMoment B raw5750step0 raw5750step0Labels = mixedMoment B raw5750step1 raw5750step1Labels := by
      have ha : raw5750step1 = (fun i j => raw5750step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5750step1 raw5750step0; decide +kernel
      have hl : raw5750step1Labels = raw5750step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5750step0 raw5750step0Labels permutation48 permutation4
    mixedMoment B raw5750step1 raw5750step1Labels = mixedMoment B raw5750step2 raw5750step2Labels := by
      have ha : raw5750step2 = -raw5750step1 := by apply Matrix.ext; change ∀ i j, raw5750step2 i j = -(raw5750step1 i j); unfold raw5750step2 raw5750step1; decide +kernel
      have hl : raw5750step2Labels = raw5750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

theorem canonical5751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5751 raw5751Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5751 raw5751Labels = mixedMoment B raw5751step0 raw5751step0Labels := by
      have hz : ∀ j, raw5751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5751step0 = (fun i j => raw5751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5751step0 raw5751; decide +kernel
      have hl : raw5751step0Labels = raw5751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5751 raw5751Labels permutation434 hz
    mixedMoment B raw5751step0 raw5751step0Labels = mixedMoment B raw5751step1 raw5751step1Labels := by
      have ha : raw5751step1 = (fun i j => raw5751step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5751step1 raw5751step0; decide +kernel
      have hl : raw5751step1Labels = raw5751step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5751step0 raw5751step0Labels permutation48 permutation4
    mixedMoment B raw5751step1 raw5751step1Labels = mixedMoment B raw5751step2 raw5751step2Labels := by
      have ha : raw5751step2 = -raw5751step1 := by apply Matrix.ext; change ∀ i j, raw5751step2 i j = -(raw5751step1 i j); unfold raw5751step2 raw5751step1; decide +kernel
      have hl : raw5751step2Labels = raw5751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3625 node3625Labels := by rfl

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

theorem canonical5753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5753 raw5753Labels = mixedMoment B node2507 node2507Labels := by
  calc
    mixedMoment B raw5753 raw5753Labels = mixedMoment B raw5753step0 raw5753step0Labels := by
      have ha : raw5753step0 = (fun i j => raw5753 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5753step0 raw5753; decide +kernel
      have hl : raw5753step0Labels = raw5753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5753 raw5753Labels permutation674 permutation2
    _ = mixedMoment B node2507 node2507Labels := by rfl

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

theorem canonical5758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5758 raw5758Labels = mixedMoment B node1056 node1056Labels := by
  calc
    mixedMoment B raw5758 raw5758Labels = mixedMoment B raw5758step0 raw5758step0Labels := by
      have ha : raw5758step0 = (fun i j => raw5758 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5758step0 raw5758; decide +kernel
      have hl : raw5758step0Labels = raw5758Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5758 raw5758Labels permutation246 permutation4
    mixedMoment B raw5758step0 raw5758step0Labels = mixedMoment B raw5758step1 raw5758step1Labels := by
      have ha : raw5758step1 = -raw5758step0 := by apply Matrix.ext; change ∀ i j, raw5758step1 i j = -(raw5758step0 i j); unfold raw5758step1 raw5758step0; decide +kernel
      have hl : raw5758step1Labels = raw5758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1056 node1056Labels := by rfl

theorem canonical5759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5759 raw5759Labels = mixedMoment B node1038 node1038Labels := by
  calc
    mixedMoment B raw5759 raw5759Labels = mixedMoment B raw5759step0 raw5759step0Labels := by
      have ha : raw5759step0 = (fun i j => raw5759 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5759step0 raw5759; decide +kernel
      have hl : raw5759step0Labels = raw5759Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5759 raw5759Labels permutation224 permutation4
    mixedMoment B raw5759step0 raw5759step0Labels = mixedMoment B raw5759step1 raw5759step1Labels := by
      have ha : raw5759step1 = -raw5759step0 := by apply Matrix.ext; change ∀ i j, raw5759step1 i j = -(raw5759step0 i j); unfold raw5759step1 raw5759step0; decide +kernel
      have hl : raw5759step1Labels = raw5759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1038 node1038Labels := by rfl

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

theorem canonical5760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5760 raw5760Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5760 raw5760Labels = mixedMoment B raw5760step0 raw5760step0Labels := by
      have hz : ∀ j, raw5760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5760step0 = (fun i j => raw5760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5760step0 raw5760; decide +kernel
      have hl : raw5760step0Labels = raw5760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5760 raw5760Labels permutation265 hz
    mixedMoment B raw5760step0 raw5760step0Labels = mixedMoment B raw5760step1 raw5760step1Labels := by
      have ha : raw5760step1 = (fun i j => raw5760step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5760step1 raw5760step0; decide +kernel
      have hl : raw5760step1Labels = raw5760step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5760step0 raw5760step0Labels permutation50 permutation4
    mixedMoment B raw5760step1 raw5760step1Labels = mixedMoment B raw5760step2 raw5760step2Labels := by
      have ha : raw5760step2 = -raw5760step1 := by apply Matrix.ext; change ∀ i j, raw5760step2 i j = -(raw5760step1 i j); unfold raw5760step2 raw5760step1; decide +kernel
      have hl : raw5760step2Labels = raw5760step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical5761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5761 raw5761Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5761 raw5761Labels = mixedMoment B raw5761step0 raw5761step0Labels := by
      have hz : ∀ j, raw5761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5761step0 = (fun i j => raw5761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5761step0 raw5761; decide +kernel
      have hl : raw5761step0Labels = raw5761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5761 raw5761Labels permutation346 hz
    mixedMoment B raw5761step0 raw5761step0Labels = mixedMoment B raw5761step1 raw5761step1Labels := by
      have ha : raw5761step1 = (fun i j => raw5761step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5761step1 raw5761step0; decide +kernel
      have hl : raw5761step1Labels = raw5761step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5761step0 raw5761step0Labels permutation50 permutation4
    mixedMoment B raw5761step1 raw5761step1Labels = mixedMoment B raw5761step2 raw5761step2Labels := by
      have ha : raw5761step2 = -raw5761step1 := by apply Matrix.ext; change ∀ i j, raw5761step2 i j = -(raw5761step1 i j); unfold raw5761step2 raw5761step1; decide +kernel
      have hl : raw5761step2Labels = raw5761step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical5762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5762 raw5762Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5762 raw5762Labels = mixedMoment B raw5762step0 raw5762step0Labels := by
      have hz : ∀ j, raw5762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5762step0 = (fun i j => raw5762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5762step0 raw5762; decide +kernel
      have hl : raw5762step0Labels = raw5762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5762 raw5762Labels permutation434 hz
    mixedMoment B raw5762step0 raw5762step0Labels = mixedMoment B raw5762step1 raw5762step1Labels := by
      have ha : raw5762step1 = (fun i j => raw5762step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5762step1 raw5762step0; decide +kernel
      have hl : raw5762step1Labels = raw5762step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5762step0 raw5762step0Labels permutation50 permutation4
    mixedMoment B raw5762step1 raw5762step1Labels = mixedMoment B raw5762step2 raw5762step2Labels := by
      have ha : raw5762step2 = -raw5762step1 := by apply Matrix.ext; change ∀ i j, raw5762step2 i j = -(raw5762step1 i j); unfold raw5762step2 raw5762step1; decide +kernel
      have hl : raw5762step2Labels = raw5762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2277 node2277Labels := by rfl

theorem canonical5763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5763 raw5763Labels = mixedMoment B node2131 node2131Labels := by
  calc
    mixedMoment B raw5763 raw5763Labels = mixedMoment B raw5763step0 raw5763step0Labels := by
      have ha : raw5763step0 = (fun i j => raw5763 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5763step0 raw5763; decide +kernel
      have hl : raw5763step0Labels = raw5763Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5763 raw5763Labels permutation246 permutation4
    mixedMoment B raw5763step0 raw5763step0Labels = mixedMoment B raw5763step1 raw5763step1Labels := by
      have ha : raw5763step1 = -raw5763step0 := by apply Matrix.ext; change ∀ i j, raw5763step1 i j = -(raw5763step0 i j); unfold raw5763step1 raw5763step0; decide +kernel
      have hl : raw5763step1Labels = raw5763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2131 node2131Labels := by rfl

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

theorem canonical5769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5769 raw5769Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5769 raw5769Labels = mixedMoment B raw5769step0 raw5769step0Labels := by
      have hz : ∀ j, raw5769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5769step0 = (fun i j => raw5769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5769step0 raw5769; decide +kernel
      have hl : raw5769step0Labels = raw5769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5769 raw5769Labels permutation346 hz
    mixedMoment B raw5769step0 raw5769step0Labels = mixedMoment B raw5769step1 raw5769step1Labels := by
      have ha : raw5769step1 = (fun i j => raw5769step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5769step1 raw5769step0; decide +kernel
      have hl : raw5769step1Labels = raw5769step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5769step0 raw5769step0Labels permutation44 permutation4
    mixedMoment B raw5769step1 raw5769step1Labels = mixedMoment B raw5769step2 raw5769step2Labels := by
      have ha : raw5769step2 = -raw5769step1 := by apply Matrix.ext; change ∀ i j, raw5769step2 i j = -(raw5769step1 i j); unfold raw5769step2 raw5769step1; decide +kernel
      have hl : raw5769step2Labels = raw5769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical5770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5770 raw5770Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5770 raw5770Labels = mixedMoment B raw5770step0 raw5770step0Labels := by
      have hz : ∀ j, raw5770 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5770step0 = (fun i j => raw5770 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5770step0 raw5770; decide +kernel
      have hl : raw5770step0Labels = raw5770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5770 raw5770Labels permutation434 hz
    mixedMoment B raw5770step0 raw5770step0Labels = mixedMoment B raw5770step1 raw5770step1Labels := by
      have ha : raw5770step1 = (fun i j => raw5770step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5770step1 raw5770step0; decide +kernel
      have hl : raw5770step1Labels = raw5770step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5770step0 raw5770step0Labels permutation44 permutation4
    mixedMoment B raw5770step1 raw5770step1Labels = mixedMoment B raw5770step2 raw5770step2Labels := by
      have ha : raw5770step2 = -raw5770step1 := by apply Matrix.ext; change ∀ i j, raw5770step2 i j = -(raw5770step1 i j); unfold raw5770step2 raw5770step1; decide +kernel
      have hl : raw5770step2Labels = raw5770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2262 node2262Labels := by rfl

theorem canonical5861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5861 raw5861Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw5861 raw5861Labels = mixedMoment B raw5861step0 raw5861step0Labels := by
      have hz : ∀ j, raw5861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5861step0 = (fun i j => raw5861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5861step0 raw5861; decide +kernel
      have hl : raw5861step0Labels = raw5861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5861 raw5861Labels permutation434 hz
    mixedMoment B raw5861step0 raw5861step0Labels = mixedMoment B raw5861step1 raw5861step1Labels := by
      have hz : ∀ j, raw5861step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5861step1 = (fun i j => raw5861step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5861step1 raw5861step0; decide +kernel
      have hl : raw5861step1Labels = raw5861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5861step0 raw5861step0Labels permutation80 hz
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical5862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5862 raw5862Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw5862 raw5862Labels = mixedMoment B raw5862step0 raw5862step0Labels := by
      have hz : ∀ j, raw5862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5862step0 = (fun i j => raw5862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5862step0 raw5862; decide +kernel
      have hl : raw5862step0Labels = raw5862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5862 raw5862Labels permutation434 hz
    mixedMoment B raw5862step0 raw5862step0Labels = mixedMoment B raw5862step1 raw5862step1Labels := by
      have hz : ∀ j, raw5862step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5862step1 = (fun i j => raw5862step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5862step1 raw5862step0; decide +kernel
      have hl : raw5862step1Labels = raw5862step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5862step0 raw5862step0Labels permutation80 hz
    mixedMoment B raw5862step1 raw5862step1Labels = mixedMoment B raw5862step2 raw5862step2Labels := by
      have ha : raw5862step2 = (fun i j => raw5862step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5862step2 raw5862step1; decide +kernel
      have hl : raw5862step2Labels = raw5862step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5862step1 raw5862step1Labels permutation22 permutation4
    mixedMoment B raw5862step2 raw5862step2Labels = mixedMoment B raw5862step3 raw5862step3Labels := by
      have ha : raw5862step3 = -raw5862step2 := by apply Matrix.ext; change ∀ i j, raw5862step3 i j = -(raw5862step2 i j); unfold raw5862step3 raw5862step2; decide +kernel
      have hl : raw5862step3Labels = raw5862step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical5863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5863 raw5863Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5863 raw5863Labels = mixedMoment B raw5863step0 raw5863step0Labels := by
      have hz : ∀ j, raw5863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5863step0 = (fun i j => raw5863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5863step0 raw5863; decide +kernel
      have hl : raw5863step0Labels = raw5863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5863 raw5863Labels permutation434 hz
    mixedMoment B raw5863step0 raw5863step0Labels = mixedMoment B raw5863step1 raw5863step1Labels := by
      have ha : raw5863step1 = (fun i j => raw5863step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5863step1 raw5863step0; decide +kernel
      have hl : raw5863step1Labels = raw5863step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5863step0 raw5863step0Labels permutation116 permutation4
    mixedMoment B raw5863step1 raw5863step1Labels = mixedMoment B raw5863step2 raw5863step2Labels := by
      have ha : raw5863step2 = -raw5863step1 := by apply Matrix.ext; change ∀ i j, raw5863step2 i j = -(raw5863step1 i j); unfold raw5863step2 raw5863step1; decide +kernel
      have hl : raw5863step2Labels = raw5863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical5864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5864 raw5864Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5864 raw5864Labels = mixedMoment B raw5864step0 raw5864step0Labels := by
      have hz : ∀ j, raw5864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5864step0 = (fun i j => raw5864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5864step0 raw5864; decide +kernel
      have hl : raw5864step0Labels = raw5864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5864 raw5864Labels permutation346 hz
    mixedMoment B raw5864step0 raw5864step0Labels = mixedMoment B raw5864step1 raw5864step1Labels := by
      have ha : raw5864step1 = (fun i j => raw5864step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5864step1 raw5864step0; decide +kernel
      have hl : raw5864step1Labels = raw5864step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5864step0 raw5864step0Labels permutation116 permutation4
    mixedMoment B raw5864step1 raw5864step1Labels = mixedMoment B raw5864step2 raw5864step2Labels := by
      have ha : raw5864step2 = -raw5864step1 := by apply Matrix.ext; change ∀ i j, raw5864step2 i j = -(raw5864step1 i j); unfold raw5864step2 raw5864step1; decide +kernel
      have hl : raw5864step2Labels = raw5864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical5865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5865 raw5865Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5865 raw5865Labels = mixedMoment B raw5865step0 raw5865step0Labels := by
      have hz : ∀ j, raw5865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5865step0 = (fun i j => raw5865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5865step0 raw5865; decide +kernel
      have hl : raw5865step0Labels = raw5865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5865 raw5865Labels permutation434 hz
    mixedMoment B raw5865step0 raw5865step0Labels = mixedMoment B raw5865step1 raw5865step1Labels := by
      have hz : ∀ j, raw5865step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5865step1 = (fun i j => raw5865step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5865step1 raw5865step0; decide +kernel
      have hl : raw5865step1Labels = raw5865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5865step0 raw5865step0Labels permutation80 hz
    mixedMoment B raw5865step1 raw5865step1Labels = mixedMoment B raw5865step2 raw5865step2Labels := by
      have ha : raw5865step2 = (fun i j => raw5865step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5865step2 raw5865step1; decide +kernel
      have hl : raw5865step2Labels = raw5865step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5865step1 raw5865step1Labels permutation20 permutation4
    mixedMoment B raw5865step2 raw5865step2Labels = mixedMoment B raw5865step3 raw5865step3Labels := by
      have ha : raw5865step3 = -raw5865step2 := by apply Matrix.ext; change ∀ i j, raw5865step3 i j = -(raw5865step2 i j); unfold raw5865step3 raw5865step2; decide +kernel
      have hl : raw5865step3Labels = raw5865step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical5866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5866 raw5866Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw5866 raw5866Labels = mixedMoment B raw5866step0 raw5866step0Labels := by
      have hz : ∀ j, raw5866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5866step0 = (fun i j => raw5866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5866step0 raw5866; decide +kernel
      have hl : raw5866step0Labels = raw5866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5866 raw5866Labels permutation434 hz
    mixedMoment B raw5866step0 raw5866step0Labels = mixedMoment B raw5866step1 raw5866step1Labels := by
      have hz : ∀ j, raw5866step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5866step1 = (fun i j => raw5866step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5866step1 raw5866step0; decide +kernel
      have hl : raw5866step1Labels = raw5866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5866step0 raw5866step0Labels permutation80 hz
    mixedMoment B raw5866step1 raw5866step1Labels = mixedMoment B raw5866step2 raw5866step2Labels := by
      have ha : raw5866step2 = (fun i j => raw5866step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5866step2 raw5866step1; decide +kernel
      have hl : raw5866step2Labels = raw5866step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5866step1 raw5866step1Labels permutation21 permutation4
    mixedMoment B raw5866step2 raw5866step2Labels = mixedMoment B raw5866step3 raw5866step3Labels := by
      have ha : raw5866step3 = -raw5866step2 := by apply Matrix.ext; change ∀ i j, raw5866step3 i j = -(raw5866step2 i j); unfold raw5866step3 raw5866step2; decide +kernel
      have hl : raw5866step3Labels = raw5866step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

theorem canonical5867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5867 raw5867Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5867 raw5867Labels = mixedMoment B raw5867step0 raw5867step0Labels := by
      have hz : ∀ j, raw5867 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5867step0 = (fun i j => raw5867 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5867step0 raw5867; decide +kernel
      have hl : raw5867step0Labels = raw5867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867 raw5867Labels permutation590 hz
    mixedMoment B raw5867step0 raw5867step0Labels = mixedMoment B raw5867step1 raw5867step1Labels := by
      have hz : ∀ j, raw5867step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5867step1 = (fun i j => raw5867step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5867step1 raw5867step0; decide +kernel
      have hl : raw5867step1Labels = raw5867step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867step0 raw5867step0Labels permutation104 hz
    mixedMoment B raw5867step1 raw5867step1Labels = mixedMoment B raw5867step2 raw5867step2Labels := by
      have hz : ∀ j, raw5867step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5867step2 = (fun i j => raw5867step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5867step2 raw5867step1; decide +kernel
      have hl : raw5867step2Labels = raw5867step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5867step1 raw5867step1Labels permutation20 hz
    mixedMoment B raw5867step2 raw5867step2Labels = mixedMoment B raw5867step3 raw5867step3Labels := by
      have ha : raw5867step3 = (fun i j => raw5867step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5867step3 raw5867step2; decide +kernel
      have hl : raw5867step3Labels = raw5867step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5867step2 raw5867step2Labels permutation7 permutation0
    mixedMoment B raw5867step3 raw5867step3Labels = mixedMoment B raw5867step4 raw5867step4Labels := by
      have ha : raw5867step4 = -raw5867step3 := by apply Matrix.ext; change ∀ i j, raw5867step4 i j = -(raw5867step3 i j); unfold raw5867step4 raw5867step3; decide +kernel
      have hl : raw5867step4Labels = raw5867step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical5868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5868 raw5868Labels = mixedMoment B node1296 node1296Labels := by
  calc
    mixedMoment B raw5868 raw5868Labels = mixedMoment B raw5868step0 raw5868step0Labels := by
      have hz : ∀ j, raw5868 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5868step0 = (fun i j => raw5868 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5868step0 raw5868; decide +kernel
      have hl : raw5868step0Labels = raw5868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5868 raw5868Labels permutation434 hz
    mixedMoment B raw5868step0 raw5868step0Labels = mixedMoment B raw5868step1 raw5868step1Labels := by
      have hz : ∀ j, raw5868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5868step1 = (fun i j => raw5868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5868step1 raw5868step0; decide +kernel
      have hl : raw5868step1Labels = raw5868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5868step0 raw5868step0Labels permutation80 hz
    _ = mixedMoment B node1296 node1296Labels := by rfl

theorem canonical5869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5869 raw5869Labels = mixedMoment B node1238 node1238Labels := by
  calc
    mixedMoment B raw5869 raw5869Labels = mixedMoment B raw5869step0 raw5869step0Labels := by
      have hz : ∀ j, raw5869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5869step0 = (fun i j => raw5869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5869step0 raw5869; decide +kernel
      have hl : raw5869step0Labels = raw5869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5869 raw5869Labels permutation434 hz
    _ = mixedMoment B node1238 node1238Labels := by rfl

theorem canonical5870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5870 raw5870Labels = mixedMoment B node1238 node1238Labels := by
  calc
    mixedMoment B raw5870 raw5870Labels = mixedMoment B raw5870step0 raw5870step0Labels := by
      have hz : ∀ j, raw5870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5870step0 = (fun i j => raw5870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5870step0 raw5870; decide +kernel
      have hl : raw5870step0Labels = raw5870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5870 raw5870Labels permutation346 hz
    _ = mixedMoment B node1238 node1238Labels := by rfl

theorem canonical5871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5871 raw5871Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw5871 raw5871Labels = mixedMoment B raw5871step0 raw5871step0Labels := by
      have hz : ∀ j, raw5871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5871step0 = (fun i j => raw5871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5871step0 raw5871; decide +kernel
      have hl : raw5871step0Labels = raw5871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5871 raw5871Labels permutation434 hz
    mixedMoment B raw5871step0 raw5871step0Labels = mixedMoment B raw5871step1 raw5871step1Labels := by
      have hz : ∀ j, raw5871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5871step1 = (fun i j => raw5871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5871step1 raw5871step0; decide +kernel
      have hl : raw5871step1Labels = raw5871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5871step0 raw5871step0Labels permutation80 hz
    mixedMoment B raw5871step1 raw5871step1Labels = mixedMoment B raw5871step2 raw5871step2Labels := by
      have ha : raw5871step2 = (fun i j => raw5871step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5871step2 raw5871step1; decide +kernel
      have hl : raw5871step2Labels = raw5871step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5871step1 raw5871step1Labels permutation9 permutation2
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical5872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5872 raw5872Labels = mixedMoment B node1244 node1244Labels := by
  calc
    mixedMoment B raw5872 raw5872Labels = mixedMoment B raw5872step0 raw5872step0Labels := by
      have hz : ∀ j, raw5872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5872step0 = (fun i j => raw5872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5872step0 raw5872; decide +kernel
      have hl : raw5872step0Labels = raw5872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5872 raw5872Labels permutation434 hz
    mixedMoment B raw5872step0 raw5872step0Labels = mixedMoment B raw5872step1 raw5872step1Labels := by
      have hz : ∀ j, raw5872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5872step1 = (fun i j => raw5872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5872step1 raw5872step0; decide +kernel
      have hl : raw5872step1Labels = raw5872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5872step0 raw5872step0Labels permutation80 hz
    _ = mixedMoment B node1244 node1244Labels := by rfl

theorem canonical5873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5873 raw5873Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw5873 raw5873Labels = mixedMoment B raw5873step0 raw5873step0Labels := by
      have hz : ∀ j, raw5873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5873step0 = (fun i j => raw5873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5873step0 raw5873; decide +kernel
      have hl : raw5873step0Labels = raw5873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5873 raw5873Labels permutation434 hz
    mixedMoment B raw5873step0 raw5873step0Labels = mixedMoment B raw5873step1 raw5873step1Labels := by
      have ha : raw5873step1 = (fun i j => raw5873step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5873step1 raw5873step0; decide +kernel
      have hl : raw5873step1Labels = raw5873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5873step0 raw5873step0Labels permutation38 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

theorem canonical5874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5874 raw5874Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw5874 raw5874Labels = mixedMoment B raw5874step0 raw5874step0Labels := by
      have hz : ∀ j, raw5874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5874step0 = (fun i j => raw5874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5874step0 raw5874; decide +kernel
      have hl : raw5874step0Labels = raw5874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5874 raw5874Labels permutation346 hz
    mixedMoment B raw5874step0 raw5874step0Labels = mixedMoment B raw5874step1 raw5874step1Labels := by
      have ha : raw5874step1 = (fun i j => raw5874step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5874step1 raw5874step0; decide +kernel
      have hl : raw5874step1Labels = raw5874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5874step0 raw5874step0Labels permutation38 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

theorem canonical5875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5875 raw5875Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw5875 raw5875Labels = mixedMoment B raw5875step0 raw5875step0Labels := by
      have hz : ∀ j, raw5875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5875step0 = (fun i j => raw5875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5875step0 raw5875; decide +kernel
      have hl : raw5875step0Labels = raw5875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5875 raw5875Labels permutation434 hz
    mixedMoment B raw5875step0 raw5875step0Labels = mixedMoment B raw5875step1 raw5875step1Labels := by
      have hz : ∀ j, raw5875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5875step1 = (fun i j => raw5875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5875step1 raw5875step0; decide +kernel
      have hl : raw5875step1Labels = raw5875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5875step0 raw5875step0Labels permutation80 hz
    mixedMoment B raw5875step1 raw5875step1Labels = mixedMoment B raw5875step2 raw5875step2Labels := by
      have ha : raw5875step2 = (fun i j => raw5875step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5875step2 raw5875step1; decide +kernel
      have hl : raw5875step2Labels = raw5875step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5875step1 raw5875step1Labels permutation21 permutation4
    mixedMoment B raw5875step2 raw5875step2Labels = mixedMoment B raw5875step3 raw5875step3Labels := by
      have ha : raw5875step3 = -raw5875step2 := by apply Matrix.ext; change ∀ i j, raw5875step3 i j = -(raw5875step2 i j); unfold raw5875step3 raw5875step2; decide +kernel
      have hl : raw5875step3Labels = raw5875step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2138 node2138Labels := by rfl

theorem canonical5876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5876 raw5876Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw5876 raw5876Labels = mixedMoment B raw5876step0 raw5876step0Labels := by
      have hz : ∀ j, raw5876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5876step0 = (fun i j => raw5876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5876step0 raw5876; decide +kernel
      have hl : raw5876step0Labels = raw5876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5876 raw5876Labels permutation434 hz
    mixedMoment B raw5876step0 raw5876step0Labels = mixedMoment B raw5876step1 raw5876step1Labels := by
      have hz : ∀ j, raw5876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5876step1 = (fun i j => raw5876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5876step1 raw5876step0; decide +kernel
      have hl : raw5876step1Labels = raw5876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5876step0 raw5876step0Labels permutation80 hz
    mixedMoment B raw5876step1 raw5876step1Labels = mixedMoment B raw5876step2 raw5876step2Labels := by
      have ha : raw5876step2 = (fun i j => raw5876step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5876step2 raw5876step1; decide +kernel
      have hl : raw5876step2Labels = raw5876step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5876step1 raw5876step1Labels permutation9 permutation2
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

theorem sound2279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2279 node2279Labels = Sparse.eval nodeValue2279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2279) = mixedMoment B node2279 node2279Labels := rfl
  simpa [nodeValue2279, Sparse.eval] using hc.symm

theorem sound3626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3626 node3626Labels = Sparse.eval nodeValue3626 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3626) = mixedMoment B node3626 node3626Labels := rfl
  simpa [nodeValue3626, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = 0 := by
  exact mixedMoment_alpha B hF node1038 node1038Labels 1 permutation161
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1038 node1038Labels = Sparse.eval nodeValue1038 (mixedVector B) := by
  simpa only [nodeValue1038, Sparse.eval_nil] using zero1038 B _hB _hF

theorem sound1056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1056 node1056Labels = Sparse.eval nodeValue1056 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1056) = mixedMoment B node1056 node1056Labels := rfl
  simpa [nodeValue1056, Sparse.eval] using hc.symm

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

theorem sound1238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1238 node1238Labels = Sparse.eval nodeValue1238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1238) = mixedMoment B node1238 node1238Labels := rfl
  simpa [nodeValue1238, Sparse.eval] using hc.symm

theorem sound1244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1244 node1244Labels = Sparse.eval nodeValue1244 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1244) = mixedMoment B node1244 node1244Labels := rfl
  simpa [nodeValue1244, Sparse.eval] using hc.symm

theorem sound1245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1245 node1245Labels = Sparse.eval nodeValue1245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1245) = mixedMoment B node1245 node1245Labels := rfl
  simpa [nodeValue1245, Sparse.eval] using hc.symm

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

theorem sound1296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1296 node1296Labels = Sparse.eval nodeValue1296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1296) = mixedMoment B node1296 node1296Labels := rfl
  simpa [nodeValue1296, Sparse.eval] using hc.symm

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

theorem sound1464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1464 node1464Labels = Sparse.eval nodeValue1464 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1464) = mixedMoment B node1464 node1464Labels := rfl
  simpa [nodeValue1464, Sparse.eval] using hc.symm

theorem sound1467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1467 node1467Labels = Sparse.eval nodeValue1467 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1467) = mixedMoment B node1467 node1467Labels := rfl
  simpa [nodeValue1467, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1474 node1474Labels = Sparse.eval nodeValue1474 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1474) = mixedMoment B node1474 node1474Labels := rfl
  simpa [nodeValue1474, Sparse.eval] using hc.symm

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

theorem sound2131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2131 node2131Labels = Sparse.eval nodeValue2131 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2131) = mixedMoment B node2131 node2131Labels := rfl
  simpa [nodeValue2131, Sparse.eval] using hc.symm

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

theorem sound2252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2252 node2252Labels = Sparse.eval nodeValue2252 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2252) = mixedMoment B node2252 node2252Labels := rfl
  simpa [nodeValue2252, Sparse.eval] using hc.symm

theorem sound2262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2262 node2262Labels = Sparse.eval nodeValue2262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2262) = mixedMoment B node2262 node2262Labels := rfl
  simpa [nodeValue2262, Sparse.eval] using hc.symm

theorem sound2277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2277 node2277Labels = Sparse.eval nodeValue2277 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2277) = mixedMoment B node2277 node2277Labels := rfl
  simpa [nodeValue2277, Sparse.eval] using hc.symm

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

theorem sound2471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2471 node2471Labels = Sparse.eval nodeValue2471 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2471) = mixedMoment B node2471 node2471Labels := rfl
  simpa [nodeValue2471, Sparse.eval] using hc.symm

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

theorem sound2507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2507 node2507Labels = Sparse.eval nodeValue2507 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2507) = mixedMoment B node2507 node2507Labels := rfl
  simpa [nodeValue2507, Sparse.eval] using hc.symm

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

theorem sound2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2592 node2592Labels = Sparse.eval nodeValue2592 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2592) = mixedMoment B node2592 node2592Labels := rfl
  simpa [nodeValue2592, Sparse.eval] using hc.symm

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

theorem sound2707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2707 node2707Labels = Sparse.eval nodeValue2707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2707) = mixedMoment B node2707 node2707Labels := rfl
  simpa [nodeValue2707, Sparse.eval] using hc.symm

theorem sound2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2744 node2744Labels = Sparse.eval nodeValue2744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2744) = mixedMoment B node2744 node2744Labels := rfl
  simpa [nodeValue2744, Sparse.eval] using hc.symm

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

theorem sound2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2781 node2781Labels = Sparse.eval nodeValue2781 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2781) = mixedMoment B node2781 node2781Labels := rfl
  simpa [nodeValue2781, Sparse.eval] using hc.symm

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

theorem sound3172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3172 node3172Labels = Sparse.eval nodeValue3172 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3172) = mixedMoment B node3172 node3172Labels := rfl
  simpa [nodeValue3172, Sparse.eval] using hc.symm

theorem sound3179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3179 node3179Labels = Sparse.eval nodeValue3179 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3179) = mixedMoment B node3179 node3179Labels := rfl
  simpa [nodeValue3179, Sparse.eval] using hc.symm

theorem sound3197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3197 node3197Labels = Sparse.eval nodeValue3197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3197) = mixedMoment B node3197 node3197Labels := rfl
  simpa [nodeValue3197, Sparse.eval] using hc.symm

theorem sound3199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3199 node3199Labels = Sparse.eval nodeValue3199 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3199) = mixedMoment B node3199 node3199Labels := rfl
  simpa [nodeValue3199, Sparse.eval] using hc.symm

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

theorem sound3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3221 node3221Labels = Sparse.eval nodeValue3221 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3221) = mixedMoment B node3221 node3221Labels := rfl
  simpa [nodeValue3221, Sparse.eval] using hc.symm

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

theorem sound3541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3541 node3541Labels = Sparse.eval nodeValue3541 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3541) = mixedMoment B node3541 node3541Labels := rfl
  simpa [nodeValue3541, Sparse.eval] using hc.symm

theorem sound3576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3576 node3576Labels = Sparse.eval nodeValue3576 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3576) = mixedMoment B node3576 node3576Labels := rfl
  simpa [nodeValue3576, Sparse.eval] using hc.symm

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

theorem sound3625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3625 node3625Labels = Sparse.eval nodeValue3625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3625) = mixedMoment B node3625 node3625Labels := rfl
  simpa [nodeValue3625, Sparse.eval] using hc.symm

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

theorem sound3801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3801 node3801Labels = Sparse.eval nodeValue3801 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3801) = mixedMoment B node3801 node3801Labels := rfl
  simpa [nodeValue3801, Sparse.eval] using hc.symm

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

theorem sound3899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3899 node3899Labels = Sparse.eval nodeValue3899 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3899) = mixedMoment B node3899 node3899Labels := rfl
  simpa [nodeValue3899, Sparse.eval] using hc.symm

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

theorem sound4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4025 node4025Labels = Sparse.eval nodeValue4025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4025) = mixedMoment B node4025 node4025Labels := rfl
  simpa [nodeValue4025, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources6
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm205 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA205 + difference 0 0) (sourceB205 + difference 0 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA205 + difference 0 0) (sourceB205 + difference 0 0) sourceC205) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA205 + difference 0 1) (sourceB205 + difference 1 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA205 + difference 0 1) (sourceB205 + difference 1 0) sourceC205) = raw5631 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5631; decide +kernel
    rw [ha]
    exact (canonical5631 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA205 + difference 0 2) (sourceB205 + difference 2 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA205 + difference 0 2) (sourceB205 + difference 2 0) sourceC205) = raw5632 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5632; decide +kernel
    rw [ha]
    exact (canonical5632 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA205 + difference 0 3) (sourceB205 + difference 3 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA205 + difference 0 3) (sourceB205 + difference 3 0) sourceC205) = raw5633 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5633; decide +kernel
    rw [ha]
    exact (canonical5633 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA205 + difference 0 4) (sourceB205 + difference 4 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA205 + difference 0 4) (sourceB205 + difference 4 0) sourceC205) = raw5634 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5634; decide +kernel
    rw [ha]
    exact (canonical5634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA205 + difference 0 5) (sourceB205 + difference 5 0) sourceC205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 4025) := by
    have ha : (tripleCharges (sourceA205 + difference 0 5) (sourceB205 + difference 5 0) sourceC205) = raw5635 := by
      apply Matrix.ext; unfold tripleCharges sourceA205 sourceB205 sourceC205 difference raw5635; decide +kernel
    rw [ha]
    exact (canonical5635 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA205 + sourceB205) sourceC205) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA205 + sourceB205) sourceC205) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA205 sourceB205 sourceC205 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA205 sourceB205 sourceC205
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm205, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm206 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA206 + difference 0 0) (sourceB206 + difference 0 0) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA206 + difference 0 0) (sourceB206 + difference 0 0) sourceC206) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA206 + difference 1 0) (sourceB206 + difference 0 1) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA206 + difference 1 0) (sourceB206 + difference 0 1) sourceC206) = raw5637 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5637; decide +kernel
    rw [ha]
    exact (canonical5637 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA206 + difference 2 0) (sourceB206 + difference 0 2) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA206 + difference 2 0) (sourceB206 + difference 0 2) sourceC206) = raw5638 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5638; decide +kernel
    rw [ha]
    exact (canonical5638 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA206 + difference 3 0) (sourceB206 + difference 0 3) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA206 + difference 3 0) (sourceB206 + difference 0 3) sourceC206) = raw5639 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5639; decide +kernel
    rw [ha]
    exact (canonical5639 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA206 + difference 4 0) (sourceB206 + difference 0 4) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1467) := by
    have ha : (tripleCharges (sourceA206 + difference 4 0) (sourceB206 + difference 0 4) sourceC206) = raw5640 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5640; decide +kernel
    rw [ha]
    exact (canonical5640 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA206 + difference 5 0) (sourceB206 + difference 0 5) sourceC206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1474) := by
    have ha : (tripleCharges (sourceA206 + difference 5 0) (sourceB206 + difference 0 5) sourceC206) = raw5641 := by
      apply Matrix.ext; unfold tripleCharges sourceA206 sourceB206 sourceC206 difference raw5641; decide +kernel
    rw [ha]
    exact (canonical5641 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA206 + sourceB206) sourceC206) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA206 + sourceB206) sourceC206) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA206 sourceB206 sourceC206 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA206 sourceB206 sourceC206
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm206, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm207 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA207 + difference 1 0) (sourceB207 + difference 0 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1464) := by
    have ha : (tripleCharges (sourceA207 + difference 1 0) (sourceB207 + difference 0 1) sourceC207) = raw5637 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5637; decide +kernel
    rw [ha]
    exact (canonical5637 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA207 + difference 1 1) (sourceB207 + difference 1 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA207 + difference 1 1) (sourceB207 + difference 1 1) sourceC207) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA207 + difference 1 2) (sourceB207 + difference 2 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA207 + difference 1 2) (sourceB207 + difference 2 1) sourceC207) = raw5642 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5642; decide +kernel
    rw [ha]
    exact (canonical5642 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA207 + difference 1 3) (sourceB207 + difference 3 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA207 + difference 1 3) (sourceB207 + difference 3 1) sourceC207) = raw5643 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5643; decide +kernel
    rw [ha]
    exact (canonical5643 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA207 + difference 1 4) (sourceB207 + difference 4 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA207 + difference 1 4) (sourceB207 + difference 4 1) sourceC207) = raw5644 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5644; decide +kernel
    rw [ha]
    exact (canonical5644 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA207 + difference 1 5) (sourceB207 + difference 5 1) sourceC207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3172) := by
    have ha : (tripleCharges (sourceA207 + difference 1 5) (sourceB207 + difference 5 1) sourceC207) = raw5645 := by
      apply Matrix.ext; unfold tripleCharges sourceA207 sourceB207 sourceC207 difference raw5645; decide +kernel
    rw [ha]
    exact (canonical5645 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA207 + sourceB207) sourceC207) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA207 + sourceB207) sourceC207) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA207 sourceB207 sourceC207 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA207 sourceB207 sourceC207
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm207, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm208 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA208 + difference 0 1) (sourceB208 + difference 1 0) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3801) := by
    have ha : (tripleCharges (sourceA208 + difference 0 1) (sourceB208 + difference 1 0) sourceC208) = raw5631 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5631; decide +kernel
    rw [ha]
    exact (canonical5631 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA208 + difference 1 1) (sourceB208 + difference 1 1) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA208 + difference 1 1) (sourceB208 + difference 1 1) sourceC208) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA208 + difference 2 1) (sourceB208 + difference 1 2) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA208 + difference 2 1) (sourceB208 + difference 1 2) sourceC208) = raw5646 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5646; decide +kernel
    rw [ha]
    exact (canonical5646 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA208 + difference 3 1) (sourceB208 + difference 1 3) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3202) := by
    have ha : (tripleCharges (sourceA208 + difference 3 1) (sourceB208 + difference 1 3) sourceC208) = raw5647 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5647; decide +kernel
    rw [ha]
    exact (canonical5647 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA208 + difference 4 1) (sourceB208 + difference 1 4) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA208 + difference 4 1) (sourceB208 + difference 1 4) sourceC208) = raw5648 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5648; decide +kernel
    rw [ha]
    exact (canonical5648 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA208 + difference 5 1) (sourceB208 + difference 1 5) sourceC208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA208 + difference 5 1) (sourceB208 + difference 1 5) sourceC208) = raw5649 := by
      apply Matrix.ext; unfold tripleCharges sourceA208 sourceB208 sourceC208 difference raw5649; decide +kernel
    rw [ha]
    exact (canonical5649 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA208 + sourceB208) sourceC208) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA208 + sourceB208) sourceC208) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA208 sourceB208 sourceC208 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA208 sourceB208 sourceC208
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm208, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm209 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA209 + difference 4 0) (sourceB209 + difference 0 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1467) := by
    have ha : (tripleCharges (sourceA209 + difference 4 0) (sourceB209 + difference 0 4) sourceC209) = raw5640 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5640; decide +kernel
    rw [ha]
    exact (canonical5640 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA209 + difference 4 1) (sourceB209 + difference 1 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA209 + difference 4 1) (sourceB209 + difference 1 4) sourceC209) = raw5648 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5648; decide +kernel
    rw [ha]
    exact (canonical5648 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA209 + difference 4 2) (sourceB209 + difference 2 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA209 + difference 4 2) (sourceB209 + difference 2 4) sourceC209) = raw5650 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5650; decide +kernel
    rw [ha]
    exact (canonical5650 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA209 + difference 4 3) (sourceB209 + difference 3 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3199) := by
    have ha : (tripleCharges (sourceA209 + difference 4 3) (sourceB209 + difference 3 4) sourceC209) = raw5651 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5651; decide +kernel
    rw [ha]
    exact (canonical5651 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA209 + difference 4 4) (sourceB209 + difference 4 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA209 + difference 4 4) (sourceB209 + difference 4 4) sourceC209) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA209 + difference 4 5) (sourceB209 + difference 5 4) sourceC209) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3179) := by
    have ha : (tripleCharges (sourceA209 + difference 4 5) (sourceB209 + difference 5 4) sourceC209) = raw5652 := by
      apply Matrix.ext; unfold tripleCharges sourceA209 sourceB209 sourceC209 difference raw5652; decide +kernel
    rw [ha]
    exact (canonical5652 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA209 + sourceB209) sourceC209) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA209 + sourceB209) sourceC209) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA209 sourceB209 sourceC209 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA209 sourceB209 sourceC209
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm209, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm210 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA210 + difference 0 4) (sourceB210 + difference 4 0) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA210 + difference 0 4) (sourceB210 + difference 4 0) sourceC210) = raw5634 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5634; decide +kernel
    rw [ha]
    exact (canonical5634 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA210 + difference 1 4) (sourceB210 + difference 4 1) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA210 + difference 1 4) (sourceB210 + difference 4 1) sourceC210) = raw5644 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5644; decide +kernel
    rw [ha]
    exact (canonical5644 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA210 + difference 2 4) (sourceB210 + difference 4 2) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA210 + difference 2 4) (sourceB210 + difference 4 2) sourceC210) = raw5653 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5653; decide +kernel
    rw [ha]
    exact (canonical5653 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA210 + difference 3 4) (sourceB210 + difference 4 3) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3197) := by
    have ha : (tripleCharges (sourceA210 + difference 3 4) (sourceB210 + difference 4 3) sourceC210) = raw5654 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5654; decide +kernel
    rw [ha]
    exact (canonical5654 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA210 + difference 4 4) (sourceB210 + difference 4 4) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA210 + difference 4 4) (sourceB210 + difference 4 4) sourceC210) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA210 + difference 5 4) (sourceB210 + difference 4 5) sourceC210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA210 + difference 5 4) (sourceB210 + difference 4 5) sourceC210) = raw5655 := by
      apply Matrix.ext; unfold tripleCharges sourceA210 sourceB210 sourceC210 difference raw5655; decide +kernel
    rw [ha]
    exact (canonical5655 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA210 + sourceB210) sourceC210) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA210 + sourceB210) sourceC210) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA210 sourceB210 sourceC210 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA210 sourceB210 sourceC210
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm210, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm211 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA211 + difference 5 0) (sourceB211 + difference 0 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1474) := by
    have ha : (tripleCharges (sourceA211 + difference 5 0) (sourceB211 + difference 0 5) sourceC211) = raw5641 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5641; decide +kernel
    rw [ha]
    exact (canonical5641 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA211 + difference 5 1) (sourceB211 + difference 1 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA211 + difference 5 1) (sourceB211 + difference 1 5) sourceC211) = raw5649 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5649; decide +kernel
    rw [ha]
    exact (canonical5649 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA211 + difference 5 2) (sourceB211 + difference 2 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA211 + difference 5 2) (sourceB211 + difference 2 5) sourceC211) = raw5656 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5656; decide +kernel
    rw [ha]
    exact (canonical5656 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA211 + difference 5 3) (sourceB211 + difference 3 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2471) := by
    have ha : (tripleCharges (sourceA211 + difference 5 3) (sourceB211 + difference 3 5) sourceC211) = raw5657 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5657; decide +kernel
    rw [ha]
    exact (canonical5657 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA211 + difference 5 4) (sourceB211 + difference 4 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2707) := by
    have ha : (tripleCharges (sourceA211 + difference 5 4) (sourceB211 + difference 4 5) sourceC211) = raw5655 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5655; decide +kernel
    rw [ha]
    exact (canonical5655 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA211 + difference 5 5) (sourceB211 + difference 5 5) sourceC211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3221) := by
    have ha : (tripleCharges (sourceA211 + difference 5 5) (sourceB211 + difference 5 5) sourceC211) = raw5630 := by
      apply Matrix.ext; unfold tripleCharges sourceA211 sourceB211 sourceC211 difference raw5630; decide +kernel
    rw [ha]
    exact (canonical5630 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA211 + sourceB211) sourceC211) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA211 + sourceB211) sourceC211) = raw5636 := by
      apply Matrix.ext; unfold doubleCharges sourceA211 sourceB211 sourceC211 raw5636; decide +kernel
    rw [ha]
    exact (canonical5636 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA211 sourceB211 sourceC211
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm211, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm215 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA215 + difference 0 0) (sourceB215 + difference 0 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA215 + difference 0 0) (sourceB215 + difference 0 0) sourceC215) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA215 + difference 0 1) (sourceB215 + difference 1 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA215 + difference 0 1) (sourceB215 + difference 1 0) sourceC215) = raw5749 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5749; decide +kernel
    rw [ha]
    exact (canonical5749 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA215 + difference 0 2) (sourceB215 + difference 2 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA215 + difference 0 2) (sourceB215 + difference 2 0) sourceC215) = raw5750 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5750; decide +kernel
    rw [ha]
    exact (canonical5750 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA215 + difference 0 3) (sourceB215 + difference 3 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3625) := by
    have ha : (tripleCharges (sourceA215 + difference 0 3) (sourceB215 + difference 3 0) sourceC215) = raw5751 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5751; decide +kernel
    rw [ha]
    exact (canonical5751 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA215 + difference 0 4) (sourceB215 + difference 4 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3576) := by
    have ha : (tripleCharges (sourceA215 + difference 0 4) (sourceB215 + difference 4 0) sourceC215) = raw5752 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5752; decide +kernel
    rw [ha]
    exact (canonical5752 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA215 + difference 0 5) (sourceB215 + difference 5 0) sourceC215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2507) := by
    have ha : (tripleCharges (sourceA215 + difference 0 5) (sourceB215 + difference 5 0) sourceC215) = raw5753 := by
      apply Matrix.ext; unfold tripleCharges sourceA215 sourceB215 sourceC215 difference raw5753; decide +kernel
    rw [ha]
    exact (canonical5753 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA215 + sourceB215) sourceC215) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA215 + sourceB215) sourceC215) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA215 sourceB215 sourceC215 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA215 sourceB215 sourceC215
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm215, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm217 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA217 + difference 4 0) (sourceB217 + difference 0 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1056) := by
    have ha : (tripleCharges (sourceA217 + difference 4 0) (sourceB217 + difference 0 4) sourceC217) = raw5758 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5758; decide +kernel
    rw [ha]
    exact (canonical5758 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA217 + difference 4 1) (sourceB217 + difference 1 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA217 + difference 4 1) (sourceB217 + difference 1 4) sourceC217) = raw5760 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5760; decide +kernel
    rw [ha]
    exact (canonical5760 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA217 + difference 4 2) (sourceB217 + difference 2 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA217 + difference 4 2) (sourceB217 + difference 2 4) sourceC217) = raw5761 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5761; decide +kernel
    rw [ha]
    exact (canonical5761 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA217 + difference 4 3) (sourceB217 + difference 3 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2277) := by
    have ha : (tripleCharges (sourceA217 + difference 4 3) (sourceB217 + difference 3 4) sourceC217) = raw5762 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5762; decide +kernel
    rw [ha]
    exact (canonical5762 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA217 + difference 4 4) (sourceB217 + difference 4 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA217 + difference 4 4) (sourceB217 + difference 4 4) sourceC217) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA217 + difference 4 5) (sourceB217 + difference 5 4) sourceC217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2131) := by
    have ha : (tripleCharges (sourceA217 + difference 4 5) (sourceB217 + difference 5 4) sourceC217) = raw5763 := by
      apply Matrix.ext; unfold tripleCharges sourceA217 sourceB217 sourceC217 difference raw5763; decide +kernel
    rw [ha]
    exact (canonical5763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA217 + sourceB217) sourceC217) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA217 + sourceB217) sourceC217) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA217 sourceB217 sourceC217 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA217 sourceB217 sourceC217
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm217, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm219 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA219 + difference 5 0) (sourceB219 + difference 0 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1038) := by
    have ha : (tripleCharges (sourceA219 + difference 5 0) (sourceB219 + difference 0 5) sourceC219) = raw5759 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5759; decide +kernel
    rw [ha]
    exact (canonical5759 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA219 + difference 5 1) (sourceB219 + difference 1 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA219 + difference 5 1) (sourceB219 + difference 1 5) sourceC219) = raw5768 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5768; decide +kernel
    rw [ha]
    exact (canonical5768 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA219 + difference 5 2) (sourceB219 + difference 2 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA219 + difference 5 2) (sourceB219 + difference 2 5) sourceC219) = raw5769 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5769; decide +kernel
    rw [ha]
    exact (canonical5769 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA219 + difference 5 3) (sourceB219 + difference 3 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2262) := by
    have ha : (tripleCharges (sourceA219 + difference 5 3) (sourceB219 + difference 3 5) sourceC219) = raw5770 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5770; decide +kernel
    rw [ha]
    exact (canonical5770 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA219 + difference 5 4) (sourceB219 + difference 4 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2104) := by
    have ha : (tripleCharges (sourceA219 + difference 5 4) (sourceB219 + difference 4 5) sourceC219) = raw5767 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5767; decide +kernel
    rw [ha]
    exact (canonical5767 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA219 + difference 5 5) (sourceB219 + difference 5 5) sourceC219) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2252) := by
    have ha : (tripleCharges (sourceA219 + difference 5 5) (sourceB219 + difference 5 5) sourceC219) = raw5748 := by
      apply Matrix.ext; unfold tripleCharges sourceA219 sourceB219 sourceC219 difference raw5748; decide +kernel
    rw [ha]
    exact (canonical5748 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA219 + sourceB219) sourceC219) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA219 + sourceB219) sourceC219) = raw5754 := by
      apply Matrix.ext; unfold doubleCharges sourceA219 sourceB219 sourceC219 raw5754; decide +kernel
    rw [ha]
    exact (canonical5754 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA219 sourceB219 sourceC219
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm219, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm223 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA223 + difference 0 0) (sourceB223 + difference 0 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA223 + difference 0 0) (sourceB223 + difference 0 0) sourceC223) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA223 + difference 0 1) (sourceB223 + difference 1 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3626) := by
    have ha : (tripleCharges (sourceA223 + difference 0 1) (sourceB223 + difference 1 0) sourceC223) = raw5862 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5862; decide +kernel
    rw [ha]
    exact (canonical5862 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA223 + difference 0 2) (sourceB223 + difference 2 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA223 + difference 0 2) (sourceB223 + difference 2 0) sourceC223) = raw5863 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5863; decide +kernel
    rw [ha]
    exact (canonical5863 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA223 + difference 0 3) (sourceB223 + difference 3 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3541) := by
    have ha : (tripleCharges (sourceA223 + difference 0 3) (sourceB223 + difference 3 0) sourceC223) = raw5864 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5864; decide +kernel
    rw [ha]
    exact (canonical5864 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA223 + difference 0 4) (sourceB223 + difference 4 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2279) := by
    have ha : (tripleCharges (sourceA223 + difference 0 4) (sourceB223 + difference 4 0) sourceC223) = raw5865 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5865; decide +kernel
    rw [ha]
    exact (canonical5865 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA223 + difference 0 5) (sourceB223 + difference 5 0) sourceC223) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3632) := by
    have ha : (tripleCharges (sourceA223 + difference 0 5) (sourceB223 + difference 5 0) sourceC223) = raw5866 := by
      apply Matrix.ext; unfold tripleCharges sourceA223 sourceB223 sourceC223 difference raw5866; decide +kernel
    rw [ha]
    exact (canonical5866 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA223 + sourceB223) sourceC223) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA223 + sourceB223) sourceC223) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA223 sourceB223 sourceC223 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA223 sourceB223 sourceC223
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm223, Integer.Sparse.eval]
  linarith only [hs]

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

theorem sourceEq224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm224 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA224 + difference 0 0) (sourceB224 + difference 0 0) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA224 + difference 0 0) (sourceB224 + difference 0 0) sourceC224) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA224 + difference 1 0) (sourceB224 + difference 0 1) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1296) := by
    have ha : (tripleCharges (sourceA224 + difference 1 0) (sourceB224 + difference 0 1) sourceC224) = raw5868 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5868; decide +kernel
    rw [ha]
    exact (canonical5868 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA224 + difference 2 0) (sourceB224 + difference 0 2) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1238) := by
    have ha : (tripleCharges (sourceA224 + difference 2 0) (sourceB224 + difference 0 2) sourceC224) = raw5869 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5869; decide +kernel
    rw [ha]
    exact (canonical5869 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA224 + difference 3 0) (sourceB224 + difference 0 3) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1238) := by
    have ha : (tripleCharges (sourceA224 + difference 3 0) (sourceB224 + difference 0 3) sourceC224) = raw5870 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5870; decide +kernel
    rw [ha]
    exact (canonical5870 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA224 + difference 4 0) (sourceB224 + difference 0 4) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1245) := by
    have ha : (tripleCharges (sourceA224 + difference 4 0) (sourceB224 + difference 0 4) sourceC224) = raw5871 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5871; decide +kernel
    rw [ha]
    exact (canonical5871 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA224 + difference 5 0) (sourceB224 + difference 0 5) sourceC224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1244) := by
    have ha : (tripleCharges (sourceA224 + difference 5 0) (sourceB224 + difference 0 5) sourceC224) = raw5872 := by
      apply Matrix.ext; unfold tripleCharges sourceA224 sourceB224 sourceC224 difference raw5872; decide +kernel
    rw [ha]
    exact (canonical5872 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA224 + sourceB224) sourceC224) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA224 + sourceB224) sourceC224) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA224 sourceB224 sourceC224 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA224 sourceB224 sourceC224
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm224, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm225 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA225 + difference 1 0) (sourceB225 + difference 0 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1296) := by
    have ha : (tripleCharges (sourceA225 + difference 1 0) (sourceB225 + difference 0 1) sourceC225) = raw5868 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5868; decide +kernel
    rw [ha]
    exact (canonical5868 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA225 + difference 1 1) (sourceB225 + difference 1 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2744) := by
    have ha : (tripleCharges (sourceA225 + difference 1 1) (sourceB225 + difference 1 1) sourceC225) = raw5861 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5861; decide +kernel
    rw [ha]
    exact (canonical5861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA225 + difference 1 2) (sourceB225 + difference 2 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA225 + difference 1 2) (sourceB225 + difference 2 1) sourceC225) = raw5873 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5873; decide +kernel
    rw [ha]
    exact (canonical5873 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA225 + difference 1 3) (sourceB225 + difference 3 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2592) := by
    have ha : (tripleCharges (sourceA225 + difference 1 3) (sourceB225 + difference 3 1) sourceC225) = raw5874 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5874; decide +kernel
    rw [ha]
    exact (canonical5874 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA225 + difference 1 4) (sourceB225 + difference 4 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2138) := by
    have ha : (tripleCharges (sourceA225 + difference 1 4) (sourceB225 + difference 4 1) sourceC225) = raw5875 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5875; decide +kernel
    rw [ha]
    exact (canonical5875 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA225 + difference 1 5) (sourceB225 + difference 5 1) sourceC225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2781) := by
    have ha : (tripleCharges (sourceA225 + difference 1 5) (sourceB225 + difference 5 1) sourceC225) = raw5876 := by
      apply Matrix.ext; unfold tripleCharges sourceA225 sourceB225 sourceC225 difference raw5876; decide +kernel
    rw [ha]
    exact (canonical5876 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA225 + sourceB225) sourceC225) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA225 + sourceB225) sourceC225) = raw5867 := by
      apply Matrix.ext; unfold doubleCharges sourceA225 sourceB225 sourceC225 raw5867; decide +kernel
    rw [ha]
    exact (canonical5867 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA225 sourceB225 sourceC225
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm225, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck177 : Integer.Sparse.reindex keyMap MixedData.row177 = numericRow177 := by decide +kernel

theorem numericCheck177 (x : Master → ℝ) : Integer.Sparse.eval numericRow177 x =
    (1 : ℝ) * reducedSource177 x := by
  norm_num [numericRow177, reducedSource177, Integer.Sparse.eval, Sparse.eval, nodeValue3221, nodeValue3801, nodeValue3899, nodeValue4025, nodeValue4091]

theorem reindexCheck178 : Integer.Sparse.reindex keyMap MixedData.row178 = numericRow178 := by decide +kernel

theorem numericCheck178 (x : Master → ℝ) : Integer.Sparse.eval numericRow178 x =
    (1 : ℝ) * reducedSource178 x := by
  norm_num [numericRow178, reducedSource178, Integer.Sparse.eval, Sparse.eval, nodeValue1464, nodeValue1467, nodeValue1474, nodeValue3221, nodeValue4091]

theorem reindexCheck179 : Integer.Sparse.reindex keyMap MixedData.row179 = numericRow179 := by decide +kernel

theorem numericCheck179 (x : Master → ℝ) : Integer.Sparse.eval numericRow179 x =
    (1 : ℝ) * reducedSource179 x := by
  norm_num [numericRow179, reducedSource179, Integer.Sparse.eval, Sparse.eval, nodeValue1464, nodeValue3172, nodeValue3197, nodeValue3202, nodeValue3221, nodeValue4091]

theorem reindexCheck180 : Integer.Sparse.reindex keyMap MixedData.row180 = numericRow180 := by decide +kernel

theorem numericCheck180 (x : Master → ℝ) : Integer.Sparse.eval numericRow180 x =
    (1 : ℝ) * reducedSource180 x := by
  norm_num [numericRow180, reducedSource180, Integer.Sparse.eval, Sparse.eval, nodeValue2471, nodeValue3199, nodeValue3202, nodeValue3221, nodeValue3801, nodeValue4091]

theorem reindexCheck181 : Integer.Sparse.reindex keyMap MixedData.row181 = numericRow181 := by decide +kernel

theorem numericCheck181 (x : Master → ℝ) : Integer.Sparse.eval numericRow181 x =
    (1 : ℝ) * reducedSource181 x := by
  norm_num [numericRow181, reducedSource181, Integer.Sparse.eval, Sparse.eval, nodeValue1467, nodeValue3179, nodeValue3199, nodeValue3221, nodeValue4091]

theorem reindexCheck182 : Integer.Sparse.reindex keyMap MixedData.row182 = numericRow182 := by decide +kernel

theorem numericCheck182 (x : Master → ℝ) : Integer.Sparse.eval numericRow182 x =
    (1 : ℝ) * reducedSource182 x := by
  norm_num [numericRow182, reducedSource182, Integer.Sparse.eval, Sparse.eval, nodeValue2707, nodeValue3197, nodeValue3221, nodeValue3899, nodeValue4091]

theorem reindexCheck183 : Integer.Sparse.reindex keyMap MixedData.row183 = numericRow183 := by decide +kernel

theorem numericCheck183 (x : Master → ℝ) : Integer.Sparse.eval numericRow183 x =
    (1 : ℝ) * reducedSource183 x := by
  norm_num [numericRow183, reducedSource183, Integer.Sparse.eval, Sparse.eval, nodeValue1474, nodeValue2471, nodeValue2707, nodeValue3221, nodeValue4091]

theorem reindexCheck185 : Integer.Sparse.reindex keyMap MixedData.row185 = numericRow185 := by decide +kernel

theorem numericCheck185 (x : Master → ℝ) : Integer.Sparse.eval numericRow185 x =
    (1 : ℝ) * reducedSource185 x := by
  norm_num [numericRow185, reducedSource185, Integer.Sparse.eval, Sparse.eval, nodeValue2252, nodeValue2507, nodeValue3576, nodeValue3625, nodeValue4084]

theorem reindexCheck186 : Integer.Sparse.reindex keyMap MixedData.row186 = numericRow186 := by decide +kernel

theorem numericCheck186 (x : Master → ℝ) : Integer.Sparse.eval numericRow186 x =
    (1 : ℝ) * reducedSource186 x := by
  norm_num [numericRow186, reducedSource186, Integer.Sparse.eval, Sparse.eval, nodeValue1056, nodeValue2131, nodeValue2252, nodeValue2277, nodeValue4084]

theorem reindexCheck187 : Integer.Sparse.reindex keyMap MixedData.row187 = numericRow187 := by decide +kernel

theorem numericCheck187 (x : Master → ℝ) : Integer.Sparse.eval numericRow187 x =
    (1 : ℝ) * reducedSource187 x := by
  norm_num [numericRow187, reducedSource187, Integer.Sparse.eval, Sparse.eval, nodeValue1038, nodeValue2104, nodeValue2252, nodeValue2262, nodeValue4084]

theorem reindexCheck189 : Integer.Sparse.reindex keyMap MixedData.row189 = numericRow189 := by decide +kernel

theorem numericCheck189 (x : Master → ℝ) : Integer.Sparse.eval numericRow189 x =
    (1 : ℝ) * reducedSource189 x := by
  norm_num [numericRow189, reducedSource189, Integer.Sparse.eval, Sparse.eval, nodeValue2279, nodeValue2744, nodeValue3541, nodeValue3626, nodeValue3632, nodeValue4084]

theorem reindexCheck190 : Integer.Sparse.reindex keyMap MixedData.row190 = numericRow190 := by decide +kernel

theorem numericCheck190 (x : Master → ℝ) : Integer.Sparse.eval numericRow190 x =
    (1 : ℝ) * reducedSource190 x := by
  norm_num [numericRow190, reducedSource190, Integer.Sparse.eval, Sparse.eval, nodeValue1238, nodeValue1244, nodeValue1245, nodeValue1296, nodeValue2744, nodeValue4084]

theorem reindexCheck191 : Integer.Sparse.reindex keyMap MixedData.row191 = numericRow191 := by decide +kernel

theorem numericCheck191 (x : Master → ℝ) : Integer.Sparse.eval numericRow191 x =
    (1 : ℝ) * reducedSource191 x := by
  norm_num [numericRow191, reducedSource191, Integer.Sparse.eval, Sparse.eval, nodeValue1296, nodeValue2138, nodeValue2592, nodeValue2744, nodeValue2781, nodeValue4084]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource177 (mixedVector B) = 0 := by
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h4025 : mixedVector B (Sum.inr 4025) = Sparse.eval nodeValue4025 (mixedVector B) := by
    change mixedMoment B node4025 node4025Labels = _
    exact sound4025 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm205, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3221, h3801, h3899, h4025, h4091, reducedSource177] using sourceEq205 B hB

theorem rowSound177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row177 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck177, numericCheck177, reducedZero177 B hB hF, mul_zero]

theorem reducedZero178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource178 (mixedVector B) = 0 := by
  have h1464 : mixedVector B (Sum.inr 1464) = Sparse.eval nodeValue1464 (mixedVector B) := by
    change mixedMoment B node1464 node1464Labels = _
    exact sound1464 B hB hF
  have h1467 : mixedVector B (Sum.inr 1467) = Sparse.eval nodeValue1467 (mixedVector B) := by
    change mixedMoment B node1467 node1467Labels = _
    exact sound1467 B hB hF
  have h1474 : mixedVector B (Sum.inr 1474) = Sparse.eval nodeValue1474 (mixedVector B) := by
    change mixedMoment B node1474 node1474Labels = _
    exact sound1474 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm206, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1464, h1467, h1474, h3221, h4091, reducedSource178] using sourceEq206 B hB

theorem rowSound178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row178 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck178, numericCheck178, reducedZero178 B hB hF, mul_zero]

theorem reducedZero179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource179 (mixedVector B) = 0 := by
  have h1464 : mixedVector B (Sum.inr 1464) = Sparse.eval nodeValue1464 (mixedVector B) := by
    change mixedMoment B node1464 node1464Labels = _
    exact sound1464 B hB hF
  have h3172 : mixedVector B (Sum.inr 3172) = Sparse.eval nodeValue3172 (mixedVector B) := by
    change mixedMoment B node3172 node3172Labels = _
    exact sound3172 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm207, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1464, h3172, h3197, h3202, h3221, h4091, reducedSource179] using sourceEq207 B hB

theorem rowSound179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row179 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck179, numericCheck179, reducedZero179 B hB hF, mul_zero]

theorem reducedZero180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource180 (mixedVector B) = 0 := by
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3202 : mixedVector B (Sum.inr 3202) = Sparse.eval nodeValue3202 (mixedVector B) := by
    change mixedMoment B node3202 node3202Labels = _
    exact sound3202 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3801 : mixedVector B (Sum.inr 3801) = Sparse.eval nodeValue3801 (mixedVector B) := by
    change mixedMoment B node3801 node3801Labels = _
    exact sound3801 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm208, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2471, h3199, h3202, h3221, h3801, h4091, reducedSource180] using sourceEq208 B hB

theorem rowSound180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row180 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck180, numericCheck180, reducedZero180 B hB hF, mul_zero]

theorem reducedZero181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource181 (mixedVector B) = 0 := by
  have h1467 : mixedVector B (Sum.inr 1467) = Sparse.eval nodeValue1467 (mixedVector B) := by
    change mixedMoment B node1467 node1467Labels = _
    exact sound1467 B hB hF
  have h3179 : mixedVector B (Sum.inr 3179) = Sparse.eval nodeValue3179 (mixedVector B) := by
    change mixedMoment B node3179 node3179Labels = _
    exact sound3179 B hB hF
  have h3199 : mixedVector B (Sum.inr 3199) = Sparse.eval nodeValue3199 (mixedVector B) := by
    change mixedMoment B node3199 node3199Labels = _
    exact sound3199 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm209, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1467, h3179, h3199, h3221, h4091, reducedSource181] using sourceEq209 B hB

theorem rowSound181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row181 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck181, numericCheck181, reducedZero181 B hB hF, mul_zero]

theorem reducedZero182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource182 (mixedVector B) = 0 := by
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h3197 : mixedVector B (Sum.inr 3197) = Sparse.eval nodeValue3197 (mixedVector B) := by
    change mixedMoment B node3197 node3197Labels = _
    exact sound3197 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm210, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2707, h3197, h3221, h3899, h4091, reducedSource182] using sourceEq210 B hB

theorem rowSound182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row182 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck182, numericCheck182, reducedZero182 B hB hF, mul_zero]

theorem reducedZero183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource183 (mixedVector B) = 0 := by
  have h1474 : mixedVector B (Sum.inr 1474) = Sparse.eval nodeValue1474 (mixedVector B) := by
    change mixedMoment B node1474 node1474Labels = _
    exact sound1474 B hB hF
  have h2471 : mixedVector B (Sum.inr 2471) = Sparse.eval nodeValue2471 (mixedVector B) := by
    change mixedMoment B node2471 node2471Labels = _
    exact sound2471 B hB hF
  have h2707 : mixedVector B (Sum.inr 2707) = Sparse.eval nodeValue2707 (mixedVector B) := by
    change mixedMoment B node2707 node2707Labels = _
    exact sound2707 B hB hF
  have h3221 : mixedVector B (Sum.inr 3221) = Sparse.eval nodeValue3221 (mixedVector B) := by
    change mixedMoment B node3221 node3221Labels = _
    exact sound3221 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm211, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1474, h2471, h2707, h3221, h4091, reducedSource183] using sourceEq211 B hB

theorem rowSound183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row183 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck183, numericCheck183, reducedZero183 B hB hF, mul_zero]

theorem reducedZero185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource185 (mixedVector B) = 0 := by
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2507 : mixedVector B (Sum.inr 2507) = Sparse.eval nodeValue2507 (mixedVector B) := by
    change mixedMoment B node2507 node2507Labels = _
    exact sound2507 B hB hF
  have h3576 : mixedVector B (Sum.inr 3576) = Sparse.eval nodeValue3576 (mixedVector B) := by
    change mixedMoment B node3576 node3576Labels = _
    exact sound3576 B hB hF
  have h3625 : mixedVector B (Sum.inr 3625) = Sparse.eval nodeValue3625 (mixedVector B) := by
    change mixedMoment B node3625 node3625Labels = _
    exact sound3625 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm215, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2252, h2507, h3576, h3625, h4084, reducedSource185] using sourceEq215 B hB

theorem rowSound185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row185 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck185, numericCheck185, reducedZero185 B hB hF, mul_zero]

theorem reducedZero186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource186 (mixedVector B) = 0 := by
  have h1056 : mixedVector B (Sum.inr 1056) = Sparse.eval nodeValue1056 (mixedVector B) := by
    change mixedMoment B node1056 node1056Labels = _
    exact sound1056 B hB hF
  have h2131 : mixedVector B (Sum.inr 2131) = Sparse.eval nodeValue2131 (mixedVector B) := by
    change mixedMoment B node2131 node2131Labels = _
    exact sound2131 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2277 : mixedVector B (Sum.inr 2277) = Sparse.eval nodeValue2277 (mixedVector B) := by
    change mixedMoment B node2277 node2277Labels = _
    exact sound2277 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm217, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1056, h2131, h2252, h2277, h4084, reducedSource186] using sourceEq217 B hB

theorem rowSound186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row186 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck186, numericCheck186, reducedZero186 B hB hF, mul_zero]

theorem reducedZero187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource187 (mixedVector B) = 0 := by
  have h1038 : mixedVector B (Sum.inr 1038) = Sparse.eval nodeValue1038 (mixedVector B) := by
    change mixedMoment B node1038 node1038Labels = _
    exact sound1038 B hB hF
  have h2104 : mixedVector B (Sum.inr 2104) = Sparse.eval nodeValue2104 (mixedVector B) := by
    change mixedMoment B node2104 node2104Labels = _
    exact sound2104 B hB hF
  have h2252 : mixedVector B (Sum.inr 2252) = Sparse.eval nodeValue2252 (mixedVector B) := by
    change mixedMoment B node2252 node2252Labels = _
    exact sound2252 B hB hF
  have h2262 : mixedVector B (Sum.inr 2262) = Sparse.eval nodeValue2262 (mixedVector B) := by
    change mixedMoment B node2262 node2262Labels = _
    exact sound2262 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm219, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1038, h2104, h2252, h2262, h4084, reducedSource187] using sourceEq219 B hB

theorem rowSound187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row187 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck187, numericCheck187, reducedZero187 B hB hF, mul_zero]

theorem reducedZero189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource189 (mixedVector B) = 0 := by
  have h2279 : mixedVector B (Sum.inr 2279) = Sparse.eval nodeValue2279 (mixedVector B) := by
    change mixedMoment B node2279 node2279Labels = _
    exact sound2279 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h3541 : mixedVector B (Sum.inr 3541) = Sparse.eval nodeValue3541 (mixedVector B) := by
    change mixedMoment B node3541 node3541Labels = _
    exact sound3541 B hB hF
  have h3626 : mixedVector B (Sum.inr 3626) = Sparse.eval nodeValue3626 (mixedVector B) := by
    change mixedMoment B node3626 node3626Labels = _
    exact sound3626 B hB hF
  have h3632 : mixedVector B (Sum.inr 3632) = Sparse.eval nodeValue3632 (mixedVector B) := by
    change mixedMoment B node3632 node3632Labels = _
    exact sound3632 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm223, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2279, h2744, h3541, h3626, h3632, h4084, reducedSource189] using sourceEq223 B hB

theorem rowSound189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row189 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck189, numericCheck189, reducedZero189 B hB hF, mul_zero]

theorem reducedZero190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource190 (mixedVector B) = 0 := by
  have h1238 : mixedVector B (Sum.inr 1238) = Sparse.eval nodeValue1238 (mixedVector B) := by
    change mixedMoment B node1238 node1238Labels = _
    exact sound1238 B hB hF
  have h1244 : mixedVector B (Sum.inr 1244) = Sparse.eval nodeValue1244 (mixedVector B) := by
    change mixedMoment B node1244 node1244Labels = _
    exact sound1244 B hB hF
  have h1245 : mixedVector B (Sum.inr 1245) = Sparse.eval nodeValue1245 (mixedVector B) := by
    change mixedMoment B node1245 node1245Labels = _
    exact sound1245 B hB hF
  have h1296 : mixedVector B (Sum.inr 1296) = Sparse.eval nodeValue1296 (mixedVector B) := by
    change mixedMoment B node1296 node1296Labels = _
    exact sound1296 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm224, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1238, h1244, h1245, h1296, h2744, h4084, reducedSource190] using sourceEq224 B hB

theorem rowSound190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row190 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck190, numericCheck190, reducedZero190 B hB hF, mul_zero]

theorem reducedZero191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource191 (mixedVector B) = 0 := by
  have h1296 : mixedVector B (Sum.inr 1296) = Sparse.eval nodeValue1296 (mixedVector B) := by
    change mixedMoment B node1296 node1296Labels = _
    exact sound1296 B hB hF
  have h2138 : mixedVector B (Sum.inr 2138) = Sparse.eval nodeValue2138 (mixedVector B) := by
    change mixedMoment B node2138 node2138Labels = _
    exact sound2138 B hB hF
  have h2592 : mixedVector B (Sum.inr 2592) = Sparse.eval nodeValue2592 (mixedVector B) := by
    change mixedMoment B node2592 node2592Labels = _
    exact sound2592 B hB hF
  have h2744 : mixedVector B (Sum.inr 2744) = Sparse.eval nodeValue2744 (mixedVector B) := by
    change mixedMoment B node2744 node2744Labels = _
    exact sound2744 B hB hF
  have h2781 : mixedVector B (Sum.inr 2781) = Sparse.eval nodeValue2781 (mixedVector B) := by
    change mixedMoment B node2781 node2781Labels = _
    exact sound2781 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm225, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1296, h2138, h2592, h2744, h2781, h4084, reducedSource191] using sourceEq225 B hB

theorem rowSound191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row191 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck191, numericCheck191, reducedZero191 B hB hF, mul_zero]

theorem sourceRowsAt176 : MixedData.sourceRows (176 : Fin 2425) =
    MixedData.row176 := by decide +kernel

theorem sourceRowsAt177 : MixedData.sourceRows (177 : Fin 2425) =
    MixedData.row177 := by decide +kernel

theorem sourceRowsAt178 : MixedData.sourceRows (178 : Fin 2425) =
    MixedData.row178 := by decide +kernel

theorem sourceRowsAt179 : MixedData.sourceRows (179 : Fin 2425) =
    MixedData.row179 := by decide +kernel

theorem sourceRowsAt180 : MixedData.sourceRows (180 : Fin 2425) =
    MixedData.row180 := by decide +kernel

theorem sourceRowsAt181 : MixedData.sourceRows (181 : Fin 2425) =
    MixedData.row181 := by decide +kernel

theorem sourceRowsAt182 : MixedData.sourceRows (182 : Fin 2425) =
    MixedData.row182 := by decide +kernel

theorem sourceRowsAt183 : MixedData.sourceRows (183 : Fin 2425) =
    MixedData.row183 := by decide +kernel

theorem sourceRowsAt184 : MixedData.sourceRows (184 : Fin 2425) =
    MixedData.row184 := by decide +kernel

theorem sourceRowsAt185 : MixedData.sourceRows (185 : Fin 2425) =
    MixedData.row185 := by decide +kernel

theorem sourceRowsAt186 : MixedData.sourceRows (186 : Fin 2425) =
    MixedData.row186 := by decide +kernel

theorem sourceRowsAt187 : MixedData.sourceRows (187 : Fin 2425) =
    MixedData.row187 := by decide +kernel

theorem sourceRowsAt188 : MixedData.sourceRows (188 : Fin 2425) =
    MixedData.row188 := by decide +kernel

theorem sourceRowsAt189 : MixedData.sourceRows (189 : Fin 2425) =
    MixedData.row189 := by decide +kernel

theorem sourceRowsAt190 : MixedData.sourceRows (190 : Fin 2425) =
    MixedData.row190 := by decide +kernel

theorem sourceRowsAt191 : MixedData.sourceRows (191 : Fin 2425) =
    MixedData.row191 := by decide +kernel

theorem chunkSound11_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 11) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 176 ∨ k.val = 177 ∨ k.val = 178 ∨ k.val = 179 ∨ k.val = 180 ∨ k.val = 181 ∨ k.val = 182 ∨ k.val = 183 ∨ k.val = 184 ∨ k.val = 185 ∨ k.val = 186 ∨ k.val = 187 ∨ k.val = 188 ∨ k.val = 189 ∨ k.val = 190 ∨ k.val = 191 := by omega
  rcases heq with h176 | h177 | h178 | h179 | h180 | h181 | h182 | h183 | h184 | h185 | h186 | h187 | h188 | h189 | h190 | h191
  · have he : k = (176 : Fin 2425) := Fin.ext h176
    subst k
    rw [sourceRowsAt176]
    exact rowSound176_e B hB hF
  · have he : k = (177 : Fin 2425) := Fin.ext h177
    subst k
    rw [sourceRowsAt177]
    exact rowSound177 B hB hF
  · have he : k = (178 : Fin 2425) := Fin.ext h178
    subst k
    rw [sourceRowsAt178]
    exact rowSound178 B hB hF
  · have he : k = (179 : Fin 2425) := Fin.ext h179
    subst k
    rw [sourceRowsAt179]
    exact rowSound179 B hB hF
  · have he : k = (180 : Fin 2425) := Fin.ext h180
    subst k
    rw [sourceRowsAt180]
    exact rowSound180 B hB hF
  · have he : k = (181 : Fin 2425) := Fin.ext h181
    subst k
    rw [sourceRowsAt181]
    exact rowSound181 B hB hF
  · have he : k = (182 : Fin 2425) := Fin.ext h182
    subst k
    rw [sourceRowsAt182]
    exact rowSound182 B hB hF
  · have he : k = (183 : Fin 2425) := Fin.ext h183
    subst k
    rw [sourceRowsAt183]
    exact rowSound183 B hB hF
  · have he : k = (184 : Fin 2425) := Fin.ext h184
    subst k
    rw [sourceRowsAt184]
    exact rowSound184_e B hB hF
  · have he : k = (185 : Fin 2425) := Fin.ext h185
    subst k
    rw [sourceRowsAt185]
    exact rowSound185 B hB hF
  · have he : k = (186 : Fin 2425) := Fin.ext h186
    subst k
    rw [sourceRowsAt186]
    exact rowSound186 B hB hF
  · have he : k = (187 : Fin 2425) := Fin.ext h187
    subst k
    rw [sourceRowsAt187]
    exact rowSound187 B hB hF
  · have he : k = (188 : Fin 2425) := Fin.ext h188
    subst k
    rw [sourceRowsAt188]
    exact rowSound188_e B hB hF
  · have he : k = (189 : Fin 2425) := Fin.ext h189
    subst k
    rw [sourceRowsAt189]
    exact rowSound189 B hB hF
  · have he : k = (190 : Fin 2425) := Fin.ext h190
    subst k
    rw [sourceRowsAt190]
    exact rowSound190 B hB hF
  · have he : k = (191 : Fin 2425) := Fin.ext h191
    subst k
    rw [sourceRowsAt191]
    exact rowSound191 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound11_e_oai
