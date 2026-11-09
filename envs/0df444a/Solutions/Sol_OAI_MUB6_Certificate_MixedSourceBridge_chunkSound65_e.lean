-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:29:12.432215+00:00
-- url     : https://prove2.me/submissions/d9f41bf1-10c6-424d-a646-93ce75297490

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E108
import Definitions.Def_OAIQ106E109
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E124
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical156
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20088 raw20088Labels = mixedMoment B node621 node621Labels := by
  calc
    mixedMoment B raw20088 raw20088Labels = mixedMoment B raw20088step0 raw20088step0Labels := by
      have hz : ∀ j, raw20088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20088step0 = (fun i j => raw20088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20088step0 raw20088; decide +kernel
      have hl : raw20088step0Labels = raw20088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088 raw20088Labels permutation434 hz
    mixedMoment B raw20088step0 raw20088step0Labels = mixedMoment B raw20088step1 raw20088step1Labels := by
      have hz : ∀ j, raw20088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20088step1 = (fun i j => raw20088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20088step1 raw20088step0; decide +kernel
      have hl : raw20088step1Labels = raw20088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088step0 raw20088step0Labels permutation80 hz
    mixedMoment B raw20088step1 raw20088step1Labels = mixedMoment B raw20088step2 raw20088step2Labels := by
      have hz : ∀ j, raw20088step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20088step2 = (fun i j => raw20088step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20088step2 raw20088step1; decide +kernel
      have hl : raw20088step2Labels = raw20088step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088step1 raw20088step1Labels permutation14 hz
    _ = mixedMoment B node621 node621Labels := by rfl

theorem canonical20089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20089 raw20089Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20089 raw20089Labels = mixedMoment B raw20089step0 raw20089step0Labels := by
      have hz : ∀ j, raw20089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20089step0 = (fun i j => raw20089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20089step0 raw20089; decide +kernel
      have hl : raw20089step0Labels = raw20089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20089 raw20089Labels permutation434 hz
    mixedMoment B raw20089step0 raw20089step0Labels = mixedMoment B raw20089step1 raw20089step1Labels := by
      have hz : ∀ j, raw20089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20089step1 = (fun i j => raw20089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20089step1 raw20089step0; decide +kernel
      have hl : raw20089step1Labels = raw20089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20089step0 raw20089step0Labels permutation80 hz
    _ = mixedMoment B node940 node940Labels := by rfl

theorem canonical20090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20090 raw20090Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20090 raw20090Labels = mixedMoment B raw20090step0 raw20090step0Labels := by
      have hz : ∀ j, raw20090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20090step0 = (fun i j => raw20090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20090step0 raw20090; decide +kernel
      have hl : raw20090step0Labels = raw20090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20090 raw20090Labels permutation434 hz
    mixedMoment B raw20090step0 raw20090step0Labels = mixedMoment B raw20090step1 raw20090step1Labels := by
      have hz : ∀ j, raw20090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20090step1 = (fun i j => raw20090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20090step1 raw20090step0; decide +kernel
      have hl : raw20090step1Labels = raw20090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20090step0 raw20090step0Labels permutation56 hz
    _ = mixedMoment B node940 node940Labels := by rfl

theorem canonical20091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20091 raw20091Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20091 raw20091Labels = mixedMoment B raw20091step0 raw20091step0Labels := by
      have hz : ∀ j, raw20091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20091step0 = (fun i j => raw20091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20091step0 raw20091; decide +kernel
      have hl : raw20091step0Labels = raw20091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20091 raw20091Labels permutation346 hz
    mixedMoment B raw20091step0 raw20091step0Labels = mixedMoment B raw20091step1 raw20091step1Labels := by
      have hz : ∀ j, raw20091step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20091step1 = (fun i j => raw20091step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20091step1 raw20091step0; decide +kernel
      have hl : raw20091step1Labels = raw20091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20091step0 raw20091step0Labels permutation56 hz
    _ = mixedMoment B node940 node940Labels := by rfl

theorem canonical20092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20092 raw20092Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw20092 raw20092Labels = mixedMoment B raw20092step0 raw20092step0Labels := by
      have hz : ∀ j, raw20092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20092step0 = (fun i j => raw20092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20092step0 raw20092; decide +kernel
      have hl : raw20092step0Labels = raw20092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092 raw20092Labels permutation434 hz
    mixedMoment B raw20092step0 raw20092step0Labels = mixedMoment B raw20092step1 raw20092step1Labels := by
      have hz : ∀ j, raw20092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20092step1 = (fun i j => raw20092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20092step1 raw20092step0; decide +kernel
      have hl : raw20092step1Labels = raw20092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092step0 raw20092step0Labels permutation80 hz
    mixedMoment B raw20092step1 raw20092step1Labels = mixedMoment B raw20092step2 raw20092step2Labels := by
      have hz : ∀ j, raw20092step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20092step2 = (fun i j => raw20092step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20092step2 raw20092step1; decide +kernel
      have hl : raw20092step2Labels = raw20092step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092step1 raw20092step1Labels permutation14 hz
    mixedMoment B raw20092step2 raw20092step2Labels = mixedMoment B raw20092step3 raw20092step3Labels := by
      have ha : raw20092step3 = (fun i j => raw20092step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20092step3 raw20092step2; decide +kernel
      have hl : raw20092step3Labels = raw20092step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20092step2 raw20092step2Labels permutation3 permutation2
    _ = mixedMoment B node1094 node1094Labels := by rfl

theorem canonical20093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20093 raw20093Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw20093 raw20093Labels = mixedMoment B raw20093step0 raw20093step0Labels := by
      have hz : ∀ j, raw20093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20093step0 = (fun i j => raw20093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20093step0 raw20093; decide +kernel
      have hl : raw20093step0Labels = raw20093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20093 raw20093Labels permutation434 hz
    mixedMoment B raw20093step0 raw20093step0Labels = mixedMoment B raw20093step1 raw20093step1Labels := by
      have hz : ∀ j, raw20093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20093step1 = (fun i j => raw20093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20093step1 raw20093step0; decide +kernel
      have hl : raw20093step1Labels = raw20093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20093step0 raw20093step0Labels permutation80 hz
    mixedMoment B raw20093step1 raw20093step1Labels = mixedMoment B raw20093step2 raw20093step2Labels := by
      have hz : ∀ j, raw20093step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20093step2 = (fun i j => raw20093step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20093step2 raw20093step1; decide +kernel
      have hl : raw20093step2Labels = raw20093step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20093step1 raw20093step1Labels permutation14 hz
    mixedMoment B raw20093step2 raw20093step2Labels = mixedMoment B raw20093step3 raw20093step3Labels := by
      have ha : raw20093step3 = (fun i j => raw20093step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20093step3 raw20093step2; decide +kernel
      have hl : raw20093step3Labels = raw20093step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20093step2 raw20093step2Labels permutation3 permutation4
    mixedMoment B raw20093step3 raw20093step3Labels = mixedMoment B raw20093step4 raw20093step4Labels := by
      have ha : raw20093step4 = -raw20093step3 := by apply Matrix.ext; change ∀ i j, raw20093step4 i j = -(raw20093step3 i j); unfold raw20093step4 raw20093step3; decide +kernel
      have hl : raw20093step4Labels = raw20093step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1747 node1747Labels := by rfl

theorem canonical20094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20094 raw20094Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw20094 raw20094Labels = mixedMoment B raw20094step0 raw20094step0Labels := by
      have hz : ∀ j, raw20094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20094step0 = (fun i j => raw20094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20094step0 raw20094; decide +kernel
      have hl : raw20094step0Labels = raw20094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20094 raw20094Labels permutation434 hz
    mixedMoment B raw20094step0 raw20094step0Labels = mixedMoment B raw20094step1 raw20094step1Labels := by
      have hz : ∀ j, raw20094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20094step1 = (fun i j => raw20094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20094step1 raw20094step0; decide +kernel
      have hl : raw20094step1Labels = raw20094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20094step0 raw20094step0Labels permutation80 hz
    mixedMoment B raw20094step1 raw20094step1Labels = mixedMoment B raw20094step2 raw20094step2Labels := by
      have ha : raw20094step2 = (fun i j => raw20094step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20094step2 raw20094step1; decide +kernel
      have hl : raw20094step2Labels = raw20094step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20094step1 raw20094step1Labels permutation29 permutation2
    _ = mixedMoment B node2064 node2064Labels := by rfl

theorem canonical20095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20095 raw20095Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw20095 raw20095Labels = mixedMoment B raw20095step0 raw20095step0Labels := by
      have hz : ∀ j, raw20095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20095step0 = (fun i j => raw20095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20095step0 raw20095; decide +kernel
      have hl : raw20095step0Labels = raw20095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20095 raw20095Labels permutation434 hz
    mixedMoment B raw20095step0 raw20095step0Labels = mixedMoment B raw20095step1 raw20095step1Labels := by
      have hz : ∀ j, raw20095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20095step1 = (fun i j => raw20095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20095step1 raw20095step0; decide +kernel
      have hl : raw20095step1Labels = raw20095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20095step0 raw20095step0Labels permutation56 hz
    mixedMoment B raw20095step1 raw20095step1Labels = mixedMoment B raw20095step2 raw20095step2Labels := by
      have ha : raw20095step2 = (fun i j => raw20095step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20095step2 raw20095step1; decide +kernel
      have hl : raw20095step2Labels = raw20095step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20095step1 raw20095step1Labels permutation29 permutation2
    _ = mixedMoment B node2064 node2064Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20096 raw20096Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw20096 raw20096Labels = mixedMoment B raw20096step0 raw20096step0Labels := by
      have hz : ∀ j, raw20096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20096step0 = (fun i j => raw20096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20096step0 raw20096; decide +kernel
      have hl : raw20096step0Labels = raw20096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20096 raw20096Labels permutation346 hz
    mixedMoment B raw20096step0 raw20096step0Labels = mixedMoment B raw20096step1 raw20096step1Labels := by
      have hz : ∀ j, raw20096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20096step1 = (fun i j => raw20096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20096step1 raw20096step0; decide +kernel
      have hl : raw20096step1Labels = raw20096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20096step0 raw20096step0Labels permutation56 hz
    mixedMoment B raw20096step1 raw20096step1Labels = mixedMoment B raw20096step2 raw20096step2Labels := by
      have ha : raw20096step2 = (fun i j => raw20096step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20096step2 raw20096step1; decide +kernel
      have hl : raw20096step2Labels = raw20096step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20096step1 raw20096step1Labels permutation29 permutation2
    _ = mixedMoment B node2064 node2064Labels := by rfl

theorem canonical20097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20097 raw20097Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20097 raw20097Labels = mixedMoment B raw20097step0 raw20097step0Labels := by
      have hz : ∀ j, raw20097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20097step0 = (fun i j => raw20097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20097step0 raw20097; decide +kernel
      have hl : raw20097step0Labels = raw20097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097 raw20097Labels permutation434 hz
    mixedMoment B raw20097step0 raw20097step0Labels = mixedMoment B raw20097step1 raw20097step1Labels := by
      have hz : ∀ j, raw20097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20097step1 = (fun i j => raw20097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20097step1 raw20097step0; decide +kernel
      have hl : raw20097step1Labels = raw20097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097step0 raw20097step0Labels permutation80 hz
    mixedMoment B raw20097step1 raw20097step1Labels = mixedMoment B raw20097step2 raw20097step2Labels := by
      have hz : ∀ j, raw20097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20097step2 = (fun i j => raw20097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20097step2 raw20097step1; decide +kernel
      have hl : raw20097step2Labels = raw20097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097step1 raw20097step1Labels permutation14 hz
    mixedMoment B raw20097step2 raw20097step2Labels = mixedMoment B raw20097step3 raw20097step3Labels := by
      have ha : raw20097step3 = (fun i j => raw20097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20097step3 raw20097step2; decide +kernel
      have hl : raw20097step3Labels = raw20097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20097step2 raw20097step2Labels permutation7 permutation2
    _ = mixedMoment B node2289 node2289Labels := by rfl

theorem canonical20098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20098 raw20098Labels = mixedMoment B node1093 node1093Labels := by
  calc
    mixedMoment B raw20098 raw20098Labels = mixedMoment B raw20098step0 raw20098step0Labels := by
      have hz : ∀ j, raw20098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20098step0 = (fun i j => raw20098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20098step0 raw20098; decide +kernel
      have hl : raw20098step0Labels = raw20098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20098 raw20098Labels permutation434 hz
    mixedMoment B raw20098step0 raw20098step0Labels = mixedMoment B raw20098step1 raw20098step1Labels := by
      have hz : ∀ j, raw20098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20098step1 = (fun i j => raw20098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20098step1 raw20098step0; decide +kernel
      have hl : raw20098step1Labels = raw20098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20098step0 raw20098step0Labels permutation80 hz
    mixedMoment B raw20098step1 raw20098step1Labels = mixedMoment B raw20098step2 raw20098step2Labels := by
      have hz : ∀ j, raw20098step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20098step2 = (fun i j => raw20098step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20098step2 raw20098step1; decide +kernel
      have hl : raw20098step2Labels = raw20098step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20098step1 raw20098step1Labels permutation14 hz
    mixedMoment B raw20098step2 raw20098step2Labels = mixedMoment B raw20098step3 raw20098step3Labels := by
      have ha : raw20098step3 = (fun i j => raw20098step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20098step3 raw20098step2; decide +kernel
      have hl : raw20098step3Labels = raw20098step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20098step2 raw20098step2Labels permutation7 permutation2
    _ = mixedMoment B node1093 node1093Labels := by rfl

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

theorem canonical20100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20100 raw20100Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw20100 raw20100Labels = mixedMoment B raw20100step0 raw20100step0Labels := by
      have hz : ∀ j, raw20100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20100step0 = (fun i j => raw20100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20100step0 raw20100; decide +kernel
      have hl : raw20100step0Labels = raw20100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20100 raw20100Labels permutation434 hz
    mixedMoment B raw20100step0 raw20100step0Labels = mixedMoment B raw20100step1 raw20100step1Labels := by
      have hz : ∀ j, raw20100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20100step1 = (fun i j => raw20100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20100step1 raw20100step0; decide +kernel
      have hl : raw20100step1Labels = raw20100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20100step0 raw20100step0Labels permutation80 hz
    mixedMoment B raw20100step1 raw20100step1Labels = mixedMoment B raw20100step2 raw20100step2Labels := by
      have ha : raw20100step2 = (fun i j => raw20100step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20100step2 raw20100step1; decide +kernel
      have hl : raw20100step2Labels = raw20100step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20100step1 raw20100step1Labels permutation12 permutation4
    mixedMoment B raw20100step2 raw20100step2Labels = mixedMoment B raw20100step3 raw20100step3Labels := by
      have ha : raw20100step3 = -raw20100step2 := by apply Matrix.ext; change ∀ i j, raw20100step3 i j = -(raw20100step2 i j); unfold raw20100step3 raw20100step2; decide +kernel
      have hl : raw20100step3Labels = raw20100step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical20101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20101 raw20101Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw20101 raw20101Labels = mixedMoment B raw20101step0 raw20101step0Labels := by
      have hz : ∀ j, raw20101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20101step0 = (fun i j => raw20101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20101step0 raw20101; decide +kernel
      have hl : raw20101step0Labels = raw20101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20101 raw20101Labels permutation434 hz
    mixedMoment B raw20101step0 raw20101step0Labels = mixedMoment B raw20101step1 raw20101step1Labels := by
      have hz : ∀ j, raw20101step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20101step1 = (fun i j => raw20101step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20101step1 raw20101step0; decide +kernel
      have hl : raw20101step1Labels = raw20101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20101step0 raw20101step0Labels permutation56 hz
    mixedMoment B raw20101step1 raw20101step1Labels = mixedMoment B raw20101step2 raw20101step2Labels := by
      have ha : raw20101step2 = (fun i j => raw20101step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20101step2 raw20101step1; decide +kernel
      have hl : raw20101step2Labels = raw20101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20101step1 raw20101step1Labels permutation12 permutation4
    mixedMoment B raw20101step2 raw20101step2Labels = mixedMoment B raw20101step3 raw20101step3Labels := by
      have ha : raw20101step3 = -raw20101step2 := by apply Matrix.ext; change ∀ i j, raw20101step3 i j = -(raw20101step2 i j); unfold raw20101step3 raw20101step2; decide +kernel
      have hl : raw20101step3Labels = raw20101step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical20102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20102 raw20102Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw20102 raw20102Labels = mixedMoment B raw20102step0 raw20102step0Labels := by
      have hz : ∀ j, raw20102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20102step0 = (fun i j => raw20102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20102step0 raw20102; decide +kernel
      have hl : raw20102step0Labels = raw20102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20102 raw20102Labels permutation346 hz
    mixedMoment B raw20102step0 raw20102step0Labels = mixedMoment B raw20102step1 raw20102step1Labels := by
      have hz : ∀ j, raw20102step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20102step1 = (fun i j => raw20102step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20102step1 raw20102step0; decide +kernel
      have hl : raw20102step1Labels = raw20102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20102step0 raw20102step0Labels permutation56 hz
    mixedMoment B raw20102step1 raw20102step1Labels = mixedMoment B raw20102step2 raw20102step2Labels := by
      have ha : raw20102step2 = (fun i j => raw20102step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20102step2 raw20102step1; decide +kernel
      have hl : raw20102step2Labels = raw20102step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20102step1 raw20102step1Labels permutation12 permutation4
    mixedMoment B raw20102step2 raw20102step2Labels = mixedMoment B raw20102step3 raw20102step3Labels := by
      have ha : raw20102step3 = -raw20102step2 := by apply Matrix.ext; change ∀ i j, raw20102step3 i j = -(raw20102step2 i j); unfold raw20102step3 raw20102step2; decide +kernel
      have hl : raw20102step3Labels = raw20102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical20103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20103 raw20103Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw20103 raw20103Labels = mixedMoment B raw20103step0 raw20103step0Labels := by
      have hz : ∀ j, raw20103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20103step0 = (fun i j => raw20103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20103step0 raw20103; decide +kernel
      have hl : raw20103step0Labels = raw20103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103 raw20103Labels permutation434 hz
    mixedMoment B raw20103step0 raw20103step0Labels = mixedMoment B raw20103step1 raw20103step1Labels := by
      have hz : ∀ j, raw20103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20103step1 = (fun i j => raw20103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20103step1 raw20103step0; decide +kernel
      have hl : raw20103step1Labels = raw20103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103step0 raw20103step0Labels permutation80 hz
    mixedMoment B raw20103step1 raw20103step1Labels = mixedMoment B raw20103step2 raw20103step2Labels := by
      have hz : ∀ j, raw20103step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20103step2 = (fun i j => raw20103step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20103step2 raw20103step1; decide +kernel
      have hl : raw20103step2Labels = raw20103step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103step1 raw20103step1Labels permutation14 hz
    mixedMoment B raw20103step2 raw20103step2Labels = mixedMoment B raw20103step3 raw20103step3Labels := by
      have ha : raw20103step3 = (fun i j => raw20103step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20103step3 raw20103step2; decide +kernel
      have hl : raw20103step3Labels = raw20103step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20103step2 raw20103step2Labels permutation3 permutation4
    mixedMoment B raw20103step3 raw20103step3Labels = mixedMoment B raw20103step4 raw20103step4Labels := by
      have ha : raw20103step4 = -raw20103step3 := by apply Matrix.ext; change ∀ i j, raw20103step4 i j = -(raw20103step3 i j); unfold raw20103step4 raw20103step3; decide +kernel
      have hl : raw20103step4Labels = raw20103step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1756 node1756Labels := by rfl

theorem canonical20104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20104 raw20104Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw20104 raw20104Labels = mixedMoment B raw20104step0 raw20104step0Labels := by
      have hz : ∀ j, raw20104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20104step0 = (fun i j => raw20104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20104step0 raw20104; decide +kernel
      have hl : raw20104step0Labels = raw20104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20104 raw20104Labels permutation434 hz
    mixedMoment B raw20104step0 raw20104step0Labels = mixedMoment B raw20104step1 raw20104step1Labels := by
      have hz : ∀ j, raw20104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20104step1 = (fun i j => raw20104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20104step1 raw20104step0; decide +kernel
      have hl : raw20104step1Labels = raw20104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20104step0 raw20104step0Labels permutation80 hz
    mixedMoment B raw20104step1 raw20104step1Labels = mixedMoment B raw20104step2 raw20104step2Labels := by
      have hz : ∀ j, raw20104step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20104step2 = (fun i j => raw20104step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20104step2 raw20104step1; decide +kernel
      have hl : raw20104step2Labels = raw20104step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20104step1 raw20104step1Labels permutation14 hz
    mixedMoment B raw20104step2 raw20104step2Labels = mixedMoment B raw20104step3 raw20104step3Labels := by
      have ha : raw20104step3 = (fun i j => raw20104step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20104step3 raw20104step2; decide +kernel
      have hl : raw20104step3Labels = raw20104step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20104step2 raw20104step2Labels permutation3 permutation4
    mixedMoment B raw20104step3 raw20104step3Labels = mixedMoment B raw20104step4 raw20104step4Labels := by
      have ha : raw20104step4 = -raw20104step3 := by apply Matrix.ext; change ∀ i j, raw20104step4 i j = -(raw20104step3 i j); unfold raw20104step4 raw20104step3; decide +kernel
      have hl : raw20104step4Labels = raw20104step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node860 node860Labels := by rfl

theorem canonical20105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20105 raw20105Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20105 raw20105Labels = mixedMoment B raw20105step0 raw20105step0Labels := by
      have hz : ∀ j, raw20105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20105step0 = (fun i j => raw20105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20105step0 raw20105; decide +kernel
      have hl : raw20105step0Labels = raw20105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20105 raw20105Labels permutation434 hz
    mixedMoment B raw20105step0 raw20105step0Labels = mixedMoment B raw20105step1 raw20105step1Labels := by
      have hz : ∀ j, raw20105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20105step1 = (fun i j => raw20105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20105step1 raw20105step0; decide +kernel
      have hl : raw20105step1Labels = raw20105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20105step0 raw20105step0Labels permutation80 hz
    mixedMoment B raw20105step1 raw20105step1Labels = mixedMoment B raw20105step2 raw20105step2Labels := by
      have ha : raw20105step2 = (fun i j => raw20105step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20105step2 raw20105step1; decide +kernel
      have hl : raw20105step2Labels = raw20105step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20105step1 raw20105step1Labels permutation9 permutation4
    mixedMoment B raw20105step2 raw20105step2Labels = mixedMoment B raw20105step3 raw20105step3Labels := by
      have ha : raw20105step3 = -raw20105step2 := by apply Matrix.ext; change ∀ i j, raw20105step3 i j = -(raw20105step2 i j); unfold raw20105step3 raw20105step2; decide +kernel
      have hl : raw20105step3Labels = raw20105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

theorem canonical20106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20106 raw20106Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20106 raw20106Labels = mixedMoment B raw20106step0 raw20106step0Labels := by
      have hz : ∀ j, raw20106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20106step0 = (fun i j => raw20106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20106step0 raw20106; decide +kernel
      have hl : raw20106step0Labels = raw20106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20106 raw20106Labels permutation434 hz
    mixedMoment B raw20106step0 raw20106step0Labels = mixedMoment B raw20106step1 raw20106step1Labels := by
      have hz : ∀ j, raw20106step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20106step1 = (fun i j => raw20106step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20106step1 raw20106step0; decide +kernel
      have hl : raw20106step1Labels = raw20106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20106step0 raw20106step0Labels permutation56 hz
    mixedMoment B raw20106step1 raw20106step1Labels = mixedMoment B raw20106step2 raw20106step2Labels := by
      have ha : raw20106step2 = (fun i j => raw20106step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20106step2 raw20106step1; decide +kernel
      have hl : raw20106step2Labels = raw20106step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20106step1 raw20106step1Labels permutation9 permutation4
    mixedMoment B raw20106step2 raw20106step2Labels = mixedMoment B raw20106step3 raw20106step3Labels := by
      have ha : raw20106step3 = -raw20106step2 := by apply Matrix.ext; change ∀ i j, raw20106step3 i j = -(raw20106step2 i j); unfold raw20106step3 raw20106step2; decide +kernel
      have hl : raw20106step3Labels = raw20106step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

theorem canonical20107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20107 raw20107Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20107 raw20107Labels = mixedMoment B raw20107step0 raw20107step0Labels := by
      have hz : ∀ j, raw20107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20107step0 = (fun i j => raw20107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20107step0 raw20107; decide +kernel
      have hl : raw20107step0Labels = raw20107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20107 raw20107Labels permutation346 hz
    mixedMoment B raw20107step0 raw20107step0Labels = mixedMoment B raw20107step1 raw20107step1Labels := by
      have hz : ∀ j, raw20107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20107step1 = (fun i j => raw20107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20107step1 raw20107step0; decide +kernel
      have hl : raw20107step1Labels = raw20107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20107step0 raw20107step0Labels permutation56 hz
    mixedMoment B raw20107step1 raw20107step1Labels = mixedMoment B raw20107step2 raw20107step2Labels := by
      have ha : raw20107step2 = (fun i j => raw20107step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20107step2 raw20107step1; decide +kernel
      have hl : raw20107step2Labels = raw20107step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20107step1 raw20107step1Labels permutation9 permutation4
    mixedMoment B raw20107step2 raw20107step2Labels = mixedMoment B raw20107step3 raw20107step3Labels := by
      have ha : raw20107step3 = -raw20107step2 := by apply Matrix.ext; change ∀ i j, raw20107step3 i j = -(raw20107step2 i j); unfold raw20107step3 raw20107step2; decide +kernel
      have hl : raw20107step3Labels = raw20107step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

theorem canonical20108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20108 raw20108Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20108 raw20108Labels = mixedMoment B raw20108step0 raw20108step0Labels := by
      have hz : ∀ j, raw20108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20108step0 = (fun i j => raw20108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20108step0 raw20108; decide +kernel
      have hl : raw20108step0Labels = raw20108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20108 raw20108Labels permutation346 hz
    mixedMoment B raw20108step0 raw20108step0Labels = mixedMoment B raw20108step1 raw20108step1Labels := by
      have hz : ∀ j, raw20108step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20108step1 = (fun i j => raw20108step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20108step1 raw20108step0; decide +kernel
      have hl : raw20108step1Labels = raw20108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20108step0 raw20108step0Labels permutation56 hz
    _ = mixedMoment B node612 node612Labels := by rfl

theorem canonical20109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20109 raw20109Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw20109 raw20109Labels = mixedMoment B raw20109step0 raw20109step0Labels := by
      have hz : ∀ j, raw20109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20109step0 = (fun i j => raw20109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20109step0 raw20109; decide +kernel
      have hl : raw20109step0Labels = raw20109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20109 raw20109Labels permutation346 hz
    _ = mixedMoment B node931 node931Labels := by rfl

theorem canonical20110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20110 raw20110Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw20110 raw20110Labels = mixedMoment B raw20110step0 raw20110step0Labels := by
      have hz : ∀ j, raw20110 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20110step0 = (fun i j => raw20110 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20110step0 raw20110; decide +kernel
      have hl : raw20110step0Labels = raw20110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20110 raw20110Labels permutation265 hz
    _ = mixedMoment B node931 node931Labels := by rfl

theorem canonical20111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20111 raw20111Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw20111 raw20111Labels = mixedMoment B raw20111step0 raw20111step0Labels := by
      have hz : ∀ j, raw20111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20111step0 = (fun i j => raw20111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20111step0 raw20111; decide +kernel
      have hl : raw20111step0Labels = raw20111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20111 raw20111Labels permutation346 hz
    mixedMoment B raw20111step0 raw20111step0Labels = mixedMoment B raw20111step1 raw20111step1Labels := by
      have hz : ∀ j, raw20111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20111step1 = (fun i j => raw20111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20111step1 raw20111step0; decide +kernel
      have hl : raw20111step1Labels = raw20111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20111step0 raw20111step0Labels permutation56 hz
    _ = mixedMoment B node1087 node1087Labels := by rfl

theorem canonical20112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20112 raw20112Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw20112 raw20112Labels = mixedMoment B raw20112step0 raw20112step0Labels := by
      have hz : ∀ j, raw20112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20112step0 = (fun i j => raw20112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20112step0 raw20112; decide +kernel
      have hl : raw20112step0Labels = raw20112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20112 raw20112Labels permutation346 hz
    mixedMoment B raw20112step0 raw20112step0Labels = mixedMoment B raw20112step1 raw20112step1Labels := by
      have hz : ∀ j, raw20112step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20112step1 = (fun i j => raw20112step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20112step1 raw20112step0; decide +kernel
      have hl : raw20112step1Labels = raw20112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20112step0 raw20112step0Labels permutation56 hz
    _ = mixedMoment B node590 node590Labels := by rfl

theorem canonical20113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20113 raw20113Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw20113 raw20113Labels = mixedMoment B raw20113step0 raw20113step0Labels := by
      have hz : ∀ j, raw20113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20113step0 = (fun i j => raw20113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20113step0 raw20113; decide +kernel
      have hl : raw20113step0Labels = raw20113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20113 raw20113Labels permutation346 hz
    _ = mixedMoment B node914 node914Labels := by rfl

theorem canonical20114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20114 raw20114Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw20114 raw20114Labels = mixedMoment B raw20114step0 raw20114step0Labels := by
      have hz : ∀ j, raw20114 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20114step0 = (fun i j => raw20114 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20114step0 raw20114; decide +kernel
      have hl : raw20114step0Labels = raw20114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20114 raw20114Labels permutation265 hz
    _ = mixedMoment B node914 node914Labels := by rfl

theorem canonical20115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20115 raw20115Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw20115 raw20115Labels = mixedMoment B raw20115step0 raw20115step0Labels := by
      have hz : ∀ j, raw20115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20115step0 = (fun i j => raw20115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20115step0 raw20115; decide +kernel
      have hl : raw20115step0Labels = raw20115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20115 raw20115Labels permutation346 hz
    mixedMoment B raw20115step0 raw20115step0Labels = mixedMoment B raw20115step1 raw20115step1Labels := by
      have hz : ∀ j, raw20115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20115step1 = (fun i j => raw20115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20115step1 raw20115step0; decide +kernel
      have hl : raw20115step1Labels = raw20115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20115step0 raw20115step0Labels permutation56 hz
    _ = mixedMoment B node954 node954Labels := by rfl

theorem canonical20116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20116 raw20116Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw20116 raw20116Labels = mixedMoment B raw20116step0 raw20116step0Labels := by
      have hz : ∀ j, raw20116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20116step0 = (fun i j => raw20116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20116step0 raw20116; decide +kernel
      have hl : raw20116step0Labels = raw20116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20116 raw20116Labels permutation346 hz
    mixedMoment B raw20116step0 raw20116step0Labels = mixedMoment B raw20116step1 raw20116step1Labels := by
      have hz : ∀ j, raw20116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20116step1 = (fun i j => raw20116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20116step1 raw20116step0; decide +kernel
      have hl : raw20116step1Labels = raw20116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20116step0 raw20116step0Labels permutation56 hz
    mixedMoment B raw20116step1 raw20116step1Labels = mixedMoment B raw20116step2 raw20116step2Labels := by
      have ha : raw20116step2 = (fun i j => raw20116step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20116step2 raw20116step1; decide +kernel
      have hl : raw20116step2Labels = raw20116step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20116step1 raw20116step1Labels permutation9 permutation2
    _ = mixedMoment B node1049 node1049Labels := by rfl

theorem canonical20117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20117 raw20117Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw20117 raw20117Labels = mixedMoment B raw20117step0 raw20117step0Labels := by
      have hz : ∀ j, raw20117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20117step0 = (fun i j => raw20117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20117step0 raw20117; decide +kernel
      have hl : raw20117step0Labels = raw20117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20117 raw20117Labels permutation346 hz
    mixedMoment B raw20117step0 raw20117step0Labels = mixedMoment B raw20117step1 raw20117step1Labels := by
      have ha : raw20117step1 = (fun i j => raw20117step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20117step1 raw20117step0; decide +kernel
      have hl : raw20117step1Labels = raw20117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20117step0 raw20117step0Labels permutation40 permutation2
    _ = mixedMoment B node1336 node1336Labels := by rfl

theorem canonical20118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20118 raw20118Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw20118 raw20118Labels = mixedMoment B raw20118step0 raw20118step0Labels := by
      have hz : ∀ j, raw20118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20118step0 = (fun i j => raw20118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20118step0 raw20118; decide +kernel
      have hl : raw20118step0Labels = raw20118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20118 raw20118Labels permutation265 hz
    mixedMoment B raw20118step0 raw20118step0Labels = mixedMoment B raw20118step1 raw20118step1Labels := by
      have ha : raw20118step1 = (fun i j => raw20118step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20118step1 raw20118step0; decide +kernel
      have hl : raw20118step1Labels = raw20118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20118step0 raw20118step0Labels permutation40 permutation2
    _ = mixedMoment B node1336 node1336Labels := by rfl

theorem canonical20119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20119 raw20119Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw20119 raw20119Labels = mixedMoment B raw20119step0 raw20119step0Labels := by
      have hz : ∀ j, raw20119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20119step0 = (fun i j => raw20119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20119step0 raw20119; decide +kernel
      have hl : raw20119step0Labels = raw20119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20119 raw20119Labels permutation346 hz
    mixedMoment B raw20119step0 raw20119step0Labels = mixedMoment B raw20119step1 raw20119step1Labels := by
      have hz : ∀ j, raw20119step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20119step1 = (fun i j => raw20119step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20119step1 raw20119step0; decide +kernel
      have hl : raw20119step1Labels = raw20119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20119step0 raw20119step0Labels permutation56 hz
    _ = mixedMoment B node1348 node1348Labels := by rfl

theorem canonical20120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20120 raw20120Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw20120 raw20120Labels = mixedMoment B raw20120step0 raw20120step0Labels := by
      have hz : ∀ j, raw20120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20120step0 = (fun i j => raw20120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20120step0 raw20120; decide +kernel
      have hl : raw20120step0Labels = raw20120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20120 raw20120Labels permutation346 hz
    mixedMoment B raw20120step0 raw20120step0Labels = mixedMoment B raw20120step1 raw20120step1Labels := by
      have hz : ∀ j, raw20120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20120step1 = (fun i j => raw20120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20120step1 raw20120step0; decide +kernel
      have hl : raw20120step1Labels = raw20120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20120step0 raw20120step0Labels permutation56 hz
    mixedMoment B raw20120step1 raw20120step1Labels = mixedMoment B raw20120step2 raw20120step2Labels := by
      have ha : raw20120step2 = (fun i j => raw20120step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20120step2 raw20120step1; decide +kernel
      have hl : raw20120step2Labels = raw20120step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20120step1 raw20120step1Labels permutation31 permutation2
    mixedMoment B raw20120step2 raw20120step2Labels = mixedMoment B raw20120step3 raw20120step3Labels := by
      have ha : raw20120step3 = -raw20120step2 := by apply Matrix.ext; change ∀ i j, raw20120step3 i j = -(raw20120step2 i j); unfold raw20120step3 raw20120step2; decide +kernel
      have hl : raw20120step3Labels = raw20120step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node951 node951Labels := by rfl

theorem canonical20121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20121 raw20121Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20121 raw20121Labels = mixedMoment B raw20121step0 raw20121step0Labels := by
      have hz : ∀ j, raw20121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20121step0 = (fun i j => raw20121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20121step0 raw20121; decide +kernel
      have hl : raw20121step0Labels = raw20121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20121 raw20121Labels permutation346 hz
    mixedMoment B raw20121step0 raw20121step0Labels = mixedMoment B raw20121step1 raw20121step1Labels := by
      have ha : raw20121step1 = (fun i j => raw20121step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20121step1 raw20121step0; decide +kernel
      have hl : raw20121step1Labels = raw20121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20121step0 raw20121step0Labels permutation139 permutation2
    _ = mixedMoment B node2045 node2045Labels := by rfl

theorem canonical20122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20122 raw20122Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20122 raw20122Labels = mixedMoment B raw20122step0 raw20122step0Labels := by
      have hz : ∀ j, raw20122 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20122step0 = (fun i j => raw20122 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20122step0 raw20122; decide +kernel
      have hl : raw20122step0Labels = raw20122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20122 raw20122Labels permutation265 hz
    mixedMoment B raw20122step0 raw20122step0Labels = mixedMoment B raw20122step1 raw20122step1Labels := by
      have ha : raw20122step1 = (fun i j => raw20122step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20122step1 raw20122step0; decide +kernel
      have hl : raw20122step1Labels = raw20122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20122step0 raw20122step0Labels permutation139 permutation2
    _ = mixedMoment B node2045 node2045Labels := by rfl

theorem canonical20123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20123 raw20123Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20123 raw20123Labels = mixedMoment B raw20123step0 raw20123step0Labels := by
      have hz : ∀ j, raw20123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20123step0 = (fun i j => raw20123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20123step0 raw20123; decide +kernel
      have hl : raw20123step0Labels = raw20123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20123 raw20123Labels permutation346 hz
    mixedMoment B raw20123step0 raw20123step0Labels = mixedMoment B raw20123step1 raw20123step1Labels := by
      have hz : ∀ j, raw20123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20123step1 = (fun i j => raw20123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20123step1 raw20123step0; decide +kernel
      have hl : raw20123step1Labels = raw20123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20123step0 raw20123step0Labels permutation56 hz
    mixedMoment B raw20123step1 raw20123step1Labels = mixedMoment B raw20123step2 raw20123step2Labels := by
      have ha : raw20123step2 = (fun i j => raw20123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20123step2 raw20123step1; decide +kernel
      have hl : raw20123step2Labels = raw20123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20123step1 raw20123step1Labels permutation31 permutation2
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical20124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20124 raw20124Labels = mixedMoment B node1072 node1072Labels := by
  calc
    mixedMoment B raw20124 raw20124Labels = mixedMoment B raw20124step0 raw20124step0Labels := by
      have hz : ∀ j, raw20124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20124step0 = (fun i j => raw20124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20124step0 raw20124; decide +kernel
      have hl : raw20124step0Labels = raw20124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20124 raw20124Labels permutation346 hz
    mixedMoment B raw20124step0 raw20124step0Labels = mixedMoment B raw20124step1 raw20124step1Labels := by
      have hz : ∀ j, raw20124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20124step1 = (fun i j => raw20124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20124step1 raw20124step0; decide +kernel
      have hl : raw20124step1Labels = raw20124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20124step0 raw20124step0Labels permutation56 hz
    mixedMoment B raw20124step1 raw20124step1Labels = mixedMoment B raw20124step2 raw20124step2Labels := by
      have ha : raw20124step2 = (fun i j => raw20124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20124step2 raw20124step1; decide +kernel
      have hl : raw20124step2Labels = raw20124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20124step1 raw20124step1Labels permutation31 permutation2
    _ = mixedMoment B node1072 node1072Labels := by rfl

theorem canonical20129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20129 raw20129Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw20129 raw20129Labels = mixedMoment B raw20129step0 raw20129step0Labels := by
      have hz : ∀ j, raw20129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20129step0 = (fun i j => raw20129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20129step0 raw20129; decide +kernel
      have hl : raw20129step0Labels = raw20129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20129 raw20129Labels permutation346 hz
    mixedMoment B raw20129step0 raw20129step0Labels = mixedMoment B raw20129step1 raw20129step1Labels := by
      have hz : ∀ j, raw20129step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20129step1 = (fun i j => raw20129step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20129step1 raw20129step0; decide +kernel
      have hl : raw20129step1Labels = raw20129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20129step0 raw20129step0Labels permutation56 hz
    mixedMoment B raw20129step1 raw20129step1Labels = mixedMoment B raw20129step2 raw20129step2Labels := by
      have ha : raw20129step2 = (fun i j => raw20129step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20129step2 raw20129step1; decide +kernel
      have hl : raw20129step2Labels = raw20129step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20129step1 raw20129step1Labels permutation9 permutation4
    mixedMoment B raw20129step2 raw20129step2Labels = mixedMoment B raw20129step3 raw20129step3Labels := by
      have ha : raw20129step3 = -raw20129step2 := by apply Matrix.ext; change ∀ i j, raw20129step3 i j = -(raw20129step2 i j); unfold raw20129step3 raw20129step2; decide +kernel
      have hl : raw20129step3Labels = raw20129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node853 node853Labels := by rfl

theorem canonical20130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20130 raw20130Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw20130 raw20130Labels = mixedMoment B raw20130step0 raw20130step0Labels := by
      have hz : ∀ j, raw20130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20130step0 = (fun i j => raw20130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20130step0 raw20130; decide +kernel
      have hl : raw20130step0Labels = raw20130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20130 raw20130Labels permutation346 hz
    mixedMoment B raw20130step0 raw20130step0Labels = mixedMoment B raw20130step1 raw20130step1Labels := by
      have ha : raw20130step1 = (fun i j => raw20130step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20130step1 raw20130step0; decide +kernel
      have hl : raw20130step1Labels = raw20130step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20130step0 raw20130step0Labels permutation50 permutation4
    mixedMoment B raw20130step1 raw20130step1Labels = mixedMoment B raw20130step2 raw20130step2Labels := by
      have ha : raw20130step2 = -raw20130step1 := by apply Matrix.ext; change ∀ i j, raw20130step2 i j = -(raw20130step1 i j); unfold raw20130step2 raw20130step1; decide +kernel
      have hl : raw20130step2Labels = raw20130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical20131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20131 raw20131Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw20131 raw20131Labels = mixedMoment B raw20131step0 raw20131step0Labels := by
      have hz : ∀ j, raw20131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20131step0 = (fun i j => raw20131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20131step0 raw20131; decide +kernel
      have hl : raw20131step0Labels = raw20131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20131 raw20131Labels permutation265 hz
    mixedMoment B raw20131step0 raw20131step0Labels = mixedMoment B raw20131step1 raw20131step1Labels := by
      have ha : raw20131step1 = (fun i j => raw20131step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20131step1 raw20131step0; decide +kernel
      have hl : raw20131step1Labels = raw20131step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20131step0 raw20131step0Labels permutation50 permutation4
    mixedMoment B raw20131step1 raw20131step1Labels = mixedMoment B raw20131step2 raw20131step2Labels := by
      have ha : raw20131step2 = -raw20131step1 := by apply Matrix.ext; change ∀ i j, raw20131step2 i j = -(raw20131step1 i j); unfold raw20131step2 raw20131step1; decide +kernel
      have hl : raw20131step2Labels = raw20131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical20132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20132 raw20132Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw20132 raw20132Labels = mixedMoment B raw20132step0 raw20132step0Labels := by
      have hz : ∀ j, raw20132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20132step0 = (fun i j => raw20132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20132step0 raw20132; decide +kernel
      have hl : raw20132step0Labels = raw20132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20132 raw20132Labels permutation346 hz
    mixedMoment B raw20132step0 raw20132step0Labels = mixedMoment B raw20132step1 raw20132step1Labels := by
      have hz : ∀ j, raw20132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20132step1 = (fun i j => raw20132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20132step1 raw20132step0; decide +kernel
      have hl : raw20132step1Labels = raw20132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20132step0 raw20132step0Labels permutation56 hz
    mixedMoment B raw20132step1 raw20132step1Labels = mixedMoment B raw20132step2 raw20132step2Labels := by
      have ha : raw20132step2 = (fun i j => raw20132step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20132step2 raw20132step1; decide +kernel
      have hl : raw20132step2Labels = raw20132step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20132step1 raw20132step1Labels permutation13 permutation4
    mixedMoment B raw20132step2 raw20132step2Labels = mixedMoment B raw20132step3 raw20132step3Labels := by
      have ha : raw20132step3 = -raw20132step2 := by apply Matrix.ext; change ∀ i j, raw20132step3 i j = -(raw20132step2 i j); unfold raw20132step3 raw20132step2; decide +kernel
      have hl : raw20132step3Labels = raw20132step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical20133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20133 raw20133Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20133 raw20133Labels = mixedMoment B raw20133step0 raw20133step0Labels := by
      have hz : ∀ j, raw20133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20133step0 = (fun i j => raw20133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20133step0 raw20133; decide +kernel
      have hl : raw20133step0Labels = raw20133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20133 raw20133Labels permutation346 hz
    mixedMoment B raw20133step0 raw20133step0Labels = mixedMoment B raw20133step1 raw20133step1Labels := by
      have hz : ∀ j, raw20133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20133step1 = (fun i j => raw20133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20133step1 raw20133step0; decide +kernel
      have hl : raw20133step1Labels = raw20133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20133step0 raw20133step0Labels permutation56 hz
    mixedMoment B raw20133step1 raw20133step1Labels = mixedMoment B raw20133step2 raw20133step2Labels := by
      have ha : raw20133step2 = (fun i j => raw20133step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20133step2 raw20133step1; decide +kernel
      have hl : raw20133step2Labels = raw20133step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20133step1 raw20133step1Labels permutation8 permutation4
    mixedMoment B raw20133step2 raw20133step2Labels = mixedMoment B raw20133step3 raw20133step3Labels := by
      have ha : raw20133step3 = -raw20133step2 := by apply Matrix.ext; change ∀ i j, raw20133step3 i j = -(raw20133step2 i j); unfold raw20133step3 raw20133step2; decide +kernel
      have hl : raw20133step3Labels = raw20133step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical20134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20134 raw20134Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20134 raw20134Labels = mixedMoment B raw20134step0 raw20134step0Labels := by
      have hz : ∀ j, raw20134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20134step0 = (fun i j => raw20134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20134step0 raw20134; decide +kernel
      have hl : raw20134step0Labels = raw20134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20134 raw20134Labels permutation346 hz
    mixedMoment B raw20134step0 raw20134step0Labels = mixedMoment B raw20134step1 raw20134step1Labels := by
      have ha : raw20134step1 = (fun i j => raw20134step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20134step1 raw20134step0; decide +kernel
      have hl : raw20134step1Labels = raw20134step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20134step0 raw20134step0Labels permutation33 permutation4
    mixedMoment B raw20134step1 raw20134step1Labels = mixedMoment B raw20134step2 raw20134step2Labels := by
      have ha : raw20134step2 = -raw20134step1 := by apply Matrix.ext; change ∀ i j, raw20134step2 i j = -(raw20134step1 i j); unfold raw20134step2 raw20134step1; decide +kernel
      have hl : raw20134step2Labels = raw20134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

theorem canonical20135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20135 raw20135Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20135 raw20135Labels = mixedMoment B raw20135step0 raw20135step0Labels := by
      have hz : ∀ j, raw20135 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20135step0 = (fun i j => raw20135 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20135step0 raw20135; decide +kernel
      have hl : raw20135step0Labels = raw20135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20135 raw20135Labels permutation265 hz
    mixedMoment B raw20135step0 raw20135step0Labels = mixedMoment B raw20135step1 raw20135step1Labels := by
      have ha : raw20135step1 = (fun i j => raw20135step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20135step1 raw20135step0; decide +kernel
      have hl : raw20135step1Labels = raw20135step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20135step0 raw20135step0Labels permutation33 permutation4
    mixedMoment B raw20135step1 raw20135step1Labels = mixedMoment B raw20135step2 raw20135step2Labels := by
      have ha : raw20135step2 = -raw20135step1 := by apply Matrix.ext; change ∀ i j, raw20135step2 i j = -(raw20135step1 i j); unfold raw20135step2 raw20135step1; decide +kernel
      have hl : raw20135step2Labels = raw20135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

theorem canonical20136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20136 raw20136Labels = mixedMoment B node606 node606Labels := by
  calc
    mixedMoment B raw20136 raw20136Labels = mixedMoment B raw20136step0 raw20136step0Labels := by
      have hz : ∀ j, raw20136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20136step0 = (fun i j => raw20136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20136step0 raw20136; decide +kernel
      have hl : raw20136step0Labels = raw20136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20136 raw20136Labels permutation346 hz
    mixedMoment B raw20136step0 raw20136step0Labels = mixedMoment B raw20136step1 raw20136step1Labels := by
      have hz : ∀ j, raw20136step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20136step1 = (fun i j => raw20136step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20136step1 raw20136step0; decide +kernel
      have hl : raw20136step1Labels = raw20136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20136step0 raw20136step0Labels permutation56 hz
    mixedMoment B raw20136step1 raw20136step1Labels = mixedMoment B raw20136step2 raw20136step2Labels := by
      have ha : raw20136step2 = (fun i j => raw20136step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20136step2 raw20136step1; decide +kernel
      have hl : raw20136step2Labels = raw20136step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20136step1 raw20136step1Labels permutation10 permutation2
    _ = mixedMoment B node606 node606Labels := by rfl

theorem canonical20137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20137 raw20137Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw20137 raw20137Labels = mixedMoment B raw20137step0 raw20137step0Labels := by
      have hz : ∀ j, raw20137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20137step0 = (fun i j => raw20137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20137step0 raw20137; decide +kernel
      have hl : raw20137step0Labels = raw20137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20137 raw20137Labels permutation346 hz
    mixedMoment B raw20137step0 raw20137step0Labels = mixedMoment B raw20137step1 raw20137step1Labels := by
      have ha : raw20137step1 = (fun i j => raw20137step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20137step1 raw20137step0; decide +kernel
      have hl : raw20137step1Labels = raw20137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20137step0 raw20137step0Labels permutation34 permutation2
    _ = mixedMoment B node925 node925Labels := by rfl

theorem canonical20138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20138 raw20138Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw20138 raw20138Labels = mixedMoment B raw20138step0 raw20138step0Labels := by
      have hz : ∀ j, raw20138 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20138step0 = (fun i j => raw20138 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20138step0 raw20138; decide +kernel
      have hl : raw20138step0Labels = raw20138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20138 raw20138Labels permutation265 hz
    mixedMoment B raw20138step0 raw20138step0Labels = mixedMoment B raw20138step1 raw20138step1Labels := by
      have ha : raw20138step1 = (fun i j => raw20138step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20138step1 raw20138step0; decide +kernel
      have hl : raw20138step1Labels = raw20138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20138step0 raw20138step0Labels permutation34 permutation2
    _ = mixedMoment B node925 node925Labels := by rfl

theorem canonical20139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20139 raw20139Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw20139 raw20139Labels = mixedMoment B raw20139step0 raw20139step0Labels := by
      have hz : ∀ j, raw20139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20139step0 = (fun i j => raw20139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20139step0 raw20139; decide +kernel
      have hl : raw20139step0Labels = raw20139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20139 raw20139Labels permutation346 hz
    mixedMoment B raw20139step0 raw20139step0Labels = mixedMoment B raw20139step1 raw20139step1Labels := by
      have hz : ∀ j, raw20139step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20139step1 = (fun i j => raw20139step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20139step1 raw20139step0; decide +kernel
      have hl : raw20139step1Labels = raw20139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20139step0 raw20139step0Labels permutation56 hz
    _ = mixedMoment B node1059 node1059Labels := by rfl

theorem canonical20140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20140 raw20140Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw20140 raw20140Labels = mixedMoment B raw20140step0 raw20140step0Labels := by
      have hz : ∀ j, raw20140 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20140step0 = (fun i j => raw20140 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20140step0 raw20140; decide +kernel
      have hl : raw20140step0Labels = raw20140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20140 raw20140Labels permutation520 hz
    mixedMoment B raw20140step0 raw20140step0Labels = mixedMoment B raw20140step1 raw20140step1Labels := by
      have hz : ∀ j, raw20140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20140step1 = (fun i j => raw20140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20140step1 raw20140step0; decide +kernel
      have hl : raw20140step1Labels = raw20140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20140step0 raw20140step0Labels permutation80 hz
    mixedMoment B raw20140step1 raw20140step1Labels = mixedMoment B raw20140step2 raw20140step2Labels := by
      have hz : ∀ j, raw20140step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20140step2 = (fun i j => raw20140step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20140step2 raw20140step1; decide +kernel
      have hl : raw20140step2Labels = raw20140step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20140step1 raw20140step1Labels permutation14 hz
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical20141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20141 raw20141Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw20141 raw20141Labels = mixedMoment B raw20141step0 raw20141step0Labels := by
      have hz : ∀ j, raw20141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20141step0 = (fun i j => raw20141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20141step0 raw20141; decide +kernel
      have hl : raw20141step0Labels = raw20141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20141 raw20141Labels permutation346 hz
    mixedMoment B raw20141step0 raw20141step0Labels = mixedMoment B raw20141step1 raw20141step1Labels := by
      have hz : ∀ j, raw20141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20141step1 = (fun i j => raw20141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20141step1 raw20141step0; decide +kernel
      have hl : raw20141step1Labels = raw20141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20141step0 raw20141step0Labels permutation56 hz
    mixedMoment B raw20141step1 raw20141step1Labels = mixedMoment B raw20141step2 raw20141step2Labels := by
      have ha : raw20141step2 = (fun i j => raw20141step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20141step2 raw20141step1; decide +kernel
      have hl : raw20141step2Labels = raw20141step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20141step1 raw20141step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical20142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20142 raw20142Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20142 raw20142Labels = mixedMoment B raw20142step0 raw20142step0Labels := by
      have hz : ∀ j, raw20142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20142step0 = (fun i j => raw20142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20142step0 raw20142; decide +kernel
      have hl : raw20142step0Labels = raw20142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142 raw20142Labels permutation520 hz
    mixedMoment B raw20142step0 raw20142step0Labels = mixedMoment B raw20142step1 raw20142step1Labels := by
      have hz : ∀ j, raw20142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20142step1 = (fun i j => raw20142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20142step1 raw20142step0; decide +kernel
      have hl : raw20142step1Labels = raw20142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step0 raw20142step0Labels permutation80 hz
    mixedMoment B raw20142step1 raw20142step1Labels = mixedMoment B raw20142step2 raw20142step2Labels := by
      have hz : ∀ j, raw20142step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20142step2 = (fun i j => raw20142step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20142step2 raw20142step1; decide +kernel
      have hl : raw20142step2Labels = raw20142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step1 raw20142step1Labels permutation14 hz
    mixedMoment B raw20142step2 raw20142step2Labels = mixedMoment B raw20142step3 raw20142step3Labels := by
      have ha : raw20142step3 = (fun i j => raw20142step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20142step3 raw20142step2; decide +kernel
      have hl : raw20142step3Labels = raw20142step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20142step2 raw20142step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical20143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20143 raw20143Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw20143 raw20143Labels = mixedMoment B raw20143step0 raw20143step0Labels := by
      have hz : ∀ j, raw20143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20143step0 = (fun i j => raw20143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20143step0 raw20143; decide +kernel
      have hl : raw20143step0Labels = raw20143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20143 raw20143Labels permutation346 hz
    mixedMoment B raw20143step0 raw20143step0Labels = mixedMoment B raw20143step1 raw20143step1Labels := by
      have hz : ∀ j, raw20143step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20143step1 = (fun i j => raw20143step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20143step1 raw20143step0; decide +kernel
      have hl : raw20143step1Labels = raw20143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20143step0 raw20143step0Labels permutation56 hz
    mixedMoment B raw20143step1 raw20143step1Labels = mixedMoment B raw20143step2 raw20143step2Labels := by
      have ha : raw20143step2 = (fun i j => raw20143step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20143step2 raw20143step1; decide +kernel
      have hl : raw20143step2Labels = raw20143step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20143step1 raw20143step1Labels permutation31 permutation2
    mixedMoment B raw20143step2 raw20143step2Labels = mixedMoment B raw20143step3 raw20143step3Labels := by
      have ha : raw20143step3 = -raw20143step2 := by apply Matrix.ext; change ∀ i j, raw20143step3 i j = -(raw20143step2 i j); unfold raw20143step3 raw20143step2; decide +kernel
      have hl : raw20143step3Labels = raw20143step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical20144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20144 raw20144Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw20144 raw20144Labels = mixedMoment B raw20144step0 raw20144step0Labels := by
      have hz : ∀ j, raw20144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20144step0 = (fun i j => raw20144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20144step0 raw20144; decide +kernel
      have hl : raw20144step0Labels = raw20144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20144 raw20144Labels permutation346 hz
    mixedMoment B raw20144step0 raw20144step0Labels = mixedMoment B raw20144step1 raw20144step1Labels := by
      have ha : raw20144step1 = (fun i j => raw20144step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20144step1 raw20144step0; decide +kernel
      have hl : raw20144step1Labels = raw20144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20144step0 raw20144step0Labels permutation38 permutation2
    _ = mixedMoment B node1317 node1317Labels := by rfl

theorem canonical20145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20145 raw20145Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw20145 raw20145Labels = mixedMoment B raw20145step0 raw20145step0Labels := by
      have hz : ∀ j, raw20145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20145step0 = (fun i j => raw20145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20145step0 raw20145; decide +kernel
      have hl : raw20145step0Labels = raw20145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20145 raw20145Labels permutation265 hz
    mixedMoment B raw20145step0 raw20145step0Labels = mixedMoment B raw20145step1 raw20145step1Labels := by
      have ha : raw20145step1 = (fun i j => raw20145step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20145step1 raw20145step0; decide +kernel
      have hl : raw20145step1Labels = raw20145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20145step0 raw20145step0Labels permutation38 permutation2
    _ = mixedMoment B node1317 node1317Labels := by rfl

theorem canonical20146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20146 raw20146Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw20146 raw20146Labels = mixedMoment B raw20146step0 raw20146step0Labels := by
      have hz : ∀ j, raw20146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20146step0 = (fun i j => raw20146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20146step0 raw20146; decide +kernel
      have hl : raw20146step0Labels = raw20146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20146 raw20146Labels permutation346 hz
    mixedMoment B raw20146step0 raw20146step0Labels = mixedMoment B raw20146step1 raw20146step1Labels := by
      have hz : ∀ j, raw20146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20146step1 = (fun i j => raw20146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20146step1 raw20146step0; decide +kernel
      have hl : raw20146step1Labels = raw20146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20146step0 raw20146step0Labels permutation56 hz
    _ = mixedMoment B node1324 node1324Labels := by rfl

theorem canonical20147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20147 raw20147Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw20147 raw20147Labels = mixedMoment B raw20147step0 raw20147step0Labels := by
      have hz : ∀ j, raw20147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20147step0 = (fun i j => raw20147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20147step0 raw20147; decide +kernel
      have hl : raw20147step0Labels = raw20147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20147 raw20147Labels permutation346 hz
    mixedMoment B raw20147step0 raw20147step0Labels = mixedMoment B raw20147step1 raw20147step1Labels := by
      have hz : ∀ j, raw20147step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20147step1 = (fun i j => raw20147step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20147step1 raw20147step0; decide +kernel
      have hl : raw20147step1Labels = raw20147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20147step0 raw20147step0Labels permutation56 hz
    mixedMoment B raw20147step1 raw20147step1Labels = mixedMoment B raw20147step2 raw20147step2Labels := by
      have ha : raw20147step2 = (fun i j => raw20147step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20147step2 raw20147step1; decide +kernel
      have hl : raw20147step2Labels = raw20147step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20147step1 raw20147step1Labels permutation31 permutation2
    mixedMoment B raw20147step2 raw20147step2Labels = mixedMoment B raw20147step3 raw20147step3Labels := by
      have ha : raw20147step3 = -raw20147step2 := by apply Matrix.ext; change ∀ i j, raw20147step3 i j = -(raw20147step2 i j); unfold raw20147step3 raw20147step2; decide +kernel
      have hl : raw20147step3Labels = raw20147step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1142 node1142Labels := by rfl

theorem canonical20148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20148 raw20148Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw20148 raw20148Labels = mixedMoment B raw20148step0 raw20148step0Labels := by
      have hz : ∀ j, raw20148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20148step0 = (fun i j => raw20148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20148step0 raw20148; decide +kernel
      have hl : raw20148step0Labels = raw20148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20148 raw20148Labels permutation346 hz
    mixedMoment B raw20148step0 raw20148step0Labels = mixedMoment B raw20148step1 raw20148step1Labels := by
      have hz : ∀ j, raw20148step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20148step1 = (fun i j => raw20148step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20148step1 raw20148step0; decide +kernel
      have hl : raw20148step1Labels = raw20148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20148step0 raw20148step0Labels permutation56 hz
    mixedMoment B raw20148step1 raw20148step1Labels = mixedMoment B raw20148step2 raw20148step2Labels := by
      have ha : raw20148step2 = (fun i j => raw20148step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20148step2 raw20148step1; decide +kernel
      have hl : raw20148step2Labels = raw20148step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20148step1 raw20148step1Labels permutation11 permutation4
    mixedMoment B raw20148step2 raw20148step2Labels = mixedMoment B raw20148step3 raw20148step3Labels := by
      have ha : raw20148step3 = -raw20148step2 := by apply Matrix.ext; change ∀ i j, raw20148step3 i j = -(raw20148step2 i j); unfold raw20148step3 raw20148step2; decide +kernel
      have hl : raw20148step3Labels = raw20148step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1729 node1729Labels := by rfl

theorem canonical20149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20149 raw20149Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw20149 raw20149Labels = mixedMoment B raw20149step0 raw20149step0Labels := by
      have hz : ∀ j, raw20149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20149step0 = (fun i j => raw20149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20149step0 raw20149; decide +kernel
      have hl : raw20149step0Labels = raw20149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20149 raw20149Labels permutation346 hz
    mixedMoment B raw20149step0 raw20149step0Labels = mixedMoment B raw20149step1 raw20149step1Labels := by
      have ha : raw20149step1 = (fun i j => raw20149step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20149step1 raw20149step0; decide +kernel
      have hl : raw20149step1Labels = raw20149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20149step0 raw20149step0Labels permutation38 permutation2
    mixedMoment B raw20149step1 raw20149step1Labels = mixedMoment B raw20149step2 raw20149step2Labels := by
      have ha : raw20149step2 = -raw20149step1 := by apply Matrix.ext; change ∀ i j, raw20149step2 i j = -(raw20149step1 i j); unfold raw20149step2 raw20149step1; decide +kernel
      have hl : raw20149step2Labels = raw20149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3242 node3242Labels := by rfl

theorem canonical20150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20150 raw20150Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw20150 raw20150Labels = mixedMoment B raw20150step0 raw20150step0Labels := by
      have hz : ∀ j, raw20150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20150step0 = (fun i j => raw20150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20150step0 raw20150; decide +kernel
      have hl : raw20150step0Labels = raw20150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20150 raw20150Labels permutation265 hz
    mixedMoment B raw20150step0 raw20150step0Labels = mixedMoment B raw20150step1 raw20150step1Labels := by
      have ha : raw20150step1 = (fun i j => raw20150step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20150step1 raw20150step0; decide +kernel
      have hl : raw20150step1Labels = raw20150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20150step0 raw20150step0Labels permutation38 permutation2
    mixedMoment B raw20150step1 raw20150step1Labels = mixedMoment B raw20150step2 raw20150step2Labels := by
      have ha : raw20150step2 = -raw20150step1 := by apply Matrix.ext; change ∀ i j, raw20150step2 i j = -(raw20150step1 i j); unfold raw20150step2 raw20150step1; decide +kernel
      have hl : raw20150step2Labels = raw20150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3242 node3242Labels := by rfl

theorem canonical20151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20151 raw20151Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20151 raw20151Labels = mixedMoment B raw20151step0 raw20151step0Labels := by
      have hz : ∀ j, raw20151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20151step0 = (fun i j => raw20151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20151step0 raw20151; decide +kernel
      have hl : raw20151step0Labels = raw20151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20151 raw20151Labels permutation346 hz
    mixedMoment B raw20151step0 raw20151step0Labels = mixedMoment B raw20151step1 raw20151step1Labels := by
      have hz : ∀ j, raw20151step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20151step1 = (fun i j => raw20151step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20151step1 raw20151step0; decide +kernel
      have hl : raw20151step1Labels = raw20151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20151step0 raw20151step0Labels permutation56 hz
    mixedMoment B raw20151step1 raw20151step1Labels = mixedMoment B raw20151step2 raw20151step2Labels := by
      have ha : raw20151step2 = -raw20151step1 := by apply Matrix.ext; change ∀ i j, raw20151step2 i j = -(raw20151step1 i j); unfold raw20151step2 raw20151step1; decide +kernel
      have hl : raw20151step2Labels = raw20151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical20152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20152 raw20152Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw20152 raw20152Labels = mixedMoment B raw20152step0 raw20152step0Labels := by
      have hz : ∀ j, raw20152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20152step0 = (fun i j => raw20152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20152step0 raw20152; decide +kernel
      have hl : raw20152step0Labels = raw20152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20152 raw20152Labels permutation346 hz
    mixedMoment B raw20152step0 raw20152step0Labels = mixedMoment B raw20152step1 raw20152step1Labels := by
      have hz : ∀ j, raw20152step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20152step1 = (fun i j => raw20152step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20152step1 raw20152step0; decide +kernel
      have hl : raw20152step1Labels = raw20152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20152step0 raw20152step0Labels permutation56 hz
    mixedMoment B raw20152step1 raw20152step1Labels = mixedMoment B raw20152step2 raw20152step2Labels := by
      have ha : raw20152step2 = -raw20152step1 := by apply Matrix.ext; change ∀ i j, raw20152step2 i j = -(raw20152step1 i j); unfold raw20152step2 raw20152step1; decide +kernel
      have hl : raw20152step2Labels = raw20152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3247 node3247Labels := by rfl

theorem canonical20153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20153 raw20153Labels = mixedMoment B node1952 node1952Labels := by
  calc
    mixedMoment B raw20153 raw20153Labels = mixedMoment B raw20153step0 raw20153step0Labels := by
      have hz : ∀ j, raw20153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20153step0 = (fun i j => raw20153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20153step0 raw20153; decide +kernel
      have hl : raw20153step0Labels = raw20153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20153 raw20153Labels permutation346 hz
    mixedMoment B raw20153step0 raw20153step0Labels = mixedMoment B raw20153step1 raw20153step1Labels := by
      have hz : ∀ j, raw20153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20153step1 = (fun i j => raw20153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20153step1 raw20153step0; decide +kernel
      have hl : raw20153step1Labels = raw20153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20153step0 raw20153step0Labels permutation56 hz
    mixedMoment B raw20153step1 raw20153step1Labels = mixedMoment B raw20153step2 raw20153step2Labels := by
      have ha : raw20153step2 = (fun i j => raw20153step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20153step2 raw20153step1; decide +kernel
      have hl : raw20153step2Labels = raw20153step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20153step1 raw20153step1Labels permutation31 permutation2
    _ = mixedMoment B node1952 node1952Labels := by rfl

theorem canonical20154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20154 raw20154Labels = mixedMoment B node808 node808Labels := by
  calc
    mixedMoment B raw20154 raw20154Labels = mixedMoment B raw20154step0 raw20154step0Labels := by
      have hz : ∀ j, raw20154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20154step0 = (fun i j => raw20154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20154step0 raw20154; decide +kernel
      have hl : raw20154step0Labels = raw20154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20154 raw20154Labels permutation346 hz
    mixedMoment B raw20154step0 raw20154step0Labels = mixedMoment B raw20154step1 raw20154step1Labels := by
      have ha : raw20154step1 = (fun i j => raw20154step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20154step1 raw20154step0; decide +kernel
      have hl : raw20154step1Labels = raw20154step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20154step0 raw20154step0Labels permutation45 permutation4
    mixedMoment B raw20154step1 raw20154step1Labels = mixedMoment B raw20154step2 raw20154step2Labels := by
      have ha : raw20154step2 = -raw20154step1 := by apply Matrix.ext; change ∀ i j, raw20154step2 i j = -(raw20154step1 i j); unfold raw20154step2 raw20154step1; decide +kernel
      have hl : raw20154step2Labels = raw20154step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node808 node808Labels := by rfl

theorem canonical20155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20155 raw20155Labels = mixedMoment B node808 node808Labels := by
  calc
    mixedMoment B raw20155 raw20155Labels = mixedMoment B raw20155step0 raw20155step0Labels := by
      have hz : ∀ j, raw20155 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20155step0 = (fun i j => raw20155 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20155step0 raw20155; decide +kernel
      have hl : raw20155step0Labels = raw20155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20155 raw20155Labels permutation265 hz
    mixedMoment B raw20155step0 raw20155step0Labels = mixedMoment B raw20155step1 raw20155step1Labels := by
      have ha : raw20155step1 = (fun i j => raw20155step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20155step1 raw20155step0; decide +kernel
      have hl : raw20155step1Labels = raw20155step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20155step0 raw20155step0Labels permutation45 permutation4
    mixedMoment B raw20155step1 raw20155step1Labels = mixedMoment B raw20155step2 raw20155step2Labels := by
      have ha : raw20155step2 = -raw20155step1 := by apply Matrix.ext; change ∀ i j, raw20155step2 i j = -(raw20155step1 i j); unfold raw20155step2 raw20155step1; decide +kernel
      have hl : raw20155step2Labels = raw20155step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node808 node808Labels := by rfl

theorem canonical20156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20156 raw20156Labels = mixedMoment B node814 node814Labels := by
  calc
    mixedMoment B raw20156 raw20156Labels = mixedMoment B raw20156step0 raw20156step0Labels := by
      have hz : ∀ j, raw20156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20156step0 = (fun i j => raw20156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20156step0 raw20156; decide +kernel
      have hl : raw20156step0Labels = raw20156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20156 raw20156Labels permutation346 hz
    mixedMoment B raw20156step0 raw20156step0Labels = mixedMoment B raw20156step1 raw20156step1Labels := by
      have hz : ∀ j, raw20156step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20156step1 = (fun i j => raw20156step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20156step1 raw20156step0; decide +kernel
      have hl : raw20156step1Labels = raw20156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20156step0 raw20156step0Labels permutation56 hz
    mixedMoment B raw20156step1 raw20156step1Labels = mixedMoment B raw20156step2 raw20156step2Labels := by
      have ha : raw20156step2 = (fun i j => raw20156step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20156step2 raw20156step1; decide +kernel
      have hl : raw20156step2Labels = raw20156step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20156step1 raw20156step1Labels permutation11 permutation4
    mixedMoment B raw20156step2 raw20156step2Labels = mixedMoment B raw20156step3 raw20156step3Labels := by
      have ha : raw20156step3 = -raw20156step2 := by apply Matrix.ext; change ∀ i j, raw20156step3 i j = -(raw20156step2 i j); unfold raw20156step3 raw20156step2; decide +kernel
      have hl : raw20156step3Labels = raw20156step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node814 node814Labels := by rfl

theorem canonical20157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20157 raw20157Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw20157 raw20157Labels = mixedMoment B raw20157step0 raw20157step0Labels := by
      have hz : ∀ j, raw20157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20157step0 = (fun i j => raw20157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20157step0 raw20157; decide +kernel
      have hl : raw20157step0Labels = raw20157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20157 raw20157Labels permutation346 hz
    mixedMoment B raw20157step0 raw20157step0Labels = mixedMoment B raw20157step1 raw20157step1Labels := by
      have hz : ∀ j, raw20157step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20157step1 = (fun i j => raw20157step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20157step1 raw20157step0; decide +kernel
      have hl : raw20157step1Labels = raw20157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20157step0 raw20157step0Labels permutation56 hz
    mixedMoment B raw20157step1 raw20157step1Labels = mixedMoment B raw20157step2 raw20157step2Labels := by
      have ha : raw20157step2 = (fun i j => raw20157step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20157step2 raw20157step1; decide +kernel
      have hl : raw20157step2Labels = raw20157step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20157step1 raw20157step1Labels permutation11 permutation4
    mixedMoment B raw20157step2 raw20157step2Labels = mixedMoment B raw20157step3 raw20157step3Labels := by
      have ha : raw20157step3 = -raw20157step2 := by apply Matrix.ext; change ∀ i j, raw20157step3 i j = -(raw20157step2 i j); unfold raw20157step3 raw20157step2; decide +kernel
      have hl : raw20157step3Labels = raw20157step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node857 node857Labels := by rfl

theorem canonical20158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20158 raw20158Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw20158 raw20158Labels = mixedMoment B raw20158step0 raw20158step0Labels := by
      have hz : ∀ j, raw20158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20158step0 = (fun i j => raw20158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20158step0 raw20158; decide +kernel
      have hl : raw20158step0Labels = raw20158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20158 raw20158Labels permutation346 hz
    mixedMoment B raw20158step0 raw20158step0Labels = mixedMoment B raw20158step1 raw20158step1Labels := by
      have hz : ∀ j, raw20158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20158step1 = (fun i j => raw20158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20158step1 raw20158step0; decide +kernel
      have hl : raw20158step1Labels = raw20158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20158step0 raw20158step0Labels permutation56 hz
    mixedMoment B raw20158step1 raw20158step1Labels = mixedMoment B raw20158step2 raw20158step2Labels := by
      have ha : raw20158step2 = (fun i j => raw20158step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20158step2 raw20158step1; decide +kernel
      have hl : raw20158step2Labels = raw20158step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20158step1 raw20158step1Labels permutation10 permutation4
    mixedMoment B raw20158step2 raw20158step2Labels = mixedMoment B raw20158step3 raw20158step3Labels := by
      have ha : raw20158step3 = -raw20158step2 := by apply Matrix.ext; change ∀ i j, raw20158step3 i j = -(raw20158step2 i j); unfold raw20158step3 raw20158step2; decide +kernel
      have hl : raw20158step3Labels = raw20158step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node815 node815Labels := by rfl

theorem canonical20159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20159 raw20159Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw20159 raw20159Labels = mixedMoment B raw20159step0 raw20159step0Labels := by
      have hz : ∀ j, raw20159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20159step0 = (fun i j => raw20159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20159step0 raw20159; decide +kernel
      have hl : raw20159step0Labels = raw20159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20159 raw20159Labels permutation346 hz
    mixedMoment B raw20159step0 raw20159step0Labels = mixedMoment B raw20159step1 raw20159step1Labels := by
      have ha : raw20159step1 = (fun i j => raw20159step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20159step1 raw20159step0; decide +kernel
      have hl : raw20159step1Labels = raw20159step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20159step0 raw20159step0Labels permutation44 permutation4
    mixedMoment B raw20159step1 raw20159step1Labels = mixedMoment B raw20159step2 raw20159step2Labels := by
      have ha : raw20159step2 = -raw20159step1 := by apply Matrix.ext; change ∀ i j, raw20159step2 i j = -(raw20159step1 i j); unfold raw20159step2 raw20159step1; decide +kernel
      have hl : raw20159step2Labels = raw20159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical20160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20160 raw20160Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw20160 raw20160Labels = mixedMoment B raw20160step0 raw20160step0Labels := by
      have hz : ∀ j, raw20160 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20160step0 = (fun i j => raw20160 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20160step0 raw20160; decide +kernel
      have hl : raw20160step0Labels = raw20160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20160 raw20160Labels permutation265 hz
    mixedMoment B raw20160step0 raw20160step0Labels = mixedMoment B raw20160step1 raw20160step1Labels := by
      have ha : raw20160step1 = (fun i j => raw20160step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20160step1 raw20160step0; decide +kernel
      have hl : raw20160step1Labels = raw20160step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20160step0 raw20160step0Labels permutation44 permutation4
    mixedMoment B raw20160step1 raw20160step1Labels = mixedMoment B raw20160step2 raw20160step2Labels := by
      have ha : raw20160step2 = -raw20160step1 := by apply Matrix.ext; change ∀ i j, raw20160step2 i j = -(raw20160step1 i j); unfold raw20160step2 raw20160step1; decide +kernel
      have hl : raw20160step2Labels = raw20160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1723 node1723Labels := by rfl

theorem canonical20161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20161 raw20161Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20161 raw20161Labels = mixedMoment B raw20161step0 raw20161step0Labels := by
      have hz : ∀ j, raw20161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20161step0 = (fun i j => raw20161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20161step0 raw20161; decide +kernel
      have hl : raw20161step0Labels = raw20161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161 raw20161Labels permutation346 hz
    mixedMoment B raw20161step0 raw20161step0Labels = mixedMoment B raw20161step1 raw20161step1Labels := by
      have hz : ∀ j, raw20161step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20161step1 = (fun i j => raw20161step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20161step1 raw20161step0; decide +kernel
      have hl : raw20161step1Labels = raw20161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161step0 raw20161step0Labels permutation56 hz
    mixedMoment B raw20161step1 raw20161step1Labels = mixedMoment B raw20161step2 raw20161step2Labels := by
      have ha : raw20161step2 = (fun i j => raw20161step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20161step2 raw20161step1; decide +kernel
      have hl : raw20161step2Labels = raw20161step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20161step1 raw20161step1Labels permutation10 permutation4
    mixedMoment B raw20161step2 raw20161step2Labels = mixedMoment B raw20161step3 raw20161step3Labels := by
      have ha : raw20161step3 = -raw20161step2 := by apply Matrix.ext; change ∀ i j, raw20161step3 i j = -(raw20161step2 i j); unfold raw20161step3 raw20161step2; decide +kernel
      have hl : raw20161step3Labels = raw20161step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20162 raw20162Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw20162 raw20162Labels = mixedMoment B raw20162step0 raw20162step0Labels := by
      have hz : ∀ j, raw20162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20162step0 = (fun i j => raw20162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20162step0 raw20162; decide +kernel
      have hl : raw20162step0Labels = raw20162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20162 raw20162Labels permutation346 hz
    mixedMoment B raw20162step0 raw20162step0Labels = mixedMoment B raw20162step1 raw20162step1Labels := by
      have ha : raw20162step1 = (fun i j => raw20162step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20162step1 raw20162step0; decide +kernel
      have hl : raw20162step1Labels = raw20162step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20162step0 raw20162step0Labels permutation35 permutation4
    mixedMoment B raw20162step1 raw20162step1Labels = mixedMoment B raw20162step2 raw20162step2Labels := by
      have ha : raw20162step2 = -raw20162step1 := by apply Matrix.ext; change ∀ i j, raw20162step2 i j = -(raw20162step1 i j); unfold raw20162step2 raw20162step1; decide +kernel
      have hl : raw20162step2Labels = raw20162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1624 node1624Labels := by rfl

theorem canonical20163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20163 raw20163Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw20163 raw20163Labels = mixedMoment B raw20163step0 raw20163step0Labels := by
      have hz : ∀ j, raw20163 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20163step0 = (fun i j => raw20163 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20163step0 raw20163; decide +kernel
      have hl : raw20163step0Labels = raw20163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20163 raw20163Labels permutation265 hz
    mixedMoment B raw20163step0 raw20163step0Labels = mixedMoment B raw20163step1 raw20163step1Labels := by
      have ha : raw20163step1 = (fun i j => raw20163step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20163step1 raw20163step0; decide +kernel
      have hl : raw20163step1Labels = raw20163step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20163step0 raw20163step0Labels permutation35 permutation4
    mixedMoment B raw20163step1 raw20163step1Labels = mixedMoment B raw20163step2 raw20163step2Labels := by
      have ha : raw20163step2 = -raw20163step1 := by apply Matrix.ext; change ∀ i j, raw20163step2 i j = -(raw20163step1 i j); unfold raw20163step2 raw20163step1; decide +kernel
      have hl : raw20163step2Labels = raw20163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1624 node1624Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3517 raw3517Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw3517 raw3517Labels = mixedMoment B raw3517step0 raw3517step0Labels := by
      have hz : ∀ j, raw3517 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3517step0 = (fun i j => raw3517 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3517step0 raw3517; decide +kernel
      have hl : raw3517step0Labels = raw3517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517 raw3517Labels permutation590 hz
    mixedMoment B raw3517step0 raw3517step0Labels = mixedMoment B raw3517step1 raw3517step1Labels := by
      have hz : ∀ j, raw3517step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3517step1 = (fun i j => raw3517step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3517step1 raw3517step0; decide +kernel
      have hl : raw3517step1Labels = raw3517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step0 raw3517step0Labels permutation104 hz
    mixedMoment B raw3517step1 raw3517step1Labels = mixedMoment B raw3517step2 raw3517step2Labels := by
      have hz : ∀ j, raw3517step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3517step2 = (fun i j => raw3517step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3517step2 raw3517step1; decide +kernel
      have hl : raw3517step2Labels = raw3517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step1 raw3517step1Labels permutation20 hz
    mixedMoment B raw3517step2 raw3517step2Labels = mixedMoment B raw3517step3 raw3517step3Labels := by
      have hz : ∀ j, raw3517step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3517step3 = (fun i j => raw3517step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3517step3 raw3517step2; decide +kernel
      have hl : raw3517step3Labels = raw3517step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3517step2 raw3517step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

theorem canonical3521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3521 raw3521Labels = mixedMoment B node1092 node1092Labels := by
  calc
    mixedMoment B raw3521 raw3521Labels = mixedMoment B raw3521step0 raw3521step0Labels := by
      have hz : ∀ j, raw3521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3521step0 = (fun i j => raw3521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3521step0 raw3521; decide +kernel
      have hl : raw3521step0Labels = raw3521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521 raw3521Labels permutation434 hz
    mixedMoment B raw3521step0 raw3521step0Labels = mixedMoment B raw3521step1 raw3521step1Labels := by
      have hz : ∀ j, raw3521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3521step1 = (fun i j => raw3521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3521step1 raw3521step0; decide +kernel
      have hl : raw3521step1Labels = raw3521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521step0 raw3521step0Labels permutation80 hz
    mixedMoment B raw3521step1 raw3521step1Labels = mixedMoment B raw3521step2 raw3521step2Labels := by
      have hz : ∀ j, raw3521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3521step2 = (fun i j => raw3521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3521step2 raw3521step1; decide +kernel
      have hl : raw3521step2Labels = raw3521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3521step1 raw3521step1Labels permutation14 hz
    _ = mixedMoment B node1092 node1092Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical3630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3630 raw3630Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3630 raw3630Labels = mixedMoment B raw3630step0 raw3630step0Labels := by
      have hz : ∀ j, raw3630 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3630step0 = (fun i j => raw3630 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3630step0 raw3630; decide +kernel
      have hl : raw3630step0Labels = raw3630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630 raw3630Labels permutation590 hz
    mixedMoment B raw3630step0 raw3630step0Labels = mixedMoment B raw3630step1 raw3630step1Labels := by
      have hz : ∀ j, raw3630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3630step1 = (fun i j => raw3630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3630step1 raw3630step0; decide +kernel
      have hl : raw3630step1Labels = raw3630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step0 raw3630step0Labels permutation80 hz
    mixedMoment B raw3630step1 raw3630step1Labels = mixedMoment B raw3630step2 raw3630step2Labels := by
      have hz : ∀ j, raw3630step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3630step2 = (fun i j => raw3630step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3630step2 raw3630step1; decide +kernel
      have hl : raw3630step2Labels = raw3630step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3630step1 raw3630step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical3633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3633 raw3633Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw3633 raw3633Labels = mixedMoment B raw3633step0 raw3633step0Labels := by
      have hz : ∀ j, raw3633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3633step0 = (fun i j => raw3633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3633step0 raw3633; decide +kernel
      have hl : raw3633step0Labels = raw3633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3633 raw3633Labels permutation346 hz
    mixedMoment B raw3633step0 raw3633step0Labels = mixedMoment B raw3633step1 raw3633step1Labels := by
      have hz : ∀ j, raw3633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3633step1 = (fun i j => raw3633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3633step1 raw3633step0; decide +kernel
      have hl : raw3633step1Labels = raw3633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3633step0 raw3633step0Labels permutation56 hz
    mixedMoment B raw3633step1 raw3633step1Labels = mixedMoment B raw3633step2 raw3633step2Labels := by
      have ha : raw3633step2 = (fun i j => raw3633step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3633step2 raw3633step1; decide +kernel
      have hl : raw3633step2Labels = raw3633step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3633step1 raw3633step1Labels permutation10 permutation2
    _ = mixedMoment B node1061 node1061Labels := by rfl

theorem canonical3634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3634 raw3634Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw3634 raw3634Labels = mixedMoment B raw3634step0 raw3634step0Labels := by
      have hz : ∀ j, raw3634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3634step0 = (fun i j => raw3634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3634step0 raw3634; decide +kernel
      have hl : raw3634step0Labels = raw3634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3634 raw3634Labels permutation346 hz
    mixedMoment B raw3634step0 raw3634step0Labels = mixedMoment B raw3634step1 raw3634step1Labels := by
      have hz : ∀ j, raw3634step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3634step1 = (fun i j => raw3634step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3634step1 raw3634step0; decide +kernel
      have hl : raw3634step1Labels = raw3634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3634step0 raw3634step0Labels permutation56 hz
    _ = mixedMoment B node1047 node1047Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4744 raw4744Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw4744 raw4744Labels = mixedMoment B raw4744step0 raw4744step0Labels := by
      have hz : ∀ j, raw4744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4744step0 = (fun i j => raw4744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4744step0 raw4744; decide +kernel
      have hl : raw4744step0Labels = raw4744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744 raw4744Labels permutation346 hz
    mixedMoment B raw4744step0 raw4744step0Labels = mixedMoment B raw4744step1 raw4744step1Labels := by
      have hz : ∀ j, raw4744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4744step1 = (fun i j => raw4744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4744step1 raw4744step0; decide +kernel
      have hl : raw4744step1Labels = raw4744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4744step0 raw4744step0Labels permutation56 hz
    mixedMoment B raw4744step1 raw4744step1Labels = mixedMoment B raw4744step2 raw4744step2Labels := by
      have ha : raw4744step2 = (fun i j => raw4744step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4744step2 raw4744step1; decide +kernel
      have hl : raw4744step2Labels = raw4744step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4744step1 raw4744step1Labels permutation26 permutation0
    mixedMoment B raw4744step2 raw4744step2Labels = mixedMoment B raw4744step3 raw4744step3Labels := by
      have ha : raw4744step3 = -raw4744step2 := by apply Matrix.ext; change ∀ i j, raw4744step3 i j = -(raw4744step2 i j); unfold raw4744step3 raw4744step2; decide +kernel
      have hl : raw4744step3Labels = raw4744step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical4748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4748 raw4748Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw4748 raw4748Labels = mixedMoment B raw4748step0 raw4748step0Labels := by
      have hz : ∀ j, raw4748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4748step0 = (fun i j => raw4748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4748step0 raw4748; decide +kernel
      have hl : raw4748step0Labels = raw4748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748 raw4748Labels permutation346 hz
    mixedMoment B raw4748step0 raw4748step0Labels = mixedMoment B raw4748step1 raw4748step1Labels := by
      have hz : ∀ j, raw4748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4748step1 = (fun i j => raw4748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4748step1 raw4748step0; decide +kernel
      have hl : raw4748step1Labels = raw4748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4748step0 raw4748step0Labels permutation56 hz
    _ = mixedMoment B node1408 node1408Labels := by rfl

theorem canonical4762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4762 raw4762Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw4762 raw4762Labels = mixedMoment B raw4762step0 raw4762step0Labels := by
      have hz : ∀ j, raw4762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4762step0 = (fun i j => raw4762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4762step0 raw4762; decide +kernel
      have hl : raw4762step0Labels = raw4762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762 raw4762Labels permutation346 hz
    mixedMoment B raw4762step0 raw4762step0Labels = mixedMoment B raw4762step1 raw4762step1Labels := by
      have hz : ∀ j, raw4762step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4762step1 = (fun i j => raw4762step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4762step1 raw4762step0; decide +kernel
      have hl : raw4762step1Labels = raw4762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4762step0 raw4762step0Labels permutation56 hz
    mixedMoment B raw4762step1 raw4762step1Labels = mixedMoment B raw4762step2 raw4762step2Labels := by
      have ha : raw4762step2 = (fun i j => raw4762step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4762step2 raw4762step1; decide +kernel
      have hl : raw4762step2Labels = raw4762step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4762step1 raw4762step1Labels permutation31 permutation2
    mixedMoment B raw4762step2 raw4762step2Labels = mixedMoment B raw4762step3 raw4762step3Labels := by
      have ha : raw4762step3 = -raw4762step2 := by apply Matrix.ext; change ∀ i j, raw4762step3 i j = -(raw4762step2 i j); unfold raw4762step3 raw4762step2; decide +kernel
      have hl : raw4762step3Labels = raw4762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical68
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical8776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8776 raw8776Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8776 raw8776Labels = mixedMoment B raw8776step0 raw8776step0Labels := by
      have hz : ∀ j, raw8776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8776step0 = (fun i j => raw8776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8776step0 raw8776; decide +kernel
      have hl : raw8776step0Labels = raw8776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776 raw8776Labels permutation346 hz
    mixedMoment B raw8776step0 raw8776step0Labels = mixedMoment B raw8776step1 raw8776step1Labels := by
      have hz : ∀ j, raw8776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8776step1 = (fun i j => raw8776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8776step1 raw8776step0; decide +kernel
      have hl : raw8776step1Labels = raw8776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8776step0 raw8776step0Labels permutation56 hz
    mixedMoment B raw8776step1 raw8776step1Labels = mixedMoment B raw8776step2 raw8776step2Labels := by
      have ha : raw8776step2 = (fun i j => raw8776step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8776step2 raw8776step1; decide +kernel
      have hl : raw8776step2Labels = raw8776step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8776step1 raw8776step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical8781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8781 raw8781Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw8781 raw8781Labels = mixedMoment B raw8781step0 raw8781step0Labels := by
      have hz : ∀ j, raw8781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8781step0 = (fun i j => raw8781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8781step0 raw8781; decide +kernel
      have hl : raw8781step0Labels = raw8781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8781 raw8781Labels permutation346 hz
    mixedMoment B raw8781step0 raw8781step0Labels = mixedMoment B raw8781step1 raw8781step1Labels := by
      have hz : ∀ j, raw8781step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8781step1 = (fun i j => raw8781step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8781step1 raw8781step0; decide +kernel
      have hl : raw8781step1Labels = raw8781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8781step0 raw8781step0Labels permutation56 hz
    _ = mixedMoment B node1372 node1372Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node808 node808Labels = Sparse.eval nodeValue808 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 808) = mixedMoment B node808 node808Labels := rfl
  simpa [nodeValue808, Sparse.eval] using hc.symm

theorem sound814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node814 node814Labels = Sparse.eval nodeValue814 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 814) = mixedMoment B node814 node814Labels := rfl
  simpa [nodeValue814, Sparse.eval] using hc.symm

theorem sound815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node815 node815Labels = Sparse.eval nodeValue815 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 815) = mixedMoment B node815 node815Labels := rfl
  simpa [nodeValue815, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node853 node853Labels = Sparse.eval nodeValue853 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 853) = mixedMoment B node853 node853Labels := rfl
  simpa [nodeValue853, Sparse.eval] using hc.symm

theorem sound857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node857 node857Labels = Sparse.eval nodeValue857 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 857) = mixedMoment B node857 node857Labels := rfl
  simpa [nodeValue857, Sparse.eval] using hc.symm

theorem sound860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node860 node860Labels = Sparse.eval nodeValue860 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 860) = mixedMoment B node860 node860Labels := rfl
  simpa [nodeValue860, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node914 node914Labels = Sparse.eval nodeValue914 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 914) = mixedMoment B node914 node914Labels := rfl
  simpa [nodeValue914, Sparse.eval] using hc.symm

theorem sound925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node925 node925Labels = Sparse.eval nodeValue925 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 925) = mixedMoment B node925 node925Labels := rfl
  simpa [nodeValue925, Sparse.eval] using hc.symm

theorem sound931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node931 node931Labels = Sparse.eval nodeValue931 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 931) = mixedMoment B node931 node931Labels := rfl
  simpa [nodeValue931, Sparse.eval] using hc.symm

theorem sound940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node940 node940Labels = Sparse.eval nodeValue940 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 940) = mixedMoment B node940 node940Labels := rfl
  simpa [nodeValue940, Sparse.eval] using hc.symm

theorem sound951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node951 node951Labels = Sparse.eval nodeValue951 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 951) = mixedMoment B node951 node951Labels := rfl
  simpa [nodeValue951, Sparse.eval] using hc.symm

theorem sound954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node954 node954Labels = Sparse.eval nodeValue954 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 954) = mixedMoment B node954 node954Labels := rfl
  simpa [nodeValue954, Sparse.eval] using hc.symm

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

theorem sound1047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1047 node1047Labels = Sparse.eval nodeValue1047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1047) = mixedMoment B node1047 node1047Labels := rfl
  simpa [nodeValue1047, Sparse.eval] using hc.symm

theorem sound1049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1049 node1049Labels = Sparse.eval nodeValue1049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1049) = mixedMoment B node1049 node1049Labels := rfl
  simpa [nodeValue1049, Sparse.eval] using hc.symm

theorem sound1059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1059 node1059Labels = Sparse.eval nodeValue1059 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1059) = mixedMoment B node1059 node1059Labels := rfl
  simpa [nodeValue1059, Sparse.eval] using hc.symm

theorem sound1061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1061 node1061Labels = Sparse.eval nodeValue1061 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1061) = mixedMoment B node1061 node1061Labels := rfl
  simpa [nodeValue1061, Sparse.eval] using hc.symm

theorem sound1072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1072 node1072Labels = Sparse.eval nodeValue1072 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1072) = mixedMoment B node1072 node1072Labels := rfl
  simpa [nodeValue1072, Sparse.eval] using hc.symm

theorem sound1083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1083 node1083Labels = Sparse.eval nodeValue1083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1083) = mixedMoment B node1083 node1083Labels := rfl
  simpa [nodeValue1083, Sparse.eval] using hc.symm

theorem sound1087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1087 node1087Labels = Sparse.eval nodeValue1087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1087) = mixedMoment B node1087 node1087Labels := rfl
  simpa [nodeValue1087, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem sound1091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1091 node1091Labels = Sparse.eval nodeValue1091 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1091) = mixedMoment B node1091 node1091Labels := rfl
  simpa [nodeValue1091, Sparse.eval] using hc.symm

theorem sound1092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1092 node1092Labels = Sparse.eval nodeValue1092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1092) = mixedMoment B node1092 node1092Labels := rfl
  simpa [nodeValue1092, Sparse.eval] using hc.symm

theorem sound1093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1093 node1093Labels = Sparse.eval nodeValue1093 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1093) = mixedMoment B node1093 node1093Labels := rfl
  simpa [nodeValue1093, Sparse.eval] using hc.symm

theorem sound1094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1094 node1094Labels = Sparse.eval nodeValue1094 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1094) = mixedMoment B node1094 node1094Labels := rfl
  simpa [nodeValue1094, Sparse.eval] using hc.symm

theorem sound1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1142 node1142Labels = Sparse.eval nodeValue1142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1142) = mixedMoment B node1142 node1142Labels := rfl
  simpa [nodeValue1142, Sparse.eval] using hc.symm

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

theorem sound1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1317 node1317Labels = Sparse.eval nodeValue1317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1317) = mixedMoment B node1317 node1317Labels := rfl
  simpa [nodeValue1317, Sparse.eval] using hc.symm

theorem sound1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1324 node1324Labels = Sparse.eval nodeValue1324 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1324) = mixedMoment B node1324 node1324Labels := rfl
  simpa [nodeValue1324, Sparse.eval] using hc.symm

theorem sound1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1336 node1336Labels = Sparse.eval nodeValue1336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1336) = mixedMoment B node1336 node1336Labels := rfl
  simpa [nodeValue1336, Sparse.eval] using hc.symm

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

theorem sound1348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1348 node1348Labels = Sparse.eval nodeValue1348 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1348) = mixedMoment B node1348 node1348Labels := rfl
  simpa [nodeValue1348, Sparse.eval] using hc.symm

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

theorem sound1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1408 node1408Labels = Sparse.eval nodeValue1408 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1408) = mixedMoment B node1408 node1408Labels := rfl
  simpa [nodeValue1408, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1619 node1619Labels = Sparse.eval nodeValue1619 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1619) = mixedMoment B node1619 node1619Labels := rfl
  simpa [nodeValue1619, Sparse.eval] using hc.symm

theorem sound1624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1624 node1624Labels = Sparse.eval nodeValue1624 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1624) = mixedMoment B node1624 node1624Labels := rfl
  simpa [nodeValue1624, Sparse.eval] using hc.symm

theorem sound1628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1628 node1628Labels = Sparse.eval nodeValue1628 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1628) = mixedMoment B node1628 node1628Labels := rfl
  simpa [nodeValue1628, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1723 node1723Labels = Sparse.eval nodeValue1723 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1723) = mixedMoment B node1723 node1723Labels := rfl
  simpa [nodeValue1723, Sparse.eval] using hc.symm

theorem sound1725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1725 node1725Labels = Sparse.eval nodeValue1725 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1725) = mixedMoment B node1725 node1725Labels := rfl
  simpa [nodeValue1725, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1729 node1729Labels = Sparse.eval nodeValue1729 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1729) = mixedMoment B node1729 node1729Labels := rfl
  simpa [nodeValue1729, Sparse.eval] using hc.symm

theorem sound1744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1744 node1744Labels = Sparse.eval nodeValue1744 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1744) = mixedMoment B node1744 node1744Labels := rfl
  simpa [nodeValue1744, Sparse.eval] using hc.symm

theorem sound1745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1745 node1745Labels = Sparse.eval nodeValue1745 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1745) = mixedMoment B node1745 node1745Labels := rfl
  simpa [nodeValue1745, Sparse.eval] using hc.symm

theorem sound1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1746 node1746Labels = Sparse.eval nodeValue1746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1746) = mixedMoment B node1746 node1746Labels := rfl
  simpa [nodeValue1746, Sparse.eval] using hc.symm

theorem sound1747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1747 node1747Labels = Sparse.eval nodeValue1747 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1747) = mixedMoment B node1747 node1747Labels := rfl
  simpa [nodeValue1747, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

theorem sound1756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1756 node1756Labels = Sparse.eval nodeValue1756 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1756) = mixedMoment B node1756 node1756Labels := rfl
  simpa [nodeValue1756, Sparse.eval] using hc.symm

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

theorem sound1952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1952 node1952Labels = Sparse.eval nodeValue1952 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1952) = mixedMoment B node1952 node1952Labels := rfl
  simpa [nodeValue1952, Sparse.eval] using hc.symm

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

theorem sound2045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2045 node2045Labels = Sparse.eval nodeValue2045 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2045) = mixedMoment B node2045 node2045Labels := rfl
  simpa [nodeValue2045, Sparse.eval] using hc.symm

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

theorem sound2064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2064 node2064Labels = Sparse.eval nodeValue2064 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2064) = mixedMoment B node2064 node2064Labels := rfl
  simpa [nodeValue2064, Sparse.eval] using hc.symm

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

theorem sound2112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2112 node2112Labels = Sparse.eval nodeValue2112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2112) = mixedMoment B node2112 node2112Labels := rfl
  simpa [nodeValue2112, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2289 node2289Labels = Sparse.eval nodeValue2289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2289) = mixedMoment B node2289 node2289Labels := rfl
  simpa [nodeValue2289, Sparse.eval] using hc.symm

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

theorem sound3242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3242 node3242Labels = Sparse.eval nodeValue3242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3242) = mixedMoment B node3242 node3242Labels := rfl
  simpa [nodeValue3242, Sparse.eval] using hc.symm

theorem sound3247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3247 node3247Labels = Sparse.eval nodeValue3247 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3247) = mixedMoment B node3247 node3247Labels := rfl
  simpa [nodeValue3247, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

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

theorem sound4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4070 node4070Labels = Sparse.eval nodeValue4070 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4070) = mixedMoment B node4070 node4070Labels := rfl
  simpa [nodeValue4070, Sparse.eval] using hc.symm

theorem sound4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4083 node4083Labels = Sparse.eval nodeValue4083 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4083) = mixedMoment B node4083 node4083Labels := rfl
  simpa [nodeValue4083, Sparse.eval] using hc.symm

theorem sound4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4084 node4084Labels = Sparse.eval nodeValue4084 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4084) = mixedMoment B node4084 node4084Labels := rfl
  simpa [nodeValue4084, Sparse.eval] using hc.symm

theorem sound4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4085 node4085Labels = Sparse.eval nodeValue4085 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4085) = mixedMoment B node4085 node4085Labels := rfl
  simpa [nodeValue4085, Sparse.eval] using hc.symm

theorem sound4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4092 node4092Labels = Sparse.eval nodeValue4092 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4092) = mixedMoment B node4092 node4092Labels := rfl
  simpa [nodeValue4092, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node590 node590Labels = Sparse.eval nodeValue590 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 590) = mixedMoment B node590 node590Labels := rfl
  simpa [nodeValue590, Sparse.eval] using hc.symm

theorem sound606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node606 node606Labels = Sparse.eval nodeValue606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 606) = mixedMoment B node606 node606Labels := rfl
  simpa [nodeValue606, Sparse.eval] using hc.symm

theorem sound612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node612 node612Labels = Sparse.eval nodeValue612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 612) = mixedMoment B node612 node612Labels := rfl
  simpa [nodeValue612, Sparse.eval] using hc.symm

theorem sound621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node621 node621Labels = Sparse.eval nodeValue621 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 621) = mixedMoment B node621 node621Labels := rfl
  simpa [nodeValue621, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources37
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1201 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1201 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 0) (sourceB1201 + difference 0 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 621) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 0) (sourceB1201 + difference 0 4) sourceC1201) = raw20088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20088; decide +kernel
    rw [ha]
    exact (canonical20088 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 1) (sourceB1201 + difference 1 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 1) (sourceB1201 + difference 1 4) sourceC1201) = raw20089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20089; decide +kernel
    rw [ha]
    exact (canonical20089 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 2) (sourceB1201 + difference 2 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 2) (sourceB1201 + difference 2 4) sourceC1201) = raw20090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20090; decide +kernel
    rw [ha]
    exact (canonical20090 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 3) (sourceB1201 + difference 3 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 940) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 3) (sourceB1201 + difference 3 4) sourceC1201) = raw20091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20091; decide +kernel
    rw [ha]
    exact (canonical20091 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 4) (sourceB1201 + difference 4 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1092) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 4) (sourceB1201 + difference 4 4) sourceC1201) = raw3521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw3521; decide +kernel
    rw [ha]
    exact (canonical3521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1201 + difference 4 5) (sourceB1201 + difference 5 4) sourceC1201) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1094) := by
    have ha : (tripleCharges (sourceA1201 + difference 4 5) (sourceB1201 + difference 5 4) sourceC1201) = raw20092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1201 sourceB1201 sourceC1201 difference raw20092; decide +kernel
    rw [ha]
    exact (canonical20092 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1201 + sourceB1201) sourceC1201) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4085) := by
    have ha : (doubleCharges (sourceA1201 + sourceB1201) sourceC1201) = raw3517 := by
      apply Matrix.ext; unfold doubleCharges sourceA1201 sourceB1201 sourceC1201 raw3517; decide +kernel
    rw [ha]
    exact (canonical3517 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1201 sourceB1201 sourceC1201
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1201, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1202 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1202 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 0) (sourceB1202 + difference 0 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 0) (sourceB1202 + difference 0 0) sourceC1202) = raw20093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20093; decide +kernel
    rw [ha]
    exact (canonical20093 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 1) (sourceB1202 + difference 1 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 1) (sourceB1202 + difference 1 0) sourceC1202) = raw20094 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20094; decide +kernel
    rw [ha]
    exact (canonical20094 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 2) (sourceB1202 + difference 2 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 2) (sourceB1202 + difference 2 0) sourceC1202) = raw20095 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20095; decide +kernel
    rw [ha]
    exact (canonical20095 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 3) (sourceB1202 + difference 3 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2064) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 3) (sourceB1202 + difference 3 0) sourceC1202) = raw20096 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20096; decide +kernel
    rw [ha]
    exact (canonical20096 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 4) (sourceB1202 + difference 4 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 4) (sourceB1202 + difference 4 0) sourceC1202) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1202 + difference 0 5) (sourceB1202 + difference 5 0) sourceC1202) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1093) := by
    have ha : (tripleCharges (sourceA1202 + difference 0 5) (sourceB1202 + difference 5 0) sourceC1202) = raw20098 := by
      apply Matrix.ext; unfold tripleCharges sourceA1202 sourceB1202 sourceC1202 difference raw20098; decide +kernel
    rw [ha]
    exact (canonical20098 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1202 + sourceB1202) sourceC1202) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1202 + sourceB1202) sourceC1202) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1202 sourceB1202 sourceC1202 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1202 sourceB1202 sourceC1202
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1202, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1203 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1203 + difference 0 4) (sourceB1203 + difference 4 0) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1203 + difference 0 4) (sourceB1203 + difference 4 0) sourceC1203) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1203 + difference 1 4) (sourceB1203 + difference 4 1) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1203 + difference 1 4) (sourceB1203 + difference 4 1) sourceC1203) = raw20100 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20100; decide +kernel
    rw [ha]
    exact (canonical20100 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1203 + difference 2 4) (sourceB1203 + difference 4 2) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1203 + difference 2 4) (sourceB1203 + difference 4 2) sourceC1203) = raw20101 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20101; decide +kernel
    rw [ha]
    exact (canonical20101 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1203 + difference 3 4) (sourceB1203 + difference 4 3) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1203 + difference 3 4) (sourceB1203 + difference 4 3) sourceC1203) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1203 + difference 4 4) (sourceB1203 + difference 4 4) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1203 + difference 4 4) (sourceB1203 + difference 4 4) sourceC1203) = raw20093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20093; decide +kernel
    rw [ha]
    exact (canonical20093 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1203 + difference 5 4) (sourceB1203 + difference 4 5) sourceC1203) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1203 + difference 5 4) (sourceB1203 + difference 4 5) sourceC1203) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1203 sourceB1203 sourceC1203 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1203 + sourceB1203) sourceC1203) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1203 + sourceB1203) sourceC1203) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1203 sourceB1203 sourceC1203 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1203 sourceB1203 sourceC1203
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1203, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1204 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1204 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 0) (sourceB1204 + difference 0 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 860) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 0) (sourceB1204 + difference 0 5) sourceC1204) = raw20104 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20104; decide +kernel
    rw [ha]
    exact (canonical20104 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 1) (sourceB1204 + difference 1 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 1) (sourceB1204 + difference 1 5) sourceC1204) = raw20105 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20105; decide +kernel
    rw [ha]
    exact (canonical20105 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 2) (sourceB1204 + difference 2 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 2) (sourceB1204 + difference 2 5) sourceC1204) = raw20106 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20106; decide +kernel
    rw [ha]
    exact (canonical20106 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 3) (sourceB1204 + difference 3 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1628) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 3) (sourceB1204 + difference 3 5) sourceC1204) = raw20107 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20107; decide +kernel
    rw [ha]
    exact (canonical20107 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 4) (sourceB1204 + difference 4 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 4) (sourceB1204 + difference 4 5) sourceC1204) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1204 + difference 5 5) (sourceB1204 + difference 5 5) sourceC1204) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1747) := by
    have ha : (tripleCharges (sourceA1204 + difference 5 5) (sourceB1204 + difference 5 5) sourceC1204) = raw20093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1204 sourceB1204 sourceC1204 difference raw20093; decide +kernel
    rw [ha]
    exact (canonical20093 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1204 + sourceB1204) sourceC1204) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1204 + sourceB1204) sourceC1204) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1204 sourceB1204 sourceC1204 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1204 sourceB1204 sourceC1204
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1204, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1205 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1205 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 0) (sourceB1205 + difference 0 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 612) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 0) (sourceB1205 + difference 0 3) sourceC1205) = raw20108 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20108; decide +kernel
    rw [ha]
    exact (canonical20108 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 1) (sourceB1205 + difference 1 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 1) (sourceB1205 + difference 1 3) sourceC1205) = raw20109 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20109; decide +kernel
    rw [ha]
    exact (canonical20109 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 2) (sourceB1205 + difference 2 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 931) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 2) (sourceB1205 + difference 2 3) sourceC1205) = raw20110 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20110; decide +kernel
    rw [ha]
    exact (canonical20110 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 3) (sourceB1205 + difference 3 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 3) (sourceB1205 + difference 3 3) sourceC1205) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 4) (sourceB1205 + difference 4 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1061) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 4) (sourceB1205 + difference 4 3) sourceC1205) = raw3633 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw3633; decide +kernel
    rw [ha]
    exact (canonical3633 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1205 + difference 3 5) (sourceB1205 + difference 5 3) sourceC1205) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1205 + difference 3 5) (sourceB1205 + difference 5 3) sourceC1205) = raw20111 := by
      apply Matrix.ext; unfold tripleCharges sourceA1205 sourceB1205 sourceC1205 difference raw20111; decide +kernel
    rw [ha]
    exact (canonical20111 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1205 + sourceB1205) sourceC1205) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1205 + sourceB1205) sourceC1205) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1205 sourceB1205 sourceC1205 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1205 sourceB1205 sourceC1205
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1205, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1206 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1206 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 0) (sourceB1206 + difference 0 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 590) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 0) (sourceB1206 + difference 0 4) sourceC1206) = raw20112 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20112; decide +kernel
    rw [ha]
    exact (canonical20112 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 1) (sourceB1206 + difference 1 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 1) (sourceB1206 + difference 1 4) sourceC1206) = raw20113 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20113; decide +kernel
    rw [ha]
    exact (canonical20113 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 2) (sourceB1206 + difference 2 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 914) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 2) (sourceB1206 + difference 2 4) sourceC1206) = raw20114 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20114; decide +kernel
    rw [ha]
    exact (canonical20114 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 3) (sourceB1206 + difference 3 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 954) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 3) (sourceB1206 + difference 3 4) sourceC1206) = raw20115 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20115; decide +kernel
    rw [ha]
    exact (canonical20115 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 4) (sourceB1206 + difference 4 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1047) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 4) (sourceB1206 + difference 4 4) sourceC1206) = raw3634 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw3634; decide +kernel
    rw [ha]
    exact (canonical3634 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1206 + difference 4 5) (sourceB1206 + difference 5 4) sourceC1206) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1049) := by
    have ha : (tripleCharges (sourceA1206 + difference 4 5) (sourceB1206 + difference 5 4) sourceC1206) = raw20116 := by
      apply Matrix.ext; unfold tripleCharges sourceA1206 sourceB1206 sourceC1206 difference raw20116; decide +kernel
    rw [ha]
    exact (canonical20116 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1206 + sourceB1206) sourceC1206) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1206 + sourceB1206) sourceC1206) = raw3630 := by
      apply Matrix.ext; unfold doubleCharges sourceA1206 sourceB1206 sourceC1206 raw3630; decide +kernel
    rw [ha]
    exact (canonical3630 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1206 sourceB1206 sourceC1206
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1206, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1207 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1207 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1207 + difference 0 3) (sourceB1207 + difference 3 0) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2112) := by
    have ha : (tripleCharges (sourceA1207 + difference 0 3) (sourceB1207 + difference 3 0) sourceC1207) = raw4762 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw4762; decide +kernel
    rw [ha]
    exact (canonical4762 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1207 + difference 1 3) (sourceB1207 + difference 3 1) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1207 + difference 1 3) (sourceB1207 + difference 3 1) sourceC1207) = raw20117 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20117; decide +kernel
    rw [ha]
    exact (canonical20117 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1207 + difference 2 3) (sourceB1207 + difference 3 2) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1207 + difference 2 3) (sourceB1207 + difference 3 2) sourceC1207) = raw20118 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20118; decide +kernel
    rw [ha]
    exact (canonical20118 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1207 + difference 3 3) (sourceB1207 + difference 3 3) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1408) := by
    have ha : (tripleCharges (sourceA1207 + difference 3 3) (sourceB1207 + difference 3 3) sourceC1207) = raw4748 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw4748; decide +kernel
    rw [ha]
    exact (canonical4748 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1207 + difference 4 3) (sourceB1207 + difference 3 4) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1348) := by
    have ha : (tripleCharges (sourceA1207 + difference 4 3) (sourceB1207 + difference 3 4) sourceC1207) = raw20119 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20119; decide +kernel
    rw [ha]
    exact (canonical20119 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1207 + difference 5 3) (sourceB1207 + difference 3 5) sourceC1207) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 951) := by
    have ha : (tripleCharges (sourceA1207 + difference 5 3) (sourceB1207 + difference 3 5) sourceC1207) = raw20120 := by
      apply Matrix.ext; unfold tripleCharges sourceA1207 sourceB1207 sourceC1207 difference raw20120; decide +kernel
    rw [ha]
    exact (canonical20120 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1207 + sourceB1207) sourceC1207) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1207 + sourceB1207) sourceC1207) = raw4744 := by
      apply Matrix.ext; unfold doubleCharges sourceA1207 sourceB1207 sourceC1207 raw4744; decide +kernel
    rw [ha]
    exact (canonical4744 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1207 sourceB1207 sourceC1207
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1207, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1208 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 0) (sourceB1208 + difference 0 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 0) (sourceB1208 + difference 0 0) sourceC1208) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 1) (sourceB1208 + difference 1 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 1) (sourceB1208 + difference 1 0) sourceC1208) = raw20121 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20121; decide +kernel
    rw [ha]
    exact (canonical20121 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 2) (sourceB1208 + difference 2 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2045) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 2) (sourceB1208 + difference 2 0) sourceC1208) = raw20122 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20122; decide +kernel
    rw [ha]
    exact (canonical20122 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 3) (sourceB1208 + difference 3 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2289) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 3) (sourceB1208 + difference 3 0) sourceC1208) = raw20097 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20097; decide +kernel
    rw [ha]
    exact (canonical20097 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 4) (sourceB1208 + difference 4 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 4) (sourceB1208 + difference 4 0) sourceC1208) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1208 + difference 0 5) (sourceB1208 + difference 5 0) sourceC1208) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1072) := by
    have ha : (tripleCharges (sourceA1208 + difference 0 5) (sourceB1208 + difference 5 0) sourceC1208) = raw20124 := by
      apply Matrix.ext; unfold tripleCharges sourceA1208 sourceB1208 sourceC1208 difference raw20124; decide +kernel
    rw [ha]
    exact (canonical20124 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1208 + sourceB1208) sourceC1208) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1208 + sourceB1208) sourceC1208) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1208 sourceB1208 sourceC1208 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1208 sourceB1208 sourceC1208
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1208, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1210 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1210 + difference 0 4) (sourceB1210 + difference 4 0) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1210 + difference 0 4) (sourceB1210 + difference 4 0) sourceC1210) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1210 + difference 1 4) (sourceB1210 + difference 4 1) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1210 + difference 1 4) (sourceB1210 + difference 4 1) sourceC1210) = raw20130 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20130; decide +kernel
    rw [ha]
    exact (canonical20130 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1210 + difference 2 4) (sourceB1210 + difference 4 2) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1210 + difference 2 4) (sourceB1210 + difference 4 2) sourceC1210) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1210 + difference 3 4) (sourceB1210 + difference 4 3) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1210 + difference 3 4) (sourceB1210 + difference 4 3) sourceC1210) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1210 + difference 4 4) (sourceB1210 + difference 4 4) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1210 + difference 4 4) (sourceB1210 + difference 4 4) sourceC1210) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1210 + difference 5 4) (sourceB1210 + difference 4 5) sourceC1210) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1210 + difference 5 4) (sourceB1210 + difference 4 5) sourceC1210) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1210 sourceB1210 sourceC1210 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1210 + sourceB1210) sourceC1210) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1210 + sourceB1210) sourceC1210) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1210 sourceB1210 sourceC1210 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1210 sourceB1210 sourceC1210
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1210, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1211 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 0) (sourceB1211 + difference 0 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 853) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 0) (sourceB1211 + difference 0 5) sourceC1211) = raw20129 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20129; decide +kernel
    rw [ha]
    exact (canonical20129 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 1) (sourceB1211 + difference 1 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 1) (sourceB1211 + difference 1 5) sourceC1211) = raw20134 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20134; decide +kernel
    rw [ha]
    exact (canonical20134 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 2) (sourceB1211 + difference 2 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1619) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 2) (sourceB1211 + difference 2 5) sourceC1211) = raw20135 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20135; decide +kernel
    rw [ha]
    exact (canonical20135 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 3) (sourceB1211 + difference 3 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1756) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 3) (sourceB1211 + difference 3 5) sourceC1211) = raw20103 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20103; decide +kernel
    rw [ha]
    exact (canonical20103 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 4) (sourceB1211 + difference 4 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 4) (sourceB1211 + difference 4 5) sourceC1211) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1211 + difference 5 5) (sourceB1211 + difference 5 5) sourceC1211) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1745) := by
    have ha : (tripleCharges (sourceA1211 + difference 5 5) (sourceB1211 + difference 5 5) sourceC1211) = raw20102 := by
      apply Matrix.ext; unfold tripleCharges sourceA1211 sourceB1211 sourceC1211 difference raw20102; decide +kernel
    rw [ha]
    exact (canonical20102 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1211 + sourceB1211) sourceC1211) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1211 + sourceB1211) sourceC1211) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1211 sourceB1211 sourceC1211 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1211 sourceB1211 sourceC1211
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1211, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1212 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 0) (sourceB1212 + difference 0 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 606) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 0) (sourceB1212 + difference 0 3) sourceC1212) = raw20136 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20136; decide +kernel
    rw [ha]
    exact (canonical20136 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 1) (sourceB1212 + difference 1 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 1) (sourceB1212 + difference 1 3) sourceC1212) = raw20137 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20137; decide +kernel
    rw [ha]
    exact (canonical20137 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 2) (sourceB1212 + difference 2 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 925) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 2) (sourceB1212 + difference 2 3) sourceC1212) = raw20138 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20138; decide +kernel
    rw [ha]
    exact (canonical20138 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 3) (sourceB1212 + difference 3 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1059) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 3) (sourceB1212 + difference 3 3) sourceC1212) = raw20139 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20139; decide +kernel
    rw [ha]
    exact (canonical20139 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 4) (sourceB1212 + difference 4 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1091) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 4) (sourceB1212 + difference 4 3) sourceC1212) = raw20140 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20140; decide +kernel
    rw [ha]
    exact (canonical20140 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1212 + difference 3 5) (sourceB1212 + difference 5 3) sourceC1212) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1212 + difference 3 5) (sourceB1212 + difference 5 3) sourceC1212) = raw20141 := by
      apply Matrix.ext; unfold tripleCharges sourceA1212 sourceB1212 sourceC1212 difference raw20141; decide +kernel
    rw [ha]
    exact (canonical20141 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1212 + sourceB1212) sourceC1212) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1212 + sourceB1212) sourceC1212) = raw20142 := by
      apply Matrix.ext; unfold doubleCharges sourceA1212 sourceB1212 sourceC1212 raw20142; decide +kernel
    rw [ha]
    exact (canonical20142 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1212 sourceB1212 sourceC1212
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1212, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1213 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1213 + difference 0 3) (sourceB1213 + difference 3 0) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1213 + difference 0 3) (sourceB1213 + difference 3 0) sourceC1213) = raw20143 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20143; decide +kernel
    rw [ha]
    exact (canonical20143 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1213 + difference 1 3) (sourceB1213 + difference 3 1) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1213 + difference 1 3) (sourceB1213 + difference 3 1) sourceC1213) = raw20144 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20144; decide +kernel
    rw [ha]
    exact (canonical20144 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1213 + difference 2 3) (sourceB1213 + difference 3 2) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1213 + difference 2 3) (sourceB1213 + difference 3 2) sourceC1213) = raw20145 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20145; decide +kernel
    rw [ha]
    exact (canonical20145 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1213 + difference 3 3) (sourceB1213 + difference 3 3) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1372) := by
    have ha : (tripleCharges (sourceA1213 + difference 3 3) (sourceB1213 + difference 3 3) sourceC1213) = raw8781 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw8781; decide +kernel
    rw [ha]
    exact (canonical8781 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1213 + difference 4 3) (sourceB1213 + difference 3 4) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1324) := by
    have ha : (tripleCharges (sourceA1213 + difference 4 3) (sourceB1213 + difference 3 4) sourceC1213) = raw20146 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20146; decide +kernel
    rw [ha]
    exact (canonical20146 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1213 + difference 5 3) (sourceB1213 + difference 3 5) sourceC1213) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1213 + difference 5 3) (sourceB1213 + difference 3 5) sourceC1213) = raw20147 := by
      apply Matrix.ext; unfold tripleCharges sourceA1213 sourceB1213 sourceC1213 difference raw20147; decide +kernel
    rw [ha]
    exact (canonical20147 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1213 + sourceB1213) sourceC1213) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1213 + sourceB1213) sourceC1213) = raw8776 := by
      apply Matrix.ext; unfold doubleCharges sourceA1213 sourceB1213 sourceC1213 raw8776; decide +kernel
    rw [ha]
    exact (canonical8776 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1213 sourceB1213 sourceC1213
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1213, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1214 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 0) (sourceB1214 + difference 0 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 0) (sourceB1214 + difference 0 0) sourceC1214) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 1) (sourceB1214 + difference 1 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 1) (sourceB1214 + difference 1 0) sourceC1214) = raw20149 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20149; decide +kernel
    rw [ha]
    exact (canonical20149 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 2) (sourceB1214 + difference 2 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3242) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 2) (sourceB1214 + difference 2 0) sourceC1214) = raw20150 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20150; decide +kernel
    rw [ha]
    exact (canonical20150 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 3) (sourceB1214 + difference 3 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 3) (sourceB1214 + difference 3 0) sourceC1214) = raw20151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20151; decide +kernel
    rw [ha]
    exact (canonical20151 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 4) (sourceB1214 + difference 4 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3247) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 4) (sourceB1214 + difference 4 0) sourceC1214) = raw20152 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20152; decide +kernel
    rw [ha]
    exact (canonical20152 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1214 + difference 0 5) (sourceB1214 + difference 5 0) sourceC1214) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1952) := by
    have ha : (tripleCharges (sourceA1214 + difference 0 5) (sourceB1214 + difference 5 0) sourceC1214) = raw20153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1214 sourceB1214 sourceC1214 difference raw20153; decide +kernel
    rw [ha]
    exact (canonical20153 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1214 + sourceB1214) sourceC1214) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1214 + sourceB1214) sourceC1214) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1214 sourceB1214 sourceC1214 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1214 sourceB1214 sourceC1214
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1214, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1215 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1215 + difference 0 0) (sourceB1215 + difference 0 0) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1215 + difference 0 0) (sourceB1215 + difference 0 0) sourceC1215) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1215 + difference 1 0) (sourceB1215 + difference 0 1) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA1215 + difference 1 0) (sourceB1215 + difference 0 1) sourceC1215) = raw20154 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20154; decide +kernel
    rw [ha]
    exact (canonical20154 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1215 + difference 2 0) (sourceB1215 + difference 0 2) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 808) := by
    have ha : (tripleCharges (sourceA1215 + difference 2 0) (sourceB1215 + difference 0 2) sourceC1215) = raw20155 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20155; decide +kernel
    rw [ha]
    exact (canonical20155 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1215 + difference 3 0) (sourceB1215 + difference 0 3) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 814) := by
    have ha : (tripleCharges (sourceA1215 + difference 3 0) (sourceB1215 + difference 0 3) sourceC1215) = raw20156 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20156; decide +kernel
    rw [ha]
    exact (canonical20156 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1215 + difference 4 0) (sourceB1215 + difference 0 4) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1215 + difference 4 0) (sourceB1215 + difference 0 4) sourceC1215) = raw20157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20157; decide +kernel
    rw [ha]
    exact (canonical20157 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1215 + difference 5 0) (sourceB1215 + difference 0 5) sourceC1215) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1215 + difference 5 0) (sourceB1215 + difference 0 5) sourceC1215) = raw20158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1215 sourceB1215 sourceC1215 difference raw20158; decide +kernel
    rw [ha]
    exact (canonical20158 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1215 + sourceB1215) sourceC1215) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1215 + sourceB1215) sourceC1215) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1215 sourceB1215 sourceC1215 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1215 sourceB1215 sourceC1215
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1215, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources38
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1216 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1216 + difference 0 3) (sourceB1216 + difference 3 0) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1216 + difference 0 3) (sourceB1216 + difference 3 0) sourceC1216) = raw20151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20151; decide +kernel
    rw [ha]
    exact (canonical20151 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1216 + difference 1 3) (sourceB1216 + difference 3 1) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1216 + difference 1 3) (sourceB1216 + difference 3 1) sourceC1216) = raw20159 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20159; decide +kernel
    rw [ha]
    exact (canonical20159 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1216 + difference 2 3) (sourceB1216 + difference 3 2) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1216 + difference 2 3) (sourceB1216 + difference 3 2) sourceC1216) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1216 + difference 3 3) (sourceB1216 + difference 3 3) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1216 + difference 3 3) (sourceB1216 + difference 3 3) sourceC1216) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1216 + difference 4 3) (sourceB1216 + difference 3 4) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1216 + difference 4 3) (sourceB1216 + difference 3 4) sourceC1216) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1216 + difference 5 3) (sourceB1216 + difference 3 5) sourceC1216) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1216 + difference 5 3) (sourceB1216 + difference 3 5) sourceC1216) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1216 sourceB1216 sourceC1216 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1216 + sourceB1216) sourceC1216) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1216 + sourceB1216) sourceC1216) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1216 sourceB1216 sourceC1216 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1216 sourceB1216 sourceC1216
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1216, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1217 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 0) (sourceB1217 + difference 0 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 857) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 0) (sourceB1217 + difference 0 4) sourceC1217) = raw20157 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20157; decide +kernel
    rw [ha]
    exact (canonical20157 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 1) (sourceB1217 + difference 1 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 1) (sourceB1217 + difference 1 4) sourceC1217) = raw20162 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20162; decide +kernel
    rw [ha]
    exact (canonical20162 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 2) (sourceB1217 + difference 2 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1624) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 2) (sourceB1217 + difference 2 4) sourceC1217) = raw20163 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20163; decide +kernel
    rw [ha]
    exact (canonical20163 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 3) (sourceB1217 + difference 3 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 3) (sourceB1217 + difference 3 4) sourceC1217) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 4) (sourceB1217 + difference 4 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 4) (sourceB1217 + difference 4 4) sourceC1217) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1217 + difference 4 5) (sourceB1217 + difference 5 4) sourceC1217) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1217 + difference 4 5) (sourceB1217 + difference 5 4) sourceC1217) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1217 sourceB1217 sourceC1217 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1217 + sourceB1217) sourceC1217) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1217 + sourceB1217) sourceC1217) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1217 sourceB1217 sourceC1217 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1217 sourceB1217 sourceC1217
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1217, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1040 : Integer.Sparse.reindex keyMap MixedData.row1040 = numericRow1040 := by decide +kernel

theorem numericCheck1040 (x : Master → ℝ) : Integer.Sparse.eval numericRow1040 x =
    (1 : ℝ) * reducedSource1040 x := by
  norm_num [numericRow1040, reducedSource1040, Integer.Sparse.eval, Sparse.eval, nodeValue621, nodeValue940, nodeValue1092, nodeValue1094, nodeValue4085]

theorem reindexCheck1041 : Integer.Sparse.reindex keyMap MixedData.row1041 = numericRow1041 := by decide +kernel

theorem numericCheck1041 (x : Master → ℝ) : Integer.Sparse.eval numericRow1041 x =
    (1 : ℝ) * reducedSource1041 x := by
  norm_num [numericRow1041, reducedSource1041, Integer.Sparse.eval, Sparse.eval, nodeValue1093, nodeValue1747, nodeValue2064, nodeValue2289, nodeValue4070]

theorem reindexCheck1042 : Integer.Sparse.reindex keyMap MixedData.row1042 = numericRow1042 := by decide +kernel

theorem numericCheck1042 (x : Master → ℝ) : Integer.Sparse.eval numericRow1042 x =
    (1 : ℝ) * reducedSource1042 x := by
  norm_num [numericRow1042, reducedSource1042, Integer.Sparse.eval, Sparse.eval, nodeValue1745, nodeValue1747, nodeValue1756, nodeValue2289, nodeValue4070]

theorem reindexCheck1043 : Integer.Sparse.reindex keyMap MixedData.row1043 = numericRow1043 := by decide +kernel

theorem numericCheck1043 (x : Master → ℝ) : Integer.Sparse.eval numericRow1043 x =
    (1 : ℝ) * reducedSource1043 x := by
  norm_num [numericRow1043, reducedSource1043, Integer.Sparse.eval, Sparse.eval, nodeValue860, nodeValue1628, nodeValue1747, nodeValue1756, nodeValue4070]

theorem reindexCheck1044 : Integer.Sparse.reindex keyMap MixedData.row1044 = numericRow1044 := by decide +kernel

theorem numericCheck1044 (x : Master → ℝ) : Integer.Sparse.eval numericRow1044 x =
    (1 : ℝ) * reducedSource1044 x := by
  norm_num [numericRow1044, reducedSource1044, Integer.Sparse.eval, Sparse.eval, nodeValue612, nodeValue931, nodeValue1047, nodeValue1061, nodeValue1087, nodeValue4084]

theorem reindexCheck1045 : Integer.Sparse.reindex keyMap MixedData.row1045 = numericRow1045 := by decide +kernel

theorem numericCheck1045 (x : Master → ℝ) : Integer.Sparse.eval numericRow1045 x =
    (1 : ℝ) * reducedSource1045 x := by
  norm_num [numericRow1045, reducedSource1045, Integer.Sparse.eval, Sparse.eval, nodeValue590, nodeValue914, nodeValue954, nodeValue1047, nodeValue1049, nodeValue4084]

theorem reindexCheck1046 : Integer.Sparse.reindex keyMap MixedData.row1046 = numericRow1046 := by decide +kernel

theorem numericCheck1046 (x : Master → ℝ) : Integer.Sparse.eval numericRow1046 x =
    (1 : ℝ) * reducedSource1046 x := by
  norm_num [numericRow1046, reducedSource1046, Integer.Sparse.eval, Sparse.eval, nodeValue951, nodeValue1336, nodeValue1348, nodeValue1408, nodeValue2112, nodeValue4083]

theorem reindexCheck1047 : Integer.Sparse.reindex keyMap MixedData.row1047 = numericRow1047 := by decide +kernel

theorem numericCheck1047 (x : Master → ℝ) : Integer.Sparse.eval numericRow1047 x =
    (1 : ℝ) * reducedSource1047 x := by
  norm_num [numericRow1047, reducedSource1047, Integer.Sparse.eval, Sparse.eval, nodeValue1072, nodeValue1745, nodeValue2045, nodeValue2226, nodeValue2289, nodeValue4070]

theorem reindexCheck1048 : Integer.Sparse.reindex keyMap MixedData.row1048 = numericRow1048 := by decide +kernel

theorem numericCheck1048 (x : Master → ℝ) : Integer.Sparse.eval numericRow1048 x =
    (1 : ℝ) * reducedSource1048 x := by
  norm_num [numericRow1048, reducedSource1048, Integer.Sparse.eval, Sparse.eval, nodeValue1744, nodeValue1745, nodeValue1746, nodeValue1750, nodeValue2226, nodeValue4070]

theorem reindexCheck1049 : Integer.Sparse.reindex keyMap MixedData.row1049 = numericRow1049 := by decide +kernel

theorem numericCheck1049 (x : Master → ℝ) : Integer.Sparse.eval numericRow1049 x =
    (1 : ℝ) * reducedSource1049 x := by
  norm_num [numericRow1049, reducedSource1049, Integer.Sparse.eval, Sparse.eval, nodeValue853, nodeValue1619, nodeValue1745, nodeValue1750, nodeValue1756, nodeValue4070]

theorem reindexCheck1050 : Integer.Sparse.reindex keyMap MixedData.row1050 = numericRow1050 := by decide +kernel

theorem numericCheck1050 (x : Master → ℝ) : Integer.Sparse.eval numericRow1050 x =
    (1 : ℝ) * reducedSource1050 x := by
  norm_num [numericRow1050, reducedSource1050, Integer.Sparse.eval, Sparse.eval, nodeValue606, nodeValue925, nodeValue1059, nodeValue1083, nodeValue1091, nodeValue4084]

theorem reindexCheck1051 : Integer.Sparse.reindex keyMap MixedData.row1051 = numericRow1051 := by decide +kernel

theorem numericCheck1051 (x : Master → ℝ) : Integer.Sparse.eval numericRow1051 x =
    (1 : ℝ) * reducedSource1051 x := by
  norm_num [numericRow1051, reducedSource1051, Integer.Sparse.eval, Sparse.eval, nodeValue1142, nodeValue1317, nodeValue1324, nodeValue1372, nodeValue2519, nodeValue4092]

theorem reindexCheck1052 : Integer.Sparse.reindex keyMap MixedData.row1052 = numericRow1052 := by decide +kernel

theorem numericCheck1052 (x : Master → ℝ) : Integer.Sparse.eval numericRow1052 x =
    (1 : ℝ) * reducedSource1052 x := by
  norm_num [numericRow1052, reducedSource1052, Integer.Sparse.eval, Sparse.eval, nodeValue1729, nodeValue1952, nodeValue3242, nodeValue3247, nodeValue3300, nodeValue4070]

theorem reindexCheck1053 : Integer.Sparse.reindex keyMap MixedData.row1053 = numericRow1053 := by decide +kernel

theorem numericCheck1053 (x : Master → ℝ) : Integer.Sparse.eval numericRow1053 x =
    (1 : ℝ) * reducedSource1053 x := by
  norm_num [numericRow1053, reducedSource1053, Integer.Sparse.eval, Sparse.eval, nodeValue808, nodeValue814, nodeValue815, nodeValue857, nodeValue1729, nodeValue4070]

theorem reindexCheck1054 : Integer.Sparse.reindex keyMap MixedData.row1054 = numericRow1054 := by decide +kernel

theorem numericCheck1054 (x : Master → ℝ) : Integer.Sparse.eval numericRow1054 x =
    (1 : ℝ) * reducedSource1054 x := by
  norm_num [numericRow1054, reducedSource1054, Integer.Sparse.eval, Sparse.eval, nodeValue1723, nodeValue1725, nodeValue1729, nodeValue1750, nodeValue3300, nodeValue4070]

theorem reindexCheck1055 : Integer.Sparse.reindex keyMap MixedData.row1055 = numericRow1055 := by decide +kernel

theorem numericCheck1055 (x : Master → ℝ) : Integer.Sparse.eval numericRow1055 x =
    (1 : ℝ) * reducedSource1055 x := by
  norm_num [numericRow1055, reducedSource1055, Integer.Sparse.eval, Sparse.eval, nodeValue857, nodeValue1624, nodeValue1729, nodeValue1746, nodeValue1750, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows65
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1040 (mixedVector B) = 0 := by
  have h621 : mixedVector B (Sum.inr 621) = Sparse.eval nodeValue621 (mixedVector B) := by
    change mixedMoment B node621 node621Labels = _
    exact sound621 B hB hF
  have h940 : mixedVector B (Sum.inr 940) = Sparse.eval nodeValue940 (mixedVector B) := by
    change mixedMoment B node940 node940Labels = _
    exact sound940 B hB hF
  have h1092 : mixedVector B (Sum.inr 1092) = Sparse.eval nodeValue1092 (mixedVector B) := by
    change mixedMoment B node1092 node1092Labels = _
    exact sound1092 B hB hF
  have h1094 : mixedVector B (Sum.inr 1094) = Sparse.eval nodeValue1094 (mixedVector B) := by
    change mixedMoment B node1094 node1094Labels = _
    exact sound1094 B hB hF
  have h4085 : mixedVector B (Sum.inr 4085) = Sparse.eval nodeValue4085 (mixedVector B) := by
    change mixedMoment B node4085 node4085Labels = _
    exact sound4085 B hB hF
  simpa only [sourceForm1201, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h621, h940, h1092, h1094, h4085, reducedSource1040] using sourceEq1201 B hB

theorem rowSound1040 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1040 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1040, numericCheck1040, reducedZero1040 B hB hF, mul_zero]

theorem reducedZero1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1041 (mixedVector B) = 0 := by
  have h1093 : mixedVector B (Sum.inr 1093) = Sparse.eval nodeValue1093 (mixedVector B) := by
    change mixedMoment B node1093 node1093Labels = _
    exact sound1093 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h2064 : mixedVector B (Sum.inr 2064) = Sparse.eval nodeValue2064 (mixedVector B) := by
    change mixedMoment B node2064 node2064Labels = _
    exact sound2064 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1202, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1093, h1747, h2064, h2289, h4070, reducedSource1041] using sourceEq1202 B hB

theorem rowSound1041 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1041 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1041, numericCheck1041, reducedZero1041 B hB hF, mul_zero]

theorem reducedZero1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1042 (mixedVector B) = 0 := by
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1203, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1745, h1747, h1756, h2289, h4070, reducedSource1042] using sourceEq1203 B hB

theorem rowSound1042 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1042 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1042, numericCheck1042, reducedZero1042 B hB hF, mul_zero]

theorem reducedZero1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1043 (mixedVector B) = 0 := by
  have h860 : mixedVector B (Sum.inr 860) = Sparse.eval nodeValue860 (mixedVector B) := by
    change mixedMoment B node860 node860Labels = _
    exact sound860 B hB hF
  have h1628 : mixedVector B (Sum.inr 1628) = Sparse.eval nodeValue1628 (mixedVector B) := by
    change mixedMoment B node1628 node1628Labels = _
    exact sound1628 B hB hF
  have h1747 : mixedVector B (Sum.inr 1747) = Sparse.eval nodeValue1747 (mixedVector B) := by
    change mixedMoment B node1747 node1747Labels = _
    exact sound1747 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1204, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h860, h1628, h1747, h1756, h4070, reducedSource1043] using sourceEq1204 B hB

theorem rowSound1043 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1043 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1043, numericCheck1043, reducedZero1043 B hB hF, mul_zero]

theorem reducedZero1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1044 (mixedVector B) = 0 := by
  have h612 : mixedVector B (Sum.inr 612) = Sparse.eval nodeValue612 (mixedVector B) := by
    change mixedMoment B node612 node612Labels = _
    exact sound612 B hB hF
  have h931 : mixedVector B (Sum.inr 931) = Sparse.eval nodeValue931 (mixedVector B) := by
    change mixedMoment B node931 node931Labels = _
    exact sound931 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1061 : mixedVector B (Sum.inr 1061) = Sparse.eval nodeValue1061 (mixedVector B) := by
    change mixedMoment B node1061 node1061Labels = _
    exact sound1061 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1205, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h612, h931, h1047, h1061, h1087, h4084, reducedSource1044] using sourceEq1205 B hB

theorem rowSound1044 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1044 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1044, numericCheck1044, reducedZero1044 B hB hF, mul_zero]

theorem reducedZero1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1045 (mixedVector B) = 0 := by
  have h590 : mixedVector B (Sum.inr 590) = Sparse.eval nodeValue590 (mixedVector B) := by
    change mixedMoment B node590 node590Labels = _
    exact sound590 B hB hF
  have h914 : mixedVector B (Sum.inr 914) = Sparse.eval nodeValue914 (mixedVector B) := by
    change mixedMoment B node914 node914Labels = _
    exact sound914 B hB hF
  have h954 : mixedVector B (Sum.inr 954) = Sparse.eval nodeValue954 (mixedVector B) := by
    change mixedMoment B node954 node954Labels = _
    exact sound954 B hB hF
  have h1047 : mixedVector B (Sum.inr 1047) = Sparse.eval nodeValue1047 (mixedVector B) := by
    change mixedMoment B node1047 node1047Labels = _
    exact sound1047 B hB hF
  have h1049 : mixedVector B (Sum.inr 1049) = Sparse.eval nodeValue1049 (mixedVector B) := by
    change mixedMoment B node1049 node1049Labels = _
    exact sound1049 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1206, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h590, h914, h954, h1047, h1049, h4084, reducedSource1045] using sourceEq1206 B hB

theorem rowSound1045 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1045 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1045, numericCheck1045, reducedZero1045 B hB hF, mul_zero]

theorem reducedZero1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1046 (mixedVector B) = 0 := by
  have h951 : mixedVector B (Sum.inr 951) = Sparse.eval nodeValue951 (mixedVector B) := by
    change mixedMoment B node951 node951Labels = _
    exact sound951 B hB hF
  have h1336 : mixedVector B (Sum.inr 1336) = Sparse.eval nodeValue1336 (mixedVector B) := by
    change mixedMoment B node1336 node1336Labels = _
    exact sound1336 B hB hF
  have h1348 : mixedVector B (Sum.inr 1348) = Sparse.eval nodeValue1348 (mixedVector B) := by
    change mixedMoment B node1348 node1348Labels = _
    exact sound1348 B hB hF
  have h1408 : mixedVector B (Sum.inr 1408) = Sparse.eval nodeValue1408 (mixedVector B) := by
    change mixedMoment B node1408 node1408Labels = _
    exact sound1408 B hB hF
  have h2112 : mixedVector B (Sum.inr 2112) = Sparse.eval nodeValue2112 (mixedVector B) := by
    change mixedMoment B node2112 node2112Labels = _
    exact sound2112 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1207, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h951, h1336, h1348, h1408, h2112, h4083, reducedSource1046] using sourceEq1207 B hB

theorem rowSound1046 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1046 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1046, numericCheck1046, reducedZero1046 B hB hF, mul_zero]

theorem reducedZero1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1047 (mixedVector B) = 0 := by
  have h1072 : mixedVector B (Sum.inr 1072) = Sparse.eval nodeValue1072 (mixedVector B) := by
    change mixedMoment B node1072 node1072Labels = _
    exact sound1072 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h2045 : mixedVector B (Sum.inr 2045) = Sparse.eval nodeValue2045 (mixedVector B) := by
    change mixedMoment B node2045 node2045Labels = _
    exact sound2045 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h2289 : mixedVector B (Sum.inr 2289) = Sparse.eval nodeValue2289 (mixedVector B) := by
    change mixedMoment B node2289 node2289Labels = _
    exact sound2289 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1208, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1072, h1745, h2045, h2226, h2289, h4070, reducedSource1047] using sourceEq1208 B hB

theorem rowSound1047 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1047 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1047, numericCheck1047, reducedZero1047 B hB hF, mul_zero]

theorem reducedZero1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1048 (mixedVector B) = 0 := by
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1210, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1744, h1745, h1746, h1750, h2226, h4070, reducedSource1048] using sourceEq1210 B hB

theorem rowSound1048 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1048 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1048, numericCheck1048, reducedZero1048 B hB hF, mul_zero]

theorem reducedZero1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1049 (mixedVector B) = 0 := by
  have h853 : mixedVector B (Sum.inr 853) = Sparse.eval nodeValue853 (mixedVector B) := by
    change mixedMoment B node853 node853Labels = _
    exact sound853 B hB hF
  have h1619 : mixedVector B (Sum.inr 1619) = Sparse.eval nodeValue1619 (mixedVector B) := by
    change mixedMoment B node1619 node1619Labels = _
    exact sound1619 B hB hF
  have h1745 : mixedVector B (Sum.inr 1745) = Sparse.eval nodeValue1745 (mixedVector B) := by
    change mixedMoment B node1745 node1745Labels = _
    exact sound1745 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h1756 : mixedVector B (Sum.inr 1756) = Sparse.eval nodeValue1756 (mixedVector B) := by
    change mixedMoment B node1756 node1756Labels = _
    exact sound1756 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1211, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h853, h1619, h1745, h1750, h1756, h4070, reducedSource1049] using sourceEq1211 B hB

theorem rowSound1049 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1049 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1049, numericCheck1049, reducedZero1049 B hB hF, mul_zero]

theorem reducedZero1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1050 (mixedVector B) = 0 := by
  have h606 : mixedVector B (Sum.inr 606) = Sparse.eval nodeValue606 (mixedVector B) := by
    change mixedMoment B node606 node606Labels = _
    exact sound606 B hB hF
  have h925 : mixedVector B (Sum.inr 925) = Sparse.eval nodeValue925 (mixedVector B) := by
    change mixedMoment B node925 node925Labels = _
    exact sound925 B hB hF
  have h1059 : mixedVector B (Sum.inr 1059) = Sparse.eval nodeValue1059 (mixedVector B) := by
    change mixedMoment B node1059 node1059Labels = _
    exact sound1059 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h1091 : mixedVector B (Sum.inr 1091) = Sparse.eval nodeValue1091 (mixedVector B) := by
    change mixedMoment B node1091 node1091Labels = _
    exact sound1091 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1212, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h606, h925, h1059, h1083, h1091, h4084, reducedSource1050] using sourceEq1212 B hB

theorem rowSound1050 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1050 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1050, numericCheck1050, reducedZero1050 B hB hF, mul_zero]

theorem reducedZero1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1051 (mixedVector B) = 0 := by
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h1324 : mixedVector B (Sum.inr 1324) = Sparse.eval nodeValue1324 (mixedVector B) := by
    change mixedMoment B node1324 node1324Labels = _
    exact sound1324 B hB hF
  have h1372 : mixedVector B (Sum.inr 1372) = Sparse.eval nodeValue1372 (mixedVector B) := by
    change mixedMoment B node1372 node1372Labels = _
    exact sound1372 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1213, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1142, h1317, h1324, h1372, h2519, h4092, reducedSource1051] using sourceEq1213 B hB

theorem rowSound1051 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1051 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1051, numericCheck1051, reducedZero1051 B hB hF, mul_zero]

theorem reducedZero1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1052 (mixedVector B) = 0 := by
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1952 : mixedVector B (Sum.inr 1952) = Sparse.eval nodeValue1952 (mixedVector B) := by
    change mixedMoment B node1952 node1952Labels = _
    exact sound1952 B hB hF
  have h3242 : mixedVector B (Sum.inr 3242) = Sparse.eval nodeValue3242 (mixedVector B) := by
    change mixedMoment B node3242 node3242Labels = _
    exact sound3242 B hB hF
  have h3247 : mixedVector B (Sum.inr 3247) = Sparse.eval nodeValue3247 (mixedVector B) := by
    change mixedMoment B node3247 node3247Labels = _
    exact sound3247 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1214, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1729, h1952, h3242, h3247, h3300, h4070, reducedSource1052] using sourceEq1214 B hB

theorem rowSound1052 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1052 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1052, numericCheck1052, reducedZero1052 B hB hF, mul_zero]

theorem reducedZero1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1053 (mixedVector B) = 0 := by
  have h808 : mixedVector B (Sum.inr 808) = Sparse.eval nodeValue808 (mixedVector B) := by
    change mixedMoment B node808 node808Labels = _
    exact sound808 B hB hF
  have h814 : mixedVector B (Sum.inr 814) = Sparse.eval nodeValue814 (mixedVector B) := by
    change mixedMoment B node814 node814Labels = _
    exact sound814 B hB hF
  have h815 : mixedVector B (Sum.inr 815) = Sparse.eval nodeValue815 (mixedVector B) := by
    change mixedMoment B node815 node815Labels = _
    exact sound815 B hB hF
  have h857 : mixedVector B (Sum.inr 857) = Sparse.eval nodeValue857 (mixedVector B) := by
    change mixedMoment B node857 node857Labels = _
    exact sound857 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1215, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h808, h814, h815, h857, h1729, h4070, reducedSource1053] using sourceEq1215 B hB

theorem rowSound1053 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1053 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1053, numericCheck1053, reducedZero1053 B hB hF, mul_zero]

theorem reducedZero1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1054 (mixedVector B) = 0 := by
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1216, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1723, h1725, h1729, h1750, h3300, h4070, reducedSource1054] using sourceEq1216 B hB

theorem rowSound1054 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1054 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1054, numericCheck1054, reducedZero1054 B hB hF, mul_zero]

theorem reducedZero1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1055 (mixedVector B) = 0 := by
  have h857 : mixedVector B (Sum.inr 857) = Sparse.eval nodeValue857 (mixedVector B) := by
    change mixedMoment B node857 node857Labels = _
    exact sound857 B hB hF
  have h1624 : mixedVector B (Sum.inr 1624) = Sparse.eval nodeValue1624 (mixedVector B) := by
    change mixedMoment B node1624 node1624Labels = _
    exact sound1624 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1217, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h857, h1624, h1729, h1746, h1750, h4070, reducedSource1055] using sourceEq1217 B hB

theorem rowSound1055 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1055 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1055, numericCheck1055, reducedZero1055 B hB hF, mul_zero]

theorem sourceRowsAt1040 : MixedData.sourceRows (1040 : Fin 2425) =
    MixedData.row1040 := by decide +kernel

theorem sourceRowsAt1041 : MixedData.sourceRows (1041 : Fin 2425) =
    MixedData.row1041 := by decide +kernel

theorem sourceRowsAt1042 : MixedData.sourceRows (1042 : Fin 2425) =
    MixedData.row1042 := by decide +kernel

theorem sourceRowsAt1043 : MixedData.sourceRows (1043 : Fin 2425) =
    MixedData.row1043 := by decide +kernel

theorem sourceRowsAt1044 : MixedData.sourceRows (1044 : Fin 2425) =
    MixedData.row1044 := by decide +kernel

theorem sourceRowsAt1045 : MixedData.sourceRows (1045 : Fin 2425) =
    MixedData.row1045 := by decide +kernel

theorem sourceRowsAt1046 : MixedData.sourceRows (1046 : Fin 2425) =
    MixedData.row1046 := by decide +kernel

theorem sourceRowsAt1047 : MixedData.sourceRows (1047 : Fin 2425) =
    MixedData.row1047 := by decide +kernel

theorem sourceRowsAt1048 : MixedData.sourceRows (1048 : Fin 2425) =
    MixedData.row1048 := by decide +kernel

theorem sourceRowsAt1049 : MixedData.sourceRows (1049 : Fin 2425) =
    MixedData.row1049 := by decide +kernel

theorem sourceRowsAt1050 : MixedData.sourceRows (1050 : Fin 2425) =
    MixedData.row1050 := by decide +kernel

theorem sourceRowsAt1051 : MixedData.sourceRows (1051 : Fin 2425) =
    MixedData.row1051 := by decide +kernel

theorem sourceRowsAt1052 : MixedData.sourceRows (1052 : Fin 2425) =
    MixedData.row1052 := by decide +kernel

theorem sourceRowsAt1053 : MixedData.sourceRows (1053 : Fin 2425) =
    MixedData.row1053 := by decide +kernel

theorem sourceRowsAt1054 : MixedData.sourceRows (1054 : Fin 2425) =
    MixedData.row1054 := by decide +kernel

theorem sourceRowsAt1055 : MixedData.sourceRows (1055 : Fin 2425) =
    MixedData.row1055 := by decide +kernel

theorem chunkSound65_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 65) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1040 ∨ k.val = 1041 ∨ k.val = 1042 ∨ k.val = 1043 ∨ k.val = 1044 ∨ k.val = 1045 ∨ k.val = 1046 ∨ k.val = 1047 ∨ k.val = 1048 ∨ k.val = 1049 ∨ k.val = 1050 ∨ k.val = 1051 ∨ k.val = 1052 ∨ k.val = 1053 ∨ k.val = 1054 ∨ k.val = 1055 := by omega
  rcases heq with h1040 | h1041 | h1042 | h1043 | h1044 | h1045 | h1046 | h1047 | h1048 | h1049 | h1050 | h1051 | h1052 | h1053 | h1054 | h1055
  · have he : k = (1040 : Fin 2425) := Fin.ext h1040
    subst k
    rw [sourceRowsAt1040]
    exact rowSound1040 B hB hF
  · have he : k = (1041 : Fin 2425) := Fin.ext h1041
    subst k
    rw [sourceRowsAt1041]
    exact rowSound1041 B hB hF
  · have he : k = (1042 : Fin 2425) := Fin.ext h1042
    subst k
    rw [sourceRowsAt1042]
    exact rowSound1042 B hB hF
  · have he : k = (1043 : Fin 2425) := Fin.ext h1043
    subst k
    rw [sourceRowsAt1043]
    exact rowSound1043 B hB hF
  · have he : k = (1044 : Fin 2425) := Fin.ext h1044
    subst k
    rw [sourceRowsAt1044]
    exact rowSound1044 B hB hF
  · have he : k = (1045 : Fin 2425) := Fin.ext h1045
    subst k
    rw [sourceRowsAt1045]
    exact rowSound1045 B hB hF
  · have he : k = (1046 : Fin 2425) := Fin.ext h1046
    subst k
    rw [sourceRowsAt1046]
    exact rowSound1046 B hB hF
  · have he : k = (1047 : Fin 2425) := Fin.ext h1047
    subst k
    rw [sourceRowsAt1047]
    exact rowSound1047 B hB hF
  · have he : k = (1048 : Fin 2425) := Fin.ext h1048
    subst k
    rw [sourceRowsAt1048]
    exact rowSound1048 B hB hF
  · have he : k = (1049 : Fin 2425) := Fin.ext h1049
    subst k
    rw [sourceRowsAt1049]
    exact rowSound1049 B hB hF
  · have he : k = (1050 : Fin 2425) := Fin.ext h1050
    subst k
    rw [sourceRowsAt1050]
    exact rowSound1050 B hB hF
  · have he : k = (1051 : Fin 2425) := Fin.ext h1051
    subst k
    rw [sourceRowsAt1051]
    exact rowSound1051 B hB hF
  · have he : k = (1052 : Fin 2425) := Fin.ext h1052
    subst k
    rw [sourceRowsAt1052]
    exact rowSound1052 B hB hF
  · have he : k = (1053 : Fin 2425) := Fin.ext h1053
    subst k
    rw [sourceRowsAt1053]
    exact rowSound1053 B hB hF
  · have he : k = (1054 : Fin 2425) := Fin.ext h1054
    subst k
    rw [sourceRowsAt1054]
    exact rowSound1054 B hB hF
  · have he : k = (1055 : Fin 2425) := Fin.ext h1055
    subst k
    rw [sourceRowsAt1055]
    exact rowSound1055 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound65_e_oai
