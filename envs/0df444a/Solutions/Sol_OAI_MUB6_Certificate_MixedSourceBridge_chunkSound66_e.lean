-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:29:45.361127+00:00
-- url     : https://prove2.me/submissions/68068c4c-50ba-4d4f-8734-d3734fcfe30f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E110
import Definitions.Def_OAIQ106E111
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical157
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

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

theorem canonical20164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20164 raw20164Labels = mixedMoment B node1604 node1604Labels := by
  calc
    mixedMoment B raw20164 raw20164Labels = mixedMoment B raw20164step0 raw20164step0Labels := by
      have hz : ∀ j, raw20164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20164step0 = (fun i j => raw20164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20164step0 raw20164; decide +kernel
      have hl : raw20164step0Labels = raw20164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20164 raw20164Labels permutation346 hz
    mixedMoment B raw20164step0 raw20164step0Labels = mixedMoment B raw20164step1 raw20164step1Labels := by
      have ha : raw20164step1 = (fun i j => raw20164step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20164step1 raw20164step0; decide +kernel
      have hl : raw20164step1Labels = raw20164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20164step0 raw20164step0Labels permutation34 permutation4
    mixedMoment B raw20164step1 raw20164step1Labels = mixedMoment B raw20164step2 raw20164step2Labels := by
      have ha : raw20164step2 = -raw20164step1 := by apply Matrix.ext; change ∀ i j, raw20164step2 i j = -(raw20164step1 i j); unfold raw20164step2 raw20164step1; decide +kernel
      have hl : raw20164step2Labels = raw20164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1604 node1604Labels := by rfl

theorem canonical20165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20165 raw20165Labels = mixedMoment B node1604 node1604Labels := by
  calc
    mixedMoment B raw20165 raw20165Labels = mixedMoment B raw20165step0 raw20165step0Labels := by
      have hz : ∀ j, raw20165 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20165step0 = (fun i j => raw20165 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20165step0 raw20165; decide +kernel
      have hl : raw20165step0Labels = raw20165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20165 raw20165Labels permutation265 hz
    mixedMoment B raw20165step0 raw20165step0Labels = mixedMoment B raw20165step1 raw20165step1Labels := by
      have ha : raw20165step1 = (fun i j => raw20165step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20165step1 raw20165step0; decide +kernel
      have hl : raw20165step1Labels = raw20165step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20165step0 raw20165step0Labels permutation34 permutation4
    mixedMoment B raw20165step1 raw20165step1Labels = mixedMoment B raw20165step2 raw20165step2Labels := by
      have ha : raw20165step2 = -raw20165step1 := by apply Matrix.ext; change ∀ i j, raw20165step2 i j = -(raw20165step1 i j); unfold raw20165step2 raw20165step1; decide +kernel
      have hl : raw20165step2Labels = raw20165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1604 node1604Labels := by rfl

theorem canonical20166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20166 raw20166Labels = mixedMoment B node1652 node1652Labels := by
  calc
    mixedMoment B raw20166 raw20166Labels = mixedMoment B raw20166step0 raw20166step0Labels := by
      have hz : ∀ j, raw20166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20166step0 = (fun i j => raw20166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20166step0 raw20166; decide +kernel
      have hl : raw20166step0Labels = raw20166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20166 raw20166Labels permutation346 hz
    mixedMoment B raw20166step0 raw20166step0Labels = mixedMoment B raw20166step1 raw20166step1Labels := by
      have hz : ∀ j, raw20166step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20166step1 = (fun i j => raw20166step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20166step1 raw20166step0; decide +kernel
      have hl : raw20166step1Labels = raw20166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20166step0 raw20166step0Labels permutation56 hz
    mixedMoment B raw20166step1 raw20166step1Labels = mixedMoment B raw20166step2 raw20166step2Labels := by
      have ha : raw20166step2 = (fun i j => raw20166step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20166step2 raw20166step1; decide +kernel
      have hl : raw20166step2Labels = raw20166step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20166step1 raw20166step1Labels permutation10 permutation4
    mixedMoment B raw20166step2 raw20166step2Labels = mixedMoment B raw20166step3 raw20166step3Labels := by
      have ha : raw20166step3 = -raw20166step2 := by apply Matrix.ext; change ∀ i j, raw20166step3 i j = -(raw20166step2 i j); unfold raw20166step3 raw20166step2; decide +kernel
      have hl : raw20166step3Labels = raw20166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1652 node1652Labels := by rfl

theorem canonical20170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20170 raw20170Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw20170 raw20170Labels = mixedMoment B raw20170step0 raw20170step0Labels := by
      have hz : ∀ j, raw20170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20170step0 = (fun i j => raw20170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20170step0 raw20170; decide +kernel
      have hl : raw20170step0Labels = raw20170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20170 raw20170Labels permutation346 hz
    mixedMoment B raw20170step0 raw20170step0Labels = mixedMoment B raw20170step1 raw20170step1Labels := by
      have hz : ∀ j, raw20170step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20170step1 = (fun i j => raw20170step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20170step1 raw20170step0; decide +kernel
      have hl : raw20170step1Labels = raw20170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20170step0 raw20170step0Labels permutation56 hz
    mixedMoment B raw20170step1 raw20170step1Labels = mixedMoment B raw20170step2 raw20170step2Labels := by
      have ha : raw20170step2 = (fun i j => raw20170step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20170step2 raw20170step1; decide +kernel
      have hl : raw20170step2Labels = raw20170step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20170step1 raw20170step1Labels permutation31 permutation2
    mixedMoment B raw20170step2 raw20170step2Labels = mixedMoment B raw20170step3 raw20170step3Labels := by
      have ha : raw20170step3 = -raw20170step2 := by apply Matrix.ext; change ∀ i j, raw20170step3 i j = -(raw20170step2 i j); unfold raw20170step3 raw20170step2; decide +kernel
      have hl : raw20170step3Labels = raw20170step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical20171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20171 raw20171Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw20171 raw20171Labels = mixedMoment B raw20171step0 raw20171step0Labels := by
      have hz : ∀ j, raw20171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20171step0 = (fun i j => raw20171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20171step0 raw20171; decide +kernel
      have hl : raw20171step0Labels = raw20171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20171 raw20171Labels permutation346 hz
    mixedMoment B raw20171step0 raw20171step0Labels = mixedMoment B raw20171step1 raw20171step1Labels := by
      have ha : raw20171step1 = (fun i j => raw20171step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20171step1 raw20171step0; decide +kernel
      have hl : raw20171step1Labels = raw20171step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20171step0 raw20171step0Labels permutation38 permutation2
    _ = mixedMoment B node1315 node1315Labels := by rfl

theorem canonical20172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20172 raw20172Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw20172 raw20172Labels = mixedMoment B raw20172step0 raw20172step0Labels := by
      have hz : ∀ j, raw20172 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20172step0 = (fun i j => raw20172 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20172step0 raw20172; decide +kernel
      have hl : raw20172step0Labels = raw20172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20172 raw20172Labels permutation265 hz
    mixedMoment B raw20172step0 raw20172step0Labels = mixedMoment B raw20172step1 raw20172step1Labels := by
      have ha : raw20172step1 = (fun i j => raw20172step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20172step1 raw20172step0; decide +kernel
      have hl : raw20172step1Labels = raw20172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20172step0 raw20172step0Labels permutation38 permutation2
    _ = mixedMoment B node1315 node1315Labels := by rfl

theorem canonical20173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20173 raw20173Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw20173 raw20173Labels = mixedMoment B raw20173step0 raw20173step0Labels := by
      have hz : ∀ j, raw20173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20173step0 = (fun i j => raw20173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20173step0 raw20173; decide +kernel
      have hl : raw20173step0Labels = raw20173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20173 raw20173Labels permutation346 hz
    mixedMoment B raw20173step0 raw20173step0Labels = mixedMoment B raw20173step1 raw20173step1Labels := by
      have hz : ∀ j, raw20173step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20173step1 = (fun i j => raw20173step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20173step1 raw20173step0; decide +kernel
      have hl : raw20173step1Labels = raw20173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20173step0 raw20173step0Labels permutation56 hz
    _ = mixedMoment B node1369 node1369Labels := by rfl

theorem canonical20174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20174 raw20174Labels = mixedMoment B node1323 node1323Labels := by
  calc
    mixedMoment B raw20174 raw20174Labels = mixedMoment B raw20174step0 raw20174step0Labels := by
      have hz : ∀ j, raw20174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20174step0 = (fun i j => raw20174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20174step0 raw20174; decide +kernel
      have hl : raw20174step0Labels = raw20174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20174 raw20174Labels permutation346 hz
    mixedMoment B raw20174step0 raw20174step0Labels = mixedMoment B raw20174step1 raw20174step1Labels := by
      have hz : ∀ j, raw20174step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20174step1 = (fun i j => raw20174step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20174step1 raw20174step0; decide +kernel
      have hl : raw20174step1Labels = raw20174step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20174step0 raw20174step0Labels permutation56 hz
    _ = mixedMoment B node1323 node1323Labels := by rfl

theorem canonical20175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20175 raw20175Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw20175 raw20175Labels = mixedMoment B raw20175step0 raw20175step0Labels := by
      have hz : ∀ j, raw20175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20175step0 = (fun i j => raw20175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20175step0 raw20175; decide +kernel
      have hl : raw20175step0Labels = raw20175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20175 raw20175Labels permutation346 hz
    mixedMoment B raw20175step0 raw20175step0Labels = mixedMoment B raw20175step1 raw20175step1Labels := by
      have hz : ∀ j, raw20175step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20175step1 = (fun i j => raw20175step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20175step1 raw20175step0; decide +kernel
      have hl : raw20175step1Labels = raw20175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20175step0 raw20175step0Labels permutation56 hz
    mixedMoment B raw20175step1 raw20175step1Labels = mixedMoment B raw20175step2 raw20175step2Labels := by
      have ha : raw20175step2 = (fun i j => raw20175step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20175step2 raw20175step1; decide +kernel
      have hl : raw20175step2Labels = raw20175step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20175step1 raw20175step1Labels permutation31 permutation2
    mixedMoment B raw20175step2 raw20175step2Labels = mixedMoment B raw20175step3 raw20175step3Labels := by
      have ha : raw20175step3 = -raw20175step2 := by apply Matrix.ext; change ∀ i j, raw20175step3 i j = -(raw20175step2 i j); unfold raw20175step3 raw20175step2; decide +kernel
      have hl : raw20175step3Labels = raw20175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node936 node936Labels := by rfl

theorem canonical20176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20176 raw20176Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20176 raw20176Labels = mixedMoment B raw20176step0 raw20176step0Labels := by
      have hz : ∀ j, raw20176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20176step0 = (fun i j => raw20176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20176step0 raw20176; decide +kernel
      have hl : raw20176step0Labels = raw20176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20176 raw20176Labels permutation520 hz
    mixedMoment B raw20176step0 raw20176step0Labels = mixedMoment B raw20176step1 raw20176step1Labels := by
      have hz : ∀ j, raw20176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20176step1 = (fun i j => raw20176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20176step1 raw20176step0; decide +kernel
      have hl : raw20176step1Labels = raw20176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20176step0 raw20176step0Labels permutation80 hz
    mixedMoment B raw20176step1 raw20176step1Labels = mixedMoment B raw20176step2 raw20176step2Labels := by
      have hz : ∀ j, raw20176step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20176step2 = (fun i j => raw20176step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20176step2 raw20176step1; decide +kernel
      have hl : raw20176step2Labels = raw20176step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20176step1 raw20176step1Labels permutation14 hz
    mixedMoment B raw20176step2 raw20176step2Labels = mixedMoment B raw20176step3 raw20176step3Labels := by
      have ha : raw20176step3 = (fun i j => raw20176step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20176step3 raw20176step2; decide +kernel
      have hl : raw20176step3Labels = raw20176step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20176step2 raw20176step2Labels permutation6 permutation0
    mixedMoment B raw20176step3 raw20176step3Labels = mixedMoment B raw20176step4 raw20176step4Labels := by
      have ha : raw20176step4 = -raw20176step3 := by apply Matrix.ext; change ∀ i j, raw20176step4 i j = -(raw20176step3 i j); unfold raw20176step4 raw20176step3; decide +kernel
      have hl : raw20176step4Labels = raw20176step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical20177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20177 raw20177Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw20177 raw20177Labels = mixedMoment B raw20177step0 raw20177step0Labels := by
      have hz : ∀ j, raw20177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20177step0 = (fun i j => raw20177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20177step0 raw20177; decide +kernel
      have hl : raw20177step0Labels = raw20177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20177 raw20177Labels permutation346 hz
    mixedMoment B raw20177step0 raw20177step0Labels = mixedMoment B raw20177step1 raw20177step1Labels := by
      have ha : raw20177step1 = (fun i j => raw20177step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20177step1 raw20177step0; decide +kernel
      have hl : raw20177step1Labels = raw20177step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20177step0 raw20177step0Labels permutation139 permutation2
    _ = mixedMoment B node2005 node2005Labels := by rfl

theorem canonical20178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20178 raw20178Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw20178 raw20178Labels = mixedMoment B raw20178step0 raw20178step0Labels := by
      have hz : ∀ j, raw20178 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20178step0 = (fun i j => raw20178 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20178step0 raw20178; decide +kernel
      have hl : raw20178step0Labels = raw20178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20178 raw20178Labels permutation265 hz
    mixedMoment B raw20178step0 raw20178step0Labels = mixedMoment B raw20178step1 raw20178step1Labels := by
      have ha : raw20178step1 = (fun i j => raw20178step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20178step1 raw20178step0; decide +kernel
      have hl : raw20178step1Labels = raw20178step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20178step0 raw20178step0Labels permutation139 permutation2
    _ = mixedMoment B node2005 node2005Labels := by rfl

theorem canonical20179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20179 raw20179Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw20179 raw20179Labels = mixedMoment B raw20179step0 raw20179step0Labels := by
      have hz : ∀ j, raw20179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20179step0 = (fun i j => raw20179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20179step0 raw20179; decide +kernel
      have hl : raw20179step0Labels = raw20179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20179 raw20179Labels permutation346 hz
    mixedMoment B raw20179step0 raw20179step0Labels = mixedMoment B raw20179step1 raw20179step1Labels := by
      have hz : ∀ j, raw20179step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20179step1 = (fun i j => raw20179step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20179step1 raw20179step0; decide +kernel
      have hl : raw20179step1Labels = raw20179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20179step0 raw20179step0Labels permutation56 hz
    mixedMoment B raw20179step1 raw20179step1Labels = mixedMoment B raw20179step2 raw20179step2Labels := by
      have ha : raw20179step2 = (fun i j => raw20179step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20179step2 raw20179step1; decide +kernel
      have hl : raw20179step2Labels = raw20179step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20179step1 raw20179step1Labels permutation31 permutation2
    _ = mixedMoment B node1011 node1011Labels := by rfl

theorem canonical20190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20190 raw20190Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw20190 raw20190Labels = mixedMoment B raw20190step0 raw20190step0Labels := by
      have hz : ∀ j, raw20190 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20190step0 = (fun i j => raw20190 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20190step0 raw20190; decide +kernel
      have hl : raw20190step0Labels = raw20190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20190 raw20190Labels permutation265 hz
    mixedMoment B raw20190step0 raw20190step0Labels = mixedMoment B raw20190step1 raw20190step1Labels := by
      have ha : raw20190step1 = (fun i j => raw20190step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20190step1 raw20190step0; decide +kernel
      have hl : raw20190step1Labels = raw20190step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20190step0 raw20190step0Labels permutation40 permutation2
    _ = mixedMoment B node581 node581Labels := by rfl

theorem canonical20191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20191 raw20191Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw20191 raw20191Labels = mixedMoment B raw20191step0 raw20191step0Labels := by
      have ha : raw20191step0 = (fun i j => raw20191 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20191step0 raw20191; decide +kernel
      have hl : raw20191step0Labels = raw20191Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20191 raw20191Labels permutation160 permutation2
    _ = mixedMoment B node905 node905Labels := by rfl

theorem canonical20192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20192 raw20192Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw20192 raw20192Labels = mixedMoment B raw20192step0 raw20192step0Labels := by
      have hz : ∀ j, raw20192 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20192step0 = (fun i j => raw20192 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20192step0 raw20192; decide +kernel
      have hl : raw20192step0Labels = raw20192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20192 raw20192Labels permutation265 hz
    _ = mixedMoment B node1022 node1022Labels := by rfl

theorem canonical20193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20193 raw20193Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw20193 raw20193Labels = mixedMoment B raw20193step0 raw20193step0Labels := by
      have hz : ∀ j, raw20193 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20193step0 = (fun i j => raw20193 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20193step0 raw20193; decide +kernel
      have hl : raw20193step0Labels = raw20193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20193 raw20193Labels permutation265 hz
    mixedMoment B raw20193step0 raw20193step0Labels = mixedMoment B raw20193step1 raw20193step1Labels := by
      have ha : raw20193step1 = (fun i j => raw20193step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20193step1 raw20193step0; decide +kernel
      have hl : raw20193step1Labels = raw20193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20193step0 raw20193step0Labels permutation40 permutation2
    _ = mixedMoment B node945 node945Labels := by rfl

theorem canonical20194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20194 raw20194Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw20194 raw20194Labels = mixedMoment B raw20194step0 raw20194step0Labels := by
      have hz : ∀ j, raw20194 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20194step0 = (fun i j => raw20194 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20194step0 raw20194; decide +kernel
      have hl : raw20194step0Labels = raw20194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20194 raw20194Labels permutation520 hz
    mixedMoment B raw20194step0 raw20194step0Labels = mixedMoment B raw20194step1 raw20194step1Labels := by
      have hz : ∀ j, raw20194step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20194step1 = (fun i j => raw20194step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20194step1 raw20194step0; decide +kernel
      have hl : raw20194step1Labels = raw20194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20194step0 raw20194step0Labels permutation56 hz
    mixedMoment B raw20194step1 raw20194step1Labels = mixedMoment B raw20194step2 raw20194step2Labels := by
      have ha : raw20194step2 = (fun i j => raw20194step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20194step2 raw20194step1; decide +kernel
      have hl : raw20194step2Labels = raw20194step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20194step1 raw20194step1Labels permutation10 permutation2
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical20195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20195 raw20195Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw20195 raw20195Labels = mixedMoment B raw20195step0 raw20195step0Labels := by
      have hz : ∀ j, raw20195 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20195step0 = (fun i j => raw20195 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20195step0 raw20195; decide +kernel
      have hl : raw20195step0Labels = raw20195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20195 raw20195Labels permutation265 hz
    mixedMoment B raw20195step0 raw20195step0Labels = mixedMoment B raw20195step1 raw20195step1Labels := by
      have ha : raw20195step1 = (fun i j => raw20195step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20195step1 raw20195step0; decide +kernel
      have hl : raw20195step1Labels = raw20195step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20195step0 raw20195step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical20196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20196 raw20196Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw20196 raw20196Labels = mixedMoment B raw20196step0 raw20196step0Labels := by
      have hz : ∀ j, raw20196 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20196step0 = (fun i j => raw20196 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20196step0 raw20196; decide +kernel
      have hl : raw20196step0Labels = raw20196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196 raw20196Labels permutation520 hz
    mixedMoment B raw20196step0 raw20196step0Labels = mixedMoment B raw20196step1 raw20196step1Labels := by
      have hz : ∀ j, raw20196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20196step1 = (fun i j => raw20196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20196step1 raw20196step0; decide +kernel
      have hl : raw20196step1Labels = raw20196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196step0 raw20196step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical20197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20197 raw20197Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw20197 raw20197Labels = mixedMoment B raw20197step0 raw20197step0Labels := by
      have hz : ∀ j, raw20197 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20197step0 = (fun i j => raw20197 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20197step0 raw20197; decide +kernel
      have hl : raw20197step0Labels = raw20197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20197 raw20197Labels permutation265 hz
    mixedMoment B raw20197step0 raw20197step0Labels = mixedMoment B raw20197step1 raw20197step1Labels := by
      have ha : raw20197step1 = (fun i j => raw20197step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20197step1 raw20197step0; decide +kernel
      have hl : raw20197step1Labels = raw20197step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20197step0 raw20197step0Labels permutation151 permutation2
    mixedMoment B raw20197step1 raw20197step1Labels = mixedMoment B raw20197step2 raw20197step2Labels := by
      have ha : raw20197step2 = -raw20197step1 := by apply Matrix.ext; change ∀ i j, raw20197step2 i j = -(raw20197step1 i j); unfold raw20197step2 raw20197step1; decide +kernel
      have hl : raw20197step2Labels = raw20197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical20198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20198 raw20198Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw20198 raw20198Labels = mixedMoment B raw20198step0 raw20198step0Labels := by
      have ha : raw20198step0 = (fun i j => raw20198 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20198step0 raw20198; decide +kernel
      have hl : raw20198step0Labels = raw20198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20198 raw20198Labels permutation182 permutation2
    _ = mixedMoment B node1327 node1327Labels := by rfl

theorem canonical20199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20199 raw20199Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw20199 raw20199Labels = mixedMoment B raw20199step0 raw20199step0Labels := by
      have hz : ∀ j, raw20199 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20199step0 = (fun i j => raw20199 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20199step0 raw20199; decide +kernel
      have hl : raw20199step0Labels = raw20199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20199 raw20199Labels permutation265 hz
    _ = mixedMoment B node1337 node1337Labels := by rfl

theorem canonical20200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20200 raw20200Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw20200 raw20200Labels = mixedMoment B raw20200step0 raw20200step0Labels := by
      have hz : ∀ j, raw20200 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20200step0 = (fun i j => raw20200 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20200step0 raw20200; decide +kernel
      have hl : raw20200step0Labels = raw20200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20200 raw20200Labels permutation265 hz
    _ = mixedMoment B node1333 node1333Labels := by rfl

theorem canonical20201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20201 raw20201Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20201 raw20201Labels = mixedMoment B raw20201step0 raw20201step0Labels := by
      have hz : ∀ j, raw20201 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20201step0 = (fun i j => raw20201 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20201step0 raw20201; decide +kernel
      have hl : raw20201step0Labels = raw20201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20201 raw20201Labels permutation265 hz
    mixedMoment B raw20201step0 raw20201step0Labels = mixedMoment B raw20201step1 raw20201step1Labels := by
      have ha : raw20201step1 = (fun i j => raw20201step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20201step1 raw20201step0; decide +kernel
      have hl : raw20201step1Labels = raw20201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20201step0 raw20201step0Labels permutation151 permutation2
    mixedMoment B raw20201step1 raw20201step1Labels = mixedMoment B raw20201step2 raw20201step2Labels := by
      have ha : raw20201step2 = -raw20201step1 := by apply Matrix.ext; change ∀ i j, raw20201step2 i j = -(raw20201step1 i j); unfold raw20201step2 raw20201step1; decide +kernel
      have hl : raw20201step2Labels = raw20201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1118 node1118Labels := by rfl

theorem canonical20202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20202 raw20202Labels = mixedMoment B node3279 node3279Labels := by
  calc
    mixedMoment B raw20202 raw20202Labels = mixedMoment B raw20202step0 raw20202step0Labels := by
      have ha : raw20202step0 = (fun i j => raw20202 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20202step0 raw20202; decide +kernel
      have hl : raw20202step0Labels = raw20202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20202 raw20202Labels permutation182 permutation2
    mixedMoment B raw20202step0 raw20202step0Labels = mixedMoment B raw20202step1 raw20202step1Labels := by
      have ha : raw20202step1 = -raw20202step0 := by apply Matrix.ext; change ∀ i j, raw20202step1 i j = -(raw20202step0 i j); unfold raw20202step1 raw20202step0; decide +kernel
      have hl : raw20202step1Labels = raw20202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3279 node3279Labels := by rfl

theorem canonical20203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20203 raw20203Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20203 raw20203Labels = mixedMoment B raw20203step0 raw20203step0Labels := by
      have hz : ∀ j, raw20203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20203step0 = (fun i j => raw20203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20203step0 raw20203; decide +kernel
      have hl : raw20203step0Labels = raw20203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20203 raw20203Labels permutation434 hz
    mixedMoment B raw20203step0 raw20203step0Labels = mixedMoment B raw20203step1 raw20203step1Labels := by
      have hz : ∀ j, raw20203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20203step1 = (fun i j => raw20203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20203step1 raw20203step0; decide +kernel
      have hl : raw20203step1Labels = raw20203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20203step0 raw20203step0Labels permutation56 hz
    mixedMoment B raw20203step1 raw20203step1Labels = mixedMoment B raw20203step2 raw20203step2Labels := by
      have ha : raw20203step2 = -raw20203step1 := by apply Matrix.ext; change ∀ i j, raw20203step2 i j = -(raw20203step1 i j); unfold raw20203step2 raw20203step1; decide +kernel
      have hl : raw20203step2Labels = raw20203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

theorem canonical20204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20204 raw20204Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw20204 raw20204Labels = mixedMoment B raw20204step0 raw20204step0Labels := by
      have hz : ∀ j, raw20204 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20204step0 = (fun i j => raw20204 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20204step0 raw20204; decide +kernel
      have hl : raw20204step0Labels = raw20204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20204 raw20204Labels permutation265 hz
    mixedMoment B raw20204step0 raw20204step0Labels = mixedMoment B raw20204step1 raw20204step1Labels := by
      have ha : raw20204step1 = -raw20204step0 := by apply Matrix.ext; change ∀ i j, raw20204step1 i j = -(raw20204step0 i j); unfold raw20204step1 raw20204step0; decide +kernel
      have hl : raw20204step1Labels = raw20204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3283 node3283Labels := by rfl

theorem canonical20205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20205 raw20205Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw20205 raw20205Labels = mixedMoment B raw20205step0 raw20205step0Labels := by
      have hz : ∀ j, raw20205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20205step0 = (fun i j => raw20205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20205step0 raw20205; decide +kernel
      have hl : raw20205step0Labels = raw20205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20205 raw20205Labels permutation265 hz
    mixedMoment B raw20205step0 raw20205step0Labels = mixedMoment B raw20205step1 raw20205step1Labels := by
      have ha : raw20205step1 = (fun i j => raw20205step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20205step1 raw20205step0; decide +kernel
      have hl : raw20205step1Labels = raw20205step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20205step0 raw20205step0Labels permutation149 permutation2
    _ = mixedMoment B node1942 node1942Labels := by rfl

theorem canonical20208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20208 raw20208Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw20208 raw20208Labels = mixedMoment B raw20208step0 raw20208step0Labels := by
      have hz : ∀ j, raw20208 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20208step0 = (fun i j => raw20208 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20208step0 raw20208; decide +kernel
      have hl : raw20208step0Labels = raw20208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20208 raw20208Labels permutation265 hz
    mixedMoment B raw20208step0 raw20208step0Labels = mixedMoment B raw20208step1 raw20208step1Labels := by
      have ha : raw20208step1 = (fun i j => raw20208step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20208step1 raw20208step0; decide +kernel
      have hl : raw20208step1Labels = raw20208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20208step0 raw20208step0Labels permutation32 permutation4
    mixedMoment B raw20208step1 raw20208step1Labels = mixedMoment B raw20208step2 raw20208step2Labels := by
      have ha : raw20208step2 = -raw20208step1 := by apply Matrix.ext; change ∀ i j, raw20208step2 i j = -(raw20208step1 i j); unfold raw20208step2 raw20208step1; decide +kernel
      have hl : raw20208step2Labels = raw20208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node847 node847Labels := by rfl

theorem canonical20209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20209 raw20209Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw20209 raw20209Labels = mixedMoment B raw20209step0 raw20209step0Labels := by
      have hz : ∀ j, raw20209 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20209step0 = (fun i j => raw20209 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20209step0 raw20209; decide +kernel
      have hl : raw20209step0Labels = raw20209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20209 raw20209Labels permutation265 hz
    mixedMoment B raw20209step0 raw20209step0Labels = mixedMoment B raw20209step1 raw20209step1Labels := by
      have ha : raw20209step1 = (fun i j => raw20209step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20209step1 raw20209step0; decide +kernel
      have hl : raw20209step1Labels = raw20209step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20209step0 raw20209step0Labels permutation44 permutation4
    mixedMoment B raw20209step1 raw20209step1Labels = mixedMoment B raw20209step2 raw20209step2Labels := by
      have ha : raw20209step2 = -raw20209step1 := by apply Matrix.ext; change ∀ i j, raw20209step2 i j = -(raw20209step1 i j); unfold raw20209step2 raw20209step1; decide +kernel
      have hl : raw20209step2Labels = raw20209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node804 node804Labels := by rfl

theorem canonical20210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20210 raw20210Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw20210 raw20210Labels = mixedMoment B raw20210step0 raw20210step0Labels := by
      have ha : raw20210step0 = (fun i j => raw20210 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20210step0 raw20210; decide +kernel
      have hl : raw20210step0Labels = raw20210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20210 raw20210Labels permutation152 permutation4
    mixedMoment B raw20210step0 raw20210step0Labels = mixedMoment B raw20210step1 raw20210step1Labels := by
      have ha : raw20210step1 = -raw20210step0 := by apply Matrix.ext; change ∀ i j, raw20210step1 i j = -(raw20210step0 i j); unfold raw20210step1 raw20210step0; decide +kernel
      have hl : raw20210step1Labels = raw20210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1613 node1613Labels := by rfl

theorem canonical20211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20211 raw20211Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20211 raw20211Labels = mixedMoment B raw20211step0 raw20211step0Labels := by
      have hz : ∀ j, raw20211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20211step0 = (fun i j => raw20211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20211step0 raw20211; decide +kernel
      have hl : raw20211step0Labels = raw20211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20211 raw20211Labels permutation434 hz
    mixedMoment B raw20211step0 raw20211step0Labels = mixedMoment B raw20211step1 raw20211step1Labels := by
      have hz : ∀ j, raw20211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20211step1 = (fun i j => raw20211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20211step1 raw20211step0; decide +kernel
      have hl : raw20211step1Labels = raw20211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20211step0 raw20211step0Labels permutation56 hz
    mixedMoment B raw20211step1 raw20211step1Labels = mixedMoment B raw20211step2 raw20211step2Labels := by
      have ha : raw20211step2 = (fun i j => raw20211step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20211step2 raw20211step1; decide +kernel
      have hl : raw20211step2Labels = raw20211step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20211step1 raw20211step1Labels permutation8 permutation4
    mixedMoment B raw20211step2 raw20211step2Labels = mixedMoment B raw20211step3 raw20211step3Labels := by
      have ha : raw20211step3 = -raw20211step2 := by apply Matrix.ext; change ∀ i j, raw20211step3 i j = -(raw20211step2 i j); unfold raw20211step3 raw20211step2; decide +kernel
      have hl : raw20211step3Labels = raw20211step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

theorem canonical20212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20212 raw20212Labels = mixedMoment B node1596 node1596Labels := by
  calc
    mixedMoment B raw20212 raw20212Labels = mixedMoment B raw20212step0 raw20212step0Labels := by
      have ha : raw20212step0 = (fun i j => raw20212 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20212step0 raw20212; decide +kernel
      have hl : raw20212step0Labels = raw20212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20212 raw20212Labels permutation164 permutation4
    mixedMoment B raw20212step0 raw20212step0Labels = mixedMoment B raw20212step1 raw20212step1Labels := by
      have ha : raw20212step1 = -raw20212step0 := by apply Matrix.ext; change ∀ i j, raw20212step1 i j = -(raw20212step0 i j); unfold raw20212step1 raw20212step0; decide +kernel
      have hl : raw20212step1Labels = raw20212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1596 node1596Labels := by rfl

theorem canonical20213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20213 raw20213Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20213 raw20213Labels = mixedMoment B raw20213step0 raw20213step0Labels := by
      have hz : ∀ j, raw20213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20213step0 = (fun i j => raw20213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20213step0 raw20213; decide +kernel
      have hl : raw20213step0Labels = raw20213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20213 raw20213Labels permutation434 hz
    mixedMoment B raw20213step0 raw20213step0Labels = mixedMoment B raw20213step1 raw20213step1Labels := by
      have hz : ∀ j, raw20213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20213step1 = (fun i j => raw20213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20213step1 raw20213step0; decide +kernel
      have hl : raw20213step1Labels = raw20213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20213step0 raw20213step0Labels permutation56 hz
    mixedMoment B raw20213step1 raw20213step1Labels = mixedMoment B raw20213step2 raw20213step2Labels := by
      have ha : raw20213step2 = (fun i j => raw20213step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20213step2 raw20213step1; decide +kernel
      have hl : raw20213step2Labels = raw20213step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20213step1 raw20213step1Labels permutation10 permutation4
    mixedMoment B raw20213step2 raw20213step2Labels = mixedMoment B raw20213step3 raw20213step3Labels := by
      have ha : raw20213step3 = -raw20213step2 := by apply Matrix.ext; change ∀ i j, raw20213step3 i j = -(raw20213step2 i j); unfold raw20213step3 raw20213step2; decide +kernel
      have hl : raw20213step3Labels = raw20213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20214 raw20214Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw20214 raw20214Labels = mixedMoment B raw20214step0 raw20214step0Labels := by
      have hz : ∀ j, raw20214 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20214step0 = (fun i j => raw20214 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20214step0 raw20214; decide +kernel
      have hl : raw20214step0Labels = raw20214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20214 raw20214Labels permutation265 hz
    mixedMoment B raw20214step0 raw20214step0Labels = mixedMoment B raw20214step1 raw20214step1Labels := by
      have ha : raw20214step1 = (fun i j => raw20214step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20214step1 raw20214step0; decide +kernel
      have hl : raw20214step1Labels = raw20214step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20214step0 raw20214step0Labels permutation44 permutation4
    mixedMoment B raw20214step1 raw20214step1Labels = mixedMoment B raw20214step2 raw20214step2Labels := by
      have ha : raw20214step2 = -raw20214step1 := by apply Matrix.ext; change ∀ i j, raw20214step2 i j = -(raw20214step1 i j); unfold raw20214step2 raw20214step1; decide +kernel
      have hl : raw20214step2Labels = raw20214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1643 node1643Labels := by rfl

theorem canonical20217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20217 raw20217Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw20217 raw20217Labels = mixedMoment B raw20217step0 raw20217step0Labels := by
      have hz : ∀ j, raw20217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20217step0 = (fun i j => raw20217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20217step0 raw20217; decide +kernel
      have hl : raw20217step0Labels = raw20217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20217 raw20217Labels permutation265 hz
    mixedMoment B raw20217step0 raw20217step0Labels = mixedMoment B raw20217step1 raw20217step1Labels := by
      have ha : raw20217step1 = (fun i j => raw20217step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20217step1 raw20217step0; decide +kernel
      have hl : raw20217step1Labels = raw20217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20217step0 raw20217step0Labels permutation38 permutation2
    _ = mixedMoment B node585 node585Labels := by rfl

theorem canonical20218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20218 raw20218Labels = mixedMoment B node909 node909Labels := by
  calc
    mixedMoment B raw20218 raw20218Labels = mixedMoment B raw20218step0 raw20218step0Labels := by
      have ha : raw20218step0 = (fun i j => raw20218 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20218step0 raw20218; decide +kernel
      have hl : raw20218step0Labels = raw20218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20218 raw20218Labels permutation158 permutation2
    _ = mixedMoment B node909 node909Labels := by rfl

theorem canonical20219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20219 raw20219Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw20219 raw20219Labels = mixedMoment B raw20219step0 raw20219step0Labels := by
      have hz : ∀ j, raw20219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20219step0 = (fun i j => raw20219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20219step0 raw20219; decide +kernel
      have hl : raw20219step0Labels = raw20219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20219 raw20219Labels permutation265 hz
    mixedMoment B raw20219step0 raw20219step0Labels = mixedMoment B raw20219step1 raw20219step1Labels := by
      have ha : raw20219step1 = (fun i j => raw20219step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20219step1 raw20219step0; decide +kernel
      have hl : raw20219step1Labels = raw20219step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20219step0 raw20219step0Labels permutation38 permutation2
    _ = mixedMoment B node949 node949Labels := by rfl

theorem canonical20220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20220 raw20220Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw20220 raw20220Labels = mixedMoment B raw20220step0 raw20220step0Labels := by
      have hz : ∀ j, raw20220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20220step0 = (fun i j => raw20220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20220step0 raw20220; decide +kernel
      have hl : raw20220step0Labels = raw20220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20220 raw20220Labels permutation265 hz
    mixedMoment B raw20220step0 raw20220step0Labels = mixedMoment B raw20220step1 raw20220step1Labels := by
      have ha : raw20220step1 = (fun i j => raw20220step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20220step1 raw20220step0; decide +kernel
      have hl : raw20220step1Labels = raw20220step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20220step0 raw20220step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

theorem canonical20221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20221 raw20221Labels = mixedMoment B node1326 node1326Labels := by
  calc
    mixedMoment B raw20221 raw20221Labels = mixedMoment B raw20221step0 raw20221step0Labels := by
      have ha : raw20221step0 = (fun i j => raw20221 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20221step0 raw20221; decide +kernel
      have hl : raw20221step0Labels = raw20221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20221 raw20221Labels permutation182 permutation2
    _ = mixedMoment B node1326 node1326Labels := by rfl

theorem canonical20222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20222 raw20222Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw20222 raw20222Labels = mixedMoment B raw20222step0 raw20222step0Labels := by
      have hz : ∀ j, raw20222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20222step0 = (fun i j => raw20222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20222step0 raw20222; decide +kernel
      have hl : raw20222step0Labels = raw20222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20222 raw20222Labels permutation265 hz
    _ = mixedMoment B node1336 node1336Labels := by rfl

theorem canonical20223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20223 raw20223Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw20223 raw20223Labels = mixedMoment B raw20223step0 raw20223step0Labels := by
      have hz : ∀ j, raw20223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20223step0 = (fun i j => raw20223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20223step0 raw20223; decide +kernel
      have hl : raw20223step0Labels = raw20223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20223 raw20223Labels permutation265 hz
    _ = mixedMoment B node1332 node1332Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical158
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical20224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20224 raw20224Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw20224 raw20224Labels = mixedMoment B raw20224step0 raw20224step0Labels := by
      have hz : ∀ j, raw20224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20224step0 = (fun i j => raw20224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20224step0 raw20224; decide +kernel
      have hl : raw20224step0Labels = raw20224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20224 raw20224Labels permutation265 hz
    mixedMoment B raw20224step0 raw20224step0Labels = mixedMoment B raw20224step1 raw20224step1Labels := by
      have ha : raw20224step1 = (fun i j => raw20224step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20224step1 raw20224step0; decide +kernel
      have hl : raw20224step1Labels = raw20224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20224step0 raw20224step0Labels permutation151 permutation2
    mixedMoment B raw20224step1 raw20224step1Labels = mixedMoment B raw20224step2 raw20224step2Labels := by
      have ha : raw20224step2 = -raw20224step1 := by apply Matrix.ext; change ∀ i j, raw20224step2 i j = -(raw20224step1 i j); unfold raw20224step2 raw20224step1; decide +kernel
      have hl : raw20224step2Labels = raw20224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node911 node911Labels := by rfl

theorem canonical20225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20225 raw20225Labels = mixedMoment B node1995 node1995Labels := by
  calc
    mixedMoment B raw20225 raw20225Labels = mixedMoment B raw20225step0 raw20225step0Labels := by
      have ha : raw20225step0 = (fun i j => raw20225 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20225step0 raw20225; decide +kernel
      have hl : raw20225step0Labels = raw20225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20225 raw20225Labels permutation620 permutation2
    _ = mixedMoment B node1995 node1995Labels := by rfl

theorem canonical20226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20226 raw20226Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20226 raw20226Labels = mixedMoment B raw20226step0 raw20226step0Labels := by
      have hz : ∀ j, raw20226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20226step0 = (fun i j => raw20226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20226step0 raw20226; decide +kernel
      have hl : raw20226step0Labels = raw20226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20226 raw20226Labels permutation434 hz
    mixedMoment B raw20226step0 raw20226step0Labels = mixedMoment B raw20226step1 raw20226step1Labels := by
      have hz : ∀ j, raw20226step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20226step1 = (fun i j => raw20226step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20226step1 raw20226step0; decide +kernel
      have hl : raw20226step1Labels = raw20226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20226step0 raw20226step0Labels permutation56 hz
    mixedMoment B raw20226step1 raw20226step1Labels = mixedMoment B raw20226step2 raw20226step2Labels := by
      have ha : raw20226step2 = (fun i j => raw20226step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20226step2 raw20226step1; decide +kernel
      have hl : raw20226step2Labels = raw20226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20226step1 raw20226step1Labels permutation31 permutation2
    _ = mixedMoment B node2226 node2226Labels := by rfl

theorem canonical20227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20227 raw20227Labels = mixedMoment B node997 node997Labels := by
  calc
    mixedMoment B raw20227 raw20227Labels = mixedMoment B raw20227step0 raw20227step0Labels := by
      have hz : ∀ j, raw20227 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20227step0 = (fun i j => raw20227 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20227step0 raw20227; decide +kernel
      have hl : raw20227step0Labels = raw20227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20227 raw20227Labels permutation265 hz
    mixedMoment B raw20227step0 raw20227step0Labels = mixedMoment B raw20227step1 raw20227step1Labels := by
      have ha : raw20227step1 = (fun i j => raw20227step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20227step1 raw20227step0; decide +kernel
      have hl : raw20227step1Labels = raw20227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20227step0 raw20227step0Labels permutation149 permutation2
    _ = mixedMoment B node997 node997Labels := by rfl

theorem canonical20230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20230 raw20230Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw20230 raw20230Labels = mixedMoment B raw20230step0 raw20230step0Labels := by
      have hz : ∀ j, raw20230 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20230step0 = (fun i j => raw20230 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20230step0 raw20230; decide +kernel
      have hl : raw20230step0Labels = raw20230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20230 raw20230Labels permutation265 hz
    mixedMoment B raw20230step0 raw20230step0Labels = mixedMoment B raw20230step1 raw20230step1Labels := by
      have ha : raw20230step1 = (fun i j => raw20230step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20230step1 raw20230step0; decide +kernel
      have hl : raw20230step1Labels = raw20230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20230step0 raw20230step0Labels permutation38 permutation2
    _ = mixedMoment B node1355 node1355Labels := by rfl

theorem canonical20231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20231 raw20231Labels = mixedMoment B node1902 node1902Labels := by
  calc
    mixedMoment B raw20231 raw20231Labels = mixedMoment B raw20231step0 raw20231step0Labels := by
      have ha : raw20231step0 = (fun i j => raw20231 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20231step0 raw20231; decide +kernel
      have hl : raw20231step0Labels = raw20231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20231 raw20231Labels permutation682 permutation2
    mixedMoment B raw20231step0 raw20231step0Labels = mixedMoment B raw20231step1 raw20231step1Labels := by
      have ha : raw20231step1 = -raw20231step0 := by apply Matrix.ext; change ∀ i j, raw20231step1 i j = -(raw20231step0 i j); unfold raw20231step1 raw20231step0; decide +kernel
      have hl : raw20231step1Labels = raw20231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1902 node1902Labels := by rfl

theorem canonical20232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20232 raw20232Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw20232 raw20232Labels = mixedMoment B raw20232step0 raw20232step0Labels := by
      have hz : ∀ j, raw20232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20232step0 = (fun i j => raw20232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20232step0 raw20232; decide +kernel
      have hl : raw20232step0Labels = raw20232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20232 raw20232Labels permutation265 hz
    mixedMoment B raw20232step0 raw20232step0Labels = mixedMoment B raw20232step1 raw20232step1Labels := by
      have ha : raw20232step1 = (fun i j => raw20232step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20232step1 raw20232step0; decide +kernel
      have hl : raw20232step1Labels = raw20232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20232step0 raw20232step0Labels permutation151 permutation2
    mixedMoment B raw20232step1 raw20232step1Labels = mixedMoment B raw20232step2 raw20232step2Labels := by
      have ha : raw20232step2 = -raw20232step1 := by apply Matrix.ext; change ∀ i j, raw20232step2 i j = -(raw20232step1 i j); unfold raw20232step2 raw20232step1; decide +kernel
      have hl : raw20232step2Labels = raw20232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

theorem canonical20233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20233 raw20233Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw20233 raw20233Labels = mixedMoment B raw20233step0 raw20233step0Labels := by
      have hz : ∀ j, raw20233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20233step0 = (fun i j => raw20233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20233step0 raw20233; decide +kernel
      have hl : raw20233step0Labels = raw20233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20233 raw20233Labels permutation265 hz
    mixedMoment B raw20233step0 raw20233step0Labels = mixedMoment B raw20233step1 raw20233step1Labels := by
      have ha : raw20233step1 = (fun i j => raw20233step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20233step1 raw20233step0; decide +kernel
      have hl : raw20233step1Labels = raw20233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20233step0 raw20233step0Labels permutation149 permutation2
    mixedMoment B raw20233step1 raw20233step1Labels = mixedMoment B raw20233step2 raw20233step2Labels := by
      have ha : raw20233step2 = -raw20233step1 := by apply Matrix.ext; change ∀ i j, raw20233step2 i j = -(raw20233step1 i j); unfold raw20233step2 raw20233step1; decide +kernel
      have hl : raw20233step2Labels = raw20233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

theorem canonical20234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20234 raw20234Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw20234 raw20234Labels = mixedMoment B raw20234step0 raw20234step0Labels := by
      have hz : ∀ j, raw20234 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20234step0 = (fun i j => raw20234 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20234step0 raw20234; decide +kernel
      have hl : raw20234step0Labels = raw20234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20234 raw20234Labels permutation265 hz
    mixedMoment B raw20234step0 raw20234step0Labels = mixedMoment B raw20234step1 raw20234step1Labels := by
      have ha : raw20234step1 = (fun i j => raw20234step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20234step1 raw20234step0; decide +kernel
      have hl : raw20234step1Labels = raw20234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20234step0 raw20234step0Labels permutation149 permutation2
    mixedMoment B raw20234step1 raw20234step1Labels = mixedMoment B raw20234step2 raw20234step2Labels := by
      have ha : raw20234step2 = -raw20234step1 := by apply Matrix.ext; change ∀ i j, raw20234step2 i j = -(raw20234step1 i j); unfold raw20234step2 raw20234step1; decide +kernel
      have hl : raw20234step2Labels = raw20234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical20235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20235 raw20235Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw20235 raw20235Labels = mixedMoment B raw20235step0 raw20235step0Labels := by
      have hz : ∀ j, raw20235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20235step0 = (fun i j => raw20235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20235step0 raw20235; decide +kernel
      have hl : raw20235step0Labels = raw20235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20235 raw20235Labels permutation265 hz
    mixedMoment B raw20235step0 raw20235step0Labels = mixedMoment B raw20235step1 raw20235step1Labels := by
      have ha : raw20235step1 = (fun i j => raw20235step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20235step1 raw20235step0; decide +kernel
      have hl : raw20235step1Labels = raw20235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20235step0 raw20235step0Labels permutation38 permutation2
    _ = mixedMoment B node3024 node3024Labels := by rfl

theorem canonical20236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20236 raw20236Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw20236 raw20236Labels = mixedMoment B raw20236step0 raw20236step0Labels := by
      have hz : ∀ j, raw20236 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20236step0 = (fun i j => raw20236 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20236step0 raw20236; decide +kernel
      have hl : raw20236step0Labels = raw20236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20236 raw20236Labels permutation265 hz
    mixedMoment B raw20236step0 raw20236step0Labels = mixedMoment B raw20236step1 raw20236step1Labels := by
      have ha : raw20236step1 = (fun i j => raw20236step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20236step1 raw20236step0; decide +kernel
      have hl : raw20236step1Labels = raw20236step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20236step0 raw20236step0Labels permutation146 permutation0
    mixedMoment B raw20236step1 raw20236step1Labels = mixedMoment B raw20236step2 raw20236step2Labels := by
      have ha : raw20236step2 = -raw20236step1 := by apply Matrix.ext; change ∀ i j, raw20236step2 i j = -(raw20236step1 i j); unfold raw20236step2 raw20236step1; decide +kernel
      have hl : raw20236step2Labels = raw20236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical20244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20244 raw20244Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw20244 raw20244Labels = mixedMoment B raw20244step0 raw20244step0Labels := by
      have hz : ∀ j, raw20244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20244step0 = (fun i j => raw20244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20244step0 raw20244; decide +kernel
      have hl : raw20244step0Labels = raw20244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20244 raw20244Labels permutation434 hz
    _ = mixedMoment B node1132 node1132Labels := by rfl

theorem canonical20245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20245 raw20245Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw20245 raw20245Labels = mixedMoment B raw20245step0 raw20245step0Labels := by
      have hz : ∀ j, raw20245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20245step0 = (fun i j => raw20245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20245step0 raw20245; decide +kernel
      have hl : raw20245step0Labels = raw20245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20245 raw20245Labels permutation346 hz
    _ = mixedMoment B node1132 node1132Labels := by rfl

theorem canonical20246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20246 raw20246Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw20246 raw20246Labels = mixedMoment B raw20246step0 raw20246step0Labels := by
      have hz : ∀ j, raw20246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20246step0 = (fun i j => raw20246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20246step0 raw20246; decide +kernel
      have hl : raw20246step0Labels = raw20246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20246 raw20246Labels permutation434 hz
    mixedMoment B raw20246step0 raw20246step0Labels = mixedMoment B raw20246step1 raw20246step1Labels := by
      have hz : ∀ j, raw20246step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20246step1 = (fun i j => raw20246step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20246step1 raw20246step0; decide +kernel
      have hl : raw20246step1Labels = raw20246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20246step0 raw20246step0Labels permutation80 hz
    _ = mixedMoment B node1145 node1145Labels := by rfl

theorem canonical20247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20247 raw20247Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw20247 raw20247Labels = mixedMoment B raw20247step0 raw20247step0Labels := by
      have hz : ∀ j, raw20247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20247step0 = (fun i j => raw20247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20247step0 raw20247; decide +kernel
      have hl : raw20247step0Labels = raw20247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20247 raw20247Labels permutation434 hz
    mixedMoment B raw20247step0 raw20247step0Labels = mixedMoment B raw20247step1 raw20247step1Labels := by
      have hz : ∀ j, raw20247step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20247step1 = (fun i j => raw20247step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20247step1 raw20247step0; decide +kernel
      have hl : raw20247step1Labels = raw20247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20247step0 raw20247step0Labels permutation80 hz
    _ = mixedMoment B node1142 node1142Labels := by rfl

theorem canonical20248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20248 raw20248Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw20248 raw20248Labels = mixedMoment B raw20248step0 raw20248step0Labels := by
      have hz : ∀ j, raw20248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20248step0 = (fun i j => raw20248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20248step0 raw20248; decide +kernel
      have hl : raw20248step0Labels = raw20248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20248 raw20248Labels permutation434 hz
    mixedMoment B raw20248step0 raw20248step0Labels = mixedMoment B raw20248step1 raw20248step1Labels := by
      have hz : ∀ j, raw20248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20248step1 = (fun i j => raw20248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20248step1 raw20248step0; decide +kernel
      have hl : raw20248step1Labels = raw20248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20248step0 raw20248step0Labels permutation80 hz
    _ = mixedMoment B node636 node636Labels := by rfl

theorem canonical20249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20249 raw20249Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw20249 raw20249Labels = mixedMoment B raw20249step0 raw20249step0Labels := by
      have hz : ∀ j, raw20249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20249step0 = (fun i j => raw20249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20249step0 raw20249; decide +kernel
      have hl : raw20249step0Labels = raw20249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20249 raw20249Labels permutation434 hz
    mixedMoment B raw20249step0 raw20249step0Labels = mixedMoment B raw20249step1 raw20249step1Labels := by
      have ha : raw20249step1 = (fun i j => raw20249step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20249step1 raw20249step0; decide +kernel
      have hl : raw20249step1Labels = raw20249step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20249step0 raw20249step0Labels permutation38 permutation2
    _ = mixedMoment B node1155 node1155Labels := by rfl

theorem canonical20250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20250 raw20250Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw20250 raw20250Labels = mixedMoment B raw20250step0 raw20250step0Labels := by
      have hz : ∀ j, raw20250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20250step0 = (fun i j => raw20250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20250step0 raw20250; decide +kernel
      have hl : raw20250step0Labels = raw20250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20250 raw20250Labels permutation346 hz
    mixedMoment B raw20250step0 raw20250step0Labels = mixedMoment B raw20250step1 raw20250step1Labels := by
      have ha : raw20250step1 = (fun i j => raw20250step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20250step1 raw20250step0; decide +kernel
      have hl : raw20250step1Labels = raw20250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20250step0 raw20250step0Labels permutation38 permutation2
    _ = mixedMoment B node1155 node1155Labels := by rfl

theorem canonical20251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20251 raw20251Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw20251 raw20251Labels = mixedMoment B raw20251step0 raw20251step0Labels := by
      have hz : ∀ j, raw20251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20251step0 = (fun i j => raw20251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20251step0 raw20251; decide +kernel
      have hl : raw20251step0Labels = raw20251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20251 raw20251Labels permutation434 hz
    mixedMoment B raw20251step0 raw20251step0Labels = mixedMoment B raw20251step1 raw20251step1Labels := by
      have hz : ∀ j, raw20251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20251step1 = (fun i j => raw20251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20251step1 raw20251step0; decide +kernel
      have hl : raw20251step1Labels = raw20251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20251step0 raw20251step0Labels permutation80 hz
    mixedMoment B raw20251step1 raw20251step1Labels = mixedMoment B raw20251step2 raw20251step2Labels := by
      have ha : raw20251step2 = (fun i j => raw20251step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20251step2 raw20251step1; decide +kernel
      have hl : raw20251step2Labels = raw20251step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20251step1 raw20251step1Labels permutation9 permutation2
    _ = mixedMoment B node1246 node1246Labels := by rfl

theorem canonical20252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20252 raw20252Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw20252 raw20252Labels = mixedMoment B raw20252step0 raw20252step0Labels := by
      have hz : ∀ j, raw20252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20252step0 = (fun i j => raw20252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20252step0 raw20252; decide +kernel
      have hl : raw20252step0Labels = raw20252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20252 raw20252Labels permutation434 hz
    mixedMoment B raw20252step0 raw20252step0Labels = mixedMoment B raw20252step1 raw20252step1Labels := by
      have hz : ∀ j, raw20252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20252step1 = (fun i j => raw20252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20252step1 raw20252step0; decide +kernel
      have hl : raw20252step1Labels = raw20252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20252step0 raw20252step0Labels permutation80 hz
    mixedMoment B raw20252step1 raw20252step1Labels = mixedMoment B raw20252step2 raw20252step2Labels := by
      have ha : raw20252step2 = (fun i j => raw20252step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20252step2 raw20252step1; decide +kernel
      have hl : raw20252step2Labels = raw20252step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20252step1 raw20252step1Labels permutation10 permutation2
    _ = mixedMoment B node641 node641Labels := by rfl

theorem canonical20253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20253 raw20253Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw20253 raw20253Labels = mixedMoment B raw20253step0 raw20253step0Labels := by
      have hz : ∀ j, raw20253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20253step0 = (fun i j => raw20253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20253step0 raw20253; decide +kernel
      have hl : raw20253step0Labels = raw20253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20253 raw20253Labels permutation434 hz
    mixedMoment B raw20253step0 raw20253step0Labels = mixedMoment B raw20253step1 raw20253step1Labels := by
      have ha : raw20253step1 = (fun i j => raw20253step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20253step1 raw20253step0; decide +kernel
      have hl : raw20253step1Labels = raw20253step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20253step0 raw20253step0Labels permutation40 permutation2
    _ = mixedMoment B node1159 node1159Labels := by rfl

theorem canonical20254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20254 raw20254Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw20254 raw20254Labels = mixedMoment B raw20254step0 raw20254step0Labels := by
      have hz : ∀ j, raw20254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20254step0 = (fun i j => raw20254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20254step0 raw20254; decide +kernel
      have hl : raw20254step0Labels = raw20254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20254 raw20254Labels permutation346 hz
    mixedMoment B raw20254step0 raw20254step0Labels = mixedMoment B raw20254step1 raw20254step1Labels := by
      have ha : raw20254step1 = (fun i j => raw20254step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20254step1 raw20254step0; decide +kernel
      have hl : raw20254step1Labels = raw20254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20254step0 raw20254step0Labels permutation40 permutation2
    _ = mixedMoment B node1159 node1159Labels := by rfl

theorem canonical20255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20255 raw20255Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20255 raw20255Labels = mixedMoment B raw20255step0 raw20255step0Labels := by
      have hz : ∀ j, raw20255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20255step0 = (fun i j => raw20255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20255step0 raw20255; decide +kernel
      have hl : raw20255step0Labels = raw20255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20255 raw20255Labels permutation434 hz
    mixedMoment B raw20255step0 raw20255step0Labels = mixedMoment B raw20255step1 raw20255step1Labels := by
      have hz : ∀ j, raw20255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20255step1 = (fun i j => raw20255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20255step1 raw20255step0; decide +kernel
      have hl : raw20255step1Labels = raw20255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20255step0 raw20255step0Labels permutation80 hz
    mixedMoment B raw20255step1 raw20255step1Labels = mixedMoment B raw20255step2 raw20255step2Labels := by
      have ha : raw20255step2 = (fun i j => raw20255step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20255step2 raw20255step1; decide +kernel
      have hl : raw20255step2Labels = raw20255step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20255step1 raw20255step1Labels permutation9 permutation4
    mixedMoment B raw20255step2 raw20255step2Labels = mixedMoment B raw20255step3 raw20255step3Labels := by
      have ha : raw20255step3 = -raw20255step2 := by apply Matrix.ext; change ∀ i j, raw20255step3 i j = -(raw20255step2 i j); unfold raw20255step3 raw20255step2; decide +kernel
      have hl : raw20255step3Labels = raw20255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical20256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20256 raw20256Labels = mixedMoment B node1652 node1652Labels := by
  calc
    mixedMoment B raw20256 raw20256Labels = mixedMoment B raw20256step0 raw20256step0Labels := by
      have hz : ∀ j, raw20256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20256step0 = (fun i j => raw20256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20256step0 raw20256; decide +kernel
      have hl : raw20256step0Labels = raw20256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20256 raw20256Labels permutation434 hz
    mixedMoment B raw20256step0 raw20256step0Labels = mixedMoment B raw20256step1 raw20256step1Labels := by
      have hz : ∀ j, raw20256step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20256step1 = (fun i j => raw20256step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20256step1 raw20256step0; decide +kernel
      have hl : raw20256step1Labels = raw20256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20256step0 raw20256step0Labels permutation80 hz
    mixedMoment B raw20256step1 raw20256step1Labels = mixedMoment B raw20256step2 raw20256step2Labels := by
      have ha : raw20256step2 = (fun i j => raw20256step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20256step2 raw20256step1; decide +kernel
      have hl : raw20256step2Labels = raw20256step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20256step1 raw20256step1Labels permutation10 permutation2
    mixedMoment B raw20256step2 raw20256step2Labels = mixedMoment B raw20256step3 raw20256step3Labels := by
      have ha : raw20256step3 = -raw20256step2 := by apply Matrix.ext; change ∀ i j, raw20256step3 i j = -(raw20256step2 i j); unfold raw20256step3 raw20256step2; decide +kernel
      have hl : raw20256step3Labels = raw20256step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1652 node1652Labels := by rfl

theorem canonical20257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20257 raw20257Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw20257 raw20257Labels = mixedMoment B raw20257step0 raw20257step0Labels := by
      have hz : ∀ j, raw20257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20257step0 = (fun i j => raw20257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20257step0 raw20257; decide +kernel
      have hl : raw20257step0Labels = raw20257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20257 raw20257Labels permutation434 hz
    mixedMoment B raw20257step0 raw20257step0Labels = mixedMoment B raw20257step1 raw20257step1Labels := by
      have ha : raw20257step1 = (fun i j => raw20257step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20257step1 raw20257step0; decide +kernel
      have hl : raw20257step1Labels = raw20257step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20257step0 raw20257step0Labels permutation44 permutation2
    mixedMoment B raw20257step1 raw20257step1Labels = mixedMoment B raw20257step2 raw20257step2Labels := by
      have ha : raw20257step2 = -raw20257step1 := by apply Matrix.ext; change ∀ i j, raw20257step2 i j = -(raw20257step1 i j); unfold raw20257step2 raw20257step1; decide +kernel
      have hl : raw20257step2Labels = raw20257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1643 node1643Labels := by rfl

theorem canonical20258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20258 raw20258Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw20258 raw20258Labels = mixedMoment B raw20258step0 raw20258step0Labels := by
      have hz : ∀ j, raw20258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20258step0 = (fun i j => raw20258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20258step0 raw20258; decide +kernel
      have hl : raw20258step0Labels = raw20258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20258 raw20258Labels permutation346 hz
    mixedMoment B raw20258step0 raw20258step0Labels = mixedMoment B raw20258step1 raw20258step1Labels := by
      have ha : raw20258step1 = (fun i j => raw20258step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20258step1 raw20258step0; decide +kernel
      have hl : raw20258step1Labels = raw20258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20258step0 raw20258step0Labels permutation44 permutation2
    mixedMoment B raw20258step1 raw20258step1Labels = mixedMoment B raw20258step2 raw20258step2Labels := by
      have ha : raw20258step2 = -raw20258step1 := by apply Matrix.ext; change ∀ i j, raw20258step2 i j = -(raw20258step1 i j); unfold raw20258step2 raw20258step1; decide +kernel
      have hl : raw20258step2Labels = raw20258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1643 node1643Labels := by rfl

theorem canonical20259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20259 raw20259Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20259 raw20259Labels = mixedMoment B raw20259step0 raw20259step0Labels := by
      have hz : ∀ j, raw20259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20259step0 = (fun i j => raw20259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20259step0 raw20259; decide +kernel
      have hl : raw20259step0Labels = raw20259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20259 raw20259Labels permutation434 hz
    mixedMoment B raw20259step0 raw20259step0Labels = mixedMoment B raw20259step1 raw20259step1Labels := by
      have hz : ∀ j, raw20259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20259step1 = (fun i j => raw20259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20259step1 raw20259step0; decide +kernel
      have hl : raw20259step1Labels = raw20259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20259step0 raw20259step0Labels permutation80 hz
    mixedMoment B raw20259step1 raw20259step1Labels = mixedMoment B raw20259step2 raw20259step2Labels := by
      have ha : raw20259step2 = (fun i j => raw20259step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20259step2 raw20259step1; decide +kernel
      have hl : raw20259step2Labels = raw20259step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20259step1 raw20259step1Labels permutation10 permutation2
    mixedMoment B raw20259step2 raw20259step2Labels = mixedMoment B raw20259step3 raw20259step3Labels := by
      have ha : raw20259step3 = -raw20259step2 := by apply Matrix.ext; change ∀ i j, raw20259step3 i j = -(raw20259step2 i j); unfold raw20259step3 raw20259step2; decide +kernel
      have hl : raw20259step3Labels = raw20259step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

theorem canonical20260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20260 raw20260Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20260 raw20260Labels = mixedMoment B raw20260step0 raw20260step0Labels := by
      have hz : ∀ j, raw20260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20260step0 = (fun i j => raw20260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20260step0 raw20260; decide +kernel
      have hl : raw20260step0Labels = raw20260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20260 raw20260Labels permutation434 hz
    mixedMoment B raw20260step0 raw20260step0Labels = mixedMoment B raw20260step1 raw20260step1Labels := by
      have hz : ∀ j, raw20260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20260step1 = (fun i j => raw20260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20260step1 raw20260step0; decide +kernel
      have hl : raw20260step1Labels = raw20260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20260step0 raw20260step0Labels permutation80 hz
    mixedMoment B raw20260step1 raw20260step1Labels = mixedMoment B raw20260step2 raw20260step2Labels := by
      have ha : raw20260step2 = (fun i j => raw20260step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20260step2 raw20260step1; decide +kernel
      have hl : raw20260step2Labels = raw20260step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20260step1 raw20260step1Labels permutation10 permutation2
    mixedMoment B raw20260step2 raw20260step2Labels = mixedMoment B raw20260step3 raw20260step3Labels := by
      have ha : raw20260step3 = -raw20260step2 := by apply Matrix.ext; change ∀ i j, raw20260step3 i j = -(raw20260step2 i j); unfold raw20260step3 raw20260step2; decide +kernel
      have hl : raw20260step3Labels = raw20260step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical3834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3834 raw3834Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3834 raw3834Labels = mixedMoment B raw3834step0 raw3834step0Labels := by
      have hz : ∀ j, raw3834 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3834step0 = (fun i j => raw3834 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3834step0 raw3834; decide +kernel
      have hl : raw3834step0Labels = raw3834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834 raw3834Labels permutation590 hz
    mixedMoment B raw3834step0 raw3834step0Labels = mixedMoment B raw3834step1 raw3834step1Labels := by
      have hz : ∀ j, raw3834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3834step1 = (fun i j => raw3834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3834step1 raw3834step0; decide +kernel
      have hl : raw3834step1Labels = raw3834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3834step0 raw3834step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical3836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3836 raw3836Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3836 raw3836Labels = mixedMoment B raw3836step0 raw3836step0Labels := by
      have hz : ∀ j, raw3836 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3836step0 = (fun i j => raw3836 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3836step0 raw3836; decide +kernel
      have hl : raw3836step0Labels = raw3836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3836 raw3836Labels permutation265 hz
    mixedMoment B raw3836step0 raw3836step0Labels = mixedMoment B raw3836step1 raw3836step1Labels := by
      have ha : raw3836step1 = (fun i j => raw3836step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3836step1 raw3836step0; decide +kernel
      have hl : raw3836step1Labels = raw3836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3836step0 raw3836step0Labels permutation40 permutation2
    _ = mixedMoment B node1024 node1024Labels := by rfl

theorem canonical3838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3838 raw3838Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw3838 raw3838Labels = mixedMoment B raw3838step0 raw3838step0Labels := by
      have hz : ∀ j, raw3838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3838step0 = (fun i j => raw3838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3838step0 raw3838; decide +kernel
      have hl : raw3838step0Labels = raw3838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3838 raw3838Labels permutation265 hz
    _ = mixedMoment B node1024 node1024Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical4905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4905 raw4905Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4905 raw4905Labels = mixedMoment B raw4905step0 raw4905step0Labels := by
      have hz : ∀ j, raw4905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4905step0 = (fun i j => raw4905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4905step0 raw4905; decide +kernel
      have hl : raw4905step0Labels = raw4905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905 raw4905Labels permutation434 hz
    mixedMoment B raw4905step0 raw4905step0Labels = mixedMoment B raw4905step1 raw4905step1Labels := by
      have hz : ∀ j, raw4905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4905step1 = (fun i j => raw4905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4905step1 raw4905step0; decide +kernel
      have hl : raw4905step1Labels = raw4905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4905step0 raw4905step0Labels permutation80 hz
    mixedMoment B raw4905step1 raw4905step1Labels = mixedMoment B raw4905step2 raw4905step2Labels := by
      have ha : raw4905step2 = (fun i j => raw4905step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4905step2 raw4905step1; decide +kernel
      have hl : raw4905step2Labels = raw4905step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4905step1 raw4905step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical4906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4906 raw4906Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw4906 raw4906Labels = mixedMoment B raw4906step0 raw4906step0Labels := by
      have hz : ∀ j, raw4906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4906step0 = (fun i j => raw4906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4906step0 raw4906; decide +kernel
      have hl : raw4906step0Labels = raw4906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4906 raw4906Labels permutation434 hz
    mixedMoment B raw4906step0 raw4906step0Labels = mixedMoment B raw4906step1 raw4906step1Labels := by
      have hz : ∀ j, raw4906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4906step1 = (fun i j => raw4906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4906step1 raw4906step0; decide +kernel
      have hl : raw4906step1Labels = raw4906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4906step0 raw4906step0Labels permutation80 hz
    mixedMoment B raw4906step1 raw4906step1Labels = mixedMoment B raw4906step2 raw4906step2Labels := by
      have ha : raw4906step2 = (fun i j => raw4906step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4906step2 raw4906step1; decide +kernel
      have hl : raw4906step2Labels = raw4906step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4906step1 raw4906step1Labels permutation10 permutation2
    _ = mixedMoment B node1242 node1242Labels := by rfl

theorem canonical4909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4909 raw4909Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw4909 raw4909Labels = mixedMoment B raw4909step0 raw4909step0Labels := by
      have hz : ∀ j, raw4909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4909step0 = (fun i j => raw4909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4909step0 raw4909; decide +kernel
      have hl : raw4909step0Labels = raw4909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909 raw4909Labels permutation434 hz
    mixedMoment B raw4909step0 raw4909step0Labels = mixedMoment B raw4909step1 raw4909step1Labels := by
      have hz : ∀ j, raw4909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4909step1 = (fun i j => raw4909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4909step1 raw4909step0; decide +kernel
      have hl : raw4909step1Labels = raw4909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4909step0 raw4909step0Labels permutation80 hz
    _ = mixedMoment B node1264 node1264Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical72
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9224 raw9224Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9224 raw9224Labels = mixedMoment B raw9224step0 raw9224step0Labels := by
      have hz : ∀ j, raw9224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9224step0 = (fun i j => raw9224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9224step0 raw9224; decide +kernel
      have hl : raw9224step0Labels = raw9224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9224 raw9224Labels permutation265 hz
    mixedMoment B raw9224step0 raw9224step0Labels = mixedMoment B raw9224step1 raw9224step1Labels := by
      have ha : raw9224step1 = (fun i j => raw9224step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9224step1 raw9224step0; decide +kernel
      have hl : raw9224step1Labels = raw9224step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9224step0 raw9224step0Labels permutation146 permutation0
    mixedMoment B raw9224step1 raw9224step1Labels = mixedMoment B raw9224step2 raw9224step2Labels := by
      have ha : raw9224step2 = -raw9224step1 := by apply Matrix.ext; change ∀ i j, raw9224step2 i j = -(raw9224step1 i j); unfold raw9224step2 raw9224step1; decide +kernel
      have hl : raw9224step2Labels = raw9224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical9229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9229 raw9229Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw9229 raw9229Labels = mixedMoment B raw9229step0 raw9229step0Labels := by
      have hz : ∀ j, raw9229 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9229step0 = (fun i j => raw9229 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9229step0 raw9229; decide +kernel
      have hl : raw9229step0Labels = raw9229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9229 raw9229Labels permutation265 hz
    _ = mixedMoment B node1388 node1388Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical73
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9457 raw9457Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw9457 raw9457Labels = mixedMoment B raw9457step0 raw9457step0Labels := by
      have hz : ∀ j, raw9457 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9457step0 = (fun i j => raw9457 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9457step0 raw9457; decide +kernel
      have hl : raw9457step0Labels = raw9457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9457 raw9457Labels permutation520 hz
    mixedMoment B raw9457step0 raw9457step0Labels = mixedMoment B raw9457step1 raw9457step1Labels := by
      have hz : ∀ j, raw9457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9457step1 = (fun i j => raw9457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9457step1 raw9457step0; decide +kernel
      have hl : raw9457step1Labels = raw9457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9457step0 raw9457step0Labels permutation56 hz
    mixedMoment B raw9457step1 raw9457step1Labels = mixedMoment B raw9457step2 raw9457step2Labels := by
      have ha : raw9457step2 = (fun i j => raw9457step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9457step2 raw9457step1; decide +kernel
      have hl : raw9457step2Labels = raw9457step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9457step1 raw9457step1Labels permutation26 permutation0
    mixedMoment B raw9457step2 raw9457step2Labels = mixedMoment B raw9457step3 raw9457step3Labels := by
      have ha : raw9457step3 = -raw9457step2 := by apply Matrix.ext; change ∀ i j, raw9457step3 i j = -(raw9457step2 i j); unfold raw9457step3 raw9457step2; decide +kernel
      have hl : raw9457step3Labels = raw9457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical9462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9462 raw9462Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw9462 raw9462Labels = mixedMoment B raw9462step0 raw9462step0Labels := by
      have hz : ∀ j, raw9462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9462step0 = (fun i j => raw9462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9462step0 raw9462; decide +kernel
      have hl : raw9462step0Labels = raw9462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9462 raw9462Labels permutation265 hz
    _ = mixedMoment B node1385 node1385Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical74
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical9473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9473 raw9473Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw9473 raw9473Labels = mixedMoment B raw9473step0 raw9473step0Labels := by
      have hz : ∀ j, raw9473 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9473step0 = (fun i j => raw9473 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9473step0 raw9473; decide +kernel
      have hl : raw9473step0Labels = raw9473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9473 raw9473Labels permutation265 hz
    mixedMoment B raw9473step0 raw9473step0Labels = mixedMoment B raw9473step1 raw9473step1Labels := by
      have ha : raw9473step1 = (fun i j => raw9473step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9473step1 raw9473step0; decide +kernel
      have hl : raw9473step1Labels = raw9473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9473step0 raw9473step0Labels permutation151 permutation2
    mixedMoment B raw9473step1 raw9473step1Labels = mixedMoment B raw9473step2 raw9473step2Labels := by
      have ha : raw9473step2 = -raw9473step1 := by apply Matrix.ext; change ∀ i j, raw9473step2 i j = -(raw9473step1 i j); unfold raw9473step2 raw9473step1; decide +kernel
      have hl : raw9473step2Labels = raw9473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical9580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9580 raw9580Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw9580 raw9580Labels = mixedMoment B raw9580step0 raw9580step0Labels := by
      have hz : ∀ j, raw9580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9580step0 = (fun i j => raw9580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9580step0 raw9580; decide +kernel
      have hl : raw9580step0Labels = raw9580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9580 raw9580Labels permutation434 hz
    mixedMoment B raw9580step0 raw9580step0Labels = mixedMoment B raw9580step1 raw9580step1Labels := by
      have hz : ∀ j, raw9580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9580step1 = (fun i j => raw9580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9580step1 raw9580step0; decide +kernel
      have hl : raw9580step1Labels = raw9580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9580step0 raw9580step0Labels permutation80 hz
    mixedMoment B raw9580step1 raw9580step1Labels = mixedMoment B raw9580step2 raw9580step2Labels := by
      have ha : raw9580step2 = (fun i j => raw9580step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9580step2 raw9580step1; decide +kernel
      have hl : raw9580step2Labels = raw9580step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9580step1 raw9580step1Labels permutation10 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node641 node641Labels = Sparse.eval nodeValue641 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 641) = mixedMoment B node641 node641Labels := rfl
  simpa [nodeValue641, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

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

theorem sound804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node804 node804Labels = Sparse.eval nodeValue804 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 804) = mixedMoment B node804 node804Labels := rfl
  simpa [nodeValue804, Sparse.eval] using hc.symm

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

theorem sound847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node847 node847Labels = Sparse.eval nodeValue847 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 847) = mixedMoment B node847 node847Labels := rfl
  simpa [nodeValue847, Sparse.eval] using hc.symm

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

theorem sound905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node905 node905Labels = Sparse.eval nodeValue905 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 905) = mixedMoment B node905 node905Labels := rfl
  simpa [nodeValue905, Sparse.eval] using hc.symm

theorem sound909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node909 node909Labels = Sparse.eval nodeValue909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 909) = mixedMoment B node909 node909Labels := rfl
  simpa [nodeValue909, Sparse.eval] using hc.symm

theorem sound911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node911 node911Labels = Sparse.eval nodeValue911 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 911) = mixedMoment B node911 node911Labels := rfl
  simpa [nodeValue911, Sparse.eval] using hc.symm

theorem sound936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node936 node936Labels = Sparse.eval nodeValue936 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 936) = mixedMoment B node936 node936Labels := rfl
  simpa [nodeValue936, Sparse.eval] using hc.symm

theorem sound945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node945 node945Labels = Sparse.eval nodeValue945 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 945) = mixedMoment B node945 node945Labels := rfl
  simpa [nodeValue945, Sparse.eval] using hc.symm

theorem sound949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node949 node949Labels = Sparse.eval nodeValue949 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 949) = mixedMoment B node949 node949Labels := rfl
  simpa [nodeValue949, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node997 node997Labels = Sparse.eval nodeValue997 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 997) = mixedMoment B node997 node997Labels := rfl
  simpa [nodeValue997, Sparse.eval] using hc.symm

theorem sound1011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1011 node1011Labels = Sparse.eval nodeValue1011 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1011) = mixedMoment B node1011 node1011Labels := rfl
  simpa [nodeValue1011, Sparse.eval] using hc.symm

theorem sound1022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1022 node1022Labels = Sparse.eval nodeValue1022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1022) = mixedMoment B node1022 node1022Labels := rfl
  simpa [nodeValue1022, Sparse.eval] using hc.symm

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

theorem sound1024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1024 node1024Labels = Sparse.eval nodeValue1024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1024) = mixedMoment B node1024 node1024Labels := rfl
  simpa [nodeValue1024, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

theorem sound1046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1046 node1046Labels = Sparse.eval nodeValue1046 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1046) = mixedMoment B node1046 node1046Labels := rfl
  simpa [nodeValue1046, Sparse.eval] using hc.symm

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

theorem sound1118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1118 node1118Labels = Sparse.eval nodeValue1118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1118) = mixedMoment B node1118 node1118Labels := rfl
  simpa [nodeValue1118, Sparse.eval] using hc.symm

theorem sound1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1132 node1132Labels = Sparse.eval nodeValue1132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1132) = mixedMoment B node1132 node1132Labels := rfl
  simpa [nodeValue1132, Sparse.eval] using hc.symm

theorem sound1142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1142 node1142Labels = Sparse.eval nodeValue1142 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1142) = mixedMoment B node1142 node1142Labels := rfl
  simpa [nodeValue1142, Sparse.eval] using hc.symm

theorem sound1145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1145 node1145Labels = Sparse.eval nodeValue1145 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1145) = mixedMoment B node1145 node1145Labels := rfl
  simpa [nodeValue1145, Sparse.eval] using hc.symm

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

theorem sound1155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1155 node1155Labels = Sparse.eval nodeValue1155 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1155) = mixedMoment B node1155 node1155Labels := rfl
  simpa [nodeValue1155, Sparse.eval] using hc.symm

theorem sound1159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1159 node1159Labels = Sparse.eval nodeValue1159 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1159) = mixedMoment B node1159 node1159Labels := rfl
  simpa [nodeValue1159, Sparse.eval] using hc.symm

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

theorem sound1242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1242 node1242Labels = Sparse.eval nodeValue1242 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1242) = mixedMoment B node1242 node1242Labels := rfl
  simpa [nodeValue1242, Sparse.eval] using hc.symm

theorem sound1243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1243 node1243Labels = Sparse.eval nodeValue1243 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1243) = mixedMoment B node1243 node1243Labels := rfl
  simpa [nodeValue1243, Sparse.eval] using hc.symm

theorem sound1246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1246 node1246Labels = Sparse.eval nodeValue1246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1246) = mixedMoment B node1246 node1246Labels := rfl
  simpa [nodeValue1246, Sparse.eval] using hc.symm

theorem sound1264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1264 node1264Labels = Sparse.eval nodeValue1264 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1264) = mixedMoment B node1264 node1264Labels := rfl
  simpa [nodeValue1264, Sparse.eval] using hc.symm

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

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

theorem sound1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1315 node1315Labels = Sparse.eval nodeValue1315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1315) = mixedMoment B node1315 node1315Labels := rfl
  simpa [nodeValue1315, Sparse.eval] using hc.symm

theorem sound1323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1323 node1323Labels = Sparse.eval nodeValue1323 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1323) = mixedMoment B node1323 node1323Labels := rfl
  simpa [nodeValue1323, Sparse.eval] using hc.symm

theorem sound1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1326 node1326Labels = Sparse.eval nodeValue1326 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1326) = mixedMoment B node1326 node1326Labels := rfl
  simpa [nodeValue1326, Sparse.eval] using hc.symm

theorem sound1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1327 node1327Labels = Sparse.eval nodeValue1327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1327) = mixedMoment B node1327 node1327Labels := rfl
  simpa [nodeValue1327, Sparse.eval] using hc.symm

theorem sound1332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1332 node1332Labels = Sparse.eval nodeValue1332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1332) = mixedMoment B node1332 node1332Labels := rfl
  simpa [nodeValue1332, Sparse.eval] using hc.symm

theorem sound1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1333 node1333Labels = Sparse.eval nodeValue1333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1333) = mixedMoment B node1333 node1333Labels := rfl
  simpa [nodeValue1333, Sparse.eval] using hc.symm

theorem sound1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1336 node1336Labels = Sparse.eval nodeValue1336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1336) = mixedMoment B node1336 node1336Labels := rfl
  simpa [nodeValue1336, Sparse.eval] using hc.symm

theorem sound1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1337 node1337Labels = Sparse.eval nodeValue1337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1337) = mixedMoment B node1337 node1337Labels := rfl
  simpa [nodeValue1337, Sparse.eval] using hc.symm

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

theorem sound1355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1355 node1355Labels = Sparse.eval nodeValue1355 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1355) = mixedMoment B node1355 node1355Labels := rfl
  simpa [nodeValue1355, Sparse.eval] using hc.symm

theorem sound1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1369 node1369Labels = Sparse.eval nodeValue1369 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1369) = mixedMoment B node1369 node1369Labels := rfl
  simpa [nodeValue1369, Sparse.eval] using hc.symm

theorem sound1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1385 node1385Labels = Sparse.eval nodeValue1385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1385) = mixedMoment B node1385 node1385Labels := rfl
  simpa [nodeValue1385, Sparse.eval] using hc.symm

theorem sound1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1388 node1388Labels = Sparse.eval nodeValue1388 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1388) = mixedMoment B node1388 node1388Labels := rfl
  simpa [nodeValue1388, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1596 node1596Labels = 0 := by
  exact mixedMoment_alpha B hF node1596 node1596Labels 1 permutation437
    (by decide +kernel)

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1596 node1596Labels = Sparse.eval nodeValue1596 (mixedVector B) := by
  simpa only [nodeValue1596, Sparse.eval_nil] using zero1596 B _hB _hF

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

theorem sound1604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1604 node1604Labels = Sparse.eval nodeValue1604 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1604) = mixedMoment B node1604 node1604Labels := rfl
  simpa [nodeValue1604, Sparse.eval] using hc.symm

theorem sound1613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1613 node1613Labels = Sparse.eval nodeValue1613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1613) = mixedMoment B node1613 node1613Labels := rfl
  simpa [nodeValue1613, Sparse.eval] using hc.symm

theorem sound1643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1643 node1643Labels = Sparse.eval nodeValue1643 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1643) = mixedMoment B node1643 node1643Labels := rfl
  simpa [nodeValue1643, Sparse.eval] using hc.symm

theorem sound1647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1647 node1647Labels = Sparse.eval nodeValue1647 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1647) = mixedMoment B node1647 node1647Labels := rfl
  simpa [nodeValue1647, Sparse.eval] using hc.symm

theorem sound1652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1652 node1652Labels = Sparse.eval nodeValue1652 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1652) = mixedMoment B node1652 node1652Labels := rfl
  simpa [nodeValue1652, Sparse.eval] using hc.symm

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

theorem sound1746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1746 node1746Labels = Sparse.eval nodeValue1746 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1746) = mixedMoment B node1746 node1746Labels := rfl
  simpa [nodeValue1746, Sparse.eval] using hc.symm

theorem sound1750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1750 node1750Labels = Sparse.eval nodeValue1750 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1750) = mixedMoment B node1750 node1750Labels := rfl
  simpa [nodeValue1750, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1902 node1902Labels = Sparse.eval nodeValue1902 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1902) = mixedMoment B node1902 node1902Labels := rfl
  simpa [nodeValue1902, Sparse.eval] using hc.symm

theorem sound1915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1915 node1915Labels = Sparse.eval nodeValue1915 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1915) = mixedMoment B node1915 node1915Labels := rfl
  simpa [nodeValue1915, Sparse.eval] using hc.symm

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

theorem sound1926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1926 node1926Labels = Sparse.eval nodeValue1926 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1926) = mixedMoment B node1926 node1926Labels := rfl
  simpa [nodeValue1926, Sparse.eval] using hc.symm

theorem sound1942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1942 node1942Labels = Sparse.eval nodeValue1942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1942) = mixedMoment B node1942 node1942Labels := rfl
  simpa [nodeValue1942, Sparse.eval] using hc.symm

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

theorem sound1995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1995 node1995Labels = Sparse.eval nodeValue1995 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1995) = mixedMoment B node1995 node1995Labels := rfl
  simpa [nodeValue1995, Sparse.eval] using hc.symm

theorem sound2005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2005 node2005Labels = Sparse.eval nodeValue2005 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2005) = mixedMoment B node2005 node2005Labels := rfl
  simpa [nodeValue2005, Sparse.eval] using hc.symm

theorem sound2025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2025 node2025Labels = Sparse.eval nodeValue2025 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2025) = mixedMoment B node2025 node2025Labels := rfl
  simpa [nodeValue2025, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2197 node2197Labels = Sparse.eval nodeValue2197 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2197) = mixedMoment B node2197 node2197Labels := rfl
  simpa [nodeValue2197, Sparse.eval] using hc.symm

theorem sound2226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2226 node2226Labels = Sparse.eval nodeValue2226 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2226) = mixedMoment B node2226 node2226Labels := rfl
  simpa [nodeValue2226, Sparse.eval] using hc.symm

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

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3024 node3024Labels = Sparse.eval nodeValue3024 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3024) = mixedMoment B node3024 node3024Labels := rfl
  simpa [nodeValue3024, Sparse.eval] using hc.symm

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

theorem sound3279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3279 node3279Labels = Sparse.eval nodeValue3279 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3279) = mixedMoment B node3279 node3279Labels := rfl
  simpa [nodeValue3279, Sparse.eval] using hc.symm

theorem sound3283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3283 node3283Labels = Sparse.eval nodeValue3283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3283) = mixedMoment B node3283 node3283Labels := rfl
  simpa [nodeValue3283, Sparse.eval] using hc.symm

theorem sound3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3300 node3300Labels = Sparse.eval nodeValue3300 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3300) = mixedMoment B node3300 node3300Labels := rfl
  simpa [nodeValue3300, Sparse.eval] using hc.symm

theorem sound3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3302 node3302Labels = Sparse.eval nodeValue3302 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3302) = mixedMoment B node3302 node3302Labels := rfl
  simpa [nodeValue3302, Sparse.eval] using hc.symm

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

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node581 node581Labels = Sparse.eval nodeValue581 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 581) = mixedMoment B node581 node581Labels := rfl
  simpa [nodeValue581, Sparse.eval] using hc.symm

theorem sound585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node585 node585Labels = Sparse.eval nodeValue585 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 585) = mixedMoment B node585 node585Labels := rfl
  simpa [nodeValue585, Sparse.eval] using hc.symm

theorem sound636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node636 node636Labels = Sparse.eval nodeValue636 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 636) = mixedMoment B node636 node636Labels := rfl
  simpa [nodeValue636, Sparse.eval] using hc.symm

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

theorem sourceEq1218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1218 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 0) (sourceB1218 + difference 0 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 815) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 0) (sourceB1218 + difference 0 5) sourceC1218) = raw20158 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20158; decide +kernel
    rw [ha]
    exact (canonical20158 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 1) (sourceB1218 + difference 1 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 1) (sourceB1218 + difference 1 5) sourceC1218) = raw20164 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20164; decide +kernel
    rw [ha]
    exact (canonical20164 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 2) (sourceB1218 + difference 2 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1604) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 2) (sourceB1218 + difference 2 5) sourceC1218) = raw20165 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20165; decide +kernel
    rw [ha]
    exact (canonical20165 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 3) (sourceB1218 + difference 3 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 3) (sourceB1218 + difference 3 5) sourceC1218) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 4) (sourceB1218 + difference 4 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1652) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 4) (sourceB1218 + difference 4 5) sourceC1218) = raw20166 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20166; decide +kernel
    rw [ha]
    exact (canonical20166 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1218 + difference 5 5) (sourceB1218 + difference 5 5) sourceC1218) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1729) := by
    have ha : (tripleCharges (sourceA1218 + difference 5 5) (sourceB1218 + difference 5 5) sourceC1218) = raw20148 := by
      apply Matrix.ext; unfold tripleCharges sourceA1218 sourceB1218 sourceC1218 difference raw20148; decide +kernel
    rw [ha]
    exact (canonical20148 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1218 + sourceB1218) sourceC1218) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1218 + sourceB1218) sourceC1218) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1218 sourceB1218 sourceC1218 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1218 sourceB1218 sourceC1218
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1218, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1220 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1220 + difference 0 3) (sourceB1220 + difference 3 0) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2062) := by
    have ha : (tripleCharges (sourceA1220 + difference 0 3) (sourceB1220 + difference 3 0) sourceC1220) = raw20170 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20170; decide +kernel
    rw [ha]
    exact (canonical20170 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1220 + difference 1 3) (sourceB1220 + difference 3 1) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1315) := by
    have ha : (tripleCharges (sourceA1220 + difference 1 3) (sourceB1220 + difference 3 1) sourceC1220) = raw20171 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20171; decide +kernel
    rw [ha]
    exact (canonical20171 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1220 + difference 2 3) (sourceB1220 + difference 3 2) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1315) := by
    have ha : (tripleCharges (sourceA1220 + difference 2 3) (sourceB1220 + difference 3 2) sourceC1220) = raw20172 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20172; decide +kernel
    rw [ha]
    exact (canonical20172 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1220 + difference 3 3) (sourceB1220 + difference 3 3) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1369) := by
    have ha : (tripleCharges (sourceA1220 + difference 3 3) (sourceB1220 + difference 3 3) sourceC1220) = raw20173 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20173; decide +kernel
    rw [ha]
    exact (canonical20173 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1220 + difference 4 3) (sourceB1220 + difference 3 4) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1323) := by
    have ha : (tripleCharges (sourceA1220 + difference 4 3) (sourceB1220 + difference 3 4) sourceC1220) = raw20174 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20174; decide +kernel
    rw [ha]
    exact (canonical20174 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1220 + difference 5 3) (sourceB1220 + difference 3 5) sourceC1220) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 936) := by
    have ha : (tripleCharges (sourceA1220 + difference 5 3) (sourceB1220 + difference 3 5) sourceC1220) = raw20175 := by
      apply Matrix.ext; unfold tripleCharges sourceA1220 sourceB1220 sourceC1220 difference raw20175; decide +kernel
    rw [ha]
    exact (canonical20175 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1220 + sourceB1220) sourceC1220) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1220 + sourceB1220) sourceC1220) = raw20176 := by
      apply Matrix.ext; unfold doubleCharges sourceA1220 sourceB1220 sourceC1220 raw20176; decide +kernel
    rw [ha]
    exact (canonical20176 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1220 sourceB1220 sourceC1220
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1220, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1221 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 0) (sourceB1221 + difference 0 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1746) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 0) (sourceB1221 + difference 0 0) sourceC1221) = raw20132 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20132; decide +kernel
    rw [ha]
    exact (canonical20132 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 1) (sourceB1221 + difference 1 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 1) (sourceB1221 + difference 1 0) sourceC1221) = raw20177 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20177; decide +kernel
    rw [ha]
    exact (canonical20177 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 2) (sourceB1221 + difference 2 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2005) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 2) (sourceB1221 + difference 2 0) sourceC1221) = raw20178 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20178; decide +kernel
    rw [ha]
    exact (canonical20178 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 3) (sourceB1221 + difference 3 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 3) (sourceB1221 + difference 3 0) sourceC1221) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 4) (sourceB1221 + difference 4 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1952) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 4) (sourceB1221 + difference 4 0) sourceC1221) = raw20153 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20153; decide +kernel
    rw [ha]
    exact (canonical20153 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1221 + difference 0 5) (sourceB1221 + difference 5 0) sourceC1221) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1011) := by
    have ha : (tripleCharges (sourceA1221 + difference 0 5) (sourceB1221 + difference 5 0) sourceC1221) = raw20179 := by
      apply Matrix.ext; unfold tripleCharges sourceA1221 sourceB1221 sourceC1221 difference raw20179; decide +kernel
    rw [ha]
    exact (canonical20179 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1221 + sourceB1221) sourceC1221) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1221 + sourceB1221) sourceC1221) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1221 sourceB1221 sourceC1221 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1221 sourceB1221 sourceC1221
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1221, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1224 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 0) (sourceB1224 + difference 0 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 581) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 0) (sourceB1224 + difference 0 2) sourceC1224) = raw20190 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20190; decide +kernel
    rw [ha]
    exact (canonical20190 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 1) (sourceB1224 + difference 1 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 905) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 1) (sourceB1224 + difference 1 2) sourceC1224) = raw20191 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20191; decide +kernel
    rw [ha]
    exact (canonical20191 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 2) (sourceB1224 + difference 2 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1022) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 2) (sourceB1224 + difference 2 2) sourceC1224) = raw20192 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20192; decide +kernel
    rw [ha]
    exact (canonical20192 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 3) (sourceB1224 + difference 3 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 945) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 3) (sourceB1224 + difference 3 2) sourceC1224) = raw20193 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20193; decide +kernel
    rw [ha]
    exact (canonical20193 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 4) (sourceB1224 + difference 4 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1046) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 4) (sourceB1224 + difference 4 2) sourceC1224) = raw20194 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20194; decide +kernel
    rw [ha]
    exact (canonical20194 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1224 + difference 2 5) (sourceB1224 + difference 5 2) sourceC1224) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1224 + difference 2 5) (sourceB1224 + difference 5 2) sourceC1224) = raw20195 := by
      apply Matrix.ext; unfold tripleCharges sourceA1224 sourceB1224 sourceC1224 difference raw20195; decide +kernel
    rw [ha]
    exact (canonical20195 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1224 + sourceB1224) sourceC1224) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1224 + sourceB1224) sourceC1224) = raw20196 := by
      apply Matrix.ext; unfold doubleCharges sourceA1224 sourceB1224 sourceC1224 raw20196; decide +kernel
    rw [ha]
    exact (canonical20196 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1224 sourceB1224 sourceC1224
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1224, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1225 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1225 + difference 0 2) (sourceB1225 + difference 2 0) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1225 + difference 0 2) (sourceB1225 + difference 2 0) sourceC1225) = raw20197 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20197; decide +kernel
    rw [ha]
    exact (canonical20197 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1225 + difference 1 2) (sourceB1225 + difference 2 1) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1225 + difference 1 2) (sourceB1225 + difference 2 1) sourceC1225) = raw20198 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20198; decide +kernel
    rw [ha]
    exact (canonical20198 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1225 + difference 2 2) (sourceB1225 + difference 2 2) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1388) := by
    have ha : (tripleCharges (sourceA1225 + difference 2 2) (sourceB1225 + difference 2 2) sourceC1225) = raw9229 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw9229; decide +kernel
    rw [ha]
    exact (canonical9229 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1225 + difference 3 2) (sourceB1225 + difference 2 3) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1337) := by
    have ha : (tripleCharges (sourceA1225 + difference 3 2) (sourceB1225 + difference 2 3) sourceC1225) = raw20199 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20199; decide +kernel
    rw [ha]
    exact (canonical20199 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1225 + difference 4 2) (sourceB1225 + difference 2 4) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1333) := by
    have ha : (tripleCharges (sourceA1225 + difference 4 2) (sourceB1225 + difference 2 4) sourceC1225) = raw20200 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20200; decide +kernel
    rw [ha]
    exact (canonical20200 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1225 + difference 5 2) (sourceB1225 + difference 2 5) sourceC1225) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1118) := by
    have ha : (tripleCharges (sourceA1225 + difference 5 2) (sourceB1225 + difference 2 5) sourceC1225) = raw20201 := by
      apply Matrix.ext; unfold tripleCharges sourceA1225 sourceB1225 sourceC1225 difference raw20201; decide +kernel
    rw [ha]
    exact (canonical20201 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1225 + sourceB1225) sourceC1225) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1225 + sourceB1225) sourceC1225) = raw9224 := by
      apply Matrix.ext; unfold doubleCharges sourceA1225 sourceB1225 sourceC1225 raw9224; decide +kernel
    rw [ha]
    exact (canonical9224 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1225 sourceB1225 sourceC1225
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1225, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1226 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 0) (sourceB1226 + difference 0 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 0) (sourceB1226 + difference 0 0) sourceC1226) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 1) (sourceB1226 + difference 1 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3279) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 1) (sourceB1226 + difference 1 0) sourceC1226) = raw20202 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20202; decide +kernel
    rw [ha]
    exact (canonical20202 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 2) (sourceB1226 + difference 2 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 2) (sourceB1226 + difference 2 0) sourceC1226) = raw20151 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20151; decide +kernel
    rw [ha]
    exact (canonical20151 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 3) (sourceB1226 + difference 3 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3300) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 3) (sourceB1226 + difference 3 0) sourceC1226) = raw20203 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20203; decide +kernel
    rw [ha]
    exact (canonical20203 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 4) (sourceB1226 + difference 4 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3283) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 4) (sourceB1226 + difference 4 0) sourceC1226) = raw20204 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20204; decide +kernel
    rw [ha]
    exact (canonical20204 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1226 + difference 0 5) (sourceB1226 + difference 5 0) sourceC1226) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1942) := by
    have ha : (tripleCharges (sourceA1226 + difference 0 5) (sourceB1226 + difference 5 0) sourceC1226) = raw20205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1226 sourceB1226 sourceC1226 difference raw20205; decide +kernel
    rw [ha]
    exact (canonical20205 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1226 + sourceB1226) sourceC1226) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1226 + sourceB1226) sourceC1226) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1226 sourceB1226 sourceC1226 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1226 sourceB1226 sourceC1226
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1226, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1228 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 0) (sourceB1228 + difference 0 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 847) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 0) (sourceB1228 + difference 0 4) sourceC1228) = raw20208 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20208; decide +kernel
    rw [ha]
    exact (canonical20208 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 1) (sourceB1228 + difference 1 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1613) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 1) (sourceB1228 + difference 1 4) sourceC1228) = raw20210 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20210; decide +kernel
    rw [ha]
    exact (canonical20210 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 2) (sourceB1228 + difference 2 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 2) (sourceB1228 + difference 2 4) sourceC1228) = raw20133 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20133; decide +kernel
    rw [ha]
    exact (canonical20133 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 3) (sourceB1228 + difference 3 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1750) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 3) (sourceB1228 + difference 3 4) sourceC1228) = raw20211 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20211; decide +kernel
    rw [ha]
    exact (canonical20211 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 4) (sourceB1228 + difference 4 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 4) (sourceB1228 + difference 4 4) sourceC1228) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1228 + difference 4 5) (sourceB1228 + difference 5 4) sourceC1228) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1228 + difference 4 5) (sourceB1228 + difference 5 4) sourceC1228) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1228 sourceB1228 sourceC1228 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1228 + sourceB1228) sourceC1228) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1228 + sourceB1228) sourceC1228) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1228 sourceB1228 sourceC1228 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1228 sourceB1228 sourceC1228
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1228, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1229 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 0) (sourceB1229 + difference 0 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 804) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 0) (sourceB1229 + difference 0 5) sourceC1229) = raw20209 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20209; decide +kernel
    rw [ha]
    exact (canonical20209 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 1) (sourceB1229 + difference 1 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1596) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 1) (sourceB1229 + difference 1 5) sourceC1229) = raw20212 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20212; decide +kernel
    rw [ha]
    exact (canonical20212 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 2) (sourceB1229 + difference 2 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 2) (sourceB1229 + difference 2 5) sourceC1229) = raw20161 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20161; decide +kernel
    rw [ha]
    exact (canonical20161 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 3) (sourceB1229 + difference 3 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 3) (sourceB1229 + difference 3 5) sourceC1229) = raw20213 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20213; decide +kernel
    rw [ha]
    exact (canonical20213 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 4) (sourceB1229 + difference 4 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 4) (sourceB1229 + difference 4 5) sourceC1229) = raw20214 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20214; decide +kernel
    rw [ha]
    exact (canonical20214 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1229 + difference 5 5) (sourceB1229 + difference 5 5) sourceC1229) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1723) := by
    have ha : (tripleCharges (sourceA1229 + difference 5 5) (sourceB1229 + difference 5 5) sourceC1229) = raw20160 := by
      apply Matrix.ext; unfold tripleCharges sourceA1229 sourceB1229 sourceC1229 difference raw20160; decide +kernel
    rw [ha]
    exact (canonical20160 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1229 + sourceB1229) sourceC1229) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1229 + sourceB1229) sourceC1229) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1229 sourceB1229 sourceC1229 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1229 sourceB1229 sourceC1229
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1229, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1231 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 0) (sourceB1231 + difference 0 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 585) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 0) (sourceB1231 + difference 0 2) sourceC1231) = raw20217 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20217; decide +kernel
    rw [ha]
    exact (canonical20217 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 1) (sourceB1231 + difference 1 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 909) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 1) (sourceB1231 + difference 1 2) sourceC1231) = raw20218 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20218; decide +kernel
    rw [ha]
    exact (canonical20218 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 2) (sourceB1231 + difference 2 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 2) (sourceB1231 + difference 2 2) sourceC1231) = raw3838 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw3838; decide +kernel
    rw [ha]
    exact (canonical3838 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 3) (sourceB1231 + difference 3 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 949) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 3) (sourceB1231 + difference 3 2) sourceC1231) = raw20219 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20219; decide +kernel
    rw [ha]
    exact (canonical20219 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 4) (sourceB1231 + difference 4 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1024) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 4) (sourceB1231 + difference 4 2) sourceC1231) = raw3836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw3836; decide +kernel
    rw [ha]
    exact (canonical3836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1231 + difference 2 5) (sourceB1231 + difference 5 2) sourceC1231) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1231 + difference 2 5) (sourceB1231 + difference 5 2) sourceC1231) = raw20220 := by
      apply Matrix.ext; unfold tripleCharges sourceA1231 sourceB1231 sourceC1231 difference raw20220; decide +kernel
    rw [ha]
    exact (canonical20220 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1231 + sourceB1231) sourceC1231) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1231 + sourceB1231) sourceC1231) = raw3834 := by
      apply Matrix.ext; unfold doubleCharges sourceA1231 sourceB1231 sourceC1231 raw3834; decide +kernel
    rw [ha]
    exact (canonical3834 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1231 sourceB1231 sourceC1231
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1231, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1232 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1232 + difference 0 2) (sourceB1232 + difference 2 0) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2025) := by
    have ha : (tripleCharges (sourceA1232 + difference 0 2) (sourceB1232 + difference 2 0) sourceC1232) = raw9473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw9473; decide +kernel
    rw [ha]
    exact (canonical9473 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1232 + difference 1 2) (sourceB1232 + difference 2 1) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1326) := by
    have ha : (tripleCharges (sourceA1232 + difference 1 2) (sourceB1232 + difference 2 1) sourceC1232) = raw20221 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20221; decide +kernel
    rw [ha]
    exact (canonical20221 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1232 + difference 2 2) (sourceB1232 + difference 2 2) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1385) := by
    have ha : (tripleCharges (sourceA1232 + difference 2 2) (sourceB1232 + difference 2 2) sourceC1232) = raw9462 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw9462; decide +kernel
    rw [ha]
    exact (canonical9462 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1232 + difference 3 2) (sourceB1232 + difference 2 3) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1336) := by
    have ha : (tripleCharges (sourceA1232 + difference 3 2) (sourceB1232 + difference 2 3) sourceC1232) = raw20222 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20222; decide +kernel
    rw [ha]
    exact (canonical20222 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1232 + difference 4 2) (sourceB1232 + difference 2 4) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1332) := by
    have ha : (tripleCharges (sourceA1232 + difference 4 2) (sourceB1232 + difference 2 4) sourceC1232) = raw20223 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20223; decide +kernel
    rw [ha]
    exact (canonical20223 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1232 + difference 5 2) (sourceB1232 + difference 2 5) sourceC1232) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 911) := by
    have ha : (tripleCharges (sourceA1232 + difference 5 2) (sourceB1232 + difference 2 5) sourceC1232) = raw20224 := by
      apply Matrix.ext; unfold tripleCharges sourceA1232 sourceB1232 sourceC1232 difference raw20224; decide +kernel
    rw [ha]
    exact (canonical20224 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1232 + sourceB1232) sourceC1232) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1232 + sourceB1232) sourceC1232) = raw9457 := by
      apply Matrix.ext; unfold doubleCharges sourceA1232 sourceB1232 sourceC1232 raw9457; decide +kernel
    rw [ha]
    exact (canonical9457 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1232 sourceB1232 sourceC1232
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1232, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1233 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 0) (sourceB1233 + difference 0 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1744) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 0) (sourceB1233 + difference 0 0) sourceC1233) = raw20131 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20131; decide +kernel
    rw [ha]
    exact (canonical20131 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 1) (sourceB1233 + difference 1 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1995) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 1) (sourceB1233 + difference 1 0) sourceC1233) = raw20225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20225; decide +kernel
    rw [ha]
    exact (canonical20225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 2) (sourceB1233 + difference 2 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 2) (sourceB1233 + difference 2 0) sourceC1233) = raw20123 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20123; decide +kernel
    rw [ha]
    exact (canonical20123 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 3) (sourceB1233 + difference 3 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2226) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 3) (sourceB1233 + difference 3 0) sourceC1233) = raw20226 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20226; decide +kernel
    rw [ha]
    exact (canonical20226 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 4) (sourceB1233 + difference 4 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1942) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 4) (sourceB1233 + difference 4 0) sourceC1233) = raw20205 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20205; decide +kernel
    rw [ha]
    exact (canonical20205 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1233 + difference 0 5) (sourceB1233 + difference 5 0) sourceC1233) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 997) := by
    have ha : (tripleCharges (sourceA1233 + difference 0 5) (sourceB1233 + difference 5 0) sourceC1233) = raw20227 := by
      apply Matrix.ext; unfold tripleCharges sourceA1233 sourceB1233 sourceC1233 difference raw20227; decide +kernel
    rw [ha]
    exact (canonical20227 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1233 + sourceB1233) sourceC1233) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1233 + sourceB1233) sourceC1233) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1233 sourceB1233 sourceC1233 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1233 sourceB1233 sourceC1233
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1233, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1235 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 0) (sourceB1235 + difference 0 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1355) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 0) (sourceB1235 + difference 0 0) sourceC1235) = raw20230 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20230; decide +kernel
    rw [ha]
    exact (canonical20230 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 1) (sourceB1235 + difference 1 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1902) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 1) (sourceB1235 + difference 1 0) sourceC1235) = raw20231 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20231; decide +kernel
    rw [ha]
    exact (canonical20231 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 2) (sourceB1235 + difference 2 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1926) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 2) (sourceB1235 + difference 2 0) sourceC1235) = raw20232 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20232; decide +kernel
    rw [ha]
    exact (canonical20232 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 3) (sourceB1235 + difference 3 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1915) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 3) (sourceB1235 + difference 3 0) sourceC1235) = raw20233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20233; decide +kernel
    rw [ha]
    exact (canonical20233 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 4) (sourceB1235 + difference 4 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2197) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 4) (sourceB1235 + difference 4 0) sourceC1235) = raw20234 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20234; decide +kernel
    rw [ha]
    exact (canonical20234 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1235 + difference 0 5) (sourceB1235 + difference 5 0) sourceC1235) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3024) := by
    have ha : (tripleCharges (sourceA1235 + difference 0 5) (sourceB1235 + difference 5 0) sourceC1235) = raw20235 := by
      apply Matrix.ext; unfold tripleCharges sourceA1235 sourceB1235 sourceC1235 difference raw20235; decide +kernel
    rw [ha]
    exact (canonical20235 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1235 + sourceB1235) sourceC1235) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1235 + sourceB1235) sourceC1235) = raw20236 := by
      apply Matrix.ext; unfold doubleCharges sourceA1235 sourceB1235 sourceC1235 raw20236; decide +kernel
    rw [ha]
    exact (canonical20236 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1235 sourceB1235 sourceC1235
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1235, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1237 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1237 + difference 0 1) (sourceB1237 + difference 1 0) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2519) := by
    have ha : (tripleCharges (sourceA1237 + difference 0 1) (sourceB1237 + difference 1 0) sourceC1237) = raw4020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw4020; decide +kernel
    rw [ha]
    exact (canonical4020 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1237 + difference 1 1) (sourceB1237 + difference 1 1) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1237 + difference 1 1) (sourceB1237 + difference 1 1) sourceC1237) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1237 + difference 2 1) (sourceB1237 + difference 1 2) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1237 + difference 2 1) (sourceB1237 + difference 1 2) sourceC1237) = raw20244 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20244; decide +kernel
    rw [ha]
    exact (canonical20244 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1237 + difference 3 1) (sourceB1237 + difference 1 3) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1237 + difference 3 1) (sourceB1237 + difference 1 3) sourceC1237) = raw20245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20245; decide +kernel
    rw [ha]
    exact (canonical20245 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1237 + difference 4 1) (sourceB1237 + difference 1 4) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1237 + difference 4 1) (sourceB1237 + difference 1 4) sourceC1237) = raw20246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20246; decide +kernel
    rw [ha]
    exact (canonical20246 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1237 + difference 5 1) (sourceB1237 + difference 1 5) sourceC1237) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1142) := by
    have ha : (tripleCharges (sourceA1237 + difference 5 1) (sourceB1237 + difference 1 5) sourceC1237) = raw20247 := by
      apply Matrix.ext; unfold tripleCharges sourceA1237 sourceB1237 sourceC1237 difference raw20247; decide +kernel
    rw [ha]
    exact (canonical20247 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1237 + sourceB1237) sourceC1237) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1237 + sourceB1237) sourceC1237) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1237 sourceB1237 sourceC1237 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1237 sourceB1237 sourceC1237
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1237, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1238 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 0) (sourceB1238 + difference 0 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 636) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 0) (sourceB1238 + difference 0 4) sourceC1238) = raw20248 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20248; decide +kernel
    rw [ha]
    exact (canonical20248 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 1) (sourceB1238 + difference 1 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1145) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 1) (sourceB1238 + difference 1 4) sourceC1238) = raw20246 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20246; decide +kernel
    rw [ha]
    exact (canonical20246 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 2) (sourceB1238 + difference 2 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 2) (sourceB1238 + difference 2 4) sourceC1238) = raw20249 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20249; decide +kernel
    rw [ha]
    exact (canonical20249 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 3) (sourceB1238 + difference 3 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1155) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 3) (sourceB1238 + difference 3 4) sourceC1238) = raw20250 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20250; decide +kernel
    rw [ha]
    exact (canonical20250 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 4) (sourceB1238 + difference 4 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1243) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 4) (sourceB1238 + difference 4 4) sourceC1238) = raw4012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw4012; decide +kernel
    rw [ha]
    exact (canonical4012 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1238 + difference 4 5) (sourceB1238 + difference 5 4) sourceC1238) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1246) := by
    have ha : (tripleCharges (sourceA1238 + difference 4 5) (sourceB1238 + difference 5 4) sourceC1238) = raw20251 := by
      apply Matrix.ext; unfold tripleCharges sourceA1238 sourceB1238 sourceC1238 difference raw20251; decide +kernel
    rw [ha]
    exact (canonical20251 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1238 + sourceB1238) sourceC1238) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1238 + sourceB1238) sourceC1238) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1238 sourceB1238 sourceC1238 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1238 sourceB1238 sourceC1238
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1238, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1239 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 0) (sourceB1239 + difference 0 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 641) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 0) (sourceB1239 + difference 0 1) sourceC1239) = raw20252 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw20252; decide +kernel
    rw [ha]
    exact (canonical20252 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 1) (sourceB1239 + difference 1 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1264) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 1) (sourceB1239 + difference 1 1) sourceC1239) = raw4909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw4909; decide +kernel
    rw [ha]
    exact (canonical4909 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 2) (sourceB1239 + difference 2 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 2) (sourceB1239 + difference 2 1) sourceC1239) = raw20253 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw20253; decide +kernel
    rw [ha]
    exact (canonical20253 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 3) (sourceB1239 + difference 3 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1159) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 3) (sourceB1239 + difference 3 1) sourceC1239) = raw20254 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw20254; decide +kernel
    rw [ha]
    exact (canonical20254 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 4) (sourceB1239 + difference 4 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1242) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 4) (sourceB1239 + difference 4 1) sourceC1239) = raw4906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw4906; decide +kernel
    rw [ha]
    exact (canonical4906 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1239 + difference 1 5) (sourceB1239 + difference 5 1) sourceC1239) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1239 + difference 1 5) (sourceB1239 + difference 5 1) sourceC1239) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1239 sourceB1239 sourceC1239 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1239 + sourceB1239) sourceC1239) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1239 + sourceB1239) sourceC1239) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA1239 sourceB1239 sourceC1239 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1239 sourceB1239 sourceC1239
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1239, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1240 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 0) (sourceB1240 + difference 0 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3302) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 0) (sourceB1240 + difference 0 0) sourceC1240) = raw20255 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20255; decide +kernel
    rw [ha]
    exact (canonical20255 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 1) (sourceB1240 + difference 1 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1652) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 1) (sourceB1240 + difference 1 0) sourceC1240) = raw20256 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20256; decide +kernel
    rw [ha]
    exact (canonical20256 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 2) (sourceB1240 + difference 2 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 2) (sourceB1240 + difference 2 0) sourceC1240) = raw20257 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20257; decide +kernel
    rw [ha]
    exact (canonical20257 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 3) (sourceB1240 + difference 3 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1643) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 3) (sourceB1240 + difference 3 0) sourceC1240) = raw20258 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20258; decide +kernel
    rw [ha]
    exact (canonical20258 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 4) (sourceB1240 + difference 4 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1725) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 4) (sourceB1240 + difference 4 0) sourceC1240) = raw20259 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20259; decide +kernel
    rw [ha]
    exact (canonical20259 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1240 + difference 0 5) (sourceB1240 + difference 5 0) sourceC1240) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1647) := by
    have ha : (tripleCharges (sourceA1240 + difference 0 5) (sourceB1240 + difference 5 0) sourceC1240) = raw20260 := by
      apply Matrix.ext; unfold tripleCharges sourceA1240 sourceB1240 sourceC1240 difference raw20260; decide +kernel
    rw [ha]
    exact (canonical20260 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1240 + sourceB1240) sourceC1240) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4070) := by
    have ha : (doubleCharges (sourceA1240 + sourceB1240) sourceC1240) = raw20099 := by
      apply Matrix.ext; unfold doubleCharges sourceA1240 sourceB1240 sourceC1240 raw20099; decide +kernel
    rw [ha]
    exact (canonical20099 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1240 sourceB1240 sourceC1240
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1240, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1056 : Integer.Sparse.reindex keyMap MixedData.row1056 = numericRow1056 := by decide +kernel

theorem numericCheck1056 (x : Master → ℝ) : Integer.Sparse.eval numericRow1056 x =
    (1 : ℝ) * reducedSource1056 x := by
  norm_num [numericRow1056, reducedSource1056, Integer.Sparse.eval, Sparse.eval, nodeValue815, nodeValue1604, nodeValue1652, nodeValue1725, nodeValue1729, nodeValue4070]

theorem reindexCheck1057 : Integer.Sparse.reindex keyMap MixedData.row1057 = numericRow1057 := by decide +kernel

theorem numericCheck1057 (x : Master → ℝ) : Integer.Sparse.eval numericRow1057 x =
    (1 : ℝ) * reducedSource1057 x := by
  norm_num [numericRow1057, reducedSource1057, Integer.Sparse.eval, Sparse.eval, nodeValue936, nodeValue1315, nodeValue1323, nodeValue1369, nodeValue2062, nodeValue4084]

theorem reindexCheck1058 : Integer.Sparse.reindex keyMap MixedData.row1058 = numericRow1058 := by decide +kernel

theorem numericCheck1058 (x : Master → ℝ) : Integer.Sparse.eval numericRow1058 x =
    (1 : ℝ) * reducedSource1058 x := by
  norm_num [numericRow1058, reducedSource1058, Integer.Sparse.eval, Sparse.eval, nodeValue1011, nodeValue1746, nodeValue1952, nodeValue2005, nodeValue2226, nodeValue4070]

theorem reindexCheck1059 : Integer.Sparse.reindex keyMap MixedData.row1059 = numericRow1059 := by decide +kernel

theorem numericCheck1059 (x : Master → ℝ) : Integer.Sparse.eval numericRow1059 x =
    (1 : ℝ) * reducedSource1059 x := by
  norm_num [numericRow1059, reducedSource1059, Integer.Sparse.eval, Sparse.eval, nodeValue581, nodeValue905, nodeValue945, nodeValue1022, nodeValue1041, nodeValue1046, nodeValue4083]

theorem reindexCheck1060 : Integer.Sparse.reindex keyMap MixedData.row1060 = numericRow1060 := by decide +kernel

theorem numericCheck1060 (x : Master → ℝ) : Integer.Sparse.eval numericRow1060 x =
    (1 : ℝ) * reducedSource1060 x := by
  norm_num [numericRow1060, reducedSource1060, Integer.Sparse.eval, Sparse.eval, nodeValue1118, nodeValue1327, nodeValue1333, nodeValue1337, nodeValue1388, nodeValue2485, nodeValue4091]

theorem reindexCheck1061 : Integer.Sparse.reindex keyMap MixedData.row1061 = numericRow1061 := by decide +kernel

theorem numericCheck1061 (x : Master → ℝ) : Integer.Sparse.eval numericRow1061 x =
    (1 : ℝ) * reducedSource1061 x := by
  norm_num [numericRow1061, reducedSource1061, Integer.Sparse.eval, Sparse.eval, nodeValue1723, nodeValue1942, nodeValue3279, nodeValue3283, nodeValue3300, nodeValue4070]

theorem reindexCheck1062 : Integer.Sparse.reindex keyMap MixedData.row1062 = numericRow1062 := by decide +kernel

theorem numericCheck1062 (x : Master → ℝ) : Integer.Sparse.eval numericRow1062 x =
    (1 : ℝ) * reducedSource1062 x := by
  norm_num [numericRow1062, reducedSource1062, Integer.Sparse.eval, Sparse.eval, nodeValue847, nodeValue1613, nodeValue1723, nodeValue1744, nodeValue1750, nodeValue4070]

theorem reindexCheck1063 : Integer.Sparse.reindex keyMap MixedData.row1063 = numericRow1063 := by decide +kernel

theorem numericCheck1063 (x : Master → ℝ) : Integer.Sparse.eval numericRow1063 x =
    (1 : ℝ) * reducedSource1063 x := by
  norm_num [numericRow1063, reducedSource1063, Integer.Sparse.eval, Sparse.eval, nodeValue804, nodeValue1596, nodeValue1643, nodeValue1723, nodeValue1725, nodeValue4070]

theorem reindexCheck1064 : Integer.Sparse.reindex keyMap MixedData.row1064 = numericRow1064 := by decide +kernel

theorem numericCheck1064 (x : Master → ℝ) : Integer.Sparse.eval numericRow1064 x =
    (1 : ℝ) * reducedSource1064 x := by
  norm_num [numericRow1064, reducedSource1064, Integer.Sparse.eval, Sparse.eval, nodeValue585, nodeValue909, nodeValue949, nodeValue1024, nodeValue1044, nodeValue4083]

theorem reindexCheck1065 : Integer.Sparse.reindex keyMap MixedData.row1065 = numericRow1065 := by decide +kernel

theorem numericCheck1065 (x : Master → ℝ) : Integer.Sparse.eval numericRow1065 x =
    (1 : ℝ) * reducedSource1065 x := by
  norm_num [numericRow1065, reducedSource1065, Integer.Sparse.eval, Sparse.eval, nodeValue911, nodeValue1326, nodeValue1332, nodeValue1336, nodeValue1385, nodeValue2025, nodeValue4083]

theorem reindexCheck1066 : Integer.Sparse.reindex keyMap MixedData.row1066 = numericRow1066 := by decide +kernel

theorem numericCheck1066 (x : Master → ℝ) : Integer.Sparse.eval numericRow1066 x =
    (1 : ℝ) * reducedSource1066 x := by
  norm_num [numericRow1066, reducedSource1066, Integer.Sparse.eval, Sparse.eval, nodeValue997, nodeValue1744, nodeValue1942, nodeValue1995, nodeValue2226, nodeValue4070]

theorem reindexCheck1067 : Integer.Sparse.reindex keyMap MixedData.row1067 = numericRow1067 := by decide +kernel

theorem numericCheck1067 (x : Master → ℝ) : Integer.Sparse.eval numericRow1067 x =
    (1 : ℝ) * reducedSource1067 x := by
  norm_num [numericRow1067, reducedSource1067, Integer.Sparse.eval, Sparse.eval, nodeValue1355, nodeValue1902, nodeValue1915, nodeValue1926, nodeValue2197, nodeValue3024, nodeValue4080]

theorem reindexCheck1068 : Integer.Sparse.reindex keyMap MixedData.row1068 = numericRow1068 := by decide +kernel

theorem numericCheck1068 (x : Master → ℝ) : Integer.Sparse.eval numericRow1068 x =
    (1 : ℝ) * reducedSource1068 x := by
  norm_num [numericRow1068, reducedSource1068, Integer.Sparse.eval, Sparse.eval, nodeValue1132, nodeValue1142, nodeValue1145, nodeValue1243, nodeValue2519, nodeValue4092]

theorem reindexCheck1069 : Integer.Sparse.reindex keyMap MixedData.row1069 = numericRow1069 := by decide +kernel

theorem numericCheck1069 (x : Master → ℝ) : Integer.Sparse.eval numericRow1069 x =
    (1 : ℝ) * reducedSource1069 x := by
  norm_num [numericRow1069, reducedSource1069, Integer.Sparse.eval, Sparse.eval, nodeValue636, nodeValue1145, nodeValue1155, nodeValue1243, nodeValue1246, nodeValue4092]

theorem reindexCheck1070 : Integer.Sparse.reindex keyMap MixedData.row1070 = numericRow1070 := by decide +kernel

theorem numericCheck1070 (x : Master → ℝ) : Integer.Sparse.eval numericRow1070 x =
    (1 : ℝ) * reducedSource1070 x := by
  norm_num [numericRow1070, reducedSource1070, Integer.Sparse.eval, Sparse.eval, nodeValue641, nodeValue1159, nodeValue1242, nodeValue1264, nodeValue1294, nodeValue4092]

theorem reindexCheck1071 : Integer.Sparse.reindex keyMap MixedData.row1071 = numericRow1071 := by decide +kernel

theorem numericCheck1071 (x : Master → ℝ) : Integer.Sparse.eval numericRow1071 x =
    (1 : ℝ) * reducedSource1071 x := by
  norm_num [numericRow1071, reducedSource1071, Integer.Sparse.eval, Sparse.eval, nodeValue1643, nodeValue1647, nodeValue1652, nodeValue1725, nodeValue3302, nodeValue4070]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows66
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1056 (mixedVector B) = 0 := by
  have h815 : mixedVector B (Sum.inr 815) = Sparse.eval nodeValue815 (mixedVector B) := by
    change mixedMoment B node815 node815Labels = _
    exact sound815 B hB hF
  have h1604 : mixedVector B (Sum.inr 1604) = Sparse.eval nodeValue1604 (mixedVector B) := by
    change mixedMoment B node1604 node1604Labels = _
    exact sound1604 B hB hF
  have h1652 : mixedVector B (Sum.inr 1652) = Sparse.eval nodeValue1652 (mixedVector B) := by
    change mixedMoment B node1652 node1652Labels = _
    exact sound1652 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h1729 : mixedVector B (Sum.inr 1729) = Sparse.eval nodeValue1729 (mixedVector B) := by
    change mixedMoment B node1729 node1729Labels = _
    exact sound1729 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1218, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h815, h1604, h1652, h1725, h1729, h4070, reducedSource1056] using sourceEq1218 B hB

theorem rowSound1056 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1056 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1056, numericCheck1056, reducedZero1056 B hB hF, mul_zero]

theorem reducedZero1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1057 (mixedVector B) = 0 := by
  have h936 : mixedVector B (Sum.inr 936) = Sparse.eval nodeValue936 (mixedVector B) := by
    change mixedMoment B node936 node936Labels = _
    exact sound936 B hB hF
  have h1315 : mixedVector B (Sum.inr 1315) = Sparse.eval nodeValue1315 (mixedVector B) := by
    change mixedMoment B node1315 node1315Labels = _
    exact sound1315 B hB hF
  have h1323 : mixedVector B (Sum.inr 1323) = Sparse.eval nodeValue1323 (mixedVector B) := by
    change mixedMoment B node1323 node1323Labels = _
    exact sound1323 B hB hF
  have h1369 : mixedVector B (Sum.inr 1369) = Sparse.eval nodeValue1369 (mixedVector B) := by
    change mixedMoment B node1369 node1369Labels = _
    exact sound1369 B hB hF
  have h2062 : mixedVector B (Sum.inr 2062) = Sparse.eval nodeValue2062 (mixedVector B) := by
    change mixedMoment B node2062 node2062Labels = _
    exact sound2062 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1220, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h936, h1315, h1323, h1369, h2062, h4084, reducedSource1057] using sourceEq1220 B hB

theorem rowSound1057 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1057 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1057, numericCheck1057, reducedZero1057 B hB hF, mul_zero]

theorem reducedZero1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1058 (mixedVector B) = 0 := by
  have h1011 : mixedVector B (Sum.inr 1011) = Sparse.eval nodeValue1011 (mixedVector B) := by
    change mixedMoment B node1011 node1011Labels = _
    exact sound1011 B hB hF
  have h1746 : mixedVector B (Sum.inr 1746) = Sparse.eval nodeValue1746 (mixedVector B) := by
    change mixedMoment B node1746 node1746Labels = _
    exact sound1746 B hB hF
  have h1952 : mixedVector B (Sum.inr 1952) = Sparse.eval nodeValue1952 (mixedVector B) := by
    change mixedMoment B node1952 node1952Labels = _
    exact sound1952 B hB hF
  have h2005 : mixedVector B (Sum.inr 2005) = Sparse.eval nodeValue2005 (mixedVector B) := by
    change mixedMoment B node2005 node2005Labels = _
    exact sound2005 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1221, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1011, h1746, h1952, h2005, h2226, h4070, reducedSource1058] using sourceEq1221 B hB

theorem rowSound1058 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1058 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1058, numericCheck1058, reducedZero1058 B hB hF, mul_zero]

theorem reducedZero1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1059 (mixedVector B) = 0 := by
  have h581 : mixedVector B (Sum.inr 581) = Sparse.eval nodeValue581 (mixedVector B) := by
    change mixedMoment B node581 node581Labels = _
    exact sound581 B hB hF
  have h905 : mixedVector B (Sum.inr 905) = Sparse.eval nodeValue905 (mixedVector B) := by
    change mixedMoment B node905 node905Labels = _
    exact sound905 B hB hF
  have h945 : mixedVector B (Sum.inr 945) = Sparse.eval nodeValue945 (mixedVector B) := by
    change mixedMoment B node945 node945Labels = _
    exact sound945 B hB hF
  have h1022 : mixedVector B (Sum.inr 1022) = Sparse.eval nodeValue1022 (mixedVector B) := by
    change mixedMoment B node1022 node1022Labels = _
    exact sound1022 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h1046 : mixedVector B (Sum.inr 1046) = Sparse.eval nodeValue1046 (mixedVector B) := by
    change mixedMoment B node1046 node1046Labels = _
    exact sound1046 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1224, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h581, h905, h945, h1022, h1041, h1046, h4083, reducedSource1059] using sourceEq1224 B hB

theorem rowSound1059 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1059 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1059, numericCheck1059, reducedZero1059 B hB hF, mul_zero]

theorem reducedZero1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1060 (mixedVector B) = 0 := by
  have h1118 : mixedVector B (Sum.inr 1118) = Sparse.eval nodeValue1118 (mixedVector B) := by
    change mixedMoment B node1118 node1118Labels = _
    exact sound1118 B hB hF
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1333 : mixedVector B (Sum.inr 1333) = Sparse.eval nodeValue1333 (mixedVector B) := by
    change mixedMoment B node1333 node1333Labels = _
    exact sound1333 B hB hF
  have h1337 : mixedVector B (Sum.inr 1337) = Sparse.eval nodeValue1337 (mixedVector B) := by
    change mixedMoment B node1337 node1337Labels = _
    exact sound1337 B hB hF
  have h1388 : mixedVector B (Sum.inr 1388) = Sparse.eval nodeValue1388 (mixedVector B) := by
    change mixedMoment B node1388 node1388Labels = _
    exact sound1388 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1225, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1118, h1327, h1333, h1337, h1388, h2485, h4091, reducedSource1060] using sourceEq1225 B hB

theorem rowSound1060 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1060 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1060, numericCheck1060, reducedZero1060 B hB hF, mul_zero]

theorem reducedZero1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1061 (mixedVector B) = 0 := by
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1942 : mixedVector B (Sum.inr 1942) = Sparse.eval nodeValue1942 (mixedVector B) := by
    change mixedMoment B node1942 node1942Labels = _
    exact sound1942 B hB hF
  have h3279 : mixedVector B (Sum.inr 3279) = Sparse.eval nodeValue3279 (mixedVector B) := by
    change mixedMoment B node3279 node3279Labels = _
    exact sound3279 B hB hF
  have h3283 : mixedVector B (Sum.inr 3283) = Sparse.eval nodeValue3283 (mixedVector B) := by
    change mixedMoment B node3283 node3283Labels = _
    exact sound3283 B hB hF
  have h3300 : mixedVector B (Sum.inr 3300) = Sparse.eval nodeValue3300 (mixedVector B) := by
    change mixedMoment B node3300 node3300Labels = _
    exact sound3300 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1226, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1723, h1942, h3279, h3283, h3300, h4070, reducedSource1061] using sourceEq1226 B hB

theorem rowSound1061 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1061 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1061, numericCheck1061, reducedZero1061 B hB hF, mul_zero]

theorem reducedZero1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1062 (mixedVector B) = 0 := by
  have h847 : mixedVector B (Sum.inr 847) = Sparse.eval nodeValue847 (mixedVector B) := by
    change mixedMoment B node847 node847Labels = _
    exact sound847 B hB hF
  have h1613 : mixedVector B (Sum.inr 1613) = Sparse.eval nodeValue1613 (mixedVector B) := by
    change mixedMoment B node1613 node1613Labels = _
    exact sound1613 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1750 : mixedVector B (Sum.inr 1750) = Sparse.eval nodeValue1750 (mixedVector B) := by
    change mixedMoment B node1750 node1750Labels = _
    exact sound1750 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1228, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h847, h1613, h1723, h1744, h1750, h4070, reducedSource1062] using sourceEq1228 B hB

theorem rowSound1062 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1062 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1062, numericCheck1062, reducedZero1062 B hB hF, mul_zero]

theorem reducedZero1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1063 (mixedVector B) = 0 := by
  have h804 : mixedVector B (Sum.inr 804) = Sparse.eval nodeValue804 (mixedVector B) := by
    change mixedMoment B node804 node804Labels = _
    exact sound804 B hB hF
  have h1596 : mixedVector B (Sum.inr 1596) = Sparse.eval nodeValue1596 (mixedVector B) := by
    change mixedMoment B node1596 node1596Labels = _
    exact sound1596 B hB hF
  have h1643 : mixedVector B (Sum.inr 1643) = Sparse.eval nodeValue1643 (mixedVector B) := by
    change mixedMoment B node1643 node1643Labels = _
    exact sound1643 B hB hF
  have h1723 : mixedVector B (Sum.inr 1723) = Sparse.eval nodeValue1723 (mixedVector B) := by
    change mixedMoment B node1723 node1723Labels = _
    exact sound1723 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1229, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h804, h1596, h1643, h1723, h1725, h4070, reducedSource1063] using sourceEq1229 B hB

theorem rowSound1063 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1063 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1063, numericCheck1063, reducedZero1063 B hB hF, mul_zero]

theorem reducedZero1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1064 (mixedVector B) = 0 := by
  have h585 : mixedVector B (Sum.inr 585) = Sparse.eval nodeValue585 (mixedVector B) := by
    change mixedMoment B node585 node585Labels = _
    exact sound585 B hB hF
  have h909 : mixedVector B (Sum.inr 909) = Sparse.eval nodeValue909 (mixedVector B) := by
    change mixedMoment B node909 node909Labels = _
    exact sound909 B hB hF
  have h949 : mixedVector B (Sum.inr 949) = Sparse.eval nodeValue949 (mixedVector B) := by
    change mixedMoment B node949 node949Labels = _
    exact sound949 B hB hF
  have h1024 : mixedVector B (Sum.inr 1024) = Sparse.eval nodeValue1024 (mixedVector B) := by
    change mixedMoment B node1024 node1024Labels = _
    exact sound1024 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1231, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h585, h909, h949, h1024, h1044, h4083, reducedSource1064] using sourceEq1231 B hB

theorem rowSound1064 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1064 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1064, numericCheck1064, reducedZero1064 B hB hF, mul_zero]

theorem reducedZero1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1065 (mixedVector B) = 0 := by
  have h911 : mixedVector B (Sum.inr 911) = Sparse.eval nodeValue911 (mixedVector B) := by
    change mixedMoment B node911 node911Labels = _
    exact sound911 B hB hF
  have h1326 : mixedVector B (Sum.inr 1326) = Sparse.eval nodeValue1326 (mixedVector B) := by
    change mixedMoment B node1326 node1326Labels = _
    exact sound1326 B hB hF
  have h1332 : mixedVector B (Sum.inr 1332) = Sparse.eval nodeValue1332 (mixedVector B) := by
    change mixedMoment B node1332 node1332Labels = _
    exact sound1332 B hB hF
  have h1336 : mixedVector B (Sum.inr 1336) = Sparse.eval nodeValue1336 (mixedVector B) := by
    change mixedMoment B node1336 node1336Labels = _
    exact sound1336 B hB hF
  have h1385 : mixedVector B (Sum.inr 1385) = Sparse.eval nodeValue1385 (mixedVector B) := by
    change mixedMoment B node1385 node1385Labels = _
    exact sound1385 B hB hF
  have h2025 : mixedVector B (Sum.inr 2025) = Sparse.eval nodeValue2025 (mixedVector B) := by
    change mixedMoment B node2025 node2025Labels = _
    exact sound2025 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1232, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h911, h1326, h1332, h1336, h1385, h2025, h4083, reducedSource1065] using sourceEq1232 B hB

theorem rowSound1065 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1065 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1065, numericCheck1065, reducedZero1065 B hB hF, mul_zero]

theorem reducedZero1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1066 (mixedVector B) = 0 := by
  have h997 : mixedVector B (Sum.inr 997) = Sparse.eval nodeValue997 (mixedVector B) := by
    change mixedMoment B node997 node997Labels = _
    exact sound997 B hB hF
  have h1744 : mixedVector B (Sum.inr 1744) = Sparse.eval nodeValue1744 (mixedVector B) := by
    change mixedMoment B node1744 node1744Labels = _
    exact sound1744 B hB hF
  have h1942 : mixedVector B (Sum.inr 1942) = Sparse.eval nodeValue1942 (mixedVector B) := by
    change mixedMoment B node1942 node1942Labels = _
    exact sound1942 B hB hF
  have h1995 : mixedVector B (Sum.inr 1995) = Sparse.eval nodeValue1995 (mixedVector B) := by
    change mixedMoment B node1995 node1995Labels = _
    exact sound1995 B hB hF
  have h2226 : mixedVector B (Sum.inr 2226) = Sparse.eval nodeValue2226 (mixedVector B) := by
    change mixedMoment B node2226 node2226Labels = _
    exact sound2226 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1233, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h997, h1744, h1942, h1995, h2226, h4070, reducedSource1066] using sourceEq1233 B hB

theorem rowSound1066 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1066 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1066, numericCheck1066, reducedZero1066 B hB hF, mul_zero]

theorem reducedZero1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1067 (mixedVector B) = 0 := by
  have h1355 : mixedVector B (Sum.inr 1355) = Sparse.eval nodeValue1355 (mixedVector B) := by
    change mixedMoment B node1355 node1355Labels = _
    exact sound1355 B hB hF
  have h1902 : mixedVector B (Sum.inr 1902) = Sparse.eval nodeValue1902 (mixedVector B) := by
    change mixedMoment B node1902 node1902Labels = _
    exact sound1902 B hB hF
  have h1915 : mixedVector B (Sum.inr 1915) = Sparse.eval nodeValue1915 (mixedVector B) := by
    change mixedMoment B node1915 node1915Labels = _
    exact sound1915 B hB hF
  have h1926 : mixedVector B (Sum.inr 1926) = Sparse.eval nodeValue1926 (mixedVector B) := by
    change mixedMoment B node1926 node1926Labels = _
    exact sound1926 B hB hF
  have h2197 : mixedVector B (Sum.inr 2197) = Sparse.eval nodeValue2197 (mixedVector B) := by
    change mixedMoment B node2197 node2197Labels = _
    exact sound2197 B hB hF
  have h3024 : mixedVector B (Sum.inr 3024) = Sparse.eval nodeValue3024 (mixedVector B) := by
    change mixedMoment B node3024 node3024Labels = _
    exact sound3024 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1235, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1355, h1902, h1915, h1926, h2197, h3024, h4080, reducedSource1067] using sourceEq1235 B hB

theorem rowSound1067 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1067 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1067, numericCheck1067, reducedZero1067 B hB hF, mul_zero]

theorem reducedZero1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1068 (mixedVector B) = 0 := by
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h1142 : mixedVector B (Sum.inr 1142) = Sparse.eval nodeValue1142 (mixedVector B) := by
    change mixedMoment B node1142 node1142Labels = _
    exact sound1142 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h2519 : mixedVector B (Sum.inr 2519) = Sparse.eval nodeValue2519 (mixedVector B) := by
    change mixedMoment B node2519 node2519Labels = _
    exact sound2519 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1237, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1132, h1142, h1145, h1243, h2519, h4092, reducedSource1068] using sourceEq1237 B hB

theorem rowSound1068 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1068 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1068, numericCheck1068, reducedZero1068 B hB hF, mul_zero]

theorem reducedZero1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1069 (mixedVector B) = 0 := by
  have h636 : mixedVector B (Sum.inr 636) = Sparse.eval nodeValue636 (mixedVector B) := by
    change mixedMoment B node636 node636Labels = _
    exact sound636 B hB hF
  have h1145 : mixedVector B (Sum.inr 1145) = Sparse.eval nodeValue1145 (mixedVector B) := by
    change mixedMoment B node1145 node1145Labels = _
    exact sound1145 B hB hF
  have h1155 : mixedVector B (Sum.inr 1155) = Sparse.eval nodeValue1155 (mixedVector B) := by
    change mixedMoment B node1155 node1155Labels = _
    exact sound1155 B hB hF
  have h1243 : mixedVector B (Sum.inr 1243) = Sparse.eval nodeValue1243 (mixedVector B) := by
    change mixedMoment B node1243 node1243Labels = _
    exact sound1243 B hB hF
  have h1246 : mixedVector B (Sum.inr 1246) = Sparse.eval nodeValue1246 (mixedVector B) := by
    change mixedMoment B node1246 node1246Labels = _
    exact sound1246 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1238, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h636, h1145, h1155, h1243, h1246, h4092, reducedSource1069] using sourceEq1238 B hB

theorem rowSound1069 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1069 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1069, numericCheck1069, reducedZero1069 B hB hF, mul_zero]

theorem reducedZero1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1070 (mixedVector B) = 0 := by
  have h641 : mixedVector B (Sum.inr 641) = Sparse.eval nodeValue641 (mixedVector B) := by
    change mixedMoment B node641 node641Labels = _
    exact sound641 B hB hF
  have h1159 : mixedVector B (Sum.inr 1159) = Sparse.eval nodeValue1159 (mixedVector B) := by
    change mixedMoment B node1159 node1159Labels = _
    exact sound1159 B hB hF
  have h1242 : mixedVector B (Sum.inr 1242) = Sparse.eval nodeValue1242 (mixedVector B) := by
    change mixedMoment B node1242 node1242Labels = _
    exact sound1242 B hB hF
  have h1264 : mixedVector B (Sum.inr 1264) = Sparse.eval nodeValue1264 (mixedVector B) := by
    change mixedMoment B node1264 node1264Labels = _
    exact sound1264 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1239, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h641, h1159, h1242, h1264, h1294, h4092, reducedSource1070] using sourceEq1239 B hB

theorem rowSound1070 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1070 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1070, numericCheck1070, reducedZero1070 B hB hF, mul_zero]

theorem reducedZero1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1071 (mixedVector B) = 0 := by
  have h1643 : mixedVector B (Sum.inr 1643) = Sparse.eval nodeValue1643 (mixedVector B) := by
    change mixedMoment B node1643 node1643Labels = _
    exact sound1643 B hB hF
  have h1647 : mixedVector B (Sum.inr 1647) = Sparse.eval nodeValue1647 (mixedVector B) := by
    change mixedMoment B node1647 node1647Labels = _
    exact sound1647 B hB hF
  have h1652 : mixedVector B (Sum.inr 1652) = Sparse.eval nodeValue1652 (mixedVector B) := by
    change mixedMoment B node1652 node1652Labels = _
    exact sound1652 B hB hF
  have h1725 : mixedVector B (Sum.inr 1725) = Sparse.eval nodeValue1725 (mixedVector B) := by
    change mixedMoment B node1725 node1725Labels = _
    exact sound1725 B hB hF
  have h3302 : mixedVector B (Sum.inr 3302) = Sparse.eval nodeValue3302 (mixedVector B) := by
    change mixedMoment B node3302 node3302Labels = _
    exact sound3302 B hB hF
  have h4070 : mixedVector B (Sum.inr 4070) = Sparse.eval nodeValue4070 (mixedVector B) := by
    change mixedMoment B node4070 node4070Labels = _
    exact sound4070 B hB hF
  simpa only [sourceForm1240, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1643, h1647, h1652, h1725, h3302, h4070, reducedSource1071] using sourceEq1240 B hB

theorem rowSound1071 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1071 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1071, numericCheck1071, reducedZero1071 B hB hF, mul_zero]

theorem sourceRowsAt1056 : MixedData.sourceRows (1056 : Fin 2425) =
    MixedData.row1056 := by decide +kernel

theorem sourceRowsAt1057 : MixedData.sourceRows (1057 : Fin 2425) =
    MixedData.row1057 := by decide +kernel

theorem sourceRowsAt1058 : MixedData.sourceRows (1058 : Fin 2425) =
    MixedData.row1058 := by decide +kernel

theorem sourceRowsAt1059 : MixedData.sourceRows (1059 : Fin 2425) =
    MixedData.row1059 := by decide +kernel

theorem sourceRowsAt1060 : MixedData.sourceRows (1060 : Fin 2425) =
    MixedData.row1060 := by decide +kernel

theorem sourceRowsAt1061 : MixedData.sourceRows (1061 : Fin 2425) =
    MixedData.row1061 := by decide +kernel

theorem sourceRowsAt1062 : MixedData.sourceRows (1062 : Fin 2425) =
    MixedData.row1062 := by decide +kernel

theorem sourceRowsAt1063 : MixedData.sourceRows (1063 : Fin 2425) =
    MixedData.row1063 := by decide +kernel

theorem sourceRowsAt1064 : MixedData.sourceRows (1064 : Fin 2425) =
    MixedData.row1064 := by decide +kernel

theorem sourceRowsAt1065 : MixedData.sourceRows (1065 : Fin 2425) =
    MixedData.row1065 := by decide +kernel

theorem sourceRowsAt1066 : MixedData.sourceRows (1066 : Fin 2425) =
    MixedData.row1066 := by decide +kernel

theorem sourceRowsAt1067 : MixedData.sourceRows (1067 : Fin 2425) =
    MixedData.row1067 := by decide +kernel

theorem sourceRowsAt1068 : MixedData.sourceRows (1068 : Fin 2425) =
    MixedData.row1068 := by decide +kernel

theorem sourceRowsAt1069 : MixedData.sourceRows (1069 : Fin 2425) =
    MixedData.row1069 := by decide +kernel

theorem sourceRowsAt1070 : MixedData.sourceRows (1070 : Fin 2425) =
    MixedData.row1070 := by decide +kernel

theorem sourceRowsAt1071 : MixedData.sourceRows (1071 : Fin 2425) =
    MixedData.row1071 := by decide +kernel

theorem chunkSound66_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 66) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1056 ∨ k.val = 1057 ∨ k.val = 1058 ∨ k.val = 1059 ∨ k.val = 1060 ∨ k.val = 1061 ∨ k.val = 1062 ∨ k.val = 1063 ∨ k.val = 1064 ∨ k.val = 1065 ∨ k.val = 1066 ∨ k.val = 1067 ∨ k.val = 1068 ∨ k.val = 1069 ∨ k.val = 1070 ∨ k.val = 1071 := by omega
  rcases heq with h1056 | h1057 | h1058 | h1059 | h1060 | h1061 | h1062 | h1063 | h1064 | h1065 | h1066 | h1067 | h1068 | h1069 | h1070 | h1071
  · have he : k = (1056 : Fin 2425) := Fin.ext h1056
    subst k
    rw [sourceRowsAt1056]
    exact rowSound1056 B hB hF
  · have he : k = (1057 : Fin 2425) := Fin.ext h1057
    subst k
    rw [sourceRowsAt1057]
    exact rowSound1057 B hB hF
  · have he : k = (1058 : Fin 2425) := Fin.ext h1058
    subst k
    rw [sourceRowsAt1058]
    exact rowSound1058 B hB hF
  · have he : k = (1059 : Fin 2425) := Fin.ext h1059
    subst k
    rw [sourceRowsAt1059]
    exact rowSound1059 B hB hF
  · have he : k = (1060 : Fin 2425) := Fin.ext h1060
    subst k
    rw [sourceRowsAt1060]
    exact rowSound1060 B hB hF
  · have he : k = (1061 : Fin 2425) := Fin.ext h1061
    subst k
    rw [sourceRowsAt1061]
    exact rowSound1061 B hB hF
  · have he : k = (1062 : Fin 2425) := Fin.ext h1062
    subst k
    rw [sourceRowsAt1062]
    exact rowSound1062 B hB hF
  · have he : k = (1063 : Fin 2425) := Fin.ext h1063
    subst k
    rw [sourceRowsAt1063]
    exact rowSound1063 B hB hF
  · have he : k = (1064 : Fin 2425) := Fin.ext h1064
    subst k
    rw [sourceRowsAt1064]
    exact rowSound1064 B hB hF
  · have he : k = (1065 : Fin 2425) := Fin.ext h1065
    subst k
    rw [sourceRowsAt1065]
    exact rowSound1065 B hB hF
  · have he : k = (1066 : Fin 2425) := Fin.ext h1066
    subst k
    rw [sourceRowsAt1066]
    exact rowSound1066 B hB hF
  · have he : k = (1067 : Fin 2425) := Fin.ext h1067
    subst k
    rw [sourceRowsAt1067]
    exact rowSound1067 B hB hF
  · have he : k = (1068 : Fin 2425) := Fin.ext h1068
    subst k
    rw [sourceRowsAt1068]
    exact rowSound1068 B hB hF
  · have he : k = (1069 : Fin 2425) := Fin.ext h1069
    subst k
    rw [sourceRowsAt1069]
    exact rowSound1069 B hB hF
  · have he : k = (1070 : Fin 2425) := Fin.ext h1070
    subst k
    rw [sourceRowsAt1070]
    exact rowSound1070 B hB hF
  · have he : k = (1071 : Fin 2425) := Fin.ext h1071
    subst k
    rw [sourceRowsAt1071]
    exact rowSound1071 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound66_e_oai
