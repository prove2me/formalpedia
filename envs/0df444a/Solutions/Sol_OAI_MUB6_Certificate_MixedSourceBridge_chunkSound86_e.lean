-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:55:38.112955+00:00
-- url     : https://prove2.me/submissions/4c4d51d0-852c-4022-b53f-0e0ae208a251

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E116
import Definitions.Def_OAIQ106E118
import Definitions.Def_OAIQ106E120
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical107
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13763 raw13763Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw13763 raw13763Labels = mixedMoment B raw13763step0 raw13763step0Labels := by
      have ha : raw13763step0 = (fun i j => raw13763 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13763step0 raw13763; decide +kernel
      have hl : raw13763step0Labels = raw13763Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13763 raw13763Labels permutation194 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical13769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13769 raw13769Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13769 raw13769Labels = mixedMoment B raw13769step0 raw13769step0Labels := by
      have hz : ∀ j, raw13769 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13769step0 = (fun i j => raw13769 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13769step0 raw13769; decide +kernel
      have hl : raw13769step0Labels = raw13769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13769 raw13769Labels permutation590 hz
    mixedMoment B raw13769step0 raw13769step0Labels = mixedMoment B raw13769step1 raw13769step1Labels := by
      have ha : raw13769step1 = (fun i j => raw13769step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13769step1 raw13769step0; decide +kernel
      have hl : raw13769step1Labels = raw13769step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13769step0 raw13769step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical185
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23794 raw23794Labels = mixedMoment B node3022 node3022Labels := by
  calc
    mixedMoment B raw23794 raw23794Labels = mixedMoment B raw23794step0 raw23794step0Labels := by
      have hz : ∀ j, raw23794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23794step0 = (fun i j => raw23794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23794step0 raw23794; decide +kernel
      have hl : raw23794step0Labels = raw23794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23794 raw23794Labels permutation346 hz
    mixedMoment B raw23794step0 raw23794step0Labels = mixedMoment B raw23794step1 raw23794step1Labels := by
      have ha : raw23794step1 = (fun i j => raw23794step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23794step1 raw23794step0; decide +kernel
      have hl : raw23794step1Labels = raw23794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23794step0 raw23794step0Labels permutation127 permutation4
    _ = mixedMoment B node3022 node3022Labels := by rfl

theorem canonical23797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23797 raw23797Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw23797 raw23797Labels = mixedMoment B raw23797step0 raw23797step0Labels := by
      have hz : ∀ j, raw23797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23797step0 = (fun i j => raw23797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23797step0 raw23797; decide +kernel
      have hl : raw23797step0Labels = raw23797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23797 raw23797Labels permutation346 hz
    mixedMoment B raw23797step0 raw23797step0Labels = mixedMoment B raw23797step1 raw23797step1Labels := by
      have hz : ∀ j, raw23797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23797step1 = (fun i j => raw23797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23797step1 raw23797step0; decide +kernel
      have hl : raw23797step1Labels = raw23797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23797step0 raw23797step0Labels permutation56 hz
    mixedMoment B raw23797step1 raw23797step1Labels = mixedMoment B raw23797step2 raw23797step2Labels := by
      have ha : raw23797step2 = (fun i j => raw23797step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23797step2 raw23797step1; decide +kernel
      have hl : raw23797step2Labels = raw23797step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23797step1 raw23797step1Labels permutation10 permutation2
    mixedMoment B raw23797step2 raw23797step2Labels = mixedMoment B raw23797step3 raw23797step3Labels := by
      have ha : raw23797step3 = -raw23797step2 := by apply Matrix.ext; change ∀ i j, raw23797step3 i j = -(raw23797step2 i j); unfold raw23797step3 raw23797step2; decide +kernel
      have hl : raw23797step3Labels = raw23797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical23799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23799 raw23799Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw23799 raw23799Labels = mixedMoment B raw23799step0 raw23799step0Labels := by
      have hz : ∀ j, raw23799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23799step0 = (fun i j => raw23799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23799step0 raw23799; decide +kernel
      have hl : raw23799step0Labels = raw23799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799 raw23799Labels permutation346 hz
    mixedMoment B raw23799step0 raw23799step0Labels = mixedMoment B raw23799step1 raw23799step1Labels := by
      have hz : ∀ j, raw23799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23799step1 = (fun i j => raw23799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23799step1 raw23799step0; decide +kernel
      have hl : raw23799step1Labels = raw23799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23799step0 raw23799step0Labels permutation56 hz
    mixedMoment B raw23799step1 raw23799step1Labels = mixedMoment B raw23799step2 raw23799step2Labels := by
      have ha : raw23799step2 = -raw23799step1 := by apply Matrix.ext; change ∀ i j, raw23799step2 i j = -(raw23799step1 i j); unfold raw23799step2 raw23799step1; decide +kernel
      have hl : raw23799step2Labels = raw23799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

theorem canonical23802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23802 raw23802Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw23802 raw23802Labels = mixedMoment B raw23802step0 raw23802step0Labels := by
      have hz : ∀ j, raw23802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23802step0 = (fun i j => raw23802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23802step0 raw23802; decide +kernel
      have hl : raw23802step0Labels = raw23802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23802 raw23802Labels permutation346 hz
    mixedMoment B raw23802step0 raw23802step0Labels = mixedMoment B raw23802step1 raw23802step1Labels := by
      have hz : ∀ j, raw23802step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23802step1 = (fun i j => raw23802step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23802step1 raw23802step0; decide +kernel
      have hl : raw23802step1Labels = raw23802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23802step0 raw23802step0Labels permutation56 hz
    mixedMoment B raw23802step1 raw23802step1Labels = mixedMoment B raw23802step2 raw23802step2Labels := by
      have ha : raw23802step2 = (fun i j => raw23802step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23802step2 raw23802step1; decide +kernel
      have hl : raw23802step2Labels = raw23802step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23802step1 raw23802step1Labels permutation12 permutation4
    mixedMoment B raw23802step2 raw23802step2Labels = mixedMoment B raw23802step3 raw23802step3Labels := by
      have ha : raw23802step3 = -raw23802step2 := by apply Matrix.ext; change ∀ i j, raw23802step3 i j = -(raw23802step2 i j); unfold raw23802step3 raw23802step2; decide +kernel
      have hl : raw23802step3Labels = raw23802step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical23803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23803 raw23803Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw23803 raw23803Labels = mixedMoment B raw23803step0 raw23803step0Labels := by
      have hz : ∀ j, raw23803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23803step0 = (fun i j => raw23803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23803step0 raw23803; decide +kernel
      have hl : raw23803step0Labels = raw23803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23803 raw23803Labels permutation346 hz
    mixedMoment B raw23803step0 raw23803step0Labels = mixedMoment B raw23803step1 raw23803step1Labels := by
      have hz : ∀ j, raw23803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23803step1 = (fun i j => raw23803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23803step1 raw23803step0; decide +kernel
      have hl : raw23803step1Labels = raw23803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23803step0 raw23803step0Labels permutation56 hz
    mixedMoment B raw23803step1 raw23803step1Labels = mixedMoment B raw23803step2 raw23803step2Labels := by
      have ha : raw23803step2 = (fun i j => raw23803step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23803step2 raw23803step1; decide +kernel
      have hl : raw23803step2Labels = raw23803step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23803step1 raw23803step1Labels permutation9 permutation4
    mixedMoment B raw23803step2 raw23803step2Labels = mixedMoment B raw23803step3 raw23803step3Labels := by
      have ha : raw23803step3 = -raw23803step2 := by apply Matrix.ext; change ∀ i j, raw23803step3 i j = -(raw23803step2 i j); unfold raw23803step3 raw23803step2; decide +kernel
      have hl : raw23803step3Labels = raw23803step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1728 node1728Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical186
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23818 raw23818Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw23818 raw23818Labels = mixedMoment B raw23818step0 raw23818step0Labels := by
      have ha : raw23818step0 = (fun i j => raw23818 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23818step0 raw23818; decide +kernel
      have hl : raw23818step0Labels = raw23818Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23818 raw23818Labels permutation188 permutation2
    mixedMoment B raw23818step0 raw23818step0Labels = mixedMoment B raw23818step1 raw23818step1Labels := by
      have ha : raw23818step1 = -raw23818step0 := by apply Matrix.ext; change ∀ i j, raw23818step1 i j = -(raw23818step0 i j); unfold raw23818step1 raw23818step0; decide +kernel
      have hl : raw23818step1Labels = raw23818step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3285 node3285Labels := by rfl

theorem canonical23823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23823 raw23823Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw23823 raw23823Labels = mixedMoment B raw23823step0 raw23823step0Labels := by
      have ha : raw23823step0 = (fun i j => raw23823 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23823step0 raw23823; decide +kernel
      have hl : raw23823step0Labels = raw23823Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23823 raw23823Labels permutation170 permutation4
    mixedMoment B raw23823step0 raw23823step0Labels = mixedMoment B raw23823step1 raw23823step1Labels := by
      have ha : raw23823step1 = -raw23823step0 := by apply Matrix.ext; change ∀ i j, raw23823step1 i j = -(raw23823step0 i j); unfold raw23823step1 raw23823step0; decide +kernel
      have hl : raw23823step1Labels = raw23823step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1607 node1607Labels := by rfl

theorem canonical23830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23830 raw23830Labels = mixedMoment B node1598 node1598Labels := by
  calc
    mixedMoment B raw23830 raw23830Labels = mixedMoment B raw23830step0 raw23830step0Labels := by
      have ha : raw23830step0 = (fun i j => raw23830 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23830step0 raw23830; decide +kernel
      have hl : raw23830step0Labels = raw23830Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23830 raw23830Labels permutation159 permutation4
    mixedMoment B raw23830step0 raw23830step0Labels = mixedMoment B raw23830step1 raw23830step1Labels := by
      have ha : raw23830step1 = -raw23830step0 := by apply Matrix.ext; change ∀ i j, raw23830step1 i j = -(raw23830step0 i j); unfold raw23830step1 raw23830step0; decide +kernel
      have hl : raw23830step1Labels = raw23830step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1598 node1598Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical187
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical23954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23954 raw23954Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23954 raw23954Labels = mixedMoment B raw23954step0 raw23954step0Labels := by
      have hz : ∀ j, raw23954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23954step0 = (fun i j => raw23954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23954step0 raw23954; decide +kernel
      have hl : raw23954step0Labels = raw23954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23954 raw23954Labels permutation346 hz
    mixedMoment B raw23954step0 raw23954step0Labels = mixedMoment B raw23954step1 raw23954step1Labels := by
      have ha : raw23954step1 = (fun i j => raw23954step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23954step1 raw23954step0; decide +kernel
      have hl : raw23954step1Labels = raw23954step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23954step0 raw23954step0Labels permutation32 permutation4
    mixedMoment B raw23954step1 raw23954step1Labels = mixedMoment B raw23954step2 raw23954step2Labels := by
      have ha : raw23954step2 = -raw23954step1 := by apply Matrix.ext; change ∀ i j, raw23954step2 i j = -(raw23954step1 i j); unfold raw23954step2 raw23954step1; decide +kernel
      have hl : raw23954step2Labels = raw23954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical23966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23966 raw23966Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw23966 raw23966Labels = mixedMoment B raw23966step0 raw23966step0Labels := by
      have hz : ∀ j, raw23966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23966step0 = (fun i j => raw23966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23966step0 raw23966; decide +kernel
      have hl : raw23966step0Labels = raw23966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23966 raw23966Labels permutation346 hz
    mixedMoment B raw23966step0 raw23966step0Labels = mixedMoment B raw23966step1 raw23966step1Labels := by
      have ha : raw23966step1 = (fun i j => raw23966step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23966step1 raw23966step0; decide +kernel
      have hl : raw23966step1Labels = raw23966step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23966step0 raw23966step0Labels permutation33 permutation4
    mixedMoment B raw23966step1 raw23966step1Labels = mixedMoment B raw23966step2 raw23966step2Labels := by
      have ha : raw23966step2 = -raw23966step1 := by apply Matrix.ext; change ∀ i j, raw23966step2 i j = -(raw23966step1 i j); unfold raw23966step2 raw23966step1; decide +kernel
      have hl : raw23966step2Labels = raw23966step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical23970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23970 raw23970Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23970 raw23970Labels = mixedMoment B raw23970step0 raw23970step0Labels := by
      have hz : ∀ j, raw23970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23970step0 = (fun i j => raw23970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23970step0 raw23970; decide +kernel
      have hl : raw23970step0Labels = raw23970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23970 raw23970Labels permutation346 hz
    mixedMoment B raw23970step0 raw23970step0Labels = mixedMoment B raw23970step1 raw23970step1Labels := by
      have ha : raw23970step1 = (fun i j => raw23970step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23970step1 raw23970step0; decide +kernel
      have hl : raw23970step1Labels = raw23970step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23970step0 raw23970step0Labels permutation44 permutation2
    mixedMoment B raw23970step1 raw23970step1Labels = mixedMoment B raw23970step2 raw23970step2Labels := by
      have ha : raw23970step2 = -raw23970step1 := by apply Matrix.ext; change ∀ i j, raw23970step2 i j = -(raw23970step1 i j); unfold raw23970step2 raw23970step1; decide +kernel
      have hl : raw23970step2Labels = raw23970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical23971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23971 raw23971Labels = mixedMoment B node1645 node1645Labels := by
  calc
    mixedMoment B raw23971 raw23971Labels = mixedMoment B raw23971step0 raw23971step0Labels := by
      have hz : ∀ j, raw23971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23971step0 = (fun i j => raw23971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23971step0 raw23971; decide +kernel
      have hl : raw23971step0Labels = raw23971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23971 raw23971Labels permutation346 hz
    mixedMoment B raw23971step0 raw23971step0Labels = mixedMoment B raw23971step1 raw23971step1Labels := by
      have ha : raw23971step1 = (fun i j => raw23971step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23971step1 raw23971step0; decide +kernel
      have hl : raw23971step1Labels = raw23971step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23971step0 raw23971step0Labels permutation44 permutation2
    mixedMoment B raw23971step1 raw23971step1Labels = mixedMoment B raw23971step2 raw23971step2Labels := by
      have ha : raw23971step2 = -raw23971step1 := by apply Matrix.ext; change ∀ i j, raw23971step2 i j = -(raw23971step1 i j); unfold raw23971step2 raw23971step1; decide +kernel
      have hl : raw23971step2Labels = raw23971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1645 node1645Labels := by rfl

theorem canonical23972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23972 raw23972Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw23972 raw23972Labels = mixedMoment B raw23972step0 raw23972step0Labels := by
      have hz : ∀ j, raw23972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23972step0 = (fun i j => raw23972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23972step0 raw23972; decide +kernel
      have hl : raw23972step0Labels = raw23972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23972 raw23972Labels permutation346 hz
    mixedMoment B raw23972step0 raw23972step0Labels = mixedMoment B raw23972step1 raw23972step1Labels := by
      have ha : raw23972step1 = (fun i j => raw23972step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23972step1 raw23972step0; decide +kernel
      have hl : raw23972step1Labels = raw23972step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23972step0 raw23972step0Labels permutation33 permutation4
    mixedMoment B raw23972step1 raw23972step1Labels = mixedMoment B raw23972step2 raw23972step2Labels := by
      have ha : raw23972step2 = -raw23972step1 := by apply Matrix.ext; change ∀ i j, raw23972step2 i j = -(raw23972step1 i j); unfold raw23972step2 raw23972step1; decide +kernel
      have hl : raw23972step2Labels = raw23972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1623 node1623Labels := by rfl

theorem canonical23973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23973 raw23973Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw23973 raw23973Labels = mixedMoment B raw23973step0 raw23973step0Labels := by
      have hz : ∀ j, raw23973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23973step0 = (fun i j => raw23973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23973step0 raw23973; decide +kernel
      have hl : raw23973step0Labels = raw23973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23973 raw23973Labels permutation346 hz
    mixedMoment B raw23973step0 raw23973step0Labels = mixedMoment B raw23973step1 raw23973step1Labels := by
      have ha : raw23973step1 = (fun i j => raw23973step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23973step1 raw23973step0; decide +kernel
      have hl : raw23973step1Labels = raw23973step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23973step0 raw23973step0Labels permutation33 permutation4
    mixedMoment B raw23973step1 raw23973step1Labels = mixedMoment B raw23973step2 raw23973step2Labels := by
      have ha : raw23973step2 = -raw23973step1 := by apply Matrix.ext; change ∀ i j, raw23973step2 i j = -(raw23973step1 i j); unfold raw23973step2 raw23973step1; decide +kernel
      have hl : raw23973step2Labels = raw23973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1603 node1603Labels := by rfl

theorem canonical23974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23974 raw23974Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw23974 raw23974Labels = mixedMoment B raw23974step0 raw23974step0Labels := by
      have hz : ∀ j, raw23974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23974step0 = (fun i j => raw23974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23974step0 raw23974; decide +kernel
      have hl : raw23974step0Labels = raw23974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23974 raw23974Labels permutation346 hz
    mixedMoment B raw23974step0 raw23974step0Labels = mixedMoment B raw23974step1 raw23974step1Labels := by
      have ha : raw23974step1 = (fun i j => raw23974step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23974step1 raw23974step0; decide +kernel
      have hl : raw23974step1Labels = raw23974step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23974step0 raw23974step0Labels permutation32 permutation4
    mixedMoment B raw23974step1 raw23974step1Labels = mixedMoment B raw23974step2 raw23974step2Labels := by
      have ha : raw23974step2 = -raw23974step1 := by apply Matrix.ext; change ∀ i j, raw23974step2 i j = -(raw23974step1 i j); unfold raw23974step2 raw23974step1; decide +kernel
      have hl : raw23974step2Labels = raw23974step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1605 node1605Labels := by rfl

theorem canonical23975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23975 raw23975Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw23975 raw23975Labels = mixedMoment B raw23975step0 raw23975step0Labels := by
      have hz : ∀ j, raw23975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23975step0 = (fun i j => raw23975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23975step0 raw23975; decide +kernel
      have hl : raw23975step0Labels = raw23975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23975 raw23975Labels permutation265 hz
    mixedMoment B raw23975step0 raw23975step0Labels = mixedMoment B raw23975step1 raw23975step1Labels := by
      have ha : raw23975step1 = (fun i j => raw23975step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23975step1 raw23975step0; decide +kernel
      have hl : raw23975step1Labels = raw23975step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23975step0 raw23975step0Labels permutation33 permutation4
    mixedMoment B raw23975step1 raw23975step1Labels = mixedMoment B raw23975step2 raw23975step2Labels := by
      have ha : raw23975step2 = -raw23975step1 := by apply Matrix.ext; change ∀ i j, raw23975step2 i j = -(raw23975step1 i j); unfold raw23975step2 raw23975step1; decide +kernel
      have hl : raw23975step2Labels = raw23975step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3294 node3294Labels := by rfl

theorem canonical23976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23976 raw23976Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw23976 raw23976Labels = mixedMoment B raw23976step0 raw23976step0Labels := by
      have hz : ∀ j, raw23976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23976step0 = (fun i j => raw23976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23976step0 raw23976; decide +kernel
      have hl : raw23976step0Labels = raw23976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23976 raw23976Labels permutation346 hz
    mixedMoment B raw23976step0 raw23976step0Labels = mixedMoment B raw23976step1 raw23976step1Labels := by
      have hz : ∀ j, raw23976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23976step1 = (fun i j => raw23976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23976step1 raw23976step0; decide +kernel
      have hl : raw23976step1Labels = raw23976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23976step0 raw23976step0Labels permutation56 hz
    mixedMoment B raw23976step1 raw23976step1Labels = mixedMoment B raw23976step2 raw23976step2Labels := by
      have ha : raw23976step2 = (fun i j => raw23976step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23976step2 raw23976step1; decide +kernel
      have hl : raw23976step2Labels = raw23976step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23976step1 raw23976step1Labels permutation11 permutation2
    mixedMoment B raw23976step2 raw23976step2Labels = mixedMoment B raw23976step3 raw23976step3Labels := by
      have ha : raw23976step3 = -raw23976step2 := by apply Matrix.ext; change ∀ i j, raw23976step3 i j = -(raw23976step2 i j); unfold raw23976step3 raw23976step2; decide +kernel
      have hl : raw23976step3Labels = raw23976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3306 node3306Labels := by rfl

theorem canonical23977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23977 raw23977Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw23977 raw23977Labels = mixedMoment B raw23977step0 raw23977step0Labels := by
      have hz : ∀ j, raw23977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23977step0 = (fun i j => raw23977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23977step0 raw23977; decide +kernel
      have hl : raw23977step0Labels = raw23977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23977 raw23977Labels permutation346 hz
    mixedMoment B raw23977step0 raw23977step0Labels = mixedMoment B raw23977step1 raw23977step1Labels := by
      have hz : ∀ j, raw23977step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23977step1 = (fun i j => raw23977step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23977step1 raw23977step0; decide +kernel
      have hl : raw23977step1Labels = raw23977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23977step0 raw23977step0Labels permutation56 hz
    mixedMoment B raw23977step1 raw23977step1Labels = mixedMoment B raw23977step2 raw23977step2Labels := by
      have ha : raw23977step2 = (fun i j => raw23977step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23977step2 raw23977step1; decide +kernel
      have hl : raw23977step2Labels = raw23977step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23977step1 raw23977step1Labels permutation10 permutation2
    mixedMoment B raw23977step2 raw23977step2Labels = mixedMoment B raw23977step3 raw23977step3Labels := by
      have ha : raw23977step3 = -raw23977step2 := by apply Matrix.ext; change ∀ i j, raw23977step3 i j = -(raw23977step2 i j); unfold raw23977step3 raw23977step2; decide +kernel
      have hl : raw23977step3Labels = raw23977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3309 node3309Labels := by rfl

theorem canonical23978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23978 raw23978Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw23978 raw23978Labels = mixedMoment B raw23978step0 raw23978step0Labels := by
      have hz : ∀ j, raw23978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23978step0 = (fun i j => raw23978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23978step0 raw23978; decide +kernel
      have hl : raw23978step0Labels = raw23978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23978 raw23978Labels permutation346 hz
    mixedMoment B raw23978step0 raw23978step0Labels = mixedMoment B raw23978step1 raw23978step1Labels := by
      have ha : raw23978step1 = (fun i j => raw23978step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23978step1 raw23978step0; decide +kernel
      have hl : raw23978step1Labels = raw23978step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23978step0 raw23978step0Labels permutation33 permutation4
    mixedMoment B raw23978step1 raw23978step1Labels = mixedMoment B raw23978step2 raw23978step2Labels := by
      have ha : raw23978step2 = -raw23978step1 := by apply Matrix.ext; change ∀ i j, raw23978step2 i j = -(raw23978step1 i j); unfold raw23978step2 raw23978step1; decide +kernel
      have hl : raw23978step2Labels = raw23978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3246 node3246Labels := by rfl

theorem canonical23979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23979 raw23979Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw23979 raw23979Labels = mixedMoment B raw23979step0 raw23979step0Labels := by
      have ha : raw23979step0 = (fun i j => raw23979 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23979step0 raw23979; decide +kernel
      have hl : raw23979step0Labels = raw23979Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23979 raw23979Labels permutation153 permutation4
    mixedMoment B raw23979step0 raw23979step0Labels = mixedMoment B raw23979step1 raw23979step1Labels := by
      have ha : raw23979step1 = -raw23979step0 := by apply Matrix.ext; change ∀ i j, raw23979step1 i j = -(raw23979step0 i j); unfold raw23979step1 raw23979step0; decide +kernel
      have hl : raw23979step1Labels = raw23979step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3282 node3282Labels := by rfl

theorem canonical23980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23980 raw23980Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw23980 raw23980Labels = mixedMoment B raw23980step0 raw23980step0Labels := by
      have hz : ∀ j, raw23980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23980step0 = (fun i j => raw23980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23980step0 raw23980; decide +kernel
      have hl : raw23980step0Labels = raw23980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23980 raw23980Labels permutation346 hz
    mixedMoment B raw23980step0 raw23980step0Labels = mixedMoment B raw23980step1 raw23980step1Labels := by
      have ha : raw23980step1 = (fun i j => raw23980step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23980step1 raw23980step0; decide +kernel
      have hl : raw23980step1Labels = raw23980step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23980step0 raw23980step0Labels permutation32 permutation4
    mixedMoment B raw23980step1 raw23980step1Labels = mixedMoment B raw23980step2 raw23980step2Labels := by
      have ha : raw23980step2 = -raw23980step1 := by apply Matrix.ext; change ∀ i j, raw23980step2 i j = -(raw23980step1 i j); unfold raw23980step2 raw23980step1; decide +kernel
      have hl : raw23980step2Labels = raw23980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical23981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23981 raw23981Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw23981 raw23981Labels = mixedMoment B raw23981step0 raw23981step0Labels := by
      have hz : ∀ j, raw23981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23981step0 = (fun i j => raw23981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23981step0 raw23981; decide +kernel
      have hl : raw23981step0Labels = raw23981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23981 raw23981Labels permutation346 hz
    mixedMoment B raw23981step0 raw23981step0Labels = mixedMoment B raw23981step1 raw23981step1Labels := by
      have ha : raw23981step1 = (fun i j => raw23981step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23981step1 raw23981step0; decide +kernel
      have hl : raw23981step1Labels = raw23981step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23981step0 raw23981step0Labels permutation36 permutation4
    mixedMoment B raw23981step1 raw23981step1Labels = mixedMoment B raw23981step2 raw23981step2Labels := by
      have ha : raw23981step2 = -raw23981step1 := by apply Matrix.ext; change ∀ i j, raw23981step2 i j = -(raw23981step1 i j); unfold raw23981step2 raw23981step1; decide +kernel
      have hl : raw23981step2Labels = raw23981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical23982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23982 raw23982Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw23982 raw23982Labels = mixedMoment B raw23982step0 raw23982step0Labels := by
      have ha : raw23982step0 = (fun i j => raw23982 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23982step0 raw23982; decide +kernel
      have hl : raw23982step0Labels = raw23982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23982 raw23982Labels permutation188 permutation2
    mixedMoment B raw23982step0 raw23982step0Labels = mixedMoment B raw23982step1 raw23982step1Labels := by
      have ha : raw23982step1 = -raw23982step0 := by apply Matrix.ext; change ∀ i j, raw23982step1 i j = -(raw23982step0 i j); unfold raw23982step1 raw23982step0; decide +kernel
      have hl : raw23982step1Labels = raw23982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical23983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23983 raw23983Labels = mixedMoment B node3240 node3240Labels := by
  calc
    mixedMoment B raw23983 raw23983Labels = mixedMoment B raw23983step0 raw23983step0Labels := by
      have hz : ∀ j, raw23983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23983step0 = (fun i j => raw23983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23983step0 raw23983; decide +kernel
      have hl : raw23983step0Labels = raw23983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23983 raw23983Labels permutation346 hz
    mixedMoment B raw23983step0 raw23983step0Labels = mixedMoment B raw23983step1 raw23983step1Labels := by
      have ha : raw23983step1 = (fun i j => raw23983step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23983step1 raw23983step0; decide +kernel
      have hl : raw23983step1Labels = raw23983step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23983step0 raw23983step0Labels permutation32 permutation4
    mixedMoment B raw23983step1 raw23983step1Labels = mixedMoment B raw23983step2 raw23983step2Labels := by
      have ha : raw23983step2 = -raw23983step1 := by apply Matrix.ext; change ∀ i j, raw23983step2 i j = -(raw23983step1 i j); unfold raw23983step2 raw23983step1; decide +kernel
      have hl : raw23983step2Labels = raw23983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3240 node3240Labels := by rfl

theorem canonical23984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23984 raw23984Labels = mixedMoment B node3278 node3278Labels := by
  calc
    mixedMoment B raw23984 raw23984Labels = mixedMoment B raw23984step0 raw23984step0Labels := by
      have ha : raw23984step0 = (fun i j => raw23984 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23984step0 raw23984; decide +kernel
      have hl : raw23984step0Labels = raw23984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23984 raw23984Labels permutation152 permutation4
    mixedMoment B raw23984step0 raw23984step0Labels = mixedMoment B raw23984step1 raw23984step1Labels := by
      have ha : raw23984step1 = -raw23984step0 := by apply Matrix.ext; change ∀ i j, raw23984step1 i j = -(raw23984step0 i j); unfold raw23984step1 raw23984step0; decide +kernel
      have hl : raw23984step1Labels = raw23984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3278 node3278Labels := by rfl

theorem canonical23985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23985 raw23985Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw23985 raw23985Labels = mixedMoment B raw23985step0 raw23985step0Labels := by
      have hz : ∀ j, raw23985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23985step0 = (fun i j => raw23985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23985step0 raw23985; decide +kernel
      have hl : raw23985step0Labels = raw23985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23985 raw23985Labels permutation346 hz
    mixedMoment B raw23985step0 raw23985step0Labels = mixedMoment B raw23985step1 raw23985step1Labels := by
      have ha : raw23985step1 = (fun i j => raw23985step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23985step1 raw23985step0; decide +kernel
      have hl : raw23985step1Labels = raw23985step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23985step0 raw23985step0Labels permutation32 permutation4
    mixedMoment B raw23985step1 raw23985step1Labels = mixedMoment B raw23985step2 raw23985step2Labels := by
      have ha : raw23985step2 = -raw23985step1 := by apply Matrix.ext; change ∀ i j, raw23985step2 i j = -(raw23985step1 i j); unfold raw23985step2 raw23985step1; decide +kernel
      have hl : raw23985step2Labels = raw23985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3287 node3287Labels := by rfl

theorem canonical23986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23986 raw23986Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw23986 raw23986Labels = mixedMoment B raw23986step0 raw23986step0Labels := by
      have hz : ∀ j, raw23986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23986step0 = (fun i j => raw23986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23986step0 raw23986; decide +kernel
      have hl : raw23986step0Labels = raw23986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23986 raw23986Labels permutation346 hz
    mixedMoment B raw23986step0 raw23986step0Labels = mixedMoment B raw23986step1 raw23986step1Labels := by
      have ha : raw23986step1 = (fun i j => raw23986step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23986step1 raw23986step0; decide +kernel
      have hl : raw23986step1Labels = raw23986step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23986step0 raw23986step0Labels permutation34 permutation2
    _ = mixedMoment B node1257 node1257Labels := by rfl

theorem canonical23987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23987 raw23987Labels = mixedMoment B node2629 node2629Labels := by
  calc
    mixedMoment B raw23987 raw23987Labels = mixedMoment B raw23987step0 raw23987step0Labels := by
      have hz : ∀ j, raw23987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23987step0 = (fun i j => raw23987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23987step0 raw23987; decide +kernel
      have hl : raw23987step0Labels = raw23987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23987 raw23987Labels permutation346 hz
    mixedMoment B raw23987step0 raw23987step0Labels = mixedMoment B raw23987step1 raw23987step1Labels := by
      have ha : raw23987step1 = (fun i j => raw23987step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23987step1 raw23987step0; decide +kernel
      have hl : raw23987step1Labels = raw23987step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23987step0 raw23987step0Labels permutation34 permutation2
    _ = mixedMoment B node2629 node2629Labels := by rfl

theorem canonical23988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23988 raw23988Labels = mixedMoment B node2565 node2565Labels := by
  calc
    mixedMoment B raw23988 raw23988Labels = mixedMoment B raw23988step0 raw23988step0Labels := by
      have ha : raw23988step0 = (fun i j => raw23988 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23988step0 raw23988; decide +kernel
      have hl : raw23988step0Labels = raw23988Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23988 raw23988Labels permutation178 permutation2
    _ = mixedMoment B node2565 node2565Labels := by rfl

theorem canonical23989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23989 raw23989Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw23989 raw23989Labels = mixedMoment B raw23989step0 raw23989step0Labels := by
      have hz : ∀ j, raw23989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23989step0 = (fun i j => raw23989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23989step0 raw23989; decide +kernel
      have hl : raw23989step0Labels = raw23989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23989 raw23989Labels permutation346 hz
    _ = mixedMoment B node2748 node2748Labels := by rfl

theorem canonical23990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23990 raw23990Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw23990 raw23990Labels = mixedMoment B raw23990step0 raw23990step0Labels := by
      have hz : ∀ j, raw23990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23990step0 = (fun i j => raw23990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23990step0 raw23990; decide +kernel
      have hl : raw23990step0Labels = raw23990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23990 raw23990Labels permutation346 hz
    mixedMoment B raw23990step0 raw23990step0Labels = mixedMoment B raw23990step1 raw23990step1Labels := by
      have ha : raw23990step1 = (fun i j => raw23990step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23990step1 raw23990step0; decide +kernel
      have hl : raw23990step1Labels = raw23990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23990step0 raw23990step0Labels permutation44 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical23991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23991 raw23991Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw23991 raw23991Labels = mixedMoment B raw23991step0 raw23991step0Labels := by
      have hz : ∀ j, raw23991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23991step0 = (fun i j => raw23991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23991step0 raw23991; decide +kernel
      have hl : raw23991step0Labels = raw23991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23991 raw23991Labels permutation346 hz
    mixedMoment B raw23991step0 raw23991step0Labels = mixedMoment B raw23991step1 raw23991step1Labels := by
      have ha : raw23991step1 = (fun i j => raw23991step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23991step1 raw23991step0; decide +kernel
      have hl : raw23991step1Labels = raw23991step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23991step0 raw23991step0Labels permutation34 permutation2
    _ = mixedMoment B node2760 node2760Labels := by rfl

theorem canonical23992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23992 raw23992Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw23992 raw23992Labels = mixedMoment B raw23992step0 raw23992step0Labels := by
      have hz : ∀ j, raw23992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23992step0 = (fun i j => raw23992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23992step0 raw23992; decide +kernel
      have hl : raw23992step0Labels = raw23992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23992 raw23992Labels permutation346 hz
    mixedMoment B raw23992step0 raw23992step0Labels = mixedMoment B raw23992step1 raw23992step1Labels := by
      have ha : raw23992step1 = (fun i j => raw23992step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23992step1 raw23992step0; decide +kernel
      have hl : raw23992step1Labels = raw23992step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23992step0 raw23992step0Labels permutation44 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical23993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23993 raw23993Labels = mixedMoment B node1130 node1130Labels := by
  calc
    _ = mixedMoment B node1130 node1130Labels := by rfl

theorem canonical23994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23994 raw23994Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw23994 raw23994Labels = mixedMoment B raw23994step0 raw23994step0Labels := by
      have hz : ∀ j, raw23994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23994step0 = (fun i j => raw23994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23994step0 raw23994; decide +kernel
      have hl : raw23994step0Labels = raw23994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23994 raw23994Labels permutation346 hz
    mixedMoment B raw23994step0 raw23994step0Labels = mixedMoment B raw23994step1 raw23994step1Labels := by
      have ha : raw23994step1 = (fun i j => raw23994step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23994step1 raw23994step0; decide +kernel
      have hl : raw23994step1Labels = raw23994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23994step0 raw23994step0Labels permutation35 permutation2
    _ = mixedMoment B node1141 node1141Labels := by rfl

theorem canonical23995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23995 raw23995Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw23995 raw23995Labels = mixedMoment B raw23995step0 raw23995step0Labels := by
      have hz : ∀ j, raw23995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23995step0 = (fun i j => raw23995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23995step0 raw23995; decide +kernel
      have hl : raw23995step0Labels = raw23995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23995 raw23995Labels permutation346 hz
    mixedMoment B raw23995step0 raw23995step0Labels = mixedMoment B raw23995step1 raw23995step1Labels := by
      have ha : raw23995step1 = (fun i j => raw23995step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23995step1 raw23995step0; decide +kernel
      have hl : raw23995step1Labels = raw23995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23995step0 raw23995step0Labels permutation33 permutation2
    _ = mixedMoment B node1138 node1138Labels := by rfl

theorem canonical23996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23996 raw23996Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw23996 raw23996Labels = mixedMoment B raw23996step0 raw23996step0Labels := by
      have hz : ∀ j, raw23996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23996step0 = (fun i j => raw23996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23996step0 raw23996; decide +kernel
      have hl : raw23996step0Labels = raw23996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23996 raw23996Labels permutation346 hz
    _ = mixedMoment B node1137 node1137Labels := by rfl

theorem canonical23997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23997 raw23997Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw23997 raw23997Labels = mixedMoment B raw23997step0 raw23997step0Labels := by
      have hz : ∀ j, raw23997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23997step0 = (fun i j => raw23997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23997step0 raw23997; decide +kernel
      have hl : raw23997step0Labels = raw23997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23997 raw23997Labels permutation346 hz
    mixedMoment B raw23997step0 raw23997step0Labels = mixedMoment B raw23997step1 raw23997step1Labels := by
      have ha : raw23997step1 = (fun i j => raw23997step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23997step1 raw23997step0; decide +kernel
      have hl : raw23997step1Labels = raw23997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23997step0 raw23997step0Labels permutation46 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

theorem canonical23998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23998 raw23998Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw23998 raw23998Labels = mixedMoment B raw23998step0 raw23998step0Labels := by
      have ha : raw23998step0 = (fun i j => raw23998 (permutation190 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23998step0 raw23998; decide +kernel
      have hl : raw23998step0Labels = raw23998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23998 raw23998Labels permutation190 permutation2
    _ = mixedMoment B node1156 node1156Labels := by rfl

theorem canonical23999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23999 raw23999Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw23999 raw23999Labels = mixedMoment B raw23999step0 raw23999step0Labels := by
      have hz : ∀ j, raw23999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23999step0 = (fun i j => raw23999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23999step0 raw23999; decide +kernel
      have hl : raw23999step0Labels = raw23999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23999 raw23999Labels permutation346 hz
    mixedMoment B raw23999step0 raw23999step0Labels = mixedMoment B raw23999step1 raw23999step1Labels := by
      have ha : raw23999step1 = (fun i j => raw23999step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23999step1 raw23999step0; decide +kernel
      have hl : raw23999step1Labels = raw23999step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23999step0 raw23999step0Labels permutation46 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical24000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24000 raw24000Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw24000 raw24000Labels = mixedMoment B raw24000step0 raw24000step0Labels := by
      have hz : ∀ j, raw24000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24000step0 = (fun i j => raw24000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24000step0 raw24000; decide +kernel
      have hl : raw24000step0Labels = raw24000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24000 raw24000Labels permutation346 hz
    mixedMoment B raw24000step0 raw24000step0Labels = mixedMoment B raw24000step1 raw24000step1Labels := by
      have ha : raw24000step1 = (fun i j => raw24000step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24000step1 raw24000step0; decide +kernel
      have hl : raw24000step1Labels = raw24000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24000step0 raw24000step0Labels permutation46 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical24001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24001 raw24001Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw24001 raw24001Labels = mixedMoment B raw24001step0 raw24001step0Labels := by
      have hz : ∀ j, raw24001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24001step0 = (fun i j => raw24001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24001step0 raw24001; decide +kernel
      have hl : raw24001step0Labels = raw24001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24001 raw24001Labels permutation346 hz
    mixedMoment B raw24001step0 raw24001step0Labels = mixedMoment B raw24001step1 raw24001step1Labels := by
      have ha : raw24001step1 = (fun i j => raw24001step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24001step1 raw24001step0; decide +kernel
      have hl : raw24001step1Labels = raw24001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24001step0 raw24001step0Labels permutation46 permutation2
    mixedMoment B raw24001step1 raw24001step1Labels = mixedMoment B raw24001step2 raw24001step2Labels := by
      have ha : raw24001step2 = -raw24001step1 := by apply Matrix.ext; change ∀ i j, raw24001step2 i j = -(raw24001step1 i j); unfold raw24001step2 raw24001step1; decide +kernel
      have hl : raw24001step2Labels = raw24001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1640 node1640Labels := by rfl

theorem canonical24002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24002 raw24002Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw24002 raw24002Labels = mixedMoment B raw24002step0 raw24002step0Labels := by
      have ha : raw24002step0 = (fun i j => raw24002 (permutation234 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24002step0 raw24002; decide +kernel
      have hl : raw24002step0Labels = raw24002Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24002 raw24002Labels permutation234 permutation2
    mixedMoment B raw24002step0 raw24002step0Labels = mixedMoment B raw24002step1 raw24002step1Labels := by
      have ha : raw24002step1 = -raw24002step0 := by apply Matrix.ext; change ∀ i j, raw24002step1 i j = -(raw24002step0 i j); unfold raw24002step1 raw24002step0; decide +kernel
      have hl : raw24002step1Labels = raw24002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1635 node1635Labels := by rfl

theorem canonical24003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24003 raw24003Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw24003 raw24003Labels = mixedMoment B raw24003step0 raw24003step0Labels := by
      have hz : ∀ j, raw24003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24003step0 = (fun i j => raw24003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24003step0 raw24003; decide +kernel
      have hl : raw24003step0Labels = raw24003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24003 raw24003Labels permutation346 hz
    mixedMoment B raw24003step0 raw24003step0Labels = mixedMoment B raw24003step1 raw24003step1Labels := by
      have ha : raw24003step1 = (fun i j => raw24003step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24003step1 raw24003step0; decide +kernel
      have hl : raw24003step1Labels = raw24003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24003step0 raw24003step0Labels permutation40 permutation2
    mixedMoment B raw24003step1 raw24003step1Labels = mixedMoment B raw24003step2 raw24003step2Labels := by
      have ha : raw24003step2 = -raw24003step1 := by apply Matrix.ext; change ∀ i j, raw24003step2 i j = -(raw24003step1 i j); unfold raw24003step2 raw24003step1; decide +kernel
      have hl : raw24003step2Labels = raw24003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical24004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24004 raw24004Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw24004 raw24004Labels = mixedMoment B raw24004step0 raw24004step0Labels := by
      have hz : ∀ j, raw24004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24004step0 = (fun i j => raw24004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24004step0 raw24004; decide +kernel
      have hl : raw24004step0Labels = raw24004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24004 raw24004Labels permutation346 hz
    mixedMoment B raw24004step0 raw24004step0Labels = mixedMoment B raw24004step1 raw24004step1Labels := by
      have ha : raw24004step1 = (fun i j => raw24004step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24004step1 raw24004step0; decide +kernel
      have hl : raw24004step1Labels = raw24004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24004step0 raw24004step0Labels permutation46 permutation2
    mixedMoment B raw24004step1 raw24004step1Labels = mixedMoment B raw24004step2 raw24004step2Labels := by
      have ha : raw24004step2 = -raw24004step1 := by apply Matrix.ext; change ∀ i j, raw24004step2 i j = -(raw24004step1 i j); unfold raw24004step2 raw24004step1; decide +kernel
      have hl : raw24004step2Labels = raw24004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1637 node1637Labels := by rfl

theorem canonical24005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24005 raw24005Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw24005 raw24005Labels = mixedMoment B raw24005step0 raw24005step0Labels := by
      have hz : ∀ j, raw24005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24005step0 = (fun i j => raw24005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24005step0 raw24005; decide +kernel
      have hl : raw24005step0Labels = raw24005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24005 raw24005Labels permutation346 hz
    mixedMoment B raw24005step0 raw24005step0Labels = mixedMoment B raw24005step1 raw24005step1Labels := by
      have ha : raw24005step1 = (fun i j => raw24005step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24005step1 raw24005step0; decide +kernel
      have hl : raw24005step1Labels = raw24005step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24005step0 raw24005step0Labels permutation36 permutation4
    mixedMoment B raw24005step1 raw24005step1Labels = mixedMoment B raw24005step2 raw24005step2Labels := by
      have ha : raw24005step2 = -raw24005step1 := by apply Matrix.ext; change ∀ i j, raw24005step2 i j = -(raw24005step1 i j); unfold raw24005step2 raw24005step1; decide +kernel
      have hl : raw24005step2Labels = raw24005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1612 node1612Labels := by rfl

theorem canonical24006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24006 raw24006Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw24006 raw24006Labels = mixedMoment B raw24006step0 raw24006step0Labels := by
      have hz : ∀ j, raw24006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24006step0 = (fun i j => raw24006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24006step0 raw24006; decide +kernel
      have hl : raw24006step0Labels = raw24006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24006 raw24006Labels permutation346 hz
    mixedMoment B raw24006step0 raw24006step0Labels = mixedMoment B raw24006step1 raw24006step1Labels := by
      have ha : raw24006step1 = (fun i j => raw24006step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24006step1 raw24006step0; decide +kernel
      have hl : raw24006step1Labels = raw24006step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24006step0 raw24006step0Labels permutation36 permutation4
    mixedMoment B raw24006step1 raw24006step1Labels = mixedMoment B raw24006step2 raw24006step2Labels := by
      have ha : raw24006step2 = -raw24006step1 := by apply Matrix.ext; change ∀ i j, raw24006step2 i j = -(raw24006step1 i j); unfold raw24006step2 raw24006step1; decide +kernel
      have hl : raw24006step2Labels = raw24006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1610 node1610Labels := by rfl

theorem canonical24007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24007 raw24007Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24007 raw24007Labels = mixedMoment B raw24007step0 raw24007step0Labels := by
      have hz : ∀ j, raw24007 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24007step0 = (fun i j => raw24007 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24007step0 raw24007; decide +kernel
      have hl : raw24007step0Labels = raw24007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24007 raw24007Labels permutation265 hz
    mixedMoment B raw24007step0 raw24007step0Labels = mixedMoment B raw24007step1 raw24007step1Labels := by
      have ha : raw24007step1 = (fun i j => raw24007step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24007step1 raw24007step0; decide +kernel
      have hl : raw24007step1Labels = raw24007step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24007step0 raw24007step0Labels permutation36 permutation4
    mixedMoment B raw24007step1 raw24007step1Labels = mixedMoment B raw24007step2 raw24007step2Labels := by
      have ha : raw24007step2 = -raw24007step1 := by apply Matrix.ext; change ∀ i j, raw24007step2 i j = -(raw24007step1 i j); unfold raw24007step2 raw24007step1; decide +kernel
      have hl : raw24007step2Labels = raw24007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical24008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24008 raw24008Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw24008 raw24008Labels = mixedMoment B raw24008step0 raw24008step0Labels := by
      have hz : ∀ j, raw24008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24008step0 = (fun i j => raw24008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24008step0 raw24008; decide +kernel
      have hl : raw24008step0Labels = raw24008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24008 raw24008Labels permutation346 hz
    mixedMoment B raw24008step0 raw24008step0Labels = mixedMoment B raw24008step1 raw24008step1Labels := by
      have hz : ∀ j, raw24008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24008step1 = (fun i j => raw24008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24008step1 raw24008step0; decide +kernel
      have hl : raw24008step1Labels = raw24008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24008step0 raw24008step0Labels permutation56 hz
    mixedMoment B raw24008step1 raw24008step1Labels = mixedMoment B raw24008step2 raw24008step2Labels := by
      have ha : raw24008step2 = -raw24008step1 := by apply Matrix.ext; change ∀ i j, raw24008step2 i j = -(raw24008step1 i j); unfold raw24008step2 raw24008step1; decide +kernel
      have hl : raw24008step2Labels = raw24008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3308 node3308Labels := by rfl

theorem canonical24009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24009 raw24009Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw24009 raw24009Labels = mixedMoment B raw24009step0 raw24009step0Labels := by
      have hz : ∀ j, raw24009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24009step0 = (fun i j => raw24009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24009step0 raw24009; decide +kernel
      have hl : raw24009step0Labels = raw24009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24009 raw24009Labels permutation346 hz
    mixedMoment B raw24009step0 raw24009step0Labels = mixedMoment B raw24009step1 raw24009step1Labels := by
      have hz : ∀ j, raw24009step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24009step1 = (fun i j => raw24009step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24009step1 raw24009step0; decide +kernel
      have hl : raw24009step1Labels = raw24009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24009step0 raw24009step0Labels permutation56 hz
    mixedMoment B raw24009step1 raw24009step1Labels = mixedMoment B raw24009step2 raw24009step2Labels := by
      have ha : raw24009step2 = (fun i j => raw24009step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24009step2 raw24009step1; decide +kernel
      have hl : raw24009step2Labels = raw24009step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24009step1 raw24009step1Labels permutation29 permutation2
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical24010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24010 raw24010Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw24010 raw24010Labels = mixedMoment B raw24010step0 raw24010step0Labels := by
      have ha : raw24010step0 = (fun i j => raw24010 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24010step0 raw24010; decide +kernel
      have hl : raw24010step0Labels = raw24010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24010 raw24010Labels permutation184 permutation2
    mixedMoment B raw24010step0 raw24010step0Labels = mixedMoment B raw24010step1 raw24010step1Labels := by
      have ha : raw24010step1 = -raw24010step0 := by apply Matrix.ext; change ∀ i j, raw24010step1 i j = -(raw24010step0 i j); unfold raw24010step1 raw24010step0; decide +kernel
      have hl : raw24010step1Labels = raw24010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical24011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24011 raw24011Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24011 raw24011Labels = mixedMoment B raw24011step0 raw24011step0Labels := by
      have hz : ∀ j, raw24011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24011step0 = (fun i j => raw24011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24011step0 raw24011; decide +kernel
      have hl : raw24011step0Labels = raw24011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24011 raw24011Labels permutation346 hz
    mixedMoment B raw24011step0 raw24011step0Labels = mixedMoment B raw24011step1 raw24011step1Labels := by
      have ha : raw24011step1 = (fun i j => raw24011step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24011step1 raw24011step0; decide +kernel
      have hl : raw24011step1Labels = raw24011step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24011step0 raw24011step0Labels permutation37 permutation4
    mixedMoment B raw24011step1 raw24011step1Labels = mixedMoment B raw24011step2 raw24011step2Labels := by
      have ha : raw24011step2 = -raw24011step1 := by apply Matrix.ext; change ∀ i j, raw24011step2 i j = -(raw24011step1 i j); unfold raw24011step2 raw24011step1; decide +kernel
      have hl : raw24011step2Labels = raw24011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical24012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24012 raw24012Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw24012 raw24012Labels = mixedMoment B raw24012step0 raw24012step0Labels := by
      have ha : raw24012step0 = (fun i j => raw24012 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24012step0 raw24012; decide +kernel
      have hl : raw24012step0Labels = raw24012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24012 raw24012Labels permutation160 permutation2
    _ = mixedMoment B node1126 node1126Labels := by rfl

theorem canonical24013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24013 raw24013Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw24013 raw24013Labels = mixedMoment B raw24013step0 raw24013step0Labels := by
      have ha : raw24013step0 = (fun i j => raw24013 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24013step0 raw24013; decide +kernel
      have hl : raw24013step0Labels = raw24013Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24013 raw24013Labels permutation154 permutation2
    _ = mixedMoment B node1113 node1113Labels := by rfl

theorem canonical24014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24014 raw24014Labels = mixedMoment B node1113 node1113Labels := by
  calc
    _ = mixedMoment B node1113 node1113Labels := by rfl

theorem canonical24015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24015 raw24015Labels = mixedMoment B node1111 node1111Labels := by
  calc
    _ = mixedMoment B node1111 node1111Labels := by rfl

theorem canonical24016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24016 raw24016Labels = mixedMoment B node623 node623Labels := by
  calc
    mixedMoment B raw24016 raw24016Labels = mixedMoment B raw24016step0 raw24016step0Labels := by
      have ha : raw24016step0 = (fun i j => raw24016 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24016step0 raw24016; decide +kernel
      have hl : raw24016step0Labels = raw24016Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24016 raw24016Labels permutation160 permutation2
    _ = mixedMoment B node623 node623Labels := by rfl

theorem canonical24017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24017 raw24017Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24017 raw24017Labels = mixedMoment B raw24017step0 raw24017step0Labels := by
      have hz : ∀ j, raw24017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24017step0 = (fun i j => raw24017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24017step0 raw24017; decide +kernel
      have hl : raw24017step0Labels = raw24017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24017 raw24017Labels permutation434 hz
    mixedMoment B raw24017step0 raw24017step0Labels = mixedMoment B raw24017step1 raw24017step1Labels := by
      have ha : raw24017step1 = (fun i j => raw24017step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24017step1 raw24017step0; decide +kernel
      have hl : raw24017step1Labels = raw24017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24017step0 raw24017step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical24018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24018 raw24018Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24018 raw24018Labels = mixedMoment B raw24018step0 raw24018step0Labels := by
      have hz : ∀ j, raw24018 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24018step0 = (fun i j => raw24018 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24018step0 raw24018; decide +kernel
      have hl : raw24018step0Labels = raw24018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24018 raw24018Labels permutation520 hz
    mixedMoment B raw24018step0 raw24018step0Labels = mixedMoment B raw24018step1 raw24018step1Labels := by
      have ha : raw24018step1 = (fun i j => raw24018step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24018step1 raw24018step0; decide +kernel
      have hl : raw24018step1Labels = raw24018step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24018step0 raw24018step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical24019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24019 raw24019Labels = mixedMoment B node629 node629Labels := by
  calc
    mixedMoment B raw24019 raw24019Labels = mixedMoment B raw24019step0 raw24019step0Labels := by
      have ha : raw24019step0 = (fun i j => raw24019 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24019step0 raw24019; decide +kernel
      have hl : raw24019step0Labels = raw24019Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24019 raw24019Labels permutation176 permutation2
    _ = mixedMoment B node629 node629Labels := by rfl

theorem canonical24020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24020 raw24020Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24020 raw24020Labels = mixedMoment B raw24020step0 raw24020step0Labels := by
      have ha : raw24020step0 = (fun i j => raw24020 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24020step0 raw24020; decide +kernel
      have hl : raw24020step0Labels = raw24020Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24020 raw24020Labels permutation176 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

theorem canonical24021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24021 raw24021Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw24021 raw24021Labels = mixedMoment B raw24021step0 raw24021step0Labels := by
      have ha : raw24021step0 = (fun i j => raw24021 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24021step0 raw24021; decide +kernel
      have hl : raw24021step0Labels = raw24021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24021 raw24021Labels permutation176 permutation2
    _ = mixedMoment B node1135 node1135Labels := by rfl

theorem canonical24022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24022 raw24022Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24022 raw24022Labels = mixedMoment B raw24022step0 raw24022step0Labels := by
      have ha : raw24022step0 = (fun i j => raw24022 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24022step0 raw24022; decide +kernel
      have hl : raw24022step0Labels = raw24022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24022 raw24022Labels permutation182 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

theorem canonical24023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24023 raw24023Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw24023 raw24023Labels = mixedMoment B raw24023step0 raw24023step0Labels := by
      have ha : raw24023step0 = (fun i j => raw24023 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24023step0 raw24023; decide +kernel
      have hl : raw24023step0Labels = raw24023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24023 raw24023Labels permutation188 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

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

theorem canonical9582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9582 raw9582Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw9582 raw9582Labels = mixedMoment B raw9582step0 raw9582step0Labels := by
      have hz : ∀ j, raw9582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9582step0 = (fun i j => raw9582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9582step0 raw9582; decide +kernel
      have hl : raw9582step0Labels = raw9582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9582 raw9582Labels permutation346 hz
    mixedMoment B raw9582step0 raw9582step0Labels = mixedMoment B raw9582step1 raw9582step1Labels := by
      have ha : raw9582step1 = (fun i j => raw9582step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9582step1 raw9582step0; decide +kernel
      have hl : raw9582step1Labels = raw9582step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9582step0 raw9582step0Labels permutation34 permutation2
    _ = mixedMoment B node1261 node1261Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical90
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11640 raw11640Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw11640 raw11640Labels = mixedMoment B raw11640step0 raw11640step0Labels := by
      have hz : ∀ j, raw11640 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11640step0 = (fun i j => raw11640 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11640step0 raw11640; decide +kernel
      have hl : raw11640step0Labels = raw11640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11640 raw11640Labels permutation520 hz
    mixedMoment B raw11640step0 raw11640step0Labels = mixedMoment B raw11640step1 raw11640step1Labels := by
      have hz : ∀ j, raw11640step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11640step1 = (fun i j => raw11640step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11640step1 raw11640step0; decide +kernel
      have hl : raw11640step1Labels = raw11640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11640step0 raw11640step0Labels permutation104 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical11642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11642 raw11642Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw11642 raw11642Labels = mixedMoment B raw11642step0 raw11642step0Labels := by
      have ha : raw11642step0 = (fun i j => raw11642 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11642step0 raw11642; decide +kernel
      have hl : raw11642step0Labels = raw11642Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11642 raw11642Labels permutation160 permutation2
    _ = mixedMoment B node1233 node1233Labels := by rfl

theorem canonical11645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11645 raw11645Labels = mixedMoment B node1212 node1212Labels := by
  calc
    _ = mixedMoment B node1212 node1212Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical91
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11653 raw11653Labels = mixedMoment B node2479 node2479Labels := by
  calc
    _ = mixedMoment B node2479 node2479Labels := by rfl

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

theorem sound1111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1111 node1111Labels = Sparse.eval nodeValue1111 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1111) = mixedMoment B node1111 node1111Labels := rfl
  simpa [nodeValue1111, Sparse.eval] using hc.symm

theorem sound1113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1113 node1113Labels = Sparse.eval nodeValue1113 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1113) = mixedMoment B node1113 node1113Labels := rfl
  simpa [nodeValue1113, Sparse.eval] using hc.symm

theorem sound1126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1126 node1126Labels = Sparse.eval nodeValue1126 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1126) = mixedMoment B node1126 node1126Labels := rfl
  simpa [nodeValue1126, Sparse.eval] using hc.symm

theorem sound1130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1130 node1130Labels = Sparse.eval nodeValue1130 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1130) = mixedMoment B node1130 node1130Labels := rfl
  simpa [nodeValue1130, Sparse.eval] using hc.symm

theorem sound1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1135 node1135Labels = Sparse.eval nodeValue1135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1135) = mixedMoment B node1135 node1135Labels := rfl
  simpa [nodeValue1135, Sparse.eval] using hc.symm

theorem sound1137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1137 node1137Labels = Sparse.eval nodeValue1137 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1137) = mixedMoment B node1137 node1137Labels := rfl
  simpa [nodeValue1137, Sparse.eval] using hc.symm

theorem sound1138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1138 node1138Labels = Sparse.eval nodeValue1138 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1138) = mixedMoment B node1138 node1138Labels := rfl
  simpa [nodeValue1138, Sparse.eval] using hc.symm

theorem sound1141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1141 node1141Labels = Sparse.eval nodeValue1141 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1141) = mixedMoment B node1141 node1141Labels := rfl
  simpa [nodeValue1141, Sparse.eval] using hc.symm

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

theorem sound1156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1156 node1156Labels = Sparse.eval nodeValue1156 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1156) = mixedMoment B node1156 node1156Labels := rfl
  simpa [nodeValue1156, Sparse.eval] using hc.symm

theorem sound1212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1212 node1212Labels = Sparse.eval nodeValue1212 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1212) = mixedMoment B node1212 node1212Labels := rfl
  simpa [nodeValue1212, Sparse.eval] using hc.symm

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

theorem sound1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1216 node1216Labels = Sparse.eval nodeValue1216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1216) = mixedMoment B node1216 node1216Labels := rfl
  simpa [nodeValue1216, Sparse.eval] using hc.symm

theorem sound1233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1233 node1233Labels = Sparse.eval nodeValue1233 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1233) = mixedMoment B node1233 node1233Labels := rfl
  simpa [nodeValue1233, Sparse.eval] using hc.symm

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1236 node1236Labels = Sparse.eval nodeValue1236 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1236) = mixedMoment B node1236 node1236Labels := rfl
  simpa [nodeValue1236, Sparse.eval] using hc.symm

theorem sound1241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1241 node1241Labels = Sparse.eval nodeValue1241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1241) = mixedMoment B node1241 node1241Labels := rfl
  simpa [nodeValue1241, Sparse.eval] using hc.symm

theorem sound1257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1257 node1257Labels = Sparse.eval nodeValue1257 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1257) = mixedMoment B node1257 node1257Labels := rfl
  simpa [nodeValue1257, Sparse.eval] using hc.symm

theorem sound1261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1261 node1261Labels = Sparse.eval nodeValue1261 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1261) = mixedMoment B node1261 node1261Labels := rfl
  simpa [nodeValue1261, Sparse.eval] using hc.symm

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

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

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

theorem zero1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1598 node1598Labels = 0 := by
  exact mixedMoment_alpha B hF node1598 node1598Labels 1 permutation436
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

theorem sound1598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1598 node1598Labels = Sparse.eval nodeValue1598 (mixedVector B) := by
  simpa only [nodeValue1598, Sparse.eval_nil] using zero1598 B _hB _hF

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

theorem sound1603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1603 node1603Labels = Sparse.eval nodeValue1603 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1603) = mixedMoment B node1603 node1603Labels := rfl
  simpa [nodeValue1603, Sparse.eval] using hc.symm

theorem sound1605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1605 node1605Labels = Sparse.eval nodeValue1605 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1605) = mixedMoment B node1605 node1605Labels := rfl
  simpa [nodeValue1605, Sparse.eval] using hc.symm

theorem sound1607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1607 node1607Labels = Sparse.eval nodeValue1607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1607) = mixedMoment B node1607 node1607Labels := rfl
  simpa [nodeValue1607, Sparse.eval] using hc.symm

theorem sound1610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1610 node1610Labels = Sparse.eval nodeValue1610 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1610) = mixedMoment B node1610 node1610Labels := rfl
  simpa [nodeValue1610, Sparse.eval] using hc.symm

theorem sound1612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1612 node1612Labels = Sparse.eval nodeValue1612 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1612) = mixedMoment B node1612 node1612Labels := rfl
  simpa [nodeValue1612, Sparse.eval] using hc.symm

theorem sound1623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1623 node1623Labels = Sparse.eval nodeValue1623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1623) = mixedMoment B node1623 node1623Labels := rfl
  simpa [nodeValue1623, Sparse.eval] using hc.symm

theorem sound1635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1635 node1635Labels = Sparse.eval nodeValue1635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1635) = mixedMoment B node1635 node1635Labels := rfl
  simpa [nodeValue1635, Sparse.eval] using hc.symm

theorem sound1637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1637 node1637Labels = Sparse.eval nodeValue1637 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1637) = mixedMoment B node1637 node1637Labels := rfl
  simpa [nodeValue1637, Sparse.eval] using hc.symm

theorem sound1640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1640 node1640Labels = Sparse.eval nodeValue1640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1640) = mixedMoment B node1640 node1640Labels := rfl
  simpa [nodeValue1640, Sparse.eval] using hc.symm

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

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

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1724 node1724Labels = Sparse.eval nodeValue1724 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1724) = mixedMoment B node1724 node1724Labels := rfl
  simpa [nodeValue1724, Sparse.eval] using hc.symm

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

theorem sound1728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1728 node1728Labels = Sparse.eval nodeValue1728 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1728) = mixedMoment B node1728 node1728Labels := rfl
  simpa [nodeValue1728, Sparse.eval] using hc.symm

theorem sound1739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1739 node1739Labels = Sparse.eval nodeValue1739 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1739) = mixedMoment B node1739 node1739Labels := rfl
  simpa [nodeValue1739, Sparse.eval] using hc.symm

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

theorem sound2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2479 node2479Labels = Sparse.eval nodeValue2479 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2479) = mixedMoment B node2479 node2479Labels := rfl
  simpa [nodeValue2479, Sparse.eval] using hc.symm

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

theorem sound2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2565 node2565Labels = Sparse.eval nodeValue2565 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2565) = mixedMoment B node2565 node2565Labels := rfl
  simpa [nodeValue2565, Sparse.eval] using hc.symm

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

theorem sound2629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2629 node2629Labels = Sparse.eval nodeValue2629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2629) = mixedMoment B node2629 node2629Labels := rfl
  simpa [nodeValue2629, Sparse.eval] using hc.symm

theorem sound2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2672 node2672Labels = Sparse.eval nodeValue2672 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2672) = mixedMoment B node2672 node2672Labels := rfl
  simpa [nodeValue2672, Sparse.eval] using hc.symm

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

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

theorem sound2748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2748 node2748Labels = Sparse.eval nodeValue2748 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2748) = mixedMoment B node2748 node2748Labels := rfl
  simpa [nodeValue2748, Sparse.eval] using hc.symm

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

theorem sound2760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2760 node2760Labels = Sparse.eval nodeValue2760 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2760) = mixedMoment B node2760 node2760Labels := rfl
  simpa [nodeValue2760, Sparse.eval] using hc.symm

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

theorem sound3022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3022 node3022Labels = Sparse.eval nodeValue3022 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3022) = mixedMoment B node3022 node3022Labels := rfl
  simpa [nodeValue3022, Sparse.eval] using hc.symm

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

theorem sound3240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3240 node3240Labels = Sparse.eval nodeValue3240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3240) = mixedMoment B node3240 node3240Labels := rfl
  simpa [nodeValue3240, Sparse.eval] using hc.symm

theorem sound3246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3246 node3246Labels = Sparse.eval nodeValue3246 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3246) = mixedMoment B node3246 node3246Labels := rfl
  simpa [nodeValue3246, Sparse.eval] using hc.symm

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

theorem sound3278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3278 node3278Labels = Sparse.eval nodeValue3278 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3278) = mixedMoment B node3278 node3278Labels := rfl
  simpa [nodeValue3278, Sparse.eval] using hc.symm

theorem sound3282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3282 node3282Labels = Sparse.eval nodeValue3282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3282) = mixedMoment B node3282 node3282Labels := rfl
  simpa [nodeValue3282, Sparse.eval] using hc.symm

theorem sound3285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3285 node3285Labels = Sparse.eval nodeValue3285 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3285) = mixedMoment B node3285 node3285Labels := rfl
  simpa [nodeValue3285, Sparse.eval] using hc.symm

theorem sound3287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3287 node3287Labels = Sparse.eval nodeValue3287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3287) = mixedMoment B node3287 node3287Labels := rfl
  simpa [nodeValue3287, Sparse.eval] using hc.symm

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

theorem sound3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3290 node3290Labels = Sparse.eval nodeValue3290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3290) = mixedMoment B node3290 node3290Labels := rfl
  simpa [nodeValue3290, Sparse.eval] using hc.symm

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

theorem sound3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3294 node3294Labels = Sparse.eval nodeValue3294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3294) = mixedMoment B node3294 node3294Labels := rfl
  simpa [nodeValue3294, Sparse.eval] using hc.symm

theorem sound3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3296 node3296Labels = Sparse.eval nodeValue3296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3296) = mixedMoment B node3296 node3296Labels := rfl
  simpa [nodeValue3296, Sparse.eval] using hc.symm

theorem sound3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3299 node3299Labels = Sparse.eval nodeValue3299 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3299) = mixedMoment B node3299 node3299Labels := rfl
  simpa [nodeValue3299, Sparse.eval] using hc.symm

theorem sound3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3305 node3305Labels = Sparse.eval nodeValue3305 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3305) = mixedMoment B node3305 node3305Labels := rfl
  simpa [nodeValue3305, Sparse.eval] using hc.symm

theorem sound3306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3306 node3306Labels = Sparse.eval nodeValue3306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3306) = mixedMoment B node3306 node3306Labels := rfl
  simpa [nodeValue3306, Sparse.eval] using hc.symm

theorem sound3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3308 node3308Labels = Sparse.eval nodeValue3308 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3308) = mixedMoment B node3308 node3308Labels := rfl
  simpa [nodeValue3308, Sparse.eval] using hc.symm

theorem sound3309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3309 node3309Labels = Sparse.eval nodeValue3309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3309) = mixedMoment B node3309 node3309Labels := rfl
  simpa [nodeValue3309, Sparse.eval] using hc.symm

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

theorem sound4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4069 node4069Labels = Sparse.eval nodeValue4069 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4069) = mixedMoment B node4069 node4069Labels := rfl
  simpa [nodeValue4069, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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

theorem sound623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node623 node623Labels = Sparse.eval nodeValue623 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 623) = mixedMoment B node623 node623Labels := rfl
  simpa [nodeValue623, Sparse.eval] using hc.symm

theorem sound629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node629 node629Labels = Sparse.eval nodeValue629 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 629) = mixedMoment B node629 node629Labels := rfl
  simpa [nodeValue629, Sparse.eval] using hc.symm

theorem sound638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node638 node638Labels = Sparse.eval nodeValue638 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 638) = mixedMoment B node638 node638Labels := rfl
  simpa [nodeValue638, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources50
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1615 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1615 + difference 0 0) (sourceB1615 + difference 0 0) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1615 + difference 0 0) (sourceB1615 + difference 0 0) sourceC1615) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1615 + difference 1 0) (sourceB1615 + difference 0 1) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1615 + difference 1 0) (sourceB1615 + difference 0 1) sourceC1615) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1615 + difference 2 0) (sourceB1615 + difference 0 2) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1598) := by
    have ha : (tripleCharges (sourceA1615 + difference 2 0) (sourceB1615 + difference 0 2) sourceC1615) = raw23830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23830; decide +kernel
    rw [ha]
    exact (canonical23830 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1615 + difference 3 0) (sourceB1615 + difference 0 3) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1615 + difference 3 0) (sourceB1615 + difference 0 3) sourceC1615) = raw23972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23972; decide +kernel
    rw [ha]
    exact (canonical23972 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1615 + difference 4 0) (sourceB1615 + difference 0 4) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1603) := by
    have ha : (tripleCharges (sourceA1615 + difference 4 0) (sourceB1615 + difference 0 4) sourceC1615) = raw23973 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23973; decide +kernel
    rw [ha]
    exact (canonical23973 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1615 + difference 5 0) (sourceB1615 + difference 0 5) sourceC1615) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1615 + difference 5 0) (sourceB1615 + difference 0 5) sourceC1615) = raw23974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1615 sourceB1615 sourceC1615 difference raw23974; decide +kernel
    rw [ha]
    exact (canonical23974 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1615 + sourceB1615) sourceC1615) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1615 + sourceB1615) sourceC1615) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1615 sourceB1615 sourceC1615 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1615 sourceB1615 sourceC1615
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1615, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1616 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 0) (sourceB1616 + difference 0 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 0) (sourceB1616 + difference 0 1) sourceC1616) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 1) (sourceB1616 + difference 1 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 1) (sourceB1616 + difference 1 1) sourceC1616) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 2) (sourceB1616 + difference 2 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 2) (sourceB1616 + difference 2 1) sourceC1616) = raw23975 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23975; decide +kernel
    rw [ha]
    exact (canonical23975 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 3) (sourceB1616 + difference 3 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 3) (sourceB1616 + difference 3 1) sourceC1616) = raw23976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23976; decide +kernel
    rw [ha]
    exact (canonical23976 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 4) (sourceB1616 + difference 4 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3309) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 4) (sourceB1616 + difference 4 1) sourceC1616) = raw23977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23977; decide +kernel
    rw [ha]
    exact (canonical23977 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1616 + difference 1 5) (sourceB1616 + difference 5 1) sourceC1616) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1616 + difference 1 5) (sourceB1616 + difference 5 1) sourceC1616) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1616 sourceB1616 sourceC1616 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1616 + sourceB1616) sourceC1616) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1616 + sourceB1616) sourceC1616) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1616 sourceB1616 sourceC1616 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1616 sourceB1616 sourceC1616
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1616, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1617 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 0) (sourceB1617 + difference 0 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 0) (sourceB1617 + difference 0 3) sourceC1617) = raw23972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23972; decide +kernel
    rw [ha]
    exact (canonical23972 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 1) (sourceB1617 + difference 1 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 1) (sourceB1617 + difference 1 3) sourceC1617) = raw23978 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23978; decide +kernel
    rw [ha]
    exact (canonical23978 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 2) (sourceB1617 + difference 2 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 2) (sourceB1617 + difference 2 3) sourceC1617) = raw23979 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23979; decide +kernel
    rw [ha]
    exact (canonical23979 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 3) (sourceB1617 + difference 3 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 3) (sourceB1617 + difference 3 3) sourceC1617) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 4) (sourceB1617 + difference 4 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 4) (sourceB1617 + difference 4 3) sourceC1617) = raw23980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23980; decide +kernel
    rw [ha]
    exact (canonical23980 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1617 + difference 3 5) (sourceB1617 + difference 5 3) sourceC1617) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1617 + difference 3 5) (sourceB1617 + difference 5 3) sourceC1617) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1617 sourceB1617 sourceC1617 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1617 + sourceB1617) sourceC1617) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1617 + sourceB1617) sourceC1617) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1617 sourceB1617 sourceC1617 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1617 sourceB1617 sourceC1617
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1617, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1618 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1618 + difference 0 4) (sourceB1618 + difference 4 0) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1618 + difference 0 4) (sourceB1618 + difference 4 0) sourceC1618) = raw23970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23970; decide +kernel
    rw [ha]
    exact (canonical23970 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1618 + difference 1 4) (sourceB1618 + difference 4 1) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3309) := by
    have ha : (tripleCharges (sourceA1618 + difference 1 4) (sourceB1618 + difference 4 1) sourceC1618) = raw23977 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23977; decide +kernel
    rw [ha]
    exact (canonical23977 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1618 + difference 2 4) (sourceB1618 + difference 4 2) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1618 + difference 2 4) (sourceB1618 + difference 4 2) sourceC1618) = raw23982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23982; decide +kernel
    rw [ha]
    exact (canonical23982 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1618 + difference 3 4) (sourceB1618 + difference 4 3) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1618 + difference 3 4) (sourceB1618 + difference 4 3) sourceC1618) = raw23980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23980; decide +kernel
    rw [ha]
    exact (canonical23980 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1618 + difference 4 4) (sourceB1618 + difference 4 4) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1618 + difference 4 4) (sourceB1618 + difference 4 4) sourceC1618) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1618 + difference 5 4) (sourceB1618 + difference 4 5) sourceC1618) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1618 + difference 5 4) (sourceB1618 + difference 4 5) sourceC1618) = raw23954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1618 sourceB1618 sourceC1618 difference raw23954; decide +kernel
    rw [ha]
    exact (canonical23954 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1618 + sourceB1618) sourceC1618) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1618 + sourceB1618) sourceC1618) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1618 sourceB1618 sourceC1618 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1618 sourceB1618 sourceC1618
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1618, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1619 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 0) (sourceB1619 + difference 0 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1605) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 0) (sourceB1619 + difference 0 5) sourceC1619) = raw23974 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23974; decide +kernel
    rw [ha]
    exact (canonical23974 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 1) (sourceB1619 + difference 1 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3240) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 1) (sourceB1619 + difference 1 5) sourceC1619) = raw23983 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23983; decide +kernel
    rw [ha]
    exact (canonical23983 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 2) (sourceB1619 + difference 2 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3278) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 2) (sourceB1619 + difference 2 5) sourceC1619) = raw23984 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23984; decide +kernel
    rw [ha]
    exact (canonical23984 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 3) (sourceB1619 + difference 3 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 3) (sourceB1619 + difference 3 5) sourceC1619) = raw23985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23985; decide +kernel
    rw [ha]
    exact (canonical23985 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 4) (sourceB1619 + difference 4 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 4) (sourceB1619 + difference 4 5) sourceC1619) = raw23954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23954; decide +kernel
    rw [ha]
    exact (canonical23954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1619 + difference 5 5) (sourceB1619 + difference 5 5) sourceC1619) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1619 + difference 5 5) (sourceB1619 + difference 5 5) sourceC1619) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1619 sourceB1619 sourceC1619 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1619 + sourceB1619) sourceC1619) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1619 + sourceB1619) sourceC1619) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1619 sourceB1619 sourceC1619 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1619 sourceB1619 sourceC1619
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1619, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1620 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1620 + difference 0 5) (sourceB1620 + difference 5 0) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1620 + difference 0 5) (sourceB1620 + difference 5 0) sourceC1620) = raw23971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23971; decide +kernel
    rw [ha]
    exact (canonical23971 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1620 + difference 1 5) (sourceB1620 + difference 5 1) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1620 + difference 1 5) (sourceB1620 + difference 5 1) sourceC1620) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1620 + difference 2 5) (sourceB1620 + difference 5 2) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA1620 + difference 2 5) (sourceB1620 + difference 5 2) sourceC1620) = raw23818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23818; decide +kernel
    rw [ha]
    exact (canonical23818 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1620 + difference 3 5) (sourceB1620 + difference 5 3) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1620 + difference 3 5) (sourceB1620 + difference 5 3) sourceC1620) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1620 + difference 4 5) (sourceB1620 + difference 5 4) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3022) := by
    have ha : (tripleCharges (sourceA1620 + difference 4 5) (sourceB1620 + difference 5 4) sourceC1620) = raw23794 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23794; decide +kernel
    rw [ha]
    exact (canonical23794 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1620 + difference 5 5) (sourceB1620 + difference 5 5) sourceC1620) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1620 + difference 5 5) (sourceB1620 + difference 5 5) sourceC1620) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1620 sourceB1620 sourceC1620 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1620 + sourceB1620) sourceC1620) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1620 + sourceB1620) sourceC1620) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1620 sourceB1620 sourceC1620 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1620 sourceB1620 sourceC1620
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1620, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1621 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 0) (sourceB1621 + difference 0 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1257) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 0) (sourceB1621 + difference 0 0) sourceC1621) = raw23986 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23986; decide +kernel
    rw [ha]
    exact (canonical23986 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 1) (sourceB1621 + difference 1 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2629) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 1) (sourceB1621 + difference 1 0) sourceC1621) = raw23987 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23987; decide +kernel
    rw [ha]
    exact (canonical23987 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 2) (sourceB1621 + difference 2 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2565) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 2) (sourceB1621 + difference 2 0) sourceC1621) = raw23988 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23988; decide +kernel
    rw [ha]
    exact (canonical23988 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 3) (sourceB1621 + difference 3 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2748) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 3) (sourceB1621 + difference 3 0) sourceC1621) = raw23989 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23989; decide +kernel
    rw [ha]
    exact (canonical23989 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 4) (sourceB1621 + difference 4 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 4) (sourceB1621 + difference 4 0) sourceC1621) = raw23990 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23990; decide +kernel
    rw [ha]
    exact (canonical23990 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1621 + difference 0 5) (sourceB1621 + difference 5 0) sourceC1621) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2760) := by
    have ha : (tripleCharges (sourceA1621 + difference 0 5) (sourceB1621 + difference 5 0) sourceC1621) = raw23991 := by
      apply Matrix.ext; unfold tripleCharges sourceA1621 sourceB1621 sourceC1621 difference raw23991; decide +kernel
    rw [ha]
    exact (canonical23991 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1621 + sourceB1621) sourceC1621) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1621 + sourceB1621) sourceC1621) = raw23992 := by
      apply Matrix.ext; unfold doubleCharges sourceA1621 sourceB1621 sourceC1621 raw23992; decide +kernel
    rw [ha]
    exact (canonical23992 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1621 sourceB1621 sourceC1621
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1621, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1622 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1622 + difference 0 1) (sourceB1622 + difference 1 0) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2515) := by
    have ha : (tripleCharges (sourceA1622 + difference 0 1) (sourceB1622 + difference 1 0) sourceC1622) = raw6233 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw6233; decide +kernel
    rw [ha]
    exact (canonical6233 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1622 + difference 1 1) (sourceB1622 + difference 1 1) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1241) := by
    have ha : (tripleCharges (sourceA1622 + difference 1 1) (sourceB1622 + difference 1 1) sourceC1622) = raw6225 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw6225; decide +kernel
    rw [ha]
    exact (canonical6225 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1622 + difference 2 1) (sourceB1622 + difference 1 2) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1130) := by
    have ha : (tripleCharges (sourceA1622 + difference 2 1) (sourceB1622 + difference 1 2) sourceC1622) = raw23993 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23993; decide +kernel
    rw [ha]
    exact (canonical23993 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1622 + difference 3 1) (sourceB1622 + difference 1 3) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1622 + difference 3 1) (sourceB1622 + difference 1 3) sourceC1622) = raw23994 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23994; decide +kernel
    rw [ha]
    exact (canonical23994 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1622 + difference 4 1) (sourceB1622 + difference 1 4) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1138) := by
    have ha : (tripleCharges (sourceA1622 + difference 4 1) (sourceB1622 + difference 1 4) sourceC1622) = raw23995 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23995; decide +kernel
    rw [ha]
    exact (canonical23995 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1622 + difference 5 1) (sourceB1622 + difference 1 5) sourceC1622) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1137) := by
    have ha : (tripleCharges (sourceA1622 + difference 5 1) (sourceB1622 + difference 1 5) sourceC1622) = raw23996 := by
      apply Matrix.ext; unfold tripleCharges sourceA1622 sourceB1622 sourceC1622 difference raw23996; decide +kernel
    rw [ha]
    exact (canonical23996 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1622 + sourceB1622) sourceC1622) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1622 + sourceB1622) sourceC1622) = raw6222 := by
      apply Matrix.ext; unfold doubleCharges sourceA1622 sourceB1622 sourceC1622 raw6222; decide +kernel
    rw [ha]
    exact (canonical6222 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1622 sourceB1622 sourceC1622
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1622, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1623 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 0) (sourceB1623 + difference 0 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 638) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 0) (sourceB1623 + difference 0 1) sourceC1623) = raw23997 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw23997; decide +kernel
    rw [ha]
    exact (canonical23997 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 1) (sourceB1623 + difference 1 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1261) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 1) (sourceB1623 + difference 1 1) sourceC1623) = raw9582 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw9582; decide +kernel
    rw [ha]
    exact (canonical9582 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 2) (sourceB1623 + difference 2 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1156) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 2) (sourceB1623 + difference 2 1) sourceC1623) = raw23998 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw23998; decide +kernel
    rw [ha]
    exact (canonical23998 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 3) (sourceB1623 + difference 3 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1294) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 3) (sourceB1623 + difference 3 1) sourceC1623) = raw9580 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw9580; decide +kernel
    rw [ha]
    exact (canonical9580 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 4) (sourceB1623 + difference 4 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 4) (sourceB1623 + difference 4 1) sourceC1623) = raw23999 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw23999; decide +kernel
    rw [ha]
    exact (canonical23999 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1623 + difference 1 5) (sourceB1623 + difference 5 1) sourceC1623) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1291) := by
    have ha : (tripleCharges (sourceA1623 + difference 1 5) (sourceB1623 + difference 5 1) sourceC1623) = raw24000 := by
      apply Matrix.ext; unfold tripleCharges sourceA1623 sourceB1623 sourceC1623 difference raw24000; decide +kernel
    rw [ha]
    exact (canonical24000 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1623 + sourceB1623) sourceC1623) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1623 + sourceB1623) sourceC1623) = raw4905 := by
      apply Matrix.ext; unfold doubleCharges sourceA1623 sourceB1623 sourceC1623 raw4905; decide +kernel
    rw [ha]
    exact (canonical4905 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1623 sourceB1623 sourceC1623
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1623, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1624 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 0) (sourceB1624 + difference 0 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 0) (sourceB1624 + difference 0 0) sourceC1624) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 1) (sourceB1624 + difference 1 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1640) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 1) (sourceB1624 + difference 1 0) sourceC1624) = raw24001 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24001; decide +kernel
    rw [ha]
    exact (canonical24001 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 2) (sourceB1624 + difference 2 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 2) (sourceB1624 + difference 2 0) sourceC1624) = raw24002 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24002; decide +kernel
    rw [ha]
    exact (canonical24002 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 3) (sourceB1624 + difference 3 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 3) (sourceB1624 + difference 3 0) sourceC1624) = raw23971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw23971; decide +kernel
    rw [ha]
    exact (canonical23971 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 4) (sourceB1624 + difference 4 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 4) (sourceB1624 + difference 4 0) sourceC1624) = raw24003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24003; decide +kernel
    rw [ha]
    exact (canonical24003 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1624 + difference 0 5) (sourceB1624 + difference 5 0) sourceC1624) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1637) := by
    have ha : (tripleCharges (sourceA1624 + difference 0 5) (sourceB1624 + difference 5 0) sourceC1624) = raw24004 := by
      apply Matrix.ext; unfold tripleCharges sourceA1624 sourceB1624 sourceC1624 difference raw24004; decide +kernel
    rw [ha]
    exact (canonical24004 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1624 + sourceB1624) sourceC1624) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1624 + sourceB1624) sourceC1624) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1624 sourceB1624 sourceC1624 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1624 sourceB1624 sourceC1624
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1624, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1625 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1625 + difference 0 0) (sourceB1625 + difference 0 0) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1625 + difference 0 0) (sourceB1625 + difference 0 0) sourceC1625) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1625 + difference 1 0) (sourceB1625 + difference 0 1) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1625 + difference 1 0) (sourceB1625 + difference 0 1) sourceC1625) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1625 + difference 2 0) (sourceB1625 + difference 0 2) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1625 + difference 2 0) (sourceB1625 + difference 0 2) sourceC1625) = raw23823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23823; decide +kernel
    rw [ha]
    exact (canonical23823 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1625 + difference 3 0) (sourceB1625 + difference 0 3) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1612) := by
    have ha : (tripleCharges (sourceA1625 + difference 3 0) (sourceB1625 + difference 0 3) sourceC1625) = raw24005 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw24005; decide +kernel
    rw [ha]
    exact (canonical24005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1625 + difference 4 0) (sourceB1625 + difference 0 4) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1610) := by
    have ha : (tripleCharges (sourceA1625 + difference 4 0) (sourceB1625 + difference 0 4) sourceC1625) = raw24006 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw24006; decide +kernel
    rw [ha]
    exact (canonical24006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1625 + difference 5 0) (sourceB1625 + difference 0 5) sourceC1625) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1623) := by
    have ha : (tripleCharges (sourceA1625 + difference 5 0) (sourceB1625 + difference 0 5) sourceC1625) = raw23972 := by
      apply Matrix.ext; unfold tripleCharges sourceA1625 sourceB1625 sourceC1625 difference raw23972; decide +kernel
    rw [ha]
    exact (canonical23972 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1625 + sourceB1625) sourceC1625) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1625 + sourceB1625) sourceC1625) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1625 sourceB1625 sourceC1625 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1625 sourceB1625 sourceC1625
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1625, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1626 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 0) (sourceB1626 + difference 0 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 0) (sourceB1626 + difference 0 1) sourceC1626) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 1) (sourceB1626 + difference 1 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 1) (sourceB1626 + difference 1 1) sourceC1626) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 2) (sourceB1626 + difference 2 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 2) (sourceB1626 + difference 2 1) sourceC1626) = raw24007 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw24007; decide +kernel
    rw [ha]
    exact (canonical24007 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 3) (sourceB1626 + difference 3 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 3) (sourceB1626 + difference 3 1) sourceC1626) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 4) (sourceB1626 + difference 4 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 4) (sourceB1626 + difference 4 1) sourceC1626) = raw24008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw24008; decide +kernel
    rw [ha]
    exact (canonical24008 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1626 + difference 1 5) (sourceB1626 + difference 5 1) sourceC1626) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1626 + difference 1 5) (sourceB1626 + difference 5 1) sourceC1626) = raw24009 := by
      apply Matrix.ext; unfold tripleCharges sourceA1626 sourceB1626 sourceC1626 difference raw24009; decide +kernel
    rw [ha]
    exact (canonical24009 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1626 + sourceB1626) sourceC1626) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1626 + sourceB1626) sourceC1626) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1626 sourceB1626 sourceC1626 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1626 sourceB1626 sourceC1626
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1626, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1627 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1627 + difference 0 4) (sourceB1627 + difference 4 0) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1627 + difference 0 4) (sourceB1627 + difference 4 0) sourceC1627) = raw24003 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24003; decide +kernel
    rw [ha]
    exact (canonical24003 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1627 + difference 1 4) (sourceB1627 + difference 4 1) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1627 + difference 1 4) (sourceB1627 + difference 4 1) sourceC1627) = raw24008 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24008; decide +kernel
    rw [ha]
    exact (canonical24008 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1627 + difference 2 4) (sourceB1627 + difference 4 2) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1627 + difference 2 4) (sourceB1627 + difference 4 2) sourceC1627) = raw24010 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24010; decide +kernel
    rw [ha]
    exact (canonical24010 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1627 + difference 3 4) (sourceB1627 + difference 4 3) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1627 + difference 3 4) (sourceB1627 + difference 4 3) sourceC1627) = raw24011 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw24011; decide +kernel
    rw [ha]
    exact (canonical24011 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1627 + difference 4 4) (sourceB1627 + difference 4 4) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3296) := by
    have ha : (tripleCharges (sourceA1627 + difference 4 4) (sourceB1627 + difference 4 4) sourceC1627) = raw23981 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw23981; decide +kernel
    rw [ha]
    exact (canonical23981 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1627 + difference 5 4) (sourceB1627 + difference 4 5) sourceC1627) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1627 + difference 5 4) (sourceB1627 + difference 4 5) sourceC1627) = raw23980 := by
      apply Matrix.ext; unfold tripleCharges sourceA1627 sourceB1627 sourceC1627 difference raw23980; decide +kernel
    rw [ha]
    exact (canonical23980 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1627 + sourceB1627) sourceC1627) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1627 + sourceB1627) sourceC1627) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1627 sourceB1627 sourceC1627 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1627 sourceB1627 sourceC1627
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1627, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1628 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1628 + difference 0 1) (sourceB1628 + difference 1 0) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2479) := by
    have ha : (tripleCharges (sourceA1628 + difference 0 1) (sourceB1628 + difference 1 0) sourceC1628) = raw11653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw11653; decide +kernel
    rw [ha]
    exact (canonical11653 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1628 + difference 1 1) (sourceB1628 + difference 1 1) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1628 + difference 1 1) (sourceB1628 + difference 1 1) sourceC1628) = raw11645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw11645; decide +kernel
    rw [ha]
    exact (canonical11645 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1628 + difference 2 1) (sourceB1628 + difference 1 2) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1628 + difference 2 1) (sourceB1628 + difference 1 2) sourceC1628) = raw24012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24012; decide +kernel
    rw [ha]
    exact (canonical24012 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1628 + difference 3 1) (sourceB1628 + difference 1 3) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1628 + difference 3 1) (sourceB1628 + difference 1 3) sourceC1628) = raw24013 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24013; decide +kernel
    rw [ha]
    exact (canonical24013 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1628 + difference 4 1) (sourceB1628 + difference 1 4) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1113) := by
    have ha : (tripleCharges (sourceA1628 + difference 4 1) (sourceB1628 + difference 1 4) sourceC1628) = raw24014 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24014; decide +kernel
    rw [ha]
    exact (canonical24014 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1628 + difference 5 1) (sourceB1628 + difference 1 5) sourceC1628) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1111) := by
    have ha : (tripleCharges (sourceA1628 + difference 5 1) (sourceB1628 + difference 1 5) sourceC1628) = raw24015 := by
      apply Matrix.ext; unfold tripleCharges sourceA1628 sourceB1628 sourceC1628 difference raw24015; decide +kernel
    rw [ha]
    exact (canonical24015 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1628 + sourceB1628) sourceC1628) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1628 + sourceB1628) sourceC1628) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA1628 sourceB1628 sourceC1628 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1628 sourceB1628 sourceC1628
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1628, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1629 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 0) (sourceB1629 + difference 0 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 623) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 0) (sourceB1629 + difference 0 2) sourceC1629) = raw24016 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24016; decide +kernel
    rw [ha]
    exact (canonical24016 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 1) (sourceB1629 + difference 1 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1126) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 1) (sourceB1629 + difference 1 2) sourceC1629) = raw24012 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24012; decide +kernel
    rw [ha]
    exact (canonical24012 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 2) (sourceB1629 + difference 2 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1212) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 2) (sourceB1629 + difference 2 2) sourceC1629) = raw11645 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw11645; decide +kernel
    rw [ha]
    exact (canonical11645 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 3) (sourceB1629 + difference 3 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 3) (sourceB1629 + difference 3 2) sourceC1629) = raw24017 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24017; decide +kernel
    rw [ha]
    exact (canonical24017 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 4) (sourceB1629 + difference 4 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1236) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 4) (sourceB1629 + difference 4 2) sourceC1629) = raw24018 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw24018; decide +kernel
    rw [ha]
    exact (canonical24018 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1629 + difference 2 5) (sourceB1629 + difference 5 2) sourceC1629) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1233) := by
    have ha : (tripleCharges (sourceA1629 + difference 2 5) (sourceB1629 + difference 5 2) sourceC1629) = raw11642 := by
      apply Matrix.ext; unfold tripleCharges sourceA1629 sourceB1629 sourceC1629 difference raw11642; decide +kernel
    rw [ha]
    exact (canonical11642 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1629 + sourceB1629) sourceC1629) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1629 + sourceB1629) sourceC1629) = raw11640 := by
      apply Matrix.ext; unfold doubleCharges sourceA1629 sourceB1629 sourceC1629 raw11640; decide +kernel
    rw [ha]
    exact (canonical11640 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1629 sourceB1629 sourceC1629
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1629, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1630 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 0) (sourceB1630 + difference 0 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 629) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 0) (sourceB1630 + difference 0 1) sourceC1630) = raw24019 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24019; decide +kernel
    rw [ha]
    exact (canonical24019 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 1) (sourceB1630 + difference 1 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 1) (sourceB1630 + difference 1 1) sourceC1630) = raw24020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24020; decide +kernel
    rw [ha]
    exact (canonical24020 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 2) (sourceB1630 + difference 2 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 2) (sourceB1630 + difference 2 1) sourceC1630) = raw24021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24021; decide +kernel
    rw [ha]
    exact (canonical24021 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 3) (sourceB1630 + difference 3 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 3) (sourceB1630 + difference 3 1) sourceC1630) = raw24022 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24022; decide +kernel
    rw [ha]
    exact (canonical24022 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 4) (sourceB1630 + difference 4 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 4) (sourceB1630 + difference 4 1) sourceC1630) = raw24023 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw24023; decide +kernel
    rw [ha]
    exact (canonical24023 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1630 + difference 1 5) (sourceB1630 + difference 5 1) sourceC1630) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1630 + difference 1 5) (sourceB1630 + difference 5 1) sourceC1630) = raw13763 := by
      apply Matrix.ext; unfold tripleCharges sourceA1630 sourceB1630 sourceC1630 difference raw13763; decide +kernel
    rw [ha]
    exact (canonical13763 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1630 + sourceB1630) sourceC1630) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1630 + sourceB1630) sourceC1630) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA1630 sourceB1630 sourceC1630 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1630 sourceB1630 sourceC1630
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1630, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1376 : Integer.Sparse.reindex keyMap MixedData.row1376 = numericRow1376 := by decide +kernel

theorem numericCheck1376 (x : Master → ℝ) : Integer.Sparse.eval numericRow1376 x =
    (1 : ℝ) * reducedSource1376 x := by
  norm_num [numericRow1376, reducedSource1376, Integer.Sparse.eval, Sparse.eval, nodeValue1598, nodeValue1603, nodeValue1605, nodeValue1623, nodeValue1728, nodeValue3294, nodeValue4069]

theorem reindexCheck1377 : Integer.Sparse.reindex keyMap MixedData.row1377 = numericRow1377 := by decide +kernel

theorem numericCheck1377 (x : Master → ℝ) : Integer.Sparse.eval numericRow1377 x =
    (1 : ℝ) * reducedSource1377 x := by
  norm_num [numericRow1377, reducedSource1377, Integer.Sparse.eval, Sparse.eval, nodeValue1728, nodeValue3294, nodeValue3305, nodeValue3306, nodeValue3309, nodeValue4069]

theorem reindexCheck1378 : Integer.Sparse.reindex keyMap MixedData.row1378 = numericRow1378 := by decide +kernel

theorem numericCheck1378 (x : Master → ℝ) : Integer.Sparse.eval numericRow1378 x =
    (1 : ℝ) * reducedSource1378 x := by
  norm_num [numericRow1378, reducedSource1378, Integer.Sparse.eval, Sparse.eval, nodeValue1623, nodeValue3246, nodeValue3282, nodeValue3294, nodeValue3296, nodeValue3299, nodeValue4069]

theorem reindexCheck1379 : Integer.Sparse.reindex keyMap MixedData.row1379 = numericRow1379 := by decide +kernel

theorem numericCheck1379 (x : Master → ℝ) : Integer.Sparse.eval numericRow1379 x =
    (1 : ℝ) * reducedSource1379 x := by
  norm_num [numericRow1379, reducedSource1379, Integer.Sparse.eval, Sparse.eval, nodeValue1724, nodeValue3290, nodeValue3293, nodeValue3294, nodeValue3299, nodeValue3309, nodeValue4069]

theorem reindexCheck1380 : Integer.Sparse.reindex keyMap MixedData.row1380 = numericRow1380 := by decide +kernel

theorem numericCheck1380 (x : Master → ℝ) : Integer.Sparse.eval numericRow1380 x =
    (1 : ℝ) * reducedSource1380 x := by
  norm_num [numericRow1380, reducedSource1380, Integer.Sparse.eval, Sparse.eval, nodeValue1605, nodeValue3240, nodeValue3278, nodeValue3287, nodeValue3293, nodeValue3294, nodeValue4069]

theorem reindexCheck1381 : Integer.Sparse.reindex keyMap MixedData.row1381 = numericRow1381 := by decide +kernel

theorem numericCheck1381 (x : Master → ℝ) : Integer.Sparse.eval numericRow1381 x =
    (1 : ℝ) * reducedSource1381 x := by
  norm_num [numericRow1381, reducedSource1381, Integer.Sparse.eval, Sparse.eval, nodeValue1645, nodeValue3022, nodeValue3285, nodeValue3294, nodeValue3296, nodeValue3305, nodeValue4069]

theorem reindexCheck1382 : Integer.Sparse.reindex keyMap MixedData.row1382 = numericRow1382 := by decide +kernel

theorem numericCheck1382 (x : Master → ℝ) : Integer.Sparse.eval numericRow1382 x =
    (1 : ℝ) * reducedSource1382 x := by
  norm_num [numericRow1382, reducedSource1382, Integer.Sparse.eval, Sparse.eval, nodeValue1257, nodeValue2565, nodeValue2629, nodeValue2672, nodeValue2748, nodeValue2760, nodeValue4088]

theorem reindexCheck1383 : Integer.Sparse.reindex keyMap MixedData.row1383 = numericRow1383 := by decide +kernel

theorem numericCheck1383 (x : Master → ℝ) : Integer.Sparse.eval numericRow1383 x =
    (1 : ℝ) * reducedSource1383 x := by
  norm_num [numericRow1383, reducedSource1383, Integer.Sparse.eval, Sparse.eval, nodeValue1130, nodeValue1137, nodeValue1138, nodeValue1141, nodeValue1241, nodeValue2515, nodeValue4092]

theorem reindexCheck1384 : Integer.Sparse.reindex keyMap MixedData.row1384 = numericRow1384 := by decide +kernel

theorem numericCheck1384 (x : Master → ℝ) : Integer.Sparse.eval numericRow1384 x =
    (1 : ℝ) * reducedSource1384 x := by
  norm_num [numericRow1384, reducedSource1384, Integer.Sparse.eval, Sparse.eval, nodeValue638, nodeValue1156, nodeValue1236, nodeValue1261, nodeValue1291, nodeValue1294, nodeValue4092]

theorem reindexCheck1385 : Integer.Sparse.reindex keyMap MixedData.row1385 = numericRow1385 := by decide +kernel

theorem numericCheck1385 (x : Master → ℝ) : Integer.Sparse.eval numericRow1385 x =
    (1 : ℝ) * reducedSource1385 x := by
  norm_num [numericRow1385, reducedSource1385, Integer.Sparse.eval, Sparse.eval, nodeValue1635, nodeValue1637, nodeValue1640, nodeValue1645, nodeValue1707, nodeValue3296, nodeValue4069]

theorem reindexCheck1386 : Integer.Sparse.reindex keyMap MixedData.row1386 = numericRow1386 := by decide +kernel

theorem numericCheck1386 (x : Master → ℝ) : Integer.Sparse.eval numericRow1386 x =
    (1 : ℝ) * reducedSource1386 x := by
  norm_num [numericRow1386, reducedSource1386, Integer.Sparse.eval, Sparse.eval, nodeValue1607, nodeValue1610, nodeValue1612, nodeValue1623, nodeValue1739, nodeValue3296, nodeValue4069]

theorem reindexCheck1387 : Integer.Sparse.reindex keyMap MixedData.row1387 = numericRow1387 := by decide +kernel

theorem numericCheck1387 (x : Master → ℝ) : Integer.Sparse.eval numericRow1387 x =
    (1 : ℝ) * reducedSource1387 x := by
  norm_num [numericRow1387, reducedSource1387, Integer.Sparse.eval, Sparse.eval, nodeValue1739, nodeValue2737, nodeValue3296, nodeValue3305, nodeValue3308, nodeValue4069]

theorem reindexCheck1388 : Integer.Sparse.reindex keyMap MixedData.row1388 = numericRow1388 := by decide +kernel

theorem numericCheck1388 (x : Master → ℝ) : Integer.Sparse.eval numericRow1388 x =
    (1 : ℝ) * reducedSource1388 x := by
  norm_num [numericRow1388, reducedSource1388, Integer.Sparse.eval, Sparse.eval, nodeValue1707, nodeValue3288, nodeValue3296, nodeValue3299, nodeValue3308, nodeValue4069]

theorem reindexCheck1389 : Integer.Sparse.reindex keyMap MixedData.row1389 = numericRow1389 := by decide +kernel

theorem numericCheck1389 (x : Master → ℝ) : Integer.Sparse.eval numericRow1389 x =
    (1 : ℝ) * reducedSource1389 x := by
  norm_num [numericRow1389, reducedSource1389, Integer.Sparse.eval, Sparse.eval, nodeValue1111, nodeValue1113, nodeValue1126, nodeValue1212, nodeValue2479, nodeValue4092]

theorem reindexCheck1390 : Integer.Sparse.reindex keyMap MixedData.row1390 = numericRow1390 := by decide +kernel

theorem numericCheck1390 (x : Master → ℝ) : Integer.Sparse.eval numericRow1390 x =
    (1 : ℝ) * reducedSource1390 x := by
  norm_num [numericRow1390, reducedSource1390, Integer.Sparse.eval, Sparse.eval, nodeValue623, nodeValue1126, nodeValue1212, nodeValue1233, nodeValue1236, nodeValue4092]

theorem reindexCheck1391 : Integer.Sparse.reindex keyMap MixedData.row1391 = numericRow1391 := by decide +kernel

theorem numericCheck1391 (x : Master → ℝ) : Integer.Sparse.eval numericRow1391 x =
    (1 : ℝ) * reducedSource1391 x := by
  norm_num [numericRow1391, reducedSource1391, Integer.Sparse.eval, Sparse.eval, nodeValue629, nodeValue1135, nodeValue1216, nodeValue1235, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1376 (mixedVector B) = 0 := by
  have h1598 : mixedVector B (Sum.inr 1598) = Sparse.eval nodeValue1598 (mixedVector B) := by
    change mixedMoment B node1598 node1598Labels = _
    exact sound1598 B hB hF
  have h1603 : mixedVector B (Sum.inr 1603) = Sparse.eval nodeValue1603 (mixedVector B) := by
    change mixedMoment B node1603 node1603Labels = _
    exact sound1603 B hB hF
  have h1605 : mixedVector B (Sum.inr 1605) = Sparse.eval nodeValue1605 (mixedVector B) := by
    change mixedMoment B node1605 node1605Labels = _
    exact sound1605 B hB hF
  have h1623 : mixedVector B (Sum.inr 1623) = Sparse.eval nodeValue1623 (mixedVector B) := by
    change mixedMoment B node1623 node1623Labels = _
    exact sound1623 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1615, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1598, h1603, h1605, h1623, h1728, h3294, h4069, reducedSource1376] using sourceEq1615 B hB

theorem rowSound1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1376 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1376, numericCheck1376, reducedZero1376 B hB hF, mul_zero]

theorem reducedZero1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1377 (mixedVector B) = 0 := by
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h3309 : mixedVector B (Sum.inr 3309) = Sparse.eval nodeValue3309 (mixedVector B) := by
    change mixedMoment B node3309 node3309Labels = _
    exact sound3309 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1616, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1728, h3294, h3305, h3306, h3309, h4069, reducedSource1377] using sourceEq1616 B hB

theorem rowSound1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1377 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1377, numericCheck1377, reducedZero1377 B hB hF, mul_zero]

theorem reducedZero1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1378 (mixedVector B) = 0 := by
  have h1623 : mixedVector B (Sum.inr 1623) = Sparse.eval nodeValue1623 (mixedVector B) := by
    change mixedMoment B node1623 node1623Labels = _
    exact sound1623 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3282 : mixedVector B (Sum.inr 3282) = Sparse.eval nodeValue3282 (mixedVector B) := by
    change mixedMoment B node3282 node3282Labels = _
    exact sound3282 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1617, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1623, h3246, h3282, h3294, h3296, h3299, h4069, reducedSource1378] using sourceEq1617 B hB

theorem rowSound1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1378 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1378, numericCheck1378, reducedZero1378 B hB hF, mul_zero]

theorem reducedZero1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1379 (mixedVector B) = 0 := by
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3309 : mixedVector B (Sum.inr 3309) = Sparse.eval nodeValue3309 (mixedVector B) := by
    change mixedMoment B node3309 node3309Labels = _
    exact sound3309 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1618, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1724, h3290, h3293, h3294, h3299, h3309, h4069, reducedSource1379] using sourceEq1618 B hB

theorem rowSound1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1379 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1379, numericCheck1379, reducedZero1379 B hB hF, mul_zero]

theorem reducedZero1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1380 (mixedVector B) = 0 := by
  have h1605 : mixedVector B (Sum.inr 1605) = Sparse.eval nodeValue1605 (mixedVector B) := by
    change mixedMoment B node1605 node1605Labels = _
    exact sound1605 B hB hF
  have h3240 : mixedVector B (Sum.inr 3240) = Sparse.eval nodeValue3240 (mixedVector B) := by
    change mixedMoment B node3240 node3240Labels = _
    exact sound3240 B hB hF
  have h3278 : mixedVector B (Sum.inr 3278) = Sparse.eval nodeValue3278 (mixedVector B) := by
    change mixedMoment B node3278 node3278Labels = _
    exact sound3278 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1619, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1605, h3240, h3278, h3287, h3293, h3294, h4069, reducedSource1380] using sourceEq1619 B hB

theorem rowSound1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1380 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1380, numericCheck1380, reducedZero1380 B hB hF, mul_zero]

theorem reducedZero1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1381 (mixedVector B) = 0 := by
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h3022 : mixedVector B (Sum.inr 3022) = Sparse.eval nodeValue3022 (mixedVector B) := by
    change mixedMoment B node3022 node3022Labels = _
    exact sound3022 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1620, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1645, h3022, h3285, h3294, h3296, h3305, h4069, reducedSource1381] using sourceEq1620 B hB

theorem rowSound1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1381 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1381, numericCheck1381, reducedZero1381 B hB hF, mul_zero]

theorem reducedZero1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1382 (mixedVector B) = 0 := by
  have h1257 : mixedVector B (Sum.inr 1257) = Sparse.eval nodeValue1257 (mixedVector B) := by
    change mixedMoment B node1257 node1257Labels = _
    exact sound1257 B hB hF
  have h2565 : mixedVector B (Sum.inr 2565) = Sparse.eval nodeValue2565 (mixedVector B) := by
    change mixedMoment B node2565 node2565Labels = _
    exact sound2565 B hB hF
  have h2629 : mixedVector B (Sum.inr 2629) = Sparse.eval nodeValue2629 (mixedVector B) := by
    change mixedMoment B node2629 node2629Labels = _
    exact sound2629 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h2748 : mixedVector B (Sum.inr 2748) = Sparse.eval nodeValue2748 (mixedVector B) := by
    change mixedMoment B node2748 node2748Labels = _
    exact sound2748 B hB hF
  have h2760 : mixedVector B (Sum.inr 2760) = Sparse.eval nodeValue2760 (mixedVector B) := by
    change mixedMoment B node2760 node2760Labels = _
    exact sound2760 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1621, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1257, h2565, h2629, h2672, h2748, h2760, h4088, reducedSource1382] using sourceEq1621 B hB

theorem rowSound1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1382 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1382, numericCheck1382, reducedZero1382 B hB hF, mul_zero]

theorem reducedZero1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1383 (mixedVector B) = 0 := by
  have h1130 : mixedVector B (Sum.inr 1130) = Sparse.eval nodeValue1130 (mixedVector B) := by
    change mixedMoment B node1130 node1130Labels = _
    exact sound1130 B hB hF
  have h1137 : mixedVector B (Sum.inr 1137) = Sparse.eval nodeValue1137 (mixedVector B) := by
    change mixedMoment B node1137 node1137Labels = _
    exact sound1137 B hB hF
  have h1138 : mixedVector B (Sum.inr 1138) = Sparse.eval nodeValue1138 (mixedVector B) := by
    change mixedMoment B node1138 node1138Labels = _
    exact sound1138 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1241 : mixedVector B (Sum.inr 1241) = Sparse.eval nodeValue1241 (mixedVector B) := by
    change mixedMoment B node1241 node1241Labels = _
    exact sound1241 B hB hF
  have h2515 : mixedVector B (Sum.inr 2515) = Sparse.eval nodeValue2515 (mixedVector B) := by
    change mixedMoment B node2515 node2515Labels = _
    exact sound2515 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1622, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1130, h1137, h1138, h1141, h1241, h2515, h4092, reducedSource1383] using sourceEq1622 B hB

theorem rowSound1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1383 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1383, numericCheck1383, reducedZero1383 B hB hF, mul_zero]

theorem reducedZero1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1384 (mixedVector B) = 0 := by
  have h638 : mixedVector B (Sum.inr 638) = Sparse.eval nodeValue638 (mixedVector B) := by
    change mixedMoment B node638 node638Labels = _
    exact sound638 B hB hF
  have h1156 : mixedVector B (Sum.inr 1156) = Sparse.eval nodeValue1156 (mixedVector B) := by
    change mixedMoment B node1156 node1156Labels = _
    exact sound1156 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h1261 : mixedVector B (Sum.inr 1261) = Sparse.eval nodeValue1261 (mixedVector B) := by
    change mixedMoment B node1261 node1261Labels = _
    exact sound1261 B hB hF
  have h1291 : mixedVector B (Sum.inr 1291) = Sparse.eval nodeValue1291 (mixedVector B) := by
    change mixedMoment B node1291 node1291Labels = _
    exact sound1291 B hB hF
  have h1294 : mixedVector B (Sum.inr 1294) = Sparse.eval nodeValue1294 (mixedVector B) := by
    change mixedMoment B node1294 node1294Labels = _
    exact sound1294 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1623, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h638, h1156, h1236, h1261, h1291, h1294, h4092, reducedSource1384] using sourceEq1623 B hB

theorem rowSound1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1384 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1384, numericCheck1384, reducedZero1384 B hB hF, mul_zero]

theorem reducedZero1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1385 (mixedVector B) = 0 := by
  have h1635 : mixedVector B (Sum.inr 1635) = Sparse.eval nodeValue1635 (mixedVector B) := by
    change mixedMoment B node1635 node1635Labels = _
    exact sound1635 B hB hF
  have h1637 : mixedVector B (Sum.inr 1637) = Sparse.eval nodeValue1637 (mixedVector B) := by
    change mixedMoment B node1637 node1637Labels = _
    exact sound1637 B hB hF
  have h1640 : mixedVector B (Sum.inr 1640) = Sparse.eval nodeValue1640 (mixedVector B) := by
    change mixedMoment B node1640 node1640Labels = _
    exact sound1640 B hB hF
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1624, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1635, h1637, h1640, h1645, h1707, h3296, h4069, reducedSource1385] using sourceEq1624 B hB

theorem rowSound1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1385 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1385, numericCheck1385, reducedZero1385 B hB hF, mul_zero]

theorem reducedZero1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1386 (mixedVector B) = 0 := by
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1610 : mixedVector B (Sum.inr 1610) = Sparse.eval nodeValue1610 (mixedVector B) := by
    change mixedMoment B node1610 node1610Labels = _
    exact sound1610 B hB hF
  have h1612 : mixedVector B (Sum.inr 1612) = Sparse.eval nodeValue1612 (mixedVector B) := by
    change mixedMoment B node1612 node1612Labels = _
    exact sound1612 B hB hF
  have h1623 : mixedVector B (Sum.inr 1623) = Sparse.eval nodeValue1623 (mixedVector B) := by
    change mixedMoment B node1623 node1623Labels = _
    exact sound1623 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1625, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1607, h1610, h1612, h1623, h1739, h3296, h4069, reducedSource1386] using sourceEq1625 B hB

theorem rowSound1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1386 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1386, numericCheck1386, reducedZero1386 B hB hF, mul_zero]

theorem reducedZero1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1387 (mixedVector B) = 0 := by
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1626, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1739, h2737, h3296, h3305, h3308, h4069, reducedSource1387] using sourceEq1626 B hB

theorem rowSound1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1387 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1387, numericCheck1387, reducedZero1387 B hB hF, mul_zero]

theorem reducedZero1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1388 (mixedVector B) = 0 := by
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3296 : mixedVector B (Sum.inr 3296) = Sparse.eval nodeValue3296 (mixedVector B) := by
    change mixedMoment B node3296 node3296Labels = _
    exact sound3296 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1627, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1707, h3288, h3296, h3299, h3308, h4069, reducedSource1388] using sourceEq1627 B hB

theorem rowSound1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1388 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1388, numericCheck1388, reducedZero1388 B hB hF, mul_zero]

theorem reducedZero1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1389 (mixedVector B) = 0 := by
  have h1111 : mixedVector B (Sum.inr 1111) = Sparse.eval nodeValue1111 (mixedVector B) := by
    change mixedMoment B node1111 node1111Labels = _
    exact sound1111 B hB hF
  have h1113 : mixedVector B (Sum.inr 1113) = Sparse.eval nodeValue1113 (mixedVector B) := by
    change mixedMoment B node1113 node1113Labels = _
    exact sound1113 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h2479 : mixedVector B (Sum.inr 2479) = Sparse.eval nodeValue2479 (mixedVector B) := by
    change mixedMoment B node2479 node2479Labels = _
    exact sound2479 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1628, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1111, h1113, h1126, h1212, h2479, h4092, reducedSource1389] using sourceEq1628 B hB

theorem rowSound1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1389 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1389, numericCheck1389, reducedZero1389 B hB hF, mul_zero]

theorem reducedZero1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1390 (mixedVector B) = 0 := by
  have h623 : mixedVector B (Sum.inr 623) = Sparse.eval nodeValue623 (mixedVector B) := by
    change mixedMoment B node623 node623Labels = _
    exact sound623 B hB hF
  have h1126 : mixedVector B (Sum.inr 1126) = Sparse.eval nodeValue1126 (mixedVector B) := by
    change mixedMoment B node1126 node1126Labels = _
    exact sound1126 B hB hF
  have h1212 : mixedVector B (Sum.inr 1212) = Sparse.eval nodeValue1212 (mixedVector B) := by
    change mixedMoment B node1212 node1212Labels = _
    exact sound1212 B hB hF
  have h1233 : mixedVector B (Sum.inr 1233) = Sparse.eval nodeValue1233 (mixedVector B) := by
    change mixedMoment B node1233 node1233Labels = _
    exact sound1233 B hB hF
  have h1236 : mixedVector B (Sum.inr 1236) = Sparse.eval nodeValue1236 (mixedVector B) := by
    change mixedMoment B node1236 node1236Labels = _
    exact sound1236 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1629, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h623, h1126, h1212, h1233, h1236, h4092, reducedSource1390] using sourceEq1629 B hB

theorem rowSound1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1390 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1390, numericCheck1390, reducedZero1390 B hB hF, mul_zero]

theorem reducedZero1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1391 (mixedVector B) = 0 := by
  have h629 : mixedVector B (Sum.inr 629) = Sparse.eval nodeValue629 (mixedVector B) := by
    change mixedMoment B node629 node629Labels = _
    exact sound629 B hB hF
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1630, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h629, h1135, h1216, h1235, h4091, reducedSource1391] using sourceEq1630 B hB

theorem rowSound1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1391 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1391, numericCheck1391, reducedZero1391 B hB hF, mul_zero]

theorem sourceRowsAt1376 : MixedData.sourceRows (1376 : Fin 2425) =
    MixedData.row1376 := by decide +kernel

theorem sourceRowsAt1377 : MixedData.sourceRows (1377 : Fin 2425) =
    MixedData.row1377 := by decide +kernel

theorem sourceRowsAt1378 : MixedData.sourceRows (1378 : Fin 2425) =
    MixedData.row1378 := by decide +kernel

theorem sourceRowsAt1379 : MixedData.sourceRows (1379 : Fin 2425) =
    MixedData.row1379 := by decide +kernel

theorem sourceRowsAt1380 : MixedData.sourceRows (1380 : Fin 2425) =
    MixedData.row1380 := by decide +kernel

theorem sourceRowsAt1381 : MixedData.sourceRows (1381 : Fin 2425) =
    MixedData.row1381 := by decide +kernel

theorem sourceRowsAt1382 : MixedData.sourceRows (1382 : Fin 2425) =
    MixedData.row1382 := by decide +kernel

theorem sourceRowsAt1383 : MixedData.sourceRows (1383 : Fin 2425) =
    MixedData.row1383 := by decide +kernel

theorem sourceRowsAt1384 : MixedData.sourceRows (1384 : Fin 2425) =
    MixedData.row1384 := by decide +kernel

theorem sourceRowsAt1385 : MixedData.sourceRows (1385 : Fin 2425) =
    MixedData.row1385 := by decide +kernel

theorem sourceRowsAt1386 : MixedData.sourceRows (1386 : Fin 2425) =
    MixedData.row1386 := by decide +kernel

theorem sourceRowsAt1387 : MixedData.sourceRows (1387 : Fin 2425) =
    MixedData.row1387 := by decide +kernel

theorem sourceRowsAt1388 : MixedData.sourceRows (1388 : Fin 2425) =
    MixedData.row1388 := by decide +kernel

theorem sourceRowsAt1389 : MixedData.sourceRows (1389 : Fin 2425) =
    MixedData.row1389 := by decide +kernel

theorem sourceRowsAt1390 : MixedData.sourceRows (1390 : Fin 2425) =
    MixedData.row1390 := by decide +kernel

theorem sourceRowsAt1391 : MixedData.sourceRows (1391 : Fin 2425) =
    MixedData.row1391 := by decide +kernel

theorem chunkSound86_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 86) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1376 ∨ k.val = 1377 ∨ k.val = 1378 ∨ k.val = 1379 ∨ k.val = 1380 ∨ k.val = 1381 ∨ k.val = 1382 ∨ k.val = 1383 ∨ k.val = 1384 ∨ k.val = 1385 ∨ k.val = 1386 ∨ k.val = 1387 ∨ k.val = 1388 ∨ k.val = 1389 ∨ k.val = 1390 ∨ k.val = 1391 := by omega
  rcases heq with h1376 | h1377 | h1378 | h1379 | h1380 | h1381 | h1382 | h1383 | h1384 | h1385 | h1386 | h1387 | h1388 | h1389 | h1390 | h1391
  · have he : k = (1376 : Fin 2425) := Fin.ext h1376
    subst k
    rw [sourceRowsAt1376]
    exact rowSound1376 B hB hF
  · have he : k = (1377 : Fin 2425) := Fin.ext h1377
    subst k
    rw [sourceRowsAt1377]
    exact rowSound1377 B hB hF
  · have he : k = (1378 : Fin 2425) := Fin.ext h1378
    subst k
    rw [sourceRowsAt1378]
    exact rowSound1378 B hB hF
  · have he : k = (1379 : Fin 2425) := Fin.ext h1379
    subst k
    rw [sourceRowsAt1379]
    exact rowSound1379 B hB hF
  · have he : k = (1380 : Fin 2425) := Fin.ext h1380
    subst k
    rw [sourceRowsAt1380]
    exact rowSound1380 B hB hF
  · have he : k = (1381 : Fin 2425) := Fin.ext h1381
    subst k
    rw [sourceRowsAt1381]
    exact rowSound1381 B hB hF
  · have he : k = (1382 : Fin 2425) := Fin.ext h1382
    subst k
    rw [sourceRowsAt1382]
    exact rowSound1382 B hB hF
  · have he : k = (1383 : Fin 2425) := Fin.ext h1383
    subst k
    rw [sourceRowsAt1383]
    exact rowSound1383 B hB hF
  · have he : k = (1384 : Fin 2425) := Fin.ext h1384
    subst k
    rw [sourceRowsAt1384]
    exact rowSound1384 B hB hF
  · have he : k = (1385 : Fin 2425) := Fin.ext h1385
    subst k
    rw [sourceRowsAt1385]
    exact rowSound1385 B hB hF
  · have he : k = (1386 : Fin 2425) := Fin.ext h1386
    subst k
    rw [sourceRowsAt1386]
    exact rowSound1386 B hB hF
  · have he : k = (1387 : Fin 2425) := Fin.ext h1387
    subst k
    rw [sourceRowsAt1387]
    exact rowSound1387 B hB hF
  · have he : k = (1388 : Fin 2425) := Fin.ext h1388
    subst k
    rw [sourceRowsAt1388]
    exact rowSound1388 B hB hF
  · have he : k = (1389 : Fin 2425) := Fin.ext h1389
    subst k
    rw [sourceRowsAt1389]
    exact rowSound1389 B hB hF
  · have he : k = (1390 : Fin 2425) := Fin.ext h1390
    subst k
    rw [sourceRowsAt1390]
    exact rowSound1390 B hB hF
  · have he : k = (1391 : Fin 2425) := Fin.ext h1391
    subst k
    rw [sourceRowsAt1391]
    exact rowSound1391 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound86_e_oai
