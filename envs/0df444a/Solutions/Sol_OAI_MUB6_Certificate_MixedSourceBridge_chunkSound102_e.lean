-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:33:26.955268+00:00
-- url     : https://prove2.me/submissions/d38c4eaa-b5a7-4af6-ba89-baf18cf28dd3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E093
import Definitions.Def_OAIQ106E100
import Definitions.Def_OAIQ106E194
import Definitions.Def_OAIQ106E102
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical135
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical17313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17313 raw17313Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17313 raw17313Labels = mixedMoment B raw17313step0 raw17313step0Labels := by
      have hz : ∀ j, raw17313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17313step0 = (fun i j => raw17313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17313step0 raw17313; decide +kernel
      have hl : raw17313step0Labels = raw17313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17313 raw17313Labels permutation434 hz
    mixedMoment B raw17313step0 raw17313step0Labels = mixedMoment B raw17313step1 raw17313step1Labels := by
      have ha : raw17313step1 = (fun i j => raw17313step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17313step1 raw17313step0; decide +kernel
      have hl : raw17313step1Labels = raw17313step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17313step0 raw17313step0Labels permutation140 permutation0
    mixedMoment B raw17313step1 raw17313step1Labels = mixedMoment B raw17313step2 raw17313step2Labels := by
      have ha : raw17313step2 = -raw17313step1 := by apply Matrix.ext; change ∀ i j, raw17313step2 i j = -(raw17313step1 i j); unfold raw17313step2 raw17313step1; decide +kernel
      have hl : raw17313step2Labels = raw17313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical24553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24553 raw24553Labels = mixedMoment B node2556 node2556Labels := by
  calc
    _ = mixedMoment B node2556 node2556Labels := by rfl

theorem canonical24557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24557 raw24557Labels = mixedMoment B node1150 node1150Labels := by
  calc
    _ = mixedMoment B node1150 node1150Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical213
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical27318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27318 raw27318Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw27318 raw27318Labels = mixedMoment B raw27318step0 raw27318step0Labels := by
      have hz : ∀ j, raw27318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27318step0 = (fun i j => raw27318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27318step0 raw27318; decide +kernel
      have hl : raw27318step0Labels = raw27318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27318 raw27318Labels permutation434 hz
    mixedMoment B raw27318step0 raw27318step0Labels = mixedMoment B raw27318step1 raw27318step1Labels := by
      have hz : ∀ j, raw27318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27318step1 = (fun i j => raw27318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27318step1 raw27318step0; decide +kernel
      have hl : raw27318step1Labels = raw27318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27318step0 raw27318step0Labels permutation80 hz
    mixedMoment B raw27318step1 raw27318step1Labels = mixedMoment B raw27318step2 raw27318step2Labels := by
      have ha : raw27318step2 = (fun i j => raw27318step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27318step2 raw27318step1; decide +kernel
      have hl : raw27318step2Labels = raw27318step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27318step1 raw27318step1Labels permutation9 permutation4
    mixedMoment B raw27318step2 raw27318step2Labels = mixedMoment B raw27318step3 raw27318step3Labels := by
      have ha : raw27318step3 = -raw27318step2 := by apply Matrix.ext; change ∀ i j, raw27318step3 i j = -(raw27318step2 i j); unfold raw27318step3 raw27318step2; decide +kernel
      have hl : raw27318step3Labels = raw27318step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2230 node2230Labels := by rfl

theorem canonical27319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27319 raw27319Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27319 raw27319Labels = mixedMoment B raw27319step0 raw27319step0Labels := by
      have hz : ∀ j, raw27319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27319step0 = (fun i j => raw27319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27319step0 raw27319; decide +kernel
      have hl : raw27319step0Labels = raw27319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319 raw27319Labels permutation434 hz
    mixedMoment B raw27319step0 raw27319step0Labels = mixedMoment B raw27319step1 raw27319step1Labels := by
      have hz : ∀ j, raw27319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27319step1 = (fun i j => raw27319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27319step1 raw27319step0; decide +kernel
      have hl : raw27319step1Labels = raw27319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319step0 raw27319step0Labels permutation80 hz
    mixedMoment B raw27319step1 raw27319step1Labels = mixedMoment B raw27319step2 raw27319step2Labels := by
      have ha : raw27319step2 = (fun i j => raw27319step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27319step2 raw27319step1; decide +kernel
      have hl : raw27319step2Labels = raw27319step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27319step1 raw27319step1Labels permutation31 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

theorem canonical27359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27359 raw27359Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27359 raw27359Labels = mixedMoment B raw27359step0 raw27359step0Labels := by
      have hz : ∀ j, raw27359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27359step0 = (fun i j => raw27359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27359step0 raw27359; decide +kernel
      have hl : raw27359step0Labels = raw27359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27359 raw27359Labels permutation346 hz
    mixedMoment B raw27359step0 raw27359step0Labels = mixedMoment B raw27359step1 raw27359step1Labels := by
      have ha : raw27359step1 = (fun i j => raw27359step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27359step1 raw27359step0; decide +kernel
      have hl : raw27359step1Labels = raw27359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27359step0 raw27359step0Labels permutation151 permutation2
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27368 raw27368Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw27368 raw27368Labels = mixedMoment B raw27368step0 raw27368step0Labels := by
      have hz : ∀ j, raw27368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27368step0 = (fun i j => raw27368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27368step0 raw27368; decide +kernel
      have hl : raw27368step0Labels = raw27368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27368 raw27368Labels permutation346 hz
    mixedMoment B raw27368step0 raw27368step0Labels = mixedMoment B raw27368step1 raw27368step1Labels := by
      have ha : raw27368step1 = (fun i j => raw27368step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27368step1 raw27368step0; decide +kernel
      have hl : raw27368step1Labels = raw27368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27368step0 raw27368step0Labels permutation34 permutation4
    mixedMoment B raw27368step1 raw27368step1Labels = mixedMoment B raw27368step2 raw27368step2Labels := by
      have ha : raw27368step2 = -raw27368step1 := by apply Matrix.ext; change ∀ i j, raw27368step2 i j = -(raw27368step1 i j); unfold raw27368step2 raw27368step1; decide +kernel
      have hl : raw27368step2Labels = raw27368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2203 node2203Labels := by rfl

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

theorem canonical27446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27446 raw27446Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27446 raw27446Labels = mixedMoment B raw27446step0 raw27446step0Labels := by
      have hz : ∀ j, raw27446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27446step0 = (fun i j => raw27446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27446step0 raw27446; decide +kernel
      have hl : raw27446step0Labels = raw27446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27446 raw27446Labels permutation346 hz
    mixedMoment B raw27446step0 raw27446step0Labels = mixedMoment B raw27446step1 raw27446step1Labels := by
      have ha : raw27446step1 = (fun i j => raw27446step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27446step1 raw27446step0; decide +kernel
      have hl : raw27446step1Labels = raw27446step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27446step0 raw27446step0Labels permutation34 permutation4
    mixedMoment B raw27446step1 raw27446step1Labels = mixedMoment B raw27446step2 raw27446step2Labels := by
      have ha : raw27446step2 = -raw27446step1 := by apply Matrix.ext; change ∀ i j, raw27446step2 i j = -(raw27446step1 i j); unfold raw27446step2 raw27446step1; decide +kernel
      have hl : raw27446step2Labels = raw27446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical27471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27471 raw27471Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw27471 raw27471Labels = mixedMoment B raw27471step0 raw27471step0Labels := by
      have hz : ∀ j, raw27471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27471step0 = (fun i j => raw27471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27471step0 raw27471; decide +kernel
      have hl : raw27471step0Labels = raw27471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27471 raw27471Labels permutation434 hz
    mixedMoment B raw27471step0 raw27471step0Labels = mixedMoment B raw27471step1 raw27471step1Labels := by
      have ha : raw27471step1 = (fun i j => raw27471step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27471step1 raw27471step0; decide +kernel
      have hl : raw27471step1Labels = raw27471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27471step0 raw27471step0Labels permutation34 permutation2
    _ = mixedMoment B node1337 node1337Labels := by rfl

theorem canonical27472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27472 raw27472Labels = mixedMoment B node2442 node2442Labels := by
  calc
    mixedMoment B raw27472 raw27472Labels = mixedMoment B raw27472step0 raw27472step0Labels := by
      have hz : ∀ j, raw27472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27472step0 = (fun i j => raw27472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27472step0 raw27472; decide +kernel
      have hl : raw27472step0Labels = raw27472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27472 raw27472Labels permutation434 hz
    mixedMoment B raw27472step0 raw27472step0Labels = mixedMoment B raw27472step1 raw27472step1Labels := by
      have ha : raw27472step1 = (fun i j => raw27472step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27472step1 raw27472step0; decide +kernel
      have hl : raw27472step1Labels = raw27472step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27472step0 raw27472step0Labels permutation145 permutation2
    mixedMoment B raw27472step1 raw27472step1Labels = mixedMoment B raw27472step2 raw27472step2Labels := by
      have ha : raw27472step2 = -raw27472step1 := by apply Matrix.ext; change ∀ i j, raw27472step2 i j = -(raw27472step1 i j); unfold raw27472step2 raw27472step1; decide +kernel
      have hl : raw27472step2Labels = raw27472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2442 node2442Labels := by rfl

theorem canonical27473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27473 raw27473Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw27473 raw27473Labels = mixedMoment B raw27473step0 raw27473step0Labels := by
      have hz : ∀ j, raw27473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27473step0 = (fun i j => raw27473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27473step0 raw27473; decide +kernel
      have hl : raw27473step0Labels = raw27473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27473 raw27473Labels permutation434 hz
    mixedMoment B raw27473step0 raw27473step0Labels = mixedMoment B raw27473step1 raw27473step1Labels := by
      have ha : raw27473step1 = (fun i j => raw27473step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27473step1 raw27473step0; decide +kernel
      have hl : raw27473step1Labels = raw27473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27473step0 raw27473step0Labels permutation151 permutation2
    mixedMoment B raw27473step1 raw27473step1Labels = mixedMoment B raw27473step2 raw27473step2Labels := by
      have ha : raw27473step2 = -raw27473step1 := by apply Matrix.ext; change ∀ i j, raw27473step2 i j = -(raw27473step1 i j); unfold raw27473step2 raw27473step1; decide +kernel
      have hl : raw27473step2Labels = raw27473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical27474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27474 raw27474Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw27474 raw27474Labels = mixedMoment B raw27474step0 raw27474step0Labels := by
      have ha : raw27474step0 = (fun i j => raw27474 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27474step0 raw27474; decide +kernel
      have hl : raw27474step0Labels = raw27474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27474 raw27474Labels permutation646 permutation2
    mixedMoment B raw27474step0 raw27474step0Labels = mixedMoment B raw27474step1 raw27474step1Labels := by
      have ha : raw27474step1 = -raw27474step0 := by apply Matrix.ext; change ∀ i j, raw27474step1 i j = -(raw27474step0 i j); unfold raw27474step1 raw27474step0; decide +kernel
      have hl : raw27474step1Labels = raw27474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2437 node2437Labels := by rfl

theorem canonical27475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27475 raw27475Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27475 raw27475Labels = mixedMoment B raw27475step0 raw27475step0Labels := by
      have hz : ∀ j, raw27475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27475step0 = (fun i j => raw27475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27475step0 raw27475; decide +kernel
      have hl : raw27475step0Labels = raw27475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27475 raw27475Labels permutation434 hz
    mixedMoment B raw27475step0 raw27475step0Labels = mixedMoment B raw27475step1 raw27475step1Labels := by
      have ha : raw27475step1 = (fun i j => raw27475step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27475step1 raw27475step0; decide +kernel
      have hl : raw27475step1Labels = raw27475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27475step0 raw27475step0Labels permutation145 permutation2
    mixedMoment B raw27475step1 raw27475step1Labels = mixedMoment B raw27475step2 raw27475step2Labels := by
      have ha : raw27475step2 = -raw27475step1 := by apply Matrix.ext; change ∀ i j, raw27475step2 i j = -(raw27475step1 i j); unfold raw27475step2 raw27475step1; decide +kernel
      have hl : raw27475step2Labels = raw27475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical27476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27476 raw27476Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw27476 raw27476Labels = mixedMoment B raw27476step0 raw27476step0Labels := by
      have hz : ∀ j, raw27476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27476step0 = (fun i j => raw27476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27476step0 raw27476; decide +kernel
      have hl : raw27476step0Labels = raw27476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27476 raw27476Labels permutation434 hz
    mixedMoment B raw27476step0 raw27476step0Labels = mixedMoment B raw27476step1 raw27476step1Labels := by
      have ha : raw27476step1 = (fun i j => raw27476step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27476step1 raw27476step0; decide +kernel
      have hl : raw27476step1Labels = raw27476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27476step0 raw27476step0Labels permutation34 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical27477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27477 raw27477Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw27477 raw27477Labels = mixedMoment B raw27477step0 raw27477step0Labels := by
      have hz : ∀ j, raw27477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27477step0 = (fun i j => raw27477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27477step0 raw27477; decide +kernel
      have hl : raw27477step0Labels = raw27477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27477 raw27477Labels permutation434 hz
    mixedMoment B raw27477step0 raw27477step0Labels = mixedMoment B raw27477step1 raw27477step1Labels := by
      have ha : raw27477step1 = (fun i j => raw27477step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27477step1 raw27477step0; decide +kernel
      have hl : raw27477step1Labels = raw27477step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27477step0 raw27477step0Labels permutation39 permutation4
    mixedMoment B raw27477step1 raw27477step1Labels = mixedMoment B raw27477step2 raw27477step2Labels := by
      have ha : raw27477step2 = -raw27477step1 := by apply Matrix.ext; change ∀ i j, raw27477step2 i j = -(raw27477step1 i j); unfold raw27477step2 raw27477step1; decide +kernel
      have hl : raw27477step2Labels = raw27477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical27478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27478 raw27478Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw27478 raw27478Labels = mixedMoment B raw27478step0 raw27478step0Labels := by
      have hz : ∀ j, raw27478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27478step0 = (fun i j => raw27478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27478step0 raw27478; decide +kernel
      have hl : raw27478step0Labels = raw27478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27478 raw27478Labels permutation434 hz
    mixedMoment B raw27478step0 raw27478step0Labels = mixedMoment B raw27478step1 raw27478step1Labels := by
      have ha : raw27478step1 = (fun i j => raw27478step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27478step1 raw27478step0; decide +kernel
      have hl : raw27478step1Labels = raw27478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27478step0 raw27478step0Labels permutation143 permutation2
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical27479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27479 raw27479Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw27479 raw27479Labels = mixedMoment B raw27479step0 raw27479step0Labels := by
      have hz : ∀ j, raw27479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27479step0 = (fun i j => raw27479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27479step0 raw27479; decide +kernel
      have hl : raw27479step0Labels = raw27479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27479 raw27479Labels permutation434 hz
    mixedMoment B raw27479step0 raw27479step0Labels = mixedMoment B raw27479step1 raw27479step1Labels := by
      have ha : raw27479step1 = (fun i j => raw27479step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27479step1 raw27479step0; decide +kernel
      have hl : raw27479step1Labels = raw27479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27479step0 raw27479step0Labels permutation145 permutation2
    _ = mixedMoment B node3385 node3385Labels := by rfl

theorem canonical27480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27480 raw27480Labels = mixedMoment B node3443 node3443Labels := by
  calc
    mixedMoment B raw27480 raw27480Labels = mixedMoment B raw27480step0 raw27480step0Labels := by
      have ha : raw27480step0 = (fun i j => raw27480 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27480step0 raw27480; decide +kernel
      have hl : raw27480step0Labels = raw27480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27480 raw27480Labels permutation164 permutation2
    mixedMoment B raw27480step0 raw27480step0Labels = mixedMoment B raw27480step1 raw27480step1Labels := by
      have ha : raw27480step1 = -raw27480step0 := by apply Matrix.ext; change ∀ i j, raw27480step1 i j = -(raw27480step0 i j); unfold raw27480step1 raw27480step0; decide +kernel
      have hl : raw27480step1Labels = raw27480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3443 node3443Labels := by rfl

theorem canonical27481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27481 raw27481Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27481 raw27481Labels = mixedMoment B raw27481step0 raw27481step0Labels := by
      have hz : ∀ j, raw27481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27481step0 = (fun i j => raw27481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27481step0 raw27481; decide +kernel
      have hl : raw27481step0Labels = raw27481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27481 raw27481Labels permutation434 hz
    mixedMoment B raw27481step0 raw27481step0Labels = mixedMoment B raw27481step1 raw27481step1Labels := by
      have ha : raw27481step1 = (fun i j => raw27481step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27481step1 raw27481step0; decide +kernel
      have hl : raw27481step1Labels = raw27481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27481step0 raw27481step0Labels permutation34 permutation2
    mixedMoment B raw27481step1 raw27481step1Labels = mixedMoment B raw27481step2 raw27481step2Labels := by
      have ha : raw27481step2 = -raw27481step1 := by apply Matrix.ext; change ∀ i j, raw27481step2 i j = -(raw27481step1 i j); unfold raw27481step2 raw27481step1; decide +kernel
      have hl : raw27481step2Labels = raw27481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical27482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27482 raw27482Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw27482 raw27482Labels = mixedMoment B raw27482step0 raw27482step0Labels := by
      have hz : ∀ j, raw27482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27482step0 = (fun i j => raw27482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27482step0 raw27482; decide +kernel
      have hl : raw27482step0Labels = raw27482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27482 raw27482Labels permutation434 hz
    mixedMoment B raw27482step0 raw27482step0Labels = mixedMoment B raw27482step1 raw27482step1Labels := by
      have ha : raw27482step1 = (fun i j => raw27482step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27482step1 raw27482step0; decide +kernel
      have hl : raw27482step1Labels = raw27482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27482step0 raw27482step0Labels permutation145 permutation2
    _ = mixedMoment B node2047 node2047Labels := by rfl

theorem canonical27483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27483 raw27483Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw27483 raw27483Labels = mixedMoment B raw27483step0 raw27483step0Labels := by
      have hz : ∀ j, raw27483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27483step0 = (fun i j => raw27483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27483step0 raw27483; decide +kernel
      have hl : raw27483step0Labels = raw27483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27483 raw27483Labels permutation434 hz
    mixedMoment B raw27483step0 raw27483step0Labels = mixedMoment B raw27483step1 raw27483step1Labels := by
      have ha : raw27483step1 = (fun i j => raw27483step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27483step1 raw27483step0; decide +kernel
      have hl : raw27483step1Labels = raw27483step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27483step0 raw27483step0Labels permutation39 permutation4
    mixedMoment B raw27483step1 raw27483step1Labels = mixedMoment B raw27483step2 raw27483step2Labels := by
      have ha : raw27483step2 = -raw27483step1 := by apply Matrix.ext; change ∀ i j, raw27483step2 i j = -(raw27483step1 i j); unfold raw27483step2 raw27483step1; decide +kernel
      have hl : raw27483step2Labels = raw27483step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2049 node2049Labels := by rfl

theorem canonical27484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27484 raw27484Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw27484 raw27484Labels = mixedMoment B raw27484step0 raw27484step0Labels := by
      have ha : raw27484step0 = (fun i j => raw27484 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27484step0 raw27484; decide +kernel
      have hl : raw27484step0Labels = raw27484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27484 raw27484Labels permutation177 permutation4
    mixedMoment B raw27484step0 raw27484step0Labels = mixedMoment B raw27484step1 raw27484step1Labels := by
      have ha : raw27484step1 = -raw27484step0 := by apply Matrix.ext; change ∀ i j, raw27484step1 i j = -(raw27484step0 i j); unfold raw27484step1 raw27484step0; decide +kernel
      have hl : raw27484step1Labels = raw27484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1998 node1998Labels := by rfl

theorem canonical27485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27485 raw27485Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw27485 raw27485Labels = mixedMoment B raw27485step0 raw27485step0Labels := by
      have hz : ∀ j, raw27485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27485step0 = (fun i j => raw27485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27485step0 raw27485; decide +kernel
      have hl : raw27485step0Labels = raw27485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27485 raw27485Labels permutation434 hz
    mixedMoment B raw27485step0 raw27485step0Labels = mixedMoment B raw27485step1 raw27485step1Labels := by
      have ha : raw27485step1 = (fun i j => raw27485step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27485step1 raw27485step0; decide +kernel
      have hl : raw27485step1Labels = raw27485step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27485step0 raw27485step0Labels permutation39 permutation4
    mixedMoment B raw27485step1 raw27485step1Labels = mixedMoment B raw27485step2 raw27485step2Labels := by
      have ha : raw27485step2 = -raw27485step1 := by apply Matrix.ext; change ∀ i j, raw27485step2 i j = -(raw27485step1 i j); unfold raw27485step2 raw27485step1; decide +kernel
      have hl : raw27485step2Labels = raw27485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2004 node2004Labels := by rfl

theorem canonical27486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27486 raw27486Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw27486 raw27486Labels = mixedMoment B raw27486step0 raw27486step0Labels := by
      have hz : ∀ j, raw27486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27486step0 = (fun i j => raw27486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27486step0 raw27486; decide +kernel
      have hl : raw27486step0Labels = raw27486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27486 raw27486Labels permutation434 hz
    mixedMoment B raw27486step0 raw27486step0Labels = mixedMoment B raw27486step1 raw27486step1Labels := by
      have ha : raw27486step1 = (fun i j => raw27486step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27486step1 raw27486step0; decide +kernel
      have hl : raw27486step1Labels = raw27486step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27486step0 raw27486step0Labels permutation38 permutation4
    mixedMoment B raw27486step1 raw27486step1Labels = mixedMoment B raw27486step2 raw27486step2Labels := by
      have ha : raw27486step2 = -raw27486step1 := by apply Matrix.ext; change ∀ i j, raw27486step2 i j = -(raw27486step1 i j); unfold raw27486step2 raw27486step1; decide +kernel
      have hl : raw27486step2Labels = raw27486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2006 node2006Labels := by rfl

theorem canonical27490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27490 raw27490Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw27490 raw27490Labels = mixedMoment B raw27490step0 raw27490step0Labels := by
      have hz : ∀ j, raw27490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27490step0 = (fun i j => raw27490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27490step0 raw27490; decide +kernel
      have hl : raw27490step0Labels = raw27490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27490 raw27490Labels permutation434 hz
    mixedMoment B raw27490step0 raw27490step0Labels = mixedMoment B raw27490step1 raw27490step1Labels := by
      have ha : raw27490step1 = (fun i j => raw27490step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27490step1 raw27490step0; decide +kernel
      have hl : raw27490step1Labels = raw27490step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27490step0 raw27490step0Labels permutation151 permutation4
    _ = mixedMoment B node3353 node3353Labels := by rfl

theorem canonical27491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27491 raw27491Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw27491 raw27491Labels = mixedMoment B raw27491step0 raw27491step0Labels := by
      have hz : ∀ j, raw27491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27491step0 = (fun i j => raw27491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27491step0 raw27491; decide +kernel
      have hl : raw27491step0Labels = raw27491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27491 raw27491Labels permutation434 hz
    mixedMoment B raw27491step0 raw27491step0Labels = mixedMoment B raw27491step1 raw27491step1Labels := by
      have ha : raw27491step1 = (fun i j => raw27491step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27491step1 raw27491step0; decide +kernel
      have hl : raw27491step1Labels = raw27491step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27491step0 raw27491step0Labels permutation144 permutation2
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical27492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27492 raw27492Labels = mixedMoment B node3615 node3615Labels := by
  calc
    mixedMoment B raw27492 raw27492Labels = mixedMoment B raw27492step0 raw27492step0Labels := by
      have hz : ∀ j, raw27492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27492step0 = (fun i j => raw27492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27492step0 raw27492; decide +kernel
      have hl : raw27492step0Labels = raw27492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27492 raw27492Labels permutation434 hz
    mixedMoment B raw27492step0 raw27492step0Labels = mixedMoment B raw27492step1 raw27492step1Labels := by
      have hz : ∀ j, raw27492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27492step1 = (fun i j => raw27492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27492step1 raw27492step0; decide +kernel
      have hl : raw27492step1Labels = raw27492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27492step0 raw27492step0Labels permutation80 hz
    mixedMoment B raw27492step1 raw27492step1Labels = mixedMoment B raw27492step2 raw27492step2Labels := by
      have ha : raw27492step2 = (fun i j => raw27492step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27492step2 raw27492step1; decide +kernel
      have hl : raw27492step2Labels = raw27492step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27492step1 raw27492step1Labels permutation31 permutation2
    _ = mixedMoment B node3615 node3615Labels := by rfl

theorem canonical27493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27493 raw27493Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw27493 raw27493Labels = mixedMoment B raw27493step0 raw27493step0Labels := by
      have ha : raw27493step0 = (fun i j => raw27493 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27493step0 raw27493; decide +kernel
      have hl : raw27493step0Labels = raw27493Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27493 raw27493Labels permutation646 permutation2
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical27494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27494 raw27494Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27494 raw27494Labels = mixedMoment B raw27494step0 raw27494step0Labels := by
      have hz : ∀ j, raw27494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27494step0 = (fun i j => raw27494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27494step0 raw27494; decide +kernel
      have hl : raw27494step0Labels = raw27494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27494 raw27494Labels permutation434 hz
    mixedMoment B raw27494step0 raw27494step0Labels = mixedMoment B raw27494step1 raw27494step1Labels := by
      have ha : raw27494step1 = (fun i j => raw27494step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27494step1 raw27494step0; decide +kernel
      have hl : raw27494step1Labels = raw27494step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27494step0 raw27494step0Labels permutation149 permutation4
    _ = mixedMoment B node3468 node3468Labels := by rfl

theorem canonical27495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27495 raw27495Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw27495 raw27495Labels = mixedMoment B raw27495step0 raw27495step0Labels := by
      have hz : ∀ j, raw27495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27495step0 = (fun i j => raw27495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27495step0 raw27495; decide +kernel
      have hl : raw27495step0Labels = raw27495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27495 raw27495Labels permutation434 hz
    mixedMoment B raw27495step0 raw27495step0Labels = mixedMoment B raw27495step1 raw27495step1Labels := by
      have ha : raw27495step1 = (fun i j => raw27495step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27495step1 raw27495step0; decide +kernel
      have hl : raw27495step1Labels = raw27495step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27495step0 raw27495step0Labels permutation149 permutation4
    _ = mixedMoment B node3343 node3343Labels := by rfl

theorem canonical27496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27496 raw27496Labels = mixedMoment B node3339 node3339Labels := by
  calc
    mixedMoment B raw27496 raw27496Labels = mixedMoment B raw27496step0 raw27496step0Labels := by
      have ha : raw27496step0 = (fun i j => raw27496 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27496step0 raw27496; decide +kernel
      have hl : raw27496step0Labels = raw27496Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27496 raw27496Labels permutation674 permutation4
    _ = mixedMoment B node3339 node3339Labels := by rfl

theorem canonical27497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27497 raw27497Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw27497 raw27497Labels = mixedMoment B raw27497step0 raw27497step0Labels := by
      have hz : ∀ j, raw27497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27497step0 = (fun i j => raw27497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27497step0 raw27497; decide +kernel
      have hl : raw27497step0Labels = raw27497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27497 raw27497Labels permutation434 hz
    mixedMoment B raw27497step0 raw27497step0Labels = mixedMoment B raw27497step1 raw27497step1Labels := by
      have ha : raw27497step1 = (fun i j => raw27497step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27497step1 raw27497step0; decide +kernel
      have hl : raw27497step1Labels = raw27497step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27497step0 raw27497step0Labels permutation151 permutation2
    mixedMoment B raw27497step1 raw27497step1Labels = mixedMoment B raw27497step2 raw27497step2Labels := by
      have ha : raw27497step2 = -raw27497step1 := by apply Matrix.ext; change ∀ i j, raw27497step2 i j = -(raw27497step1 i j); unfold raw27497step2 raw27497step1; decide +kernel
      have hl : raw27497step2Labels = raw27497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2121 node2121Labels := by rfl

theorem canonical27498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27498 raw27498Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw27498 raw27498Labels = mixedMoment B raw27498step0 raw27498step0Labels := by
      have hz : ∀ j, raw27498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27498step0 = (fun i j => raw27498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27498step0 raw27498; decide +kernel
      have hl : raw27498step0Labels = raw27498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27498 raw27498Labels permutation434 hz
    mixedMoment B raw27498step0 raw27498step0Labels = mixedMoment B raw27498step1 raw27498step1Labels := by
      have ha : raw27498step1 = (fun i j => raw27498step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27498step1 raw27498step0; decide +kernel
      have hl : raw27498step1Labels = raw27498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27498step0 raw27498step0Labels permutation150 permutation2
    mixedMoment B raw27498step1 raw27498step1Labels = mixedMoment B raw27498step2 raw27498step2Labels := by
      have ha : raw27498step2 = -raw27498step1 := by apply Matrix.ext; change ∀ i j, raw27498step2 i j = -(raw27498step1 i j); unfold raw27498step2 raw27498step1; decide +kernel
      have hl : raw27498step2Labels = raw27498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2123 node2123Labels := by rfl

theorem canonical27499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27499 raw27499Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw27499 raw27499Labels = mixedMoment B raw27499step0 raw27499step0Labels := by
      have hz : ∀ j, raw27499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27499step0 = (fun i j => raw27499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27499step0 raw27499; decide +kernel
      have hl : raw27499step0Labels = raw27499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27499 raw27499Labels permutation434 hz
    mixedMoment B raw27499step0 raw27499step0Labels = mixedMoment B raw27499step1 raw27499step1Labels := by
      have ha : raw27499step1 = (fun i j => raw27499step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27499step1 raw27499step0; decide +kernel
      have hl : raw27499step1Labels = raw27499step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27499step0 raw27499step0Labels permutation151 permutation2
    mixedMoment B raw27499step1 raw27499step1Labels = mixedMoment B raw27499step2 raw27499step2Labels := by
      have ha : raw27499step2 = -raw27499step1 := by apply Matrix.ext; change ∀ i j, raw27499step2 i j = -(raw27499step1 i j); unfold raw27499step2 raw27499step1; decide +kernel
      have hl : raw27499step2Labels = raw27499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2129 node2129Labels := by rfl

theorem canonical27500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27500 raw27500Labels = mixedMoment B node2118 node2118Labels := by
  calc
    mixedMoment B raw27500 raw27500Labels = mixedMoment B raw27500step0 raw27500step0Labels := by
      have ha : raw27500step0 = (fun i j => raw27500 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27500step0 raw27500; decide +kernel
      have hl : raw27500step0Labels = raw27500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27500 raw27500Labels permutation682 permutation2
    mixedMoment B raw27500step0 raw27500step0Labels = mixedMoment B raw27500step1 raw27500step1Labels := by
      have ha : raw27500step1 = -raw27500step0 := by apply Matrix.ext; change ∀ i j, raw27500step1 i j = -(raw27500step0 i j); unfold raw27500step1 raw27500step0; decide +kernel
      have hl : raw27500step1Labels = raw27500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2118 node2118Labels := by rfl

theorem canonical27501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27501 raw27501Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw27501 raw27501Labels = mixedMoment B raw27501step0 raw27501step0Labels := by
      have hz : ∀ j, raw27501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27501step0 = (fun i j => raw27501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27501step0 raw27501; decide +kernel
      have hl : raw27501step0Labels = raw27501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27501 raw27501Labels permutation434 hz
    mixedMoment B raw27501step0 raw27501step0Labels = mixedMoment B raw27501step1 raw27501step1Labels := by
      have ha : raw27501step1 = (fun i j => raw27501step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27501step1 raw27501step0; decide +kernel
      have hl : raw27501step1Labels = raw27501step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27501step0 raw27501step0Labels permutation145 permutation2
    mixedMoment B raw27501step1 raw27501step1Labels = mixedMoment B raw27501step2 raw27501step2Labels := by
      have ha : raw27501step2 = -raw27501step1 := by apply Matrix.ext; change ∀ i j, raw27501step2 i j = -(raw27501step1 i j); unfold raw27501step2 raw27501step1; decide +kernel
      have hl : raw27501step2Labels = raw27501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical27502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27502 raw27502Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw27502 raw27502Labels = mixedMoment B raw27502step0 raw27502step0Labels := by
      have hz : ∀ j, raw27502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27502step0 = (fun i j => raw27502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27502step0 raw27502; decide +kernel
      have hl : raw27502step0Labels = raw27502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27502 raw27502Labels permutation434 hz
    mixedMoment B raw27502step0 raw27502step0Labels = mixedMoment B raw27502step1 raw27502step1Labels := by
      have ha : raw27502step1 = (fun i j => raw27502step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27502step1 raw27502step0; decide +kernel
      have hl : raw27502step1Labels = raw27502step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27502step0 raw27502step0Labels permutation110 permutation4
    _ = mixedMoment B node2735 node2735Labels := by rfl

theorem canonical27503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27503 raw27503Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27503 raw27503Labels = mixedMoment B raw27503step0 raw27503step0Labels := by
      have hz : ∀ j, raw27503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27503step0 = (fun i j => raw27503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27503step0 raw27503; decide +kernel
      have hl : raw27503step0Labels = raw27503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27503 raw27503Labels permutation434 hz
    mixedMoment B raw27503step0 raw27503step0Labels = mixedMoment B raw27503step1 raw27503step1Labels := by
      have ha : raw27503step1 = (fun i j => raw27503step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27503step1 raw27503step0; decide +kernel
      have hl : raw27503step1Labels = raw27503step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27503step0 raw27503step0Labels permutation140 permutation0
    mixedMoment B raw27503step1 raw27503step1Labels = mixedMoment B raw27503step2 raw27503step2Labels := by
      have ha : raw27503step2 = -raw27503step1 := by apply Matrix.ext; change ∀ i j, raw27503step2 i j = -(raw27503step1 i j); unfold raw27503step2 raw27503step1; decide +kernel
      have hl : raw27503step2Labels = raw27503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

theorem canonical27504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27504 raw27504Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw27504 raw27504Labels = mixedMoment B raw27504step0 raw27504step0Labels := by
      have ha : raw27504step0 = (fun i j => raw27504 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27504step0 raw27504; decide +kernel
      have hl : raw27504step0Labels = raw27504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27504 raw27504Labels permutation686 permutation2
    mixedMoment B raw27504step0 raw27504step0Labels = mixedMoment B raw27504step1 raw27504step1Labels := by
      have ha : raw27504step1 = -raw27504step0 := by apply Matrix.ext; change ∀ i j, raw27504step1 i j = -(raw27504step0 i j); unfold raw27504step1 raw27504step0; decide +kernel
      have hl : raw27504step1Labels = raw27504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2553 node2553Labels := by rfl

theorem canonical27505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27505 raw27505Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw27505 raw27505Labels = mixedMoment B raw27505step0 raw27505step0Labels := by
      have hz : ∀ j, raw27505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27505step0 = (fun i j => raw27505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27505step0 raw27505; decide +kernel
      have hl : raw27505step0Labels = raw27505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27505 raw27505Labels permutation265 hz
    _ = mixedMoment B node2482 node2482Labels := by rfl

theorem canonical27506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27506 raw27506Labels = mixedMoment B node2542 node2542Labels := by
  calc
    _ = mixedMoment B node2542 node2542Labels := by rfl

theorem canonical27507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27507 raw27507Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw27507 raw27507Labels = mixedMoment B raw27507step0 raw27507step0Labels := by
      have ha : raw27507step0 = (fun i j => raw27507 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27507step0 raw27507; decide +kernel
      have hl : raw27507step0Labels = raw27507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27507 raw27507Labels permutation178 permutation2
    _ = mixedMoment B node2425 node2425Labels := by rfl

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

theorem canonical27509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27509 raw27509Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw27509 raw27509Labels = mixedMoment B raw27509step0 raw27509step0Labels := by
      have ha : raw27509step0 = (fun i j => raw27509 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27509step0 raw27509; decide +kernel
      have hl : raw27509step0Labels = raw27509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27509 raw27509Labels permutation686 permutation2
    mixedMoment B raw27509step0 raw27509step0Labels = mixedMoment B raw27509step1 raw27509step1Labels := by
      have ha : raw27509step1 = -raw27509step0 := by apply Matrix.ext; change ∀ i j, raw27509step1 i j = -(raw27509step0 i j); unfold raw27509step1 raw27509step0; decide +kernel
      have hl : raw27509step1Labels = raw27509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1148 node1148Labels := by rfl

theorem canonical27510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27510 raw27510Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw27510 raw27510Labels = mixedMoment B raw27510step0 raw27510step0Labels := by
      have ha : raw27510step0 = (fun i j => raw27510 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27510step0 raw27510; decide +kernel
      have hl : raw27510step0Labels = raw27510Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27510 raw27510Labels permutation662 permutation4
    _ = mixedMoment B node3513 node3513Labels := by rfl

theorem canonical27511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27511 raw27511Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw27511 raw27511Labels = mixedMoment B raw27511step0 raw27511step0Labels := by
      have ha : raw27511step0 = (fun i j => raw27511 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27511step0 raw27511; decide +kernel
      have hl : raw27511step0Labels = raw27511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27511 raw27511Labels permutation200 permutation2
    mixedMoment B raw27511step0 raw27511step0Labels = mixedMoment B raw27511step1 raw27511step1Labels := by
      have ha : raw27511step1 = -raw27511step0 := by apply Matrix.ext; change ∀ i j, raw27511step1 i j = -(raw27511step0 i j); unfold raw27511step1 raw27511step0; decide +kernel
      have hl : raw27511step1Labels = raw27511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3519 node3519Labels := by rfl

theorem canonical27512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27512 raw27512Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw27512 raw27512Labels = mixedMoment B raw27512step0 raw27512step0Labels := by
      have ha : raw27512step0 = (fun i j => raw27512 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27512step0 raw27512; decide +kernel
      have hl : raw27512step0Labels = raw27512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27512 raw27512Labels permutation161 permutation2
    mixedMoment B raw27512step0 raw27512step0Labels = mixedMoment B raw27512step1 raw27512step1Labels := by
      have ha : raw27512step1 = -raw27512step0 := by apply Matrix.ext; change ∀ i j, raw27512step1 i j = -(raw27512step0 i j); unfold raw27512step1 raw27512step0; decide +kernel
      have hl : raw27512step1Labels = raw27512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3437 node3437Labels := by rfl

theorem canonical27513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27513 raw27513Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27513 raw27513Labels = mixedMoment B raw27513step0 raw27513step0Labels := by
      have hz : ∀ j, raw27513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27513step0 = (fun i j => raw27513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27513step0 raw27513; decide +kernel
      have hl : raw27513step0Labels = raw27513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27513 raw27513Labels permutation434 hz
    mixedMoment B raw27513step0 raw27513step0Labels = mixedMoment B raw27513step1 raw27513step1Labels := by
      have ha : raw27513step1 = -raw27513step0 := by apply Matrix.ext; change ∀ i j, raw27513step1 i j = -(raw27513step0 i j); unfold raw27513step1 raw27513step0; decide +kernel
      have hl : raw27513step1Labels = raw27513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3481 node3481Labels := by rfl

theorem canonical27514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27514 raw27514Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw27514 raw27514Labels = mixedMoment B raw27514step0 raw27514step0Labels := by
      have ha : raw27514step0 = (fun i j => raw27514 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27514step0 raw27514; decide +kernel
      have hl : raw27514step0Labels = raw27514Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27514 raw27514Labels permutation159 permutation2
    mixedMoment B raw27514step0 raw27514step0Labels = mixedMoment B raw27514step1 raw27514step1Labels := by
      have ha : raw27514step1 = -raw27514step0 := by apply Matrix.ext; change ∀ i j, raw27514step1 i j = -(raw27514step0 i j); unfold raw27514step1 raw27514step0; decide +kernel
      have hl : raw27514step1Labels = raw27514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3434 node3434Labels := by rfl

theorem canonical27515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27515 raw27515Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw27515 raw27515Labels = mixedMoment B raw27515step0 raw27515step0Labels := by
      have ha : raw27515step0 = (fun i j => raw27515 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27515step0 raw27515; decide +kernel
      have hl : raw27515step0Labels = raw27515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27515 raw27515Labels permutation682 permutation2
    _ = mixedMoment B node3432 node3432Labels := by rfl

theorem canonical27516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27516 raw27516Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw27516 raw27516Labels = mixedMoment B raw27516step0 raw27516step0Labels := by
      have ha : raw27516step0 = (fun i j => raw27516 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27516step0 raw27516; decide +kernel
      have hl : raw27516step0Labels = raw27516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27516 raw27516Labels permutation188 permutation4
    mixedMoment B raw27516step0 raw27516step0Labels = mixedMoment B raw27516step1 raw27516step1Labels := by
      have ha : raw27516step1 = -raw27516step0 := by apply Matrix.ext; change ∀ i j, raw27516step1 i j = -(raw27516step0 i j); unfold raw27516step1 raw27516step0; decide +kernel
      have hl : raw27516step1Labels = raw27516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2015 node2015Labels := by rfl

theorem canonical27517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27517 raw27517Labels = mixedMoment B node1989 node1989Labels := by
  calc
    mixedMoment B raw27517 raw27517Labels = mixedMoment B raw27517step0 raw27517step0Labels := by
      have ha : raw27517step0 = (fun i j => raw27517 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27517step0 raw27517; decide +kernel
      have hl : raw27517step0Labels = raw27517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27517 raw27517Labels permutation178 permutation4
    mixedMoment B raw27517step0 raw27517step0Labels = mixedMoment B raw27517step1 raw27517step1Labels := by
      have ha : raw27517step1 = -raw27517step0 := by apply Matrix.ext; change ∀ i j, raw27517step1 i j = -(raw27517step0 i j); unfold raw27517step1 raw27517step0; decide +kernel
      have hl : raw27517step1Labels = raw27517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1989 node1989Labels := by rfl

theorem canonical27518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27518 raw27518Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw27518 raw27518Labels = mixedMoment B raw27518step0 raw27518step0Labels := by
      have ha : raw27518step0 = (fun i j => raw27518 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27518step0 raw27518; decide +kernel
      have hl : raw27518step0Labels = raw27518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27518 raw27518Labels permutation176 permutation4
    mixedMoment B raw27518step0 raw27518step0Labels = mixedMoment B raw27518step1 raw27518step1Labels := by
      have ha : raw27518step1 = -raw27518step0 := by apply Matrix.ext; change ∀ i j, raw27518step1 i j = -(raw27518step0 i j); unfold raw27518step1 raw27518step0; decide +kernel
      have hl : raw27518step1Labels = raw27518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1996 node1996Labels := by rfl

theorem canonical27519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27519 raw27519Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw27519 raw27519Labels = mixedMoment B raw27519step0 raw27519step0Labels := by
      have ha : raw27519step0 = (fun i j => raw27519 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27519step0 raw27519; decide +kernel
      have hl : raw27519step0Labels = raw27519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27519 raw27519Labels permutation662 permutation4
    _ = mixedMoment B node1986 node1986Labels := by rfl

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

theorem canonical27520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27520 raw27520Labels = mixedMoment B node3368 node3368Labels := by
  calc
    mixedMoment B raw27520 raw27520Labels = mixedMoment B raw27520step0 raw27520step0Labels := by
      have ha : raw27520step0 = (fun i j => raw27520 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27520step0 raw27520; decide +kernel
      have hl : raw27520step0Labels = raw27520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27520 raw27520Labels permutation664 permutation4
    _ = mixedMoment B node3368 node3368Labels := by rfl

theorem canonical27521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27521 raw27521Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw27521 raw27521Labels = mixedMoment B raw27521step0 raw27521step0Labels := by
      have ha : raw27521step0 = (fun i j => raw27521 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27521step0 raw27521; decide +kernel
      have hl : raw27521step0Labels = raw27521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27521 raw27521Labels permutation688 permutation4
    _ = mixedMoment B node3432 node3432Labels := by rfl

theorem canonical27522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27522 raw27522Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw27522 raw27522Labels = mixedMoment B raw27522step0 raw27522step0Labels := by
      have ha : raw27522step0 = (fun i j => raw27522 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27522step0 raw27522; decide +kernel
      have hl : raw27522step0Labels = raw27522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27522 raw27522Labels permutation664 permutation4
    _ = mixedMoment B node1996 node1996Labels := by rfl

theorem canonical27523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27523 raw27523Labels = mixedMoment B node3608 node3608Labels := by
  calc
    mixedMoment B raw27523 raw27523Labels = mixedMoment B raw27523step0 raw27523step0Labels := by
      have hz : ∀ j, raw27523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27523step0 = (fun i j => raw27523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27523step0 raw27523; decide +kernel
      have hl : raw27523step0Labels = raw27523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27523 raw27523Labels permutation434 hz
    mixedMoment B raw27523step0 raw27523step0Labels = mixedMoment B raw27523step1 raw27523step1Labels := by
      have hz : ∀ j, raw27523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27523step1 = (fun i j => raw27523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27523step1 raw27523step0; decide +kernel
      have hl : raw27523step1Labels = raw27523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27523step0 raw27523step0Labels permutation80 hz
    mixedMoment B raw27523step1 raw27523step1Labels = mixedMoment B raw27523step2 raw27523step2Labels := by
      have ha : raw27523step2 = (fun i j => raw27523step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27523step2 raw27523step1; decide +kernel
      have hl : raw27523step2Labels = raw27523step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27523step1 raw27523step1Labels permutation31 permutation4
    _ = mixedMoment B node3608 node3608Labels := by rfl

theorem canonical27524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27524 raw27524Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw27524 raw27524Labels = mixedMoment B raw27524step0 raw27524step0Labels := by
      have hz : ∀ j, raw27524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27524step0 = (fun i j => raw27524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27524step0 raw27524; decide +kernel
      have hl : raw27524step0Labels = raw27524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27524 raw27524Labels permutation346 hz
    mixedMoment B raw27524step0 raw27524step0Labels = mixedMoment B raw27524step1 raw27524step1Labels := by
      have ha : raw27524step1 = (fun i j => raw27524step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27524step1 raw27524step0; decide +kernel
      have hl : raw27524step1Labels = raw27524step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27524step0 raw27524step0Labels permutation143 permutation4
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical27525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27525 raw27525Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw27525 raw27525Labels = mixedMoment B raw27525step0 raw27525step0Labels := by
      have ha : raw27525step0 = (fun i j => raw27525 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27525step0 raw27525; decide +kernel
      have hl : raw27525step0Labels = raw27525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27525 raw27525Labels permutation686 permutation2
    mixedMoment B raw27525step0 raw27525step0Labels = mixedMoment B raw27525step1 raw27525step1Labels := by
      have ha : raw27525step1 = -raw27525step0 := by apply Matrix.ext; change ∀ i j, raw27525step1 i j = -(raw27525step0 i j); unfold raw27525step1 raw27525step0; decide +kernel
      have hl : raw27525step1Labels = raw27525step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical27526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27526 raw27526Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27526 raw27526Labels = mixedMoment B raw27526step0 raw27526step0Labels := by
      have hz : ∀ j, raw27526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27526step0 = (fun i j => raw27526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27526step0 raw27526; decide +kernel
      have hl : raw27526step0Labels = raw27526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27526 raw27526Labels permutation265 hz
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical27527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27527 raw27527Labels = mixedMoment B node2543 node2543Labels := by
  calc
    _ = mixedMoment B node2543 node2543Labels := by rfl

theorem canonical27528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27528 raw27528Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw27528 raw27528Labels = mixedMoment B raw27528step0 raw27528step0Labels := by
      have ha : raw27528step0 = (fun i j => raw27528 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27528step0 raw27528; decide +kernel
      have hl : raw27528step0Labels = raw27528Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27528 raw27528Labels permutation176 permutation2
    _ = mixedMoment B node2429 node2429Labels := by rfl

theorem canonical27529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27529 raw27529Labels = mixedMoment B node2422 node2422Labels := by
  calc
    mixedMoment B raw27529 raw27529Labels = mixedMoment B raw27529step0 raw27529step0Labels := by
      have ha : raw27529step0 = (fun i j => raw27529 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27529step0 raw27529; decide +kernel
      have hl : raw27529step0Labels = raw27529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27529 raw27529Labels permutation176 permutation2
    _ = mixedMoment B node2422 node2422Labels := by rfl

theorem canonical27530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27530 raw27530Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw27530 raw27530Labels = mixedMoment B raw27530step0 raw27530step0Labels := by
      have ha : raw27530step0 = (fun i j => raw27530 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27530step0 raw27530; decide +kernel
      have hl : raw27530step0Labels = raw27530Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27530 raw27530Labels permutation686 permutation2
    mixedMoment B raw27530step0 raw27530step0Labels = mixedMoment B raw27530step1 raw27530step1Labels := by
      have ha : raw27530step1 = -raw27530step0 := by apply Matrix.ext; change ∀ i j, raw27530step1 i j = -(raw27530step0 i j); unfold raw27530step1 raw27530step0; decide +kernel
      have hl : raw27530step1Labels = raw27530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1327 node1327Labels := by rfl

theorem canonical27531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27531 raw27531Labels = mixedMoment B node2349 node2349Labels := by
  calc
    _ = mixedMoment B node2349 node2349Labels := by rfl

theorem canonical27532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27532 raw27532Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw27532 raw27532Labels = mixedMoment B raw27532step0 raw27532step0Labels := by
      have ha : raw27532step0 = (fun i j => raw27532 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27532step0 raw27532; decide +kernel
      have hl : raw27532step0Labels = raw27532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27532 raw27532Labels permutation154 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

theorem canonical27533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27533 raw27533Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw27533 raw27533Labels = mixedMoment B raw27533step0 raw27533step0Labels := by
      have ha : raw27533step0 = (fun i j => raw27533 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27533step0 raw27533; decide +kernel
      have hl : raw27533step0Labels = raw27533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27533 raw27533Labels permutation682 permutation2
    mixedMoment B raw27533step0 raw27533step0Labels = mixedMoment B raw27533step1 raw27533step1Labels := by
      have ha : raw27533step1 = -raw27533step0 := by apply Matrix.ext; change ∀ i j, raw27533step1 i j = -(raw27533step0 i j); unfold raw27533step1 raw27533step0; decide +kernel
      have hl : raw27533step1Labels = raw27533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2071 node2071Labels := by rfl

theorem canonical27534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27534 raw27534Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw27534 raw27534Labels = mixedMoment B raw27534step0 raw27534step0Labels := by
      have ha : raw27534step0 = (fun i j => raw27534 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27534step0 raw27534; decide +kernel
      have hl : raw27534step0Labels = raw27534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27534 raw27534Labels permutation681 permutation2
    mixedMoment B raw27534step0 raw27534step0Labels = mixedMoment B raw27534step1 raw27534step1Labels := by
      have ha : raw27534step1 = -raw27534step0 := by apply Matrix.ext; change ∀ i j, raw27534step1 i j = -(raw27534step0 i j); unfold raw27534step1 raw27534step0; decide +kernel
      have hl : raw27534step1Labels = raw27534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2073 node2073Labels := by rfl

theorem canonical27535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27535 raw27535Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw27535 raw27535Labels = mixedMoment B raw27535step0 raw27535step0Labels := by
      have ha : raw27535step0 = (fun i j => raw27535 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27535step0 raw27535; decide +kernel
      have hl : raw27535step0Labels = raw27535Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27535 raw27535Labels permutation688 permutation2
    mixedMoment B raw27535step0 raw27535step0Labels = mixedMoment B raw27535step1 raw27535step1Labels := by
      have ha : raw27535step1 = -raw27535step0 := by apply Matrix.ext; change ∀ i j, raw27535step1 i j = -(raw27535step0 i j); unfold raw27535step1 raw27535step0; decide +kernel
      have hl : raw27535step1Labels = raw27535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2086 node2086Labels := by rfl

theorem canonical27536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27536 raw27536Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw27536 raw27536Labels = mixedMoment B raw27536step0 raw27536step0Labels := by
      have ha : raw27536step0 = (fun i j => raw27536 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27536step0 raw27536; decide +kernel
      have hl : raw27536step0Labels = raw27536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27536 raw27536Labels permutation680 permutation2
    mixedMoment B raw27536step0 raw27536step0Labels = mixedMoment B raw27536step1 raw27536step1Labels := by
      have ha : raw27536step1 = -raw27536step0 := by apply Matrix.ext; change ∀ i j, raw27536step1 i j = -(raw27536step0 i j); unfold raw27536step1 raw27536step0; decide +kernel
      have hl : raw27536step1Labels = raw27536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2077 node2077Labels := by rfl

theorem canonical27537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27537 raw27537Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw27537 raw27537Labels = mixedMoment B raw27537step0 raw27537step0Labels := by
      have ha : raw27537step0 = (fun i j => raw27537 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27537step0 raw27537; decide +kernel
      have hl : raw27537step0Labels = raw27537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27537 raw27537Labels permutation640 permutation2
    mixedMoment B raw27537step0 raw27537step0Labels = mixedMoment B raw27537step1 raw27537step1Labels := by
      have ha : raw27537step1 = -raw27537step0 := by apply Matrix.ext; change ∀ i j, raw27537step1 i j = -(raw27537step0 i j); unfold raw27537step1 raw27537step0; decide +kernel
      have hl : raw27537step1Labels = raw27537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2191 node2191Labels := by rfl

theorem canonical27538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27538 raw27538Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw27538 raw27538Labels = mixedMoment B raw27538step0 raw27538step0Labels := by
      have ha : raw27538step0 = (fun i j => raw27538 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27538step0 raw27538; decide +kernel
      have hl : raw27538step0Labels = raw27538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27538 raw27538Labels permutation682 permutation2
    mixedMoment B raw27538step0 raw27538step0Labels = mixedMoment B raw27538step1 raw27538step1Labels := by
      have ha : raw27538step1 = -raw27538step0 := by apply Matrix.ext; change ∀ i j, raw27538step1 i j = -(raw27538step0 i j); unfold raw27538step1 raw27538step0; decide +kernel
      have hl : raw27538step1Labels = raw27538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3558 node3558Labels := by rfl

theorem canonical27539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27539 raw27539Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw27539 raw27539Labels = mixedMoment B raw27539step0 raw27539step0Labels := by
      have ha : raw27539step0 = (fun i j => raw27539 (permutation623 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27539step0 raw27539; decide +kernel
      have hl : raw27539step0Labels = raw27539Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27539 raw27539Labels permutation623 permutation0
    mixedMoment B raw27539step0 raw27539step0Labels = mixedMoment B raw27539step1 raw27539step1Labels := by
      have ha : raw27539step1 = -raw27539step0 := by apply Matrix.ext; change ∀ i j, raw27539step1 i j = -(raw27539step0 i j); unfold raw27539step1 raw27539step0; decide +kernel
      have hl : raw27539step1Labels = raw27539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4079 node4079Labels := by rfl

theorem canonical27540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27540 raw27540Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw27540 raw27540Labels = mixedMoment B raw27540step0 raw27540step0Labels := by
      have ha : raw27540step0 = (fun i j => raw27540 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27540step0 raw27540; decide +kernel
      have hl : raw27540step0Labels = raw27540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27540 raw27540Labels permutation682 permutation2
    mixedMoment B raw27540step0 raw27540step0Labels = mixedMoment B raw27540step1 raw27540step1Labels := by
      have ha : raw27540step1 = -raw27540step0 := by apply Matrix.ext; change ∀ i j, raw27540step1 i j = -(raw27540step0 i j); unfold raw27540step1 raw27540step0; decide +kernel
      have hl : raw27540step1Labels = raw27540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2454 node2454Labels := by rfl

theorem canonical27541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27541 raw27541Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw27541 raw27541Labels = mixedMoment B raw27541step0 raw27541step0Labels := by
      have ha : raw27541step0 = (fun i j => raw27541 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27541step0 raw27541; decide +kernel
      have hl : raw27541step0Labels = raw27541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27541 raw27541Labels permutation681 permutation2
    mixedMoment B raw27541step0 raw27541step0Labels = mixedMoment B raw27541step1 raw27541step1Labels := by
      have ha : raw27541step1 = -raw27541step0 := by apply Matrix.ext; change ∀ i j, raw27541step1 i j = -(raw27541step0 i j); unfold raw27541step1 raw27541step0; decide +kernel
      have hl : raw27541step1Labels = raw27541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2456 node2456Labels := by rfl

theorem canonical27542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27542 raw27542Labels = mixedMoment B node2491 node2491Labels := by
  calc
    mixedMoment B raw27542 raw27542Labels = mixedMoment B raw27542step0 raw27542step0Labels := by
      have ha : raw27542step0 = (fun i j => raw27542 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27542step0 raw27542; decide +kernel
      have hl : raw27542step0Labels = raw27542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27542 raw27542Labels permutation688 permutation2
    mixedMoment B raw27542step0 raw27542step0Labels = mixedMoment B raw27542step1 raw27542step1Labels := by
      have ha : raw27542step1 = -raw27542step0 := by apply Matrix.ext; change ∀ i j, raw27542step1 i j = -(raw27542step0 i j); unfold raw27542step1 raw27542step0; decide +kernel
      have hl : raw27542step1Labels = raw27542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2491 node2491Labels := by rfl

theorem canonical27543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27543 raw27543Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw27543 raw27543Labels = mixedMoment B raw27543step0 raw27543step0Labels := by
      have ha : raw27543step0 = (fun i j => raw27543 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27543step0 raw27543; decide +kernel
      have hl : raw27543step0Labels = raw27543Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27543 raw27543Labels permutation680 permutation2
    mixedMoment B raw27543step0 raw27543step0Labels = mixedMoment B raw27543step1 raw27543step1Labels := by
      have ha : raw27543step1 = -raw27543step0 := by apply Matrix.ext; change ∀ i j, raw27543step1 i j = -(raw27543step0 i j); unfold raw27543step1 raw27543step0; decide +kernel
      have hl : raw27543step1Labels = raw27543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2462 node2462Labels := by rfl

theorem canonical27544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27544 raw27544Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw27544 raw27544Labels = mixedMoment B raw27544step0 raw27544step0Labels := by
      have ha : raw27544step0 = (fun i j => raw27544 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27544step0 raw27544; decide +kernel
      have hl : raw27544step0Labels = raw27544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27544 raw27544Labels permutation646 permutation2
    mixedMoment B raw27544step0 raw27544step0Labels = mixedMoment B raw27544step1 raw27544step1Labels := by
      have ha : raw27544step1 = -raw27544step0 := by apply Matrix.ext; change ∀ i j, raw27544step1 i j = -(raw27544step0 i j); unfold raw27544step1 raw27544step0; decide +kernel
      have hl : raw27544step1Labels = raw27544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2698 node2698Labels := by rfl

theorem canonical27545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27545 raw27545Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw27545 raw27545Labels = mixedMoment B raw27545step0 raw27545step0Labels := by
      have ha : raw27545step0 = (fun i j => raw27545 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27545step0 raw27545; decide +kernel
      have hl : raw27545step0Labels = raw27545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27545 raw27545Labels permutation682 permutation2
    mixedMoment B raw27545step0 raw27545step0Labels = mixedMoment B raw27545step1 raw27545step1Labels := by
      have ha : raw27545step1 = -raw27545step0 := by apply Matrix.ext; change ∀ i j, raw27545step1 i j = -(raw27545step0 i j); unfold raw27545step1 raw27545step0; decide +kernel
      have hl : raw27545step1Labels = raw27545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

theorem canonical27546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27546 raw27546Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw27546 raw27546Labels = mixedMoment B raw27546step0 raw27546step0Labels := by
      have ha : raw27546step0 = (fun i j => raw27546 (permutation434 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27546step0 raw27546; decide +kernel
      have hl : raw27546step0Labels = raw27546Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27546 raw27546Labels permutation434 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical27551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27551 raw27551Labels = mixedMoment B node1992 node1992Labels := by
  calc
    mixedMoment B raw27551 raw27551Labels = mixedMoment B raw27551step0 raw27551step0Labels := by
      have ha : raw27551step0 = (fun i j => raw27551 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27551step0 raw27551; decide +kernel
      have hl : raw27551step0Labels = raw27551Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27551 raw27551Labels permutation682 permutation2
    mixedMoment B raw27551step0 raw27551step0Labels = mixedMoment B raw27551step1 raw27551step1Labels := by
      have ha : raw27551step1 = -raw27551step0 := by apply Matrix.ext; change ∀ i j, raw27551step1 i j = -(raw27551step0 i j); unfold raw27551step1 raw27551step0; decide +kernel
      have hl : raw27551step1Labels = raw27551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1992 node1992Labels := by rfl

theorem canonical27552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27552 raw27552Labels = mixedMoment B node1994 node1994Labels := by
  calc
    mixedMoment B raw27552 raw27552Labels = mixedMoment B raw27552step0 raw27552step0Labels := by
      have ha : raw27552step0 = (fun i j => raw27552 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27552step0 raw27552; decide +kernel
      have hl : raw27552step0Labels = raw27552Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27552 raw27552Labels permutation681 permutation2
    mixedMoment B raw27552step0 raw27552step0Labels = mixedMoment B raw27552step1 raw27552step1Labels := by
      have ha : raw27552step1 = -raw27552step0 := by apply Matrix.ext; change ∀ i j, raw27552step1 i j = -(raw27552step0 i j); unfold raw27552step1 raw27552step0; decide +kernel
      have hl : raw27552step1Labels = raw27552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1994 node1994Labels := by rfl

theorem canonical27553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27553 raw27553Labels = mixedMoment B node2031 node2031Labels := by
  calc
    mixedMoment B raw27553 raw27553Labels = mixedMoment B raw27553step0 raw27553step0Labels := by
      have ha : raw27553step0 = (fun i j => raw27553 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27553step0 raw27553; decide +kernel
      have hl : raw27553step0Labels = raw27553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27553 raw27553Labels permutation688 permutation2
    mixedMoment B raw27553step0 raw27553step0Labels = mixedMoment B raw27553step1 raw27553step1Labels := by
      have ha : raw27553step1 = -raw27553step0 := by apply Matrix.ext; change ∀ i j, raw27553step1 i j = -(raw27553step0 i j); unfold raw27553step1 raw27553step0; decide +kernel
      have hl : raw27553step1Labels = raw27553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2031 node2031Labels := by rfl

theorem canonical27554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27554 raw27554Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw27554 raw27554Labels = mixedMoment B raw27554step0 raw27554step0Labels := by
      have ha : raw27554step0 = (fun i j => raw27554 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27554step0 raw27554; decide +kernel
      have hl : raw27554step0Labels = raw27554Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27554 raw27554Labels permutation680 permutation2
    mixedMoment B raw27554step0 raw27554step0Labels = mixedMoment B raw27554step1 raw27554step1Labels := by
      have ha : raw27554step1 = -raw27554step0 := by apply Matrix.ext; change ∀ i j, raw27554step1 i j = -(raw27554step0 i j); unfold raw27554step1 raw27554step0; decide +kernel
      have hl : raw27554step1Labels = raw27554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2000 node2000Labels := by rfl

theorem canonical27555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27555 raw27555Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw27555 raw27555Labels = mixedMoment B raw27555step0 raw27555step0Labels := by
      have hz : ∀ j, raw27555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27555step0 = (fun i j => raw27555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27555step0 raw27555; decide +kernel
      have hl : raw27555step0Labels = raw27555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27555 raw27555Labels permutation520 hz
    mixedMoment B raw27555step0 raw27555step0Labels = mixedMoment B raw27555step1 raw27555step1Labels := by
      have ha : raw27555step1 = (fun i j => raw27555step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27555step1 raw27555step0; decide +kernel
      have hl : raw27555step1Labels = raw27555step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27555step0 raw27555step0Labels permutation145 permutation2
    mixedMoment B raw27555step1 raw27555step1Labels = mixedMoment B raw27555step2 raw27555step2Labels := by
      have ha : raw27555step2 = -raw27555step1 := by apply Matrix.ext; change ∀ i j, raw27555step2 i j = -(raw27555step1 i j); unfold raw27555step2 raw27555step1; decide +kernel
      have hl : raw27555step2Labels = raw27555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2216 node2216Labels := by rfl

theorem canonical27556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27556 raw27556Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw27556 raw27556Labels = mixedMoment B raw27556step0 raw27556step0Labels := by
      have ha : raw27556step0 = (fun i j => raw27556 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27556step0 raw27556; decide +kernel
      have hl : raw27556step0Labels = raw27556Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27556 raw27556Labels permutation682 permutation2
    mixedMoment B raw27556step0 raw27556step0Labels = mixedMoment B raw27556step1 raw27556step1Labels := by
      have ha : raw27556step1 = -raw27556step0 := by apply Matrix.ext; change ∀ i j, raw27556step1 i j = -(raw27556step0 i j); unfold raw27556step1 raw27556step0; decide +kernel
      have hl : raw27556step1Labels = raw27556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical27557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27557 raw27557Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27557 raw27557Labels = mixedMoment B raw27557step0 raw27557step0Labels := by
      have hz : ∀ j, raw27557 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27557step0 = (fun i j => raw27557 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27557step0 raw27557; decide +kernel
      have hl : raw27557step0Labels = raw27557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27557 raw27557Labels permutation520 hz
    mixedMoment B raw27557step0 raw27557step0Labels = mixedMoment B raw27557step1 raw27557step1Labels := by
      have ha : raw27557step1 = (fun i j => raw27557step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27557step1 raw27557step0; decide +kernel
      have hl : raw27557step1Labels = raw27557step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27557step0 raw27557step0Labels permutation140 permutation0
    mixedMoment B raw27557step1 raw27557step1Labels = mixedMoment B raw27557step2 raw27557step2Labels := by
      have ha : raw27557step2 = -raw27557step1 := by apply Matrix.ext; change ∀ i j, raw27557step2 i j = -(raw27557step1 i j); unfold raw27557step2 raw27557step1; decide +kernel
      have hl : raw27557step2Labels = raw27557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

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

theorem sound1148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1148 node1148Labels = Sparse.eval nodeValue1148 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1148) = mixedMoment B node1148 node1148Labels := rfl
  simpa [nodeValue1148, Sparse.eval] using hc.symm

theorem sound1150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1150 node1150Labels = Sparse.eval nodeValue1150 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1150) = mixedMoment B node1150 node1150Labels := rfl
  simpa [nodeValue1150, Sparse.eval] using hc.symm

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

theorem sound1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1327 node1327Labels = Sparse.eval nodeValue1327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1327) = mixedMoment B node1327 node1327Labels := rfl
  simpa [nodeValue1327, Sparse.eval] using hc.symm

theorem sound1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1337 node1337Labels = Sparse.eval nodeValue1337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1337) = mixedMoment B node1337 node1337Labels := rfl
  simpa [nodeValue1337, Sparse.eval] using hc.symm

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

theorem sound1986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1986 node1986Labels = Sparse.eval nodeValue1986 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1986) = mixedMoment B node1986 node1986Labels := rfl
  simpa [nodeValue1986, Sparse.eval] using hc.symm

theorem sound1989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1989 node1989Labels = Sparse.eval nodeValue1989 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1989) = mixedMoment B node1989 node1989Labels := rfl
  simpa [nodeValue1989, Sparse.eval] using hc.symm

theorem sound1992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1992 node1992Labels = Sparse.eval nodeValue1992 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1992) = mixedMoment B node1992 node1992Labels := rfl
  simpa [nodeValue1992, Sparse.eval] using hc.symm

theorem sound1994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1994 node1994Labels = Sparse.eval nodeValue1994 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1994) = mixedMoment B node1994 node1994Labels := rfl
  simpa [nodeValue1994, Sparse.eval] using hc.symm

theorem sound1996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1996 node1996Labels = Sparse.eval nodeValue1996 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1996) = mixedMoment B node1996 node1996Labels := rfl
  simpa [nodeValue1996, Sparse.eval] using hc.symm

theorem sound1998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1998 node1998Labels = Sparse.eval nodeValue1998 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1998) = mixedMoment B node1998 node1998Labels := rfl
  simpa [nodeValue1998, Sparse.eval] using hc.symm

theorem sound2000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2000 node2000Labels = Sparse.eval nodeValue2000 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2000) = mixedMoment B node2000 node2000Labels := rfl
  simpa [nodeValue2000, Sparse.eval] using hc.symm

theorem sound2004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2004 node2004Labels = Sparse.eval nodeValue2004 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2004) = mixedMoment B node2004 node2004Labels := rfl
  simpa [nodeValue2004, Sparse.eval] using hc.symm

theorem sound2006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2006 node2006Labels = Sparse.eval nodeValue2006 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2006) = mixedMoment B node2006 node2006Labels := rfl
  simpa [nodeValue2006, Sparse.eval] using hc.symm

theorem sound2015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2015 node2015Labels = Sparse.eval nodeValue2015 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2015) = mixedMoment B node2015 node2015Labels := rfl
  simpa [nodeValue2015, Sparse.eval] using hc.symm

theorem sound2031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2031 node2031Labels = Sparse.eval nodeValue2031 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2031) = mixedMoment B node2031 node2031Labels := rfl
  simpa [nodeValue2031, Sparse.eval] using hc.symm

theorem sound2047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2047 node2047Labels = Sparse.eval nodeValue2047 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2047) = mixedMoment B node2047 node2047Labels := rfl
  simpa [nodeValue2047, Sparse.eval] using hc.symm

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

theorem sound2049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2049 node2049Labels = Sparse.eval nodeValue2049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2049) = mixedMoment B node2049 node2049Labels := rfl
  simpa [nodeValue2049, Sparse.eval] using hc.symm

theorem sound2071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2071 node2071Labels = Sparse.eval nodeValue2071 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2071) = mixedMoment B node2071 node2071Labels := rfl
  simpa [nodeValue2071, Sparse.eval] using hc.symm

theorem sound2073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2073 node2073Labels = Sparse.eval nodeValue2073 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2073) = mixedMoment B node2073 node2073Labels := rfl
  simpa [nodeValue2073, Sparse.eval] using hc.symm

theorem sound2077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2077 node2077Labels = Sparse.eval nodeValue2077 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2077) = mixedMoment B node2077 node2077Labels := rfl
  simpa [nodeValue2077, Sparse.eval] using hc.symm

theorem sound2086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2086 node2086Labels = Sparse.eval nodeValue2086 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2086) = mixedMoment B node2086 node2086Labels := rfl
  simpa [nodeValue2086, Sparse.eval] using hc.symm

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

theorem sound2118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2118 node2118Labels = Sparse.eval nodeValue2118 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2118) = mixedMoment B node2118 node2118Labels := rfl
  simpa [nodeValue2118, Sparse.eval] using hc.symm

theorem sound2121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2121 node2121Labels = Sparse.eval nodeValue2121 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2121) = mixedMoment B node2121 node2121Labels := rfl
  simpa [nodeValue2121, Sparse.eval] using hc.symm

theorem sound2123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2123 node2123Labels = Sparse.eval nodeValue2123 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2123) = mixedMoment B node2123 node2123Labels := rfl
  simpa [nodeValue2123, Sparse.eval] using hc.symm

theorem sound2129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2129 node2129Labels = Sparse.eval nodeValue2129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2129) = mixedMoment B node2129 node2129Labels := rfl
  simpa [nodeValue2129, Sparse.eval] using hc.symm

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

theorem sound2191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2191 node2191Labels = Sparse.eval nodeValue2191 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2191) = mixedMoment B node2191 node2191Labels := rfl
  simpa [nodeValue2191, Sparse.eval] using hc.symm

theorem sound2203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2203 node2203Labels = Sparse.eval nodeValue2203 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2203) = mixedMoment B node2203 node2203Labels := rfl
  simpa [nodeValue2203, Sparse.eval] using hc.symm

theorem sound2216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2216 node2216Labels = Sparse.eval nodeValue2216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2216) = mixedMoment B node2216 node2216Labels := rfl
  simpa [nodeValue2216, Sparse.eval] using hc.symm

theorem sound2230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2230 node2230Labels = Sparse.eval nodeValue2230 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2230) = mixedMoment B node2230 node2230Labels := rfl
  simpa [nodeValue2230, Sparse.eval] using hc.symm

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

theorem sound2425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2425 node2425Labels = Sparse.eval nodeValue2425 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2425) = mixedMoment B node2425 node2425Labels := rfl
  simpa [nodeValue2425, Sparse.eval] using hc.symm

theorem sound2429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2429 node2429Labels = Sparse.eval nodeValue2429 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2429) = mixedMoment B node2429 node2429Labels := rfl
  simpa [nodeValue2429, Sparse.eval] using hc.symm

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

theorem sound2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2437 node2437Labels = Sparse.eval nodeValue2437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2437) = mixedMoment B node2437 node2437Labels := rfl
  simpa [nodeValue2437, Sparse.eval] using hc.symm

theorem sound2442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2442 node2442Labels = Sparse.eval nodeValue2442 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2442) = mixedMoment B node2442 node2442Labels := rfl
  simpa [nodeValue2442, Sparse.eval] using hc.symm

theorem sound2454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2454 node2454Labels = Sparse.eval nodeValue2454 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2454) = mixedMoment B node2454 node2454Labels := rfl
  simpa [nodeValue2454, Sparse.eval] using hc.symm

theorem sound2456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2456 node2456Labels = Sparse.eval nodeValue2456 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2456) = mixedMoment B node2456 node2456Labels := rfl
  simpa [nodeValue2456, Sparse.eval] using hc.symm

theorem sound2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2462 node2462Labels = Sparse.eval nodeValue2462 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2462) = mixedMoment B node2462 node2462Labels := rfl
  simpa [nodeValue2462, Sparse.eval] using hc.symm

theorem sound2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2482 node2482Labels = Sparse.eval nodeValue2482 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2482) = mixedMoment B node2482 node2482Labels := rfl
  simpa [nodeValue2482, Sparse.eval] using hc.symm

theorem sound2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2485 node2485Labels = Sparse.eval nodeValue2485 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2485) = mixedMoment B node2485 node2485Labels := rfl
  simpa [nodeValue2485, Sparse.eval] using hc.symm

theorem sound2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2491 node2491Labels = Sparse.eval nodeValue2491 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2491) = mixedMoment B node2491 node2491Labels := rfl
  simpa [nodeValue2491, Sparse.eval] using hc.symm

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

theorem zero2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = 0 := by
  exact mixedMoment_alpha B hF node2542 node2542Labels 1 permutation158
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

theorem sound2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2542 node2542Labels = Sparse.eval nodeValue2542 (mixedVector B) := by
  simpa only [nodeValue2542, Sparse.eval_nil] using zero2542 B _hB _hF

theorem sound2543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2543 node2543Labels = Sparse.eval nodeValue2543 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2543) = mixedMoment B node2543 node2543Labels := rfl
  simpa [nodeValue2543, Sparse.eval] using hc.symm

theorem sound2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2553 node2553Labels = Sparse.eval nodeValue2553 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2553) = mixedMoment B node2553 node2553Labels := rfl
  simpa [nodeValue2553, Sparse.eval] using hc.symm

theorem sound2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2556 node2556Labels = Sparse.eval nodeValue2556 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2556) = mixedMoment B node2556 node2556Labels := rfl
  simpa [nodeValue2556, Sparse.eval] using hc.symm

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

theorem sound2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2618 node2618Labels = Sparse.eval nodeValue2618 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2618) = mixedMoment B node2618 node2618Labels := rfl
  simpa [nodeValue2618, Sparse.eval] using hc.symm

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

theorem sound2698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2698 node2698Labels = Sparse.eval nodeValue2698 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2698) = mixedMoment B node2698 node2698Labels := rfl
  simpa [nodeValue2698, Sparse.eval] using hc.symm

theorem sound2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2735 node2735Labels = Sparse.eval nodeValue2735 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2735) = mixedMoment B node2735 node2735Labels := rfl
  simpa [nodeValue2735, Sparse.eval] using hc.symm

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

theorem sound2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2924 node2924Labels = Sparse.eval nodeValue2924 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2924) = mixedMoment B node2924 node2924Labels := rfl
  simpa [nodeValue2924, Sparse.eval] using hc.symm

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

theorem zero3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3339 node3339Labels = 0 := by
  exact mixedMoment_alpha B hF node3339 node3339Labels 1 permutation437
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

theorem sound3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3339 node3339Labels = Sparse.eval nodeValue3339 (mixedVector B) := by
  simpa only [nodeValue3339, Sparse.eval_nil] using zero3339 B _hB _hF

theorem sound3343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3343 node3343Labels = Sparse.eval nodeValue3343 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3343) = mixedMoment B node3343 node3343Labels := rfl
  simpa [nodeValue3343, Sparse.eval] using hc.symm

theorem sound3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3353 node3353Labels = Sparse.eval nodeValue3353 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3353) = mixedMoment B node3353 node3353Labels := rfl
  simpa [nodeValue3353, Sparse.eval] using hc.symm

theorem sound3368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3368 node3368Labels = Sparse.eval nodeValue3368 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3368) = mixedMoment B node3368 node3368Labels := rfl
  simpa [nodeValue3368, Sparse.eval] using hc.symm

theorem sound3385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3385 node3385Labels = Sparse.eval nodeValue3385 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3385) = mixedMoment B node3385 node3385Labels := rfl
  simpa [nodeValue3385, Sparse.eval] using hc.symm

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

theorem sound3432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3432 node3432Labels = Sparse.eval nodeValue3432 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3432) = mixedMoment B node3432 node3432Labels := rfl
  simpa [nodeValue3432, Sparse.eval] using hc.symm

theorem sound3434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3434 node3434Labels = Sparse.eval nodeValue3434 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3434) = mixedMoment B node3434 node3434Labels := rfl
  simpa [nodeValue3434, Sparse.eval] using hc.symm

theorem sound3437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3437 node3437Labels = Sparse.eval nodeValue3437 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3437) = mixedMoment B node3437 node3437Labels := rfl
  simpa [nodeValue3437, Sparse.eval] using hc.symm

theorem sound3443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3443 node3443Labels = Sparse.eval nodeValue3443 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3443) = mixedMoment B node3443 node3443Labels := rfl
  simpa [nodeValue3443, Sparse.eval] using hc.symm

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

theorem zero3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = 0 := by
  exact mixedMoment_alpha B hF node3513 node3513Labels 1 permutation444
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

theorem sound3468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3468 node3468Labels = Sparse.eval nodeValue3468 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3468) = mixedMoment B node3468 node3468Labels := rfl
  simpa [nodeValue3468, Sparse.eval] using hc.symm

theorem sound3481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3481 node3481Labels = Sparse.eval nodeValue3481 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3481) = mixedMoment B node3481 node3481Labels := rfl
  simpa [nodeValue3481, Sparse.eval] using hc.symm

theorem sound3513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3513 node3513Labels = Sparse.eval nodeValue3513 (mixedVector B) := by
  simpa only [nodeValue3513, Sparse.eval_nil] using zero3513 B _hB _hF

theorem sound3517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3517 node3517Labels = Sparse.eval nodeValue3517 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3517) = mixedMoment B node3517 node3517Labels := rfl
  simpa [nodeValue3517, Sparse.eval] using hc.symm

theorem sound3519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3519 node3519Labels = Sparse.eval nodeValue3519 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3519) = mixedMoment B node3519 node3519Labels := rfl
  simpa [nodeValue3519, Sparse.eval] using hc.symm

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

theorem sound3523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3523 node3523Labels = Sparse.eval nodeValue3523 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3523) = mixedMoment B node3523 node3523Labels := rfl
  simpa [nodeValue3523, Sparse.eval] using hc.symm

theorem sound3530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3530 node3530Labels = Sparse.eval nodeValue3530 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3530) = mixedMoment B node3530 node3530Labels := rfl
  simpa [nodeValue3530, Sparse.eval] using hc.symm

theorem sound3558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3558 node3558Labels = Sparse.eval nodeValue3558 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3558) = mixedMoment B node3558 node3558Labels := rfl
  simpa [nodeValue3558, Sparse.eval] using hc.symm

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

theorem sound3608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3608 node3608Labels = Sparse.eval nodeValue3608 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3608) = mixedMoment B node3608 node3608Labels := rfl
  simpa [nodeValue3608, Sparse.eval] using hc.symm

theorem sound3615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3615 node3615Labels = Sparse.eval nodeValue3615 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3615) = mixedMoment B node3615 node3615Labels := rfl
  simpa [nodeValue3615, Sparse.eval] using hc.symm

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

theorem sound3796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3796 node3796Labels = Sparse.eval nodeValue3796 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3796) = mixedMoment B node3796 node3796Labels := rfl
  simpa [nodeValue3796, Sparse.eval] using hc.symm

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

theorem sound4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4079 node4079Labels = Sparse.eval nodeValue4079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4079) = mixedMoment B node4079 node4079Labels := rfl
  simpa [nodeValue4079, Sparse.eval] using hc.symm

theorem sound4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4080 node4080Labels = Sparse.eval nodeValue4080 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4080) = mixedMoment B node4080 node4080Labels := rfl
  simpa [nodeValue4080, Sparse.eval] using hc.symm

theorem sound4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4081 node4081Labels = Sparse.eval nodeValue4081 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4081) = mixedMoment B node4081 node4081Labels := rfl
  simpa [nodeValue4081, Sparse.eval] using hc.symm

theorem sound4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4090 node4090Labels = Sparse.eval nodeValue4090 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4090) = mixedMoment B node4090 node4090Labels := rfl
  simpa [nodeValue4090, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources60
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1925 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 0) (sourceB1925 + difference 0 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1337) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 0) (sourceB1925 + difference 0 2) sourceC1925) = raw27471 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27471; decide +kernel
    rw [ha]
    exact (canonical27471 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 1) (sourceB1925 + difference 1 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2442) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 1) (sourceB1925 + difference 1 2) sourceC1925) = raw27472 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27472; decide +kernel
    rw [ha]
    exact (canonical27472 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 2) (sourceB1925 + difference 2 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2618) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 2) (sourceB1925 + difference 2 2) sourceC1925) = raw27473 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27473; decide +kernel
    rw [ha]
    exact (canonical27473 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 3) (sourceB1925 + difference 3 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2437) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 3) (sourceB1925 + difference 3 2) sourceC1925) = raw27474 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27474; decide +kernel
    rw [ha]
    exact (canonical27474 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 4) (sourceB1925 + difference 4 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 4) (sourceB1925 + difference 4 2) sourceC1925) = raw27475 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27475; decide +kernel
    rw [ha]
    exact (canonical27475 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1925 + difference 2 5) (sourceB1925 + difference 5 2) sourceC1925) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1925 + difference 2 5) (sourceB1925 + difference 5 2) sourceC1925) = raw27476 := by
      apply Matrix.ext; unfold tripleCharges sourceA1925 sourceB1925 sourceC1925 difference raw27476; decide +kernel
    rw [ha]
    exact (canonical27476 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1925 + sourceB1925) sourceC1925) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1925 + sourceB1925) sourceC1925) = raw17313 := by
      apply Matrix.ext; unfold doubleCharges sourceA1925 sourceB1925 sourceC1925 raw17313; decide +kernel
    rw [ha]
    exact (canonical17313 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1925 sourceB1925 sourceC1925
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1925, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1926 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 0) (sourceB1926 + difference 0 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 0) (sourceB1926 + difference 0 0) sourceC1926) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 1) (sourceB1926 + difference 1 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 1) (sourceB1926 + difference 1 0) sourceC1926) = raw27478 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27478; decide +kernel
    rw [ha]
    exact (canonical27478 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 2) (sourceB1926 + difference 2 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3385) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 2) (sourceB1926 + difference 2 0) sourceC1926) = raw27479 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27479; decide +kernel
    rw [ha]
    exact (canonical27479 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 3) (sourceB1926 + difference 3 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3443) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 3) (sourceB1926 + difference 3 0) sourceC1926) = raw27480 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27480; decide +kernel
    rw [ha]
    exact (canonical27480 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 4) (sourceB1926 + difference 4 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 4) (sourceB1926 + difference 4 0) sourceC1926) = raw27481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27481; decide +kernel
    rw [ha]
    exact (canonical27481 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1926 + difference 0 5) (sourceB1926 + difference 5 0) sourceC1926) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2047) := by
    have ha : (tripleCharges (sourceA1926 + difference 0 5) (sourceB1926 + difference 5 0) sourceC1926) = raw27482 := by
      apply Matrix.ext; unfold tripleCharges sourceA1926 sourceB1926 sourceC1926 difference raw27482; decide +kernel
    rw [ha]
    exact (canonical27482 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1926 + sourceB1926) sourceC1926) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1926 + sourceB1926) sourceC1926) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1926 sourceB1926 sourceC1926 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1926 sourceB1926 sourceC1926
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1926, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1927 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1927 + difference 0 0) (sourceB1927 + difference 0 0) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1927 + difference 0 0) (sourceB1927 + difference 0 0) sourceC1927) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1927 + difference 1 0) (sourceB1927 + difference 0 1) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2049) := by
    have ha : (tripleCharges (sourceA1927 + difference 1 0) (sourceB1927 + difference 0 1) sourceC1927) = raw27483 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27483; decide +kernel
    rw [ha]
    exact (canonical27483 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1927 + difference 2 0) (sourceB1927 + difference 0 2) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2230) := by
    have ha : (tripleCharges (sourceA1927 + difference 2 0) (sourceB1927 + difference 0 2) sourceC1927) = raw27318 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27318; decide +kernel
    rw [ha]
    exact (canonical27318 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1927 + difference 3 0) (sourceB1927 + difference 0 3) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1998) := by
    have ha : (tripleCharges (sourceA1927 + difference 3 0) (sourceB1927 + difference 0 3) sourceC1927) = raw27484 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27484; decide +kernel
    rw [ha]
    exact (canonical27484 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1927 + difference 4 0) (sourceB1927 + difference 0 4) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2004) := by
    have ha : (tripleCharges (sourceA1927 + difference 4 0) (sourceB1927 + difference 0 4) sourceC1927) = raw27485 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27485; decide +kernel
    rw [ha]
    exact (canonical27485 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1927 + difference 5 0) (sourceB1927 + difference 0 5) sourceC1927) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1927 + difference 5 0) (sourceB1927 + difference 0 5) sourceC1927) = raw27486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1927 sourceB1927 sourceC1927 difference raw27486; decide +kernel
    rw [ha]
    exact (canonical27486 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1927 + sourceB1927) sourceC1927) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1927 + sourceB1927) sourceC1927) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1927 sourceB1927 sourceC1927 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1927 sourceB1927 sourceC1927
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1927, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1929 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1929 + difference 0 4) (sourceB1929 + difference 4 0) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1929 + difference 0 4) (sourceB1929 + difference 4 0) sourceC1929) = raw27481 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27481; decide +kernel
    rw [ha]
    exact (canonical27481 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1929 + difference 1 4) (sourceB1929 + difference 4 1) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1929 + difference 1 4) (sourceB1929 + difference 4 1) sourceC1929) = raw27491 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27491; decide +kernel
    rw [ha]
    exact (canonical27491 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1929 + difference 2 4) (sourceB1929 + difference 4 2) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3615) := by
    have ha : (tripleCharges (sourceA1929 + difference 2 4) (sourceB1929 + difference 4 2) sourceC1929) = raw27492 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27492; decide +kernel
    rw [ha]
    exact (canonical27492 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1929 + difference 3 4) (sourceB1929 + difference 4 3) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1929 + difference 3 4) (sourceB1929 + difference 4 3) sourceC1929) = raw27493 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27493; decide +kernel
    rw [ha]
    exact (canonical27493 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1929 + difference 4 4) (sourceB1929 + difference 4 4) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1929 + difference 4 4) (sourceB1929 + difference 4 4) sourceC1929) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1929 + difference 5 4) (sourceB1929 + difference 4 5) sourceC1929) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1929 + difference 5 4) (sourceB1929 + difference 4 5) sourceC1929) = raw27494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1929 sourceB1929 sourceC1929 difference raw27494; decide +kernel
    rw [ha]
    exact (canonical27494 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1929 + sourceB1929) sourceC1929) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1929 + sourceB1929) sourceC1929) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1929 sourceB1929 sourceC1929 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1929 sourceB1929 sourceC1929
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1929, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1930 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 0) (sourceB1930 + difference 0 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2006) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 0) (sourceB1930 + difference 0 5) sourceC1930) = raw27486 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27486; decide +kernel
    rw [ha]
    exact (canonical27486 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 1) (sourceB1930 + difference 1 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3353) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 1) (sourceB1930 + difference 1 5) sourceC1930) = raw27490 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27490; decide +kernel
    rw [ha]
    exact (canonical27490 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 2) (sourceB1930 + difference 2 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3343) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 2) (sourceB1930 + difference 2 5) sourceC1930) = raw27495 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27495; decide +kernel
    rw [ha]
    exact (canonical27495 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 3) (sourceB1930 + difference 3 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3339) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 3) (sourceB1930 + difference 3 5) sourceC1930) = raw27496 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27496; decide +kernel
    rw [ha]
    exact (canonical27496 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 4) (sourceB1930 + difference 4 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 4) (sourceB1930 + difference 4 5) sourceC1930) = raw27494 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27494; decide +kernel
    rw [ha]
    exact (canonical27494 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1930 + difference 5 5) (sourceB1930 + difference 5 5) sourceC1930) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3523) := by
    have ha : (tripleCharges (sourceA1930 + difference 5 5) (sourceB1930 + difference 5 5) sourceC1930) = raw27477 := by
      apply Matrix.ext; unfold tripleCharges sourceA1930 sourceB1930 sourceC1930 difference raw27477; decide +kernel
    rw [ha]
    exact (canonical27477 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1930 + sourceB1930) sourceC1930) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1930 + sourceB1930) sourceC1930) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1930 sourceB1930 sourceC1930 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1930 sourceB1930 sourceC1930
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1930, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1931 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 0) (sourceB1931 + difference 0 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2121) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 0) (sourceB1931 + difference 0 0) sourceC1931) = raw27497 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27497; decide +kernel
    rw [ha]
    exact (canonical27497 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 1) (sourceB1931 + difference 1 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2123) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 1) (sourceB1931 + difference 1 0) sourceC1931) = raw27498 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27498; decide +kernel
    rw [ha]
    exact (canonical27498 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 2) (sourceB1931 + difference 2 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2129) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 2) (sourceB1931 + difference 2 0) sourceC1931) = raw27499 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27499; decide +kernel
    rw [ha]
    exact (canonical27499 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 3) (sourceB1931 + difference 3 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2118) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 3) (sourceB1931 + difference 3 0) sourceC1931) = raw27500 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27500; decide +kernel
    rw [ha]
    exact (canonical27500 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 4) (sourceB1931 + difference 4 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 4) (sourceB1931 + difference 4 0) sourceC1931) = raw27501 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27501; decide +kernel
    rw [ha]
    exact (canonical27501 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1931 + difference 0 5) (sourceB1931 + difference 5 0) sourceC1931) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2735) := by
    have ha : (tripleCharges (sourceA1931 + difference 0 5) (sourceB1931 + difference 5 0) sourceC1931) = raw27502 := by
      apply Matrix.ext; unfold tripleCharges sourceA1931 sourceB1931 sourceC1931 difference raw27502; decide +kernel
    rw [ha]
    exact (canonical27502 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1931 + sourceB1931) sourceC1931) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1931 + sourceB1931) sourceC1931) = raw27503 := by
      apply Matrix.ext; unfold doubleCharges sourceA1931 sourceB1931 sourceC1931 raw27503; decide +kernel
    rw [ha]
    exact (canonical27503 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1931 sourceB1931 sourceC1931
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1931, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1932 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1932 + difference 0 2) (sourceB1932 + difference 2 0) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2553) := by
    have ha : (tripleCharges (sourceA1932 + difference 0 2) (sourceB1932 + difference 2 0) sourceC1932) = raw27504 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27504; decide +kernel
    rw [ha]
    exact (canonical27504 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1932 + difference 1 2) (sourceB1932 + difference 2 1) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2482) := by
    have ha : (tripleCharges (sourceA1932 + difference 1 2) (sourceB1932 + difference 2 1) sourceC1932) = raw27505 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27505; decide +kernel
    rw [ha]
    exact (canonical27505 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1932 + difference 2 2) (sourceB1932 + difference 2 2) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2542) := by
    have ha : (tripleCharges (sourceA1932 + difference 2 2) (sourceB1932 + difference 2 2) sourceC1932) = raw27506 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27506; decide +kernel
    rw [ha]
    exact (canonical27506 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1932 + difference 3 2) (sourceB1932 + difference 2 3) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2425) := by
    have ha : (tripleCharges (sourceA1932 + difference 3 2) (sourceB1932 + difference 2 3) sourceC1932) = raw27507 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27507; decide +kernel
    rw [ha]
    exact (canonical27507 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1932 + difference 4 2) (sourceB1932 + difference 2 4) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2347) := by
    have ha : (tripleCharges (sourceA1932 + difference 4 2) (sourceB1932 + difference 2 4) sourceC1932) = raw27508 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27508; decide +kernel
    rw [ha]
    exact (canonical27508 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1932 + difference 5 2) (sourceB1932 + difference 2 5) sourceC1932) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1148) := by
    have ha : (tripleCharges (sourceA1932 + difference 5 2) (sourceB1932 + difference 2 5) sourceC1932) = raw27509 := by
      apply Matrix.ext; unfold tripleCharges sourceA1932 sourceB1932 sourceC1932 difference raw27509; decide +kernel
    rw [ha]
    exact (canonical27509 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1932 + sourceB1932) sourceC1932) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1932 + sourceB1932) sourceC1932) = raw24746 := by
      apply Matrix.ext; unfold doubleCharges sourceA1932 sourceB1932 sourceC1932 raw24746; decide +kernel
    rw [ha]
    exact (canonical24746 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1932 sourceB1932 sourceC1932
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1932, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1933 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 0) (sourceB1933 + difference 0 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 0) (sourceB1933 + difference 0 0) sourceC1933) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 1) (sourceB1933 + difference 1 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 1) (sourceB1933 + difference 1 0) sourceC1933) = raw27511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27511; decide +kernel
    rw [ha]
    exact (canonical27511 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 2) (sourceB1933 + difference 2 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3437) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 2) (sourceB1933 + difference 2 0) sourceC1933) = raw27512 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27512; decide +kernel
    rw [ha]
    exact (canonical27512 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 3) (sourceB1933 + difference 3 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 3) (sourceB1933 + difference 3 0) sourceC1933) = raw27513 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27513; decide +kernel
    rw [ha]
    exact (canonical27513 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 4) (sourceB1933 + difference 4 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3434) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 4) (sourceB1933 + difference 4 0) sourceC1933) = raw27514 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27514; decide +kernel
    rw [ha]
    exact (canonical27514 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1933 + difference 0 5) (sourceB1933 + difference 5 0) sourceC1933) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3432) := by
    have ha : (tripleCharges (sourceA1933 + difference 0 5) (sourceB1933 + difference 5 0) sourceC1933) = raw27515 := by
      apply Matrix.ext; unfold tripleCharges sourceA1933 sourceB1933 sourceC1933 difference raw27515; decide +kernel
    rw [ha]
    exact (canonical27515 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1933 + sourceB1933) sourceC1933) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1933 + sourceB1933) sourceC1933) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1933 sourceB1933 sourceC1933 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1933 sourceB1933 sourceC1933
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1933, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1934 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1934 + difference 0 0) (sourceB1934 + difference 0 0) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1934 + difference 0 0) (sourceB1934 + difference 0 0) sourceC1934) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1934 + difference 1 0) (sourceB1934 + difference 0 1) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2015) := by
    have ha : (tripleCharges (sourceA1934 + difference 1 0) (sourceB1934 + difference 0 1) sourceC1934) = raw27516 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27516; decide +kernel
    rw [ha]
    exact (canonical27516 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1934 + difference 2 0) (sourceB1934 + difference 0 2) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1934 + difference 2 0) (sourceB1934 + difference 0 2) sourceC1934) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1934 + difference 3 0) (sourceB1934 + difference 0 3) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1989) := by
    have ha : (tripleCharges (sourceA1934 + difference 3 0) (sourceB1934 + difference 0 3) sourceC1934) = raw27517 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27517; decide +kernel
    rw [ha]
    exact (canonical27517 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1934 + difference 4 0) (sourceB1934 + difference 0 4) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA1934 + difference 4 0) (sourceB1934 + difference 0 4) sourceC1934) = raw27518 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27518; decide +kernel
    rw [ha]
    exact (canonical27518 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1934 + difference 5 0) (sourceB1934 + difference 0 5) sourceC1934) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1986) := by
    have ha : (tripleCharges (sourceA1934 + difference 5 0) (sourceB1934 + difference 0 5) sourceC1934) = raw27519 := by
      apply Matrix.ext; unfold tripleCharges sourceA1934 sourceB1934 sourceC1934 difference raw27519; decide +kernel
    rw [ha]
    exact (canonical27519 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1934 + sourceB1934) sourceC1934) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1934 + sourceB1934) sourceC1934) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1934 sourceB1934 sourceC1934 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1934 sourceB1934 sourceC1934
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1934, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1935 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1935 + difference 0 1) (sourceB1935 + difference 1 0) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3519) := by
    have ha : (tripleCharges (sourceA1935 + difference 0 1) (sourceB1935 + difference 1 0) sourceC1935) = raw27511 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27511; decide +kernel
    rw [ha]
    exact (canonical27511 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1935 + difference 1 1) (sourceB1935 + difference 1 1) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1935 + difference 1 1) (sourceB1935 + difference 1 1) sourceC1935) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1935 + difference 2 1) (sourceB1935 + difference 1 2) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1935 + difference 2 1) (sourceB1935 + difference 1 2) sourceC1935) = raw27446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27446; decide +kernel
    rw [ha]
    exact (canonical27446 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1935 + difference 3 1) (sourceB1935 + difference 1 3) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3368) := by
    have ha : (tripleCharges (sourceA1935 + difference 3 1) (sourceB1935 + difference 1 3) sourceC1935) = raw27520 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27520; decide +kernel
    rw [ha]
    exact (canonical27520 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1935 + difference 4 1) (sourceB1935 + difference 1 4) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3432) := by
    have ha : (tripleCharges (sourceA1935 + difference 4 1) (sourceB1935 + difference 1 4) sourceC1935) = raw27521 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27521; decide +kernel
    rw [ha]
    exact (canonical27521 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1935 + difference 5 1) (sourceB1935 + difference 1 5) sourceC1935) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1996) := by
    have ha : (tripleCharges (sourceA1935 + difference 5 1) (sourceB1935 + difference 1 5) sourceC1935) = raw27522 := by
      apply Matrix.ext; unfold tripleCharges sourceA1935 sourceB1935 sourceC1935 difference raw27522; decide +kernel
    rw [ha]
    exact (canonical27522 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1935 + sourceB1935) sourceC1935) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1935 + sourceB1935) sourceC1935) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1935 sourceB1935 sourceC1935 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1935 sourceB1935 sourceC1935
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1935, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1936 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 0) (sourceB1936 + difference 0 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2203) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 0) (sourceB1936 + difference 0 2) sourceC1936) = raw27368 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27368; decide +kernel
    rw [ha]
    exact (canonical27368 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 1) (sourceB1936 + difference 1 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3468) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 1) (sourceB1936 + difference 1 2) sourceC1936) = raw27446 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27446; decide +kernel
    rw [ha]
    exact (canonical27446 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 2) (sourceB1936 + difference 2 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3513) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 2) (sourceB1936 + difference 2 2) sourceC1936) = raw27510 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27510; decide +kernel
    rw [ha]
    exact (canonical27510 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 3) (sourceB1936 + difference 3 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3608) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 3) (sourceB1936 + difference 3 2) sourceC1936) = raw27523 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27523; decide +kernel
    rw [ha]
    exact (canonical27523 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 4) (sourceB1936 + difference 4 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3530) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 4) (sourceB1936 + difference 4 2) sourceC1936) = raw27524 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27524; decide +kernel
    rw [ha]
    exact (canonical27524 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1936 + difference 2 5) (sourceB1936 + difference 5 2) sourceC1936) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3481) := by
    have ha : (tripleCharges (sourceA1936 + difference 2 5) (sourceB1936 + difference 5 2) sourceC1936) = raw27359 := by
      apply Matrix.ext; unfold tripleCharges sourceA1936 sourceB1936 sourceC1936 difference raw27359; decide +kernel
    rw [ha]
    exact (canonical27359 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1936 + sourceB1936) sourceC1936) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4081) := by
    have ha : (doubleCharges (sourceA1936 + sourceB1936) sourceC1936) = raw27319 := by
      apply Matrix.ext; unfold doubleCharges sourceA1936 sourceB1936 sourceC1936 raw27319; decide +kernel
    rw [ha]
    exact (canonical27319 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1936 sourceB1936 sourceC1936
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1936, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1937 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1937 + difference 0 2) (sourceB1937 + difference 2 0) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA1937 + difference 0 2) (sourceB1937 + difference 2 0) sourceC1937) = raw27525 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27525; decide +kernel
    rw [ha]
    exact (canonical27525 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1937 + difference 1 2) (sourceB1937 + difference 2 1) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2485) := by
    have ha : (tripleCharges (sourceA1937 + difference 1 2) (sourceB1937 + difference 2 1) sourceC1937) = raw27526 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27526; decide +kernel
    rw [ha]
    exact (canonical27526 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1937 + difference 2 2) (sourceB1937 + difference 2 2) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1937 + difference 2 2) (sourceB1937 + difference 2 2) sourceC1937) = raw27527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27527; decide +kernel
    rw [ha]
    exact (canonical27527 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1937 + difference 3 2) (sourceB1937 + difference 2 3) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1937 + difference 3 2) (sourceB1937 + difference 2 3) sourceC1937) = raw27528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27528; decide +kernel
    rw [ha]
    exact (canonical27528 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1937 + difference 4 2) (sourceB1937 + difference 2 4) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2422) := by
    have ha : (tripleCharges (sourceA1937 + difference 4 2) (sourceB1937 + difference 2 4) sourceC1937) = raw27529 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27529; decide +kernel
    rw [ha]
    exact (canonical27529 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1937 + difference 5 2) (sourceB1937 + difference 2 5) sourceC1937) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1937 + difference 5 2) (sourceB1937 + difference 2 5) sourceC1937) = raw27530 := by
      apply Matrix.ext; unfold tripleCharges sourceA1937 sourceB1937 sourceC1937 difference raw27530; decide +kernel
    rw [ha]
    exact (canonical27530 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1937 + sourceB1937) sourceC1937) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1937 + sourceB1937) sourceC1937) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1937 sourceB1937 sourceC1937 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1937 sourceB1937 sourceC1937
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1937, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1938 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 0) (sourceB1938 + difference 0 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1150) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 0) (sourceB1938 + difference 0 3) sourceC1938) = raw24557 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw24557; decide +kernel
    rw [ha]
    exact (canonical24557 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 1) (sourceB1938 + difference 1 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2349) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 1) (sourceB1938 + difference 1 3) sourceC1938) = raw27531 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27531; decide +kernel
    rw [ha]
    exact (canonical27531 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 2) (sourceB1938 + difference 2 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2429) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 2) (sourceB1938 + difference 2 3) sourceC1938) = raw27528 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27528; decide +kernel
    rw [ha]
    exact (canonical27528 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 3) (sourceB1938 + difference 3 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 3) (sourceB1938 + difference 3 3) sourceC1938) = raw27527 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27527; decide +kernel
    rw [ha]
    exact (canonical27527 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 4) (sourceB1938 + difference 4 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2543) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 4) (sourceB1938 + difference 4 3) sourceC1938) = raw27532 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw27532; decide +kernel
    rw [ha]
    exact (canonical27532 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1938 + difference 3 5) (sourceB1938 + difference 5 3) sourceC1938) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2556) := by
    have ha : (tripleCharges (sourceA1938 + difference 3 5) (sourceB1938 + difference 5 3) sourceC1938) = raw24553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1938 sourceB1938 sourceC1938 difference raw24553; decide +kernel
    rw [ha]
    exact (canonical24553 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1938 + sourceB1938) sourceC1938) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1938 + sourceB1938) sourceC1938) = raw24552 := by
      apply Matrix.ext; unfold doubleCharges sourceA1938 sourceB1938 sourceC1938 raw24552; decide +kernel
    rw [ha]
    exact (canonical24552 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1938 sourceB1938 sourceC1938
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1938, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1939 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 0) (sourceB1939 + difference 0 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2071) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 0) (sourceB1939 + difference 0 0) sourceC1939) = raw27533 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27533; decide +kernel
    rw [ha]
    exact (canonical27533 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 1) (sourceB1939 + difference 1 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2073) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 1) (sourceB1939 + difference 1 0) sourceC1939) = raw27534 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27534; decide +kernel
    rw [ha]
    exact (canonical27534 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 2) (sourceB1939 + difference 2 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2086) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 2) (sourceB1939 + difference 2 0) sourceC1939) = raw27535 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27535; decide +kernel
    rw [ha]
    exact (canonical27535 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 3) (sourceB1939 + difference 3 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2077) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 3) (sourceB1939 + difference 3 0) sourceC1939) = raw27536 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27536; decide +kernel
    rw [ha]
    exact (canonical27536 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 4) (sourceB1939 + difference 4 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2191) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 4) (sourceB1939 + difference 4 0) sourceC1939) = raw27537 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27537; decide +kernel
    rw [ha]
    exact (canonical27537 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1939 + difference 0 5) (sourceB1939 + difference 5 0) sourceC1939) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3558) := by
    have ha : (tripleCharges (sourceA1939 + difference 0 5) (sourceB1939 + difference 5 0) sourceC1939) = raw27538 := by
      apply Matrix.ext; unfold tripleCharges sourceA1939 sourceB1939 sourceC1939 difference raw27538; decide +kernel
    rw [ha]
    exact (canonical27538 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1939 + sourceB1939) sourceC1939) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4079) := by
    have ha : (doubleCharges (sourceA1939 + sourceB1939) sourceC1939) = raw27539 := by
      apply Matrix.ext; unfold doubleCharges sourceA1939 sourceB1939 sourceC1939 raw27539; decide +kernel
    rw [ha]
    exact (canonical27539 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1939 sourceB1939 sourceC1939
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1939, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1940 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 0) (sourceB1940 + difference 0 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2454) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 0) (sourceB1940 + difference 0 0) sourceC1940) = raw27540 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27540; decide +kernel
    rw [ha]
    exact (canonical27540 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 1) (sourceB1940 + difference 1 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2456) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 1) (sourceB1940 + difference 1 0) sourceC1940) = raw27541 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27541; decide +kernel
    rw [ha]
    exact (canonical27541 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 2) (sourceB1940 + difference 2 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2491) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 2) (sourceB1940 + difference 2 0) sourceC1940) = raw27542 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27542; decide +kernel
    rw [ha]
    exact (canonical27542 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 3) (sourceB1940 + difference 3 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2462) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 3) (sourceB1940 + difference 3 0) sourceC1940) = raw27543 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27543; decide +kernel
    rw [ha]
    exact (canonical27543 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 4) (sourceB1940 + difference 4 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2698) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 4) (sourceB1940 + difference 4 0) sourceC1940) = raw27544 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27544; decide +kernel
    rw [ha]
    exact (canonical27544 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1940 + difference 0 5) (sourceB1940 + difference 5 0) sourceC1940) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3796) := by
    have ha : (tripleCharges (sourceA1940 + difference 0 5) (sourceB1940 + difference 5 0) sourceC1940) = raw27545 := by
      apply Matrix.ext; unfold tripleCharges sourceA1940 sourceB1940 sourceC1940 difference raw27545; decide +kernel
    rw [ha]
    exact (canonical27545 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1940 + sourceB1940) sourceC1940) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1940 + sourceB1940) sourceC1940) = raw27546 := by
      apply Matrix.ext; unfold doubleCharges sourceA1940 sourceB1940 sourceC1940 raw27546; decide +kernel
    rw [ha]
    exact (canonical27546 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1940 sourceB1940 sourceC1940
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1940, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1942 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 0) (sourceB1942 + difference 0 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1992) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 0) (sourceB1942 + difference 0 0) sourceC1942) = raw27551 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27551; decide +kernel
    rw [ha]
    exact (canonical27551 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 1) (sourceB1942 + difference 1 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1994) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 1) (sourceB1942 + difference 1 0) sourceC1942) = raw27552 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27552; decide +kernel
    rw [ha]
    exact (canonical27552 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 2) (sourceB1942 + difference 2 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2031) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 2) (sourceB1942 + difference 2 0) sourceC1942) = raw27553 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27553; decide +kernel
    rw [ha]
    exact (canonical27553 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 3) (sourceB1942 + difference 3 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2000) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 3) (sourceB1942 + difference 3 0) sourceC1942) = raw27554 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27554; decide +kernel
    rw [ha]
    exact (canonical27554 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 4) (sourceB1942 + difference 4 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2216) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 4) (sourceB1942 + difference 4 0) sourceC1942) = raw27555 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27555; decide +kernel
    rw [ha]
    exact (canonical27555 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1942 + difference 0 5) (sourceB1942 + difference 5 0) sourceC1942) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3517) := by
    have ha : (tripleCharges (sourceA1942 + difference 0 5) (sourceB1942 + difference 5 0) sourceC1942) = raw27556 := by
      apply Matrix.ext; unfold tripleCharges sourceA1942 sourceB1942 sourceC1942 difference raw27556; decide +kernel
    rw [ha]
    exact (canonical27556 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1942 + sourceB1942) sourceC1942) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4080) := by
    have ha : (doubleCharges (sourceA1942 + sourceB1942) sourceC1942) = raw27557 := by
      apply Matrix.ext; unfold doubleCharges sourceA1942 sourceB1942 sourceC1942 raw27557; decide +kernel
    rw [ha]
    exact (canonical27557 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1942 sourceB1942 sourceC1942
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1942, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1632 : Integer.Sparse.reindex keyMap MixedData.row1632 = numericRow1632 := by decide +kernel

theorem numericCheck1632 (x : Master → ℝ) : Integer.Sparse.eval numericRow1632 x =
    (1 : ℝ) * reducedSource1632 x := by
  norm_num [numericRow1632, reducedSource1632, Integer.Sparse.eval, Sparse.eval, nodeValue1337, nodeValue2437, nodeValue2442, nodeValue2485, nodeValue2618, nodeValue2954, nodeValue4091]

theorem reindexCheck1633 : Integer.Sparse.reindex keyMap MixedData.row1633 = numericRow1633 := by decide +kernel

theorem numericCheck1633 (x : Master → ℝ) : Integer.Sparse.eval numericRow1633 x =
    (1 : ℝ) * reducedSource1633 x := by
  norm_num [numericRow1633, reducedSource1633, Integer.Sparse.eval, Sparse.eval, nodeValue2047, nodeValue3385, nodeValue3443, nodeValue3468, nodeValue3523, nodeValue3530, nodeValue4081]

theorem reindexCheck1634 : Integer.Sparse.reindex keyMap MixedData.row1634 = numericRow1634 := by decide +kernel

theorem numericCheck1634 (x : Master → ℝ) : Integer.Sparse.eval numericRow1634 x =
    (1 : ℝ) * reducedSource1634 x := by
  norm_num [numericRow1634, reducedSource1634, Integer.Sparse.eval, Sparse.eval, nodeValue1998, nodeValue2004, nodeValue2006, nodeValue2049, nodeValue2230, nodeValue3523, nodeValue4081]

theorem reindexCheck1635 : Integer.Sparse.reindex keyMap MixedData.row1635 = numericRow1635 := by decide +kernel

theorem numericCheck1635 (x : Master → ℝ) : Integer.Sparse.eval numericRow1635 x =
    (1 : ℝ) * reducedSource1635 x := by
  norm_num [numericRow1635, reducedSource1635, Integer.Sparse.eval, Sparse.eval, nodeValue3468, nodeValue3519, nodeValue3523, nodeValue3615, nodeValue4081]

theorem reindexCheck1636 : Integer.Sparse.reindex keyMap MixedData.row1636 = numericRow1636 := by decide +kernel

theorem numericCheck1636 (x : Master → ℝ) : Integer.Sparse.eval numericRow1636 x =
    (1 : ℝ) * reducedSource1636 x := by
  norm_num [numericRow1636, reducedSource1636, Integer.Sparse.eval, Sparse.eval, nodeValue2006, nodeValue3339, nodeValue3343, nodeValue3353, nodeValue3468, nodeValue3523, nodeValue4081]

theorem reindexCheck1637 : Integer.Sparse.reindex keyMap MixedData.row1637 = numericRow1637 := by decide +kernel

theorem numericCheck1637 (x : Master → ℝ) : Integer.Sparse.eval numericRow1637 x =
    (1 : ℝ) * reducedSource1637 x := by
  norm_num [numericRow1637, reducedSource1637, Integer.Sparse.eval, Sparse.eval, nodeValue2118, nodeValue2121, nodeValue2123, nodeValue2129, nodeValue2216, nodeValue2735, nodeValue4080]

theorem reindexCheck1638 : Integer.Sparse.reindex keyMap MixedData.row1638 = numericRow1638 := by decide +kernel

theorem numericCheck1638 (x : Master → ℝ) : Integer.Sparse.eval numericRow1638 x =
    (1 : ℝ) * reducedSource1638 x := by
  norm_num [numericRow1638, reducedSource1638, Integer.Sparse.eval, Sparse.eval, nodeValue1148, nodeValue2347, nodeValue2425, nodeValue2482, nodeValue2542, nodeValue2553, nodeValue4092]

theorem reindexCheck1639 : Integer.Sparse.reindex keyMap MixedData.row1639 = numericRow1639 := by decide +kernel

theorem numericCheck1639 (x : Master → ℝ) : Integer.Sparse.eval numericRow1639 x =
    (1 : ℝ) * reducedSource1639 x := by
  norm_num [numericRow1639, reducedSource1639, Integer.Sparse.eval, Sparse.eval, nodeValue3432, nodeValue3434, nodeValue3437, nodeValue3481, nodeValue3513, nodeValue3519, nodeValue4081]

theorem reindexCheck1640 : Integer.Sparse.reindex keyMap MixedData.row1640 = numericRow1640 := by decide +kernel

theorem numericCheck1640 (x : Master → ℝ) : Integer.Sparse.eval numericRow1640 x =
    (1 : ℝ) * reducedSource1640 x := by
  norm_num [numericRow1640, reducedSource1640, Integer.Sparse.eval, Sparse.eval, nodeValue1986, nodeValue1989, nodeValue1996, nodeValue2015, nodeValue2203, nodeValue3513, nodeValue4081]

theorem reindexCheck1641 : Integer.Sparse.reindex keyMap MixedData.row1641 = numericRow1641 := by decide +kernel

theorem numericCheck1641 (x : Master → ℝ) : Integer.Sparse.eval numericRow1641 x =
    (1 : ℝ) * reducedSource1641 x := by
  norm_num [numericRow1641, reducedSource1641, Integer.Sparse.eval, Sparse.eval, nodeValue1996, nodeValue3368, nodeValue3432, nodeValue3468, nodeValue3513, nodeValue3519, nodeValue4081]

theorem reindexCheck1642 : Integer.Sparse.reindex keyMap MixedData.row1642 = numericRow1642 := by decide +kernel

theorem numericCheck1642 (x : Master → ℝ) : Integer.Sparse.eval numericRow1642 x =
    (1 : ℝ) * reducedSource1642 x := by
  norm_num [numericRow1642, reducedSource1642, Integer.Sparse.eval, Sparse.eval, nodeValue2203, nodeValue3468, nodeValue3481, nodeValue3513, nodeValue3530, nodeValue3608, nodeValue4081]

theorem reindexCheck1643 : Integer.Sparse.reindex keyMap MixedData.row1643 = numericRow1643 := by decide +kernel

theorem numericCheck1643 (x : Master → ℝ) : Integer.Sparse.eval numericRow1643 x =
    (1 : ℝ) * reducedSource1643 x := by
  norm_num [numericRow1643, reducedSource1643, Integer.Sparse.eval, Sparse.eval, nodeValue1327, nodeValue2422, nodeValue2429, nodeValue2485, nodeValue2543, nodeValue2924, nodeValue4091]

theorem reindexCheck1644 : Integer.Sparse.reindex keyMap MixedData.row1644 = numericRow1644 := by decide +kernel

theorem numericCheck1644 (x : Master → ℝ) : Integer.Sparse.eval numericRow1644 x =
    (1 : ℝ) * reducedSource1644 x := by
  norm_num [numericRow1644, reducedSource1644, Integer.Sparse.eval, Sparse.eval, nodeValue1150, nodeValue2349, nodeValue2429, nodeValue2543, nodeValue2556, nodeValue4091]

theorem reindexCheck1645 : Integer.Sparse.reindex keyMap MixedData.row1645 = numericRow1645 := by decide +kernel

theorem numericCheck1645 (x : Master → ℝ) : Integer.Sparse.eval numericRow1645 x =
    (1 : ℝ) * reducedSource1645 x := by
  norm_num [numericRow1645, reducedSource1645, Integer.Sparse.eval, Sparse.eval, nodeValue2071, nodeValue2073, nodeValue2077, nodeValue2086, nodeValue2191, nodeValue3558, nodeValue4079]

theorem reindexCheck1646 : Integer.Sparse.reindex keyMap MixedData.row1646 = numericRow1646 := by decide +kernel

theorem numericCheck1646 (x : Master → ℝ) : Integer.Sparse.eval numericRow1646 x =
    (1 : ℝ) * reducedSource1646 x := by
  norm_num [numericRow1646, reducedSource1646, Integer.Sparse.eval, Sparse.eval, nodeValue2454, nodeValue2456, nodeValue2462, nodeValue2491, nodeValue2698, nodeValue3796, nodeValue4090]

theorem reindexCheck1647 : Integer.Sparse.reindex keyMap MixedData.row1647 = numericRow1647 := by decide +kernel

theorem numericCheck1647 (x : Master → ℝ) : Integer.Sparse.eval numericRow1647 x =
    (1 : ℝ) * reducedSource1647 x := by
  norm_num [numericRow1647, reducedSource1647, Integer.Sparse.eval, Sparse.eval, nodeValue1992, nodeValue1994, nodeValue2000, nodeValue2031, nodeValue2216, nodeValue3517, nodeValue4080]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1632 (mixedVector B) = 0 := by
  have h1337 : mixedVector B (Sum.inr 1337) = Sparse.eval nodeValue1337 (mixedVector B) := by
    change mixedMoment B node1337 node1337Labels = _
    exact sound1337 B hB hF
  have h2437 : mixedVector B (Sum.inr 2437) = Sparse.eval nodeValue2437 (mixedVector B) := by
    change mixedMoment B node2437 node2437Labels = _
    exact sound2437 B hB hF
  have h2442 : mixedVector B (Sum.inr 2442) = Sparse.eval nodeValue2442 (mixedVector B) := by
    change mixedMoment B node2442 node2442Labels = _
    exact sound2442 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2618 : mixedVector B (Sum.inr 2618) = Sparse.eval nodeValue2618 (mixedVector B) := by
    change mixedMoment B node2618 node2618Labels = _
    exact sound2618 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1925, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1337, h2437, h2442, h2485, h2618, h2954, h4091, reducedSource1632] using sourceEq1925 B hB

theorem rowSound1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1632 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1632, numericCheck1632, reducedZero1632 B hB hF, mul_zero]

theorem reducedZero1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1633 (mixedVector B) = 0 := by
  have h2047 : mixedVector B (Sum.inr 2047) = Sparse.eval nodeValue2047 (mixedVector B) := by
    change mixedMoment B node2047 node2047Labels = _
    exact sound2047 B hB hF
  have h3385 : mixedVector B (Sum.inr 3385) = Sparse.eval nodeValue3385 (mixedVector B) := by
    change mixedMoment B node3385 node3385Labels = _
    exact sound3385 B hB hF
  have h3443 : mixedVector B (Sum.inr 3443) = Sparse.eval nodeValue3443 (mixedVector B) := by
    change mixedMoment B node3443 node3443Labels = _
    exact sound3443 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1926, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2047, h3385, h3443, h3468, h3523, h3530, h4081, reducedSource1633] using sourceEq1926 B hB

theorem rowSound1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1633 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1633, numericCheck1633, reducedZero1633 B hB hF, mul_zero]

theorem reducedZero1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1634 (mixedVector B) = 0 := by
  have h1998 : mixedVector B (Sum.inr 1998) = Sparse.eval nodeValue1998 (mixedVector B) := by
    change mixedMoment B node1998 node1998Labels = _
    exact sound1998 B hB hF
  have h2004 : mixedVector B (Sum.inr 2004) = Sparse.eval nodeValue2004 (mixedVector B) := by
    change mixedMoment B node2004 node2004Labels = _
    exact sound2004 B hB hF
  have h2006 : mixedVector B (Sum.inr 2006) = Sparse.eval nodeValue2006 (mixedVector B) := by
    change mixedMoment B node2006 node2006Labels = _
    exact sound2006 B hB hF
  have h2049 : mixedVector B (Sum.inr 2049) = Sparse.eval nodeValue2049 (mixedVector B) := by
    change mixedMoment B node2049 node2049Labels = _
    exact sound2049 B hB hF
  have h2230 : mixedVector B (Sum.inr 2230) = Sparse.eval nodeValue2230 (mixedVector B) := by
    change mixedMoment B node2230 node2230Labels = _
    exact sound2230 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1927, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1998, h2004, h2006, h2049, h2230, h3523, h4081, reducedSource1634] using sourceEq1927 B hB

theorem rowSound1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1634 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1634, numericCheck1634, reducedZero1634 B hB hF, mul_zero]

theorem reducedZero1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1635 (mixedVector B) = 0 := by
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h3615 : mixedVector B (Sum.inr 3615) = Sparse.eval nodeValue3615 (mixedVector B) := by
    change mixedMoment B node3615 node3615Labels = _
    exact sound3615 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1929, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3468, h3519, h3523, h3615, h4081, reducedSource1635] using sourceEq1929 B hB

theorem rowSound1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1635 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1635, numericCheck1635, reducedZero1635 B hB hF, mul_zero]

theorem reducedZero1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1636 (mixedVector B) = 0 := by
  have h2006 : mixedVector B (Sum.inr 2006) = Sparse.eval nodeValue2006 (mixedVector B) := by
    change mixedMoment B node2006 node2006Labels = _
    exact sound2006 B hB hF
  have h3339 : mixedVector B (Sum.inr 3339) = Sparse.eval nodeValue3339 (mixedVector B) := by
    change mixedMoment B node3339 node3339Labels = _
    exact sound3339 B hB hF
  have h3343 : mixedVector B (Sum.inr 3343) = Sparse.eval nodeValue3343 (mixedVector B) := by
    change mixedMoment B node3343 node3343Labels = _
    exact sound3343 B hB hF
  have h3353 : mixedVector B (Sum.inr 3353) = Sparse.eval nodeValue3353 (mixedVector B) := by
    change mixedMoment B node3353 node3353Labels = _
    exact sound3353 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3523 : mixedVector B (Sum.inr 3523) = Sparse.eval nodeValue3523 (mixedVector B) := by
    change mixedMoment B node3523 node3523Labels = _
    exact sound3523 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1930, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2006, h3339, h3343, h3353, h3468, h3523, h4081, reducedSource1636] using sourceEq1930 B hB

theorem rowSound1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1636 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1636, numericCheck1636, reducedZero1636 B hB hF, mul_zero]

theorem reducedZero1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1637 (mixedVector B) = 0 := by
  have h2118 : mixedVector B (Sum.inr 2118) = Sparse.eval nodeValue2118 (mixedVector B) := by
    change mixedMoment B node2118 node2118Labels = _
    exact sound2118 B hB hF
  have h2121 : mixedVector B (Sum.inr 2121) = Sparse.eval nodeValue2121 (mixedVector B) := by
    change mixedMoment B node2121 node2121Labels = _
    exact sound2121 B hB hF
  have h2123 : mixedVector B (Sum.inr 2123) = Sparse.eval nodeValue2123 (mixedVector B) := by
    change mixedMoment B node2123 node2123Labels = _
    exact sound2123 B hB hF
  have h2129 : mixedVector B (Sum.inr 2129) = Sparse.eval nodeValue2129 (mixedVector B) := by
    change mixedMoment B node2129 node2129Labels = _
    exact sound2129 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h2735 : mixedVector B (Sum.inr 2735) = Sparse.eval nodeValue2735 (mixedVector B) := by
    change mixedMoment B node2735 node2735Labels = _
    exact sound2735 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1931, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2118, h2121, h2123, h2129, h2216, h2735, h4080, reducedSource1637] using sourceEq1931 B hB

theorem rowSound1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1637 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1637, numericCheck1637, reducedZero1637 B hB hF, mul_zero]

theorem reducedZero1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1638 (mixedVector B) = 0 := by
  have h1148 : mixedVector B (Sum.inr 1148) = Sparse.eval nodeValue1148 (mixedVector B) := by
    change mixedMoment B node1148 node1148Labels = _
    exact sound1148 B hB hF
  have h2347 : mixedVector B (Sum.inr 2347) = Sparse.eval nodeValue2347 (mixedVector B) := by
    change mixedMoment B node2347 node2347Labels = _
    exact sound2347 B hB hF
  have h2425 : mixedVector B (Sum.inr 2425) = Sparse.eval nodeValue2425 (mixedVector B) := by
    change mixedMoment B node2425 node2425Labels = _
    exact sound2425 B hB hF
  have h2482 : mixedVector B (Sum.inr 2482) = Sparse.eval nodeValue2482 (mixedVector B) := by
    change mixedMoment B node2482 node2482Labels = _
    exact sound2482 B hB hF
  have h2542 : mixedVector B (Sum.inr 2542) = Sparse.eval nodeValue2542 (mixedVector B) := by
    change mixedMoment B node2542 node2542Labels = _
    exact sound2542 B hB hF
  have h2553 : mixedVector B (Sum.inr 2553) = Sparse.eval nodeValue2553 (mixedVector B) := by
    change mixedMoment B node2553 node2553Labels = _
    exact sound2553 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1932, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1148, h2347, h2425, h2482, h2542, h2553, h4092, reducedSource1638] using sourceEq1932 B hB

theorem rowSound1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1638 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1638, numericCheck1638, reducedZero1638 B hB hF, mul_zero]

theorem reducedZero1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1639 (mixedVector B) = 0 := by
  have h3432 : mixedVector B (Sum.inr 3432) = Sparse.eval nodeValue3432 (mixedVector B) := by
    change mixedMoment B node3432 node3432Labels = _
    exact sound3432 B hB hF
  have h3434 : mixedVector B (Sum.inr 3434) = Sparse.eval nodeValue3434 (mixedVector B) := by
    change mixedMoment B node3434 node3434Labels = _
    exact sound3434 B hB hF
  have h3437 : mixedVector B (Sum.inr 3437) = Sparse.eval nodeValue3437 (mixedVector B) := by
    change mixedMoment B node3437 node3437Labels = _
    exact sound3437 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1933, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h3432, h3434, h3437, h3481, h3513, h3519, h4081, reducedSource1639] using sourceEq1933 B hB

theorem rowSound1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1639 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1639, numericCheck1639, reducedZero1639 B hB hF, mul_zero]

theorem reducedZero1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1640 (mixedVector B) = 0 := by
  have h1986 : mixedVector B (Sum.inr 1986) = Sparse.eval nodeValue1986 (mixedVector B) := by
    change mixedMoment B node1986 node1986Labels = _
    exact sound1986 B hB hF
  have h1989 : mixedVector B (Sum.inr 1989) = Sparse.eval nodeValue1989 (mixedVector B) := by
    change mixedMoment B node1989 node1989Labels = _
    exact sound1989 B hB hF
  have h1996 : mixedVector B (Sum.inr 1996) = Sparse.eval nodeValue1996 (mixedVector B) := by
    change mixedMoment B node1996 node1996Labels = _
    exact sound1996 B hB hF
  have h2015 : mixedVector B (Sum.inr 2015) = Sparse.eval nodeValue2015 (mixedVector B) := by
    change mixedMoment B node2015 node2015Labels = _
    exact sound2015 B hB hF
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1934, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1986, h1989, h1996, h2015, h2203, h3513, h4081, reducedSource1640] using sourceEq1934 B hB

theorem rowSound1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1640 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1640, numericCheck1640, reducedZero1640 B hB hF, mul_zero]

theorem reducedZero1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1641 (mixedVector B) = 0 := by
  have h1996 : mixedVector B (Sum.inr 1996) = Sparse.eval nodeValue1996 (mixedVector B) := by
    change mixedMoment B node1996 node1996Labels = _
    exact sound1996 B hB hF
  have h3368 : mixedVector B (Sum.inr 3368) = Sparse.eval nodeValue3368 (mixedVector B) := by
    change mixedMoment B node3368 node3368Labels = _
    exact sound3368 B hB hF
  have h3432 : mixedVector B (Sum.inr 3432) = Sparse.eval nodeValue3432 (mixedVector B) := by
    change mixedMoment B node3432 node3432Labels = _
    exact sound3432 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3519 : mixedVector B (Sum.inr 3519) = Sparse.eval nodeValue3519 (mixedVector B) := by
    change mixedMoment B node3519 node3519Labels = _
    exact sound3519 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1935, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1996, h3368, h3432, h3468, h3513, h3519, h4081, reducedSource1641] using sourceEq1935 B hB

theorem rowSound1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1641 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1641, numericCheck1641, reducedZero1641 B hB hF, mul_zero]

theorem reducedZero1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1642 (mixedVector B) = 0 := by
  have h2203 : mixedVector B (Sum.inr 2203) = Sparse.eval nodeValue2203 (mixedVector B) := by
    change mixedMoment B node2203 node2203Labels = _
    exact sound2203 B hB hF
  have h3468 : mixedVector B (Sum.inr 3468) = Sparse.eval nodeValue3468 (mixedVector B) := by
    change mixedMoment B node3468 node3468Labels = _
    exact sound3468 B hB hF
  have h3481 : mixedVector B (Sum.inr 3481) = Sparse.eval nodeValue3481 (mixedVector B) := by
    change mixedMoment B node3481 node3481Labels = _
    exact sound3481 B hB hF
  have h3513 : mixedVector B (Sum.inr 3513) = Sparse.eval nodeValue3513 (mixedVector B) := by
    change mixedMoment B node3513 node3513Labels = _
    exact sound3513 B hB hF
  have h3530 : mixedVector B (Sum.inr 3530) = Sparse.eval nodeValue3530 (mixedVector B) := by
    change mixedMoment B node3530 node3530Labels = _
    exact sound3530 B hB hF
  have h3608 : mixedVector B (Sum.inr 3608) = Sparse.eval nodeValue3608 (mixedVector B) := by
    change mixedMoment B node3608 node3608Labels = _
    exact sound3608 B hB hF
  have h4081 : mixedVector B (Sum.inr 4081) = Sparse.eval nodeValue4081 (mixedVector B) := by
    change mixedMoment B node4081 node4081Labels = _
    exact sound4081 B hB hF
  simpa only [sourceForm1936, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2203, h3468, h3481, h3513, h3530, h3608, h4081, reducedSource1642] using sourceEq1936 B hB

theorem rowSound1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1642 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1642, numericCheck1642, reducedZero1642 B hB hF, mul_zero]

theorem reducedZero1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1643 (mixedVector B) = 0 := by
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h2422 : mixedVector B (Sum.inr 2422) = Sparse.eval nodeValue2422 (mixedVector B) := by
    change mixedMoment B node2422 node2422Labels = _
    exact sound2422 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2485 : mixedVector B (Sum.inr 2485) = Sparse.eval nodeValue2485 (mixedVector B) := by
    change mixedMoment B node2485 node2485Labels = _
    exact sound2485 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1937, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1327, h2422, h2429, h2485, h2543, h2924, h4091, reducedSource1643] using sourceEq1937 B hB

theorem rowSound1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1643 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1643, numericCheck1643, reducedZero1643 B hB hF, mul_zero]

theorem reducedZero1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1644 (mixedVector B) = 0 := by
  have h1150 : mixedVector B (Sum.inr 1150) = Sparse.eval nodeValue1150 (mixedVector B) := by
    change mixedMoment B node1150 node1150Labels = _
    exact sound1150 B hB hF
  have h2349 : mixedVector B (Sum.inr 2349) = Sparse.eval nodeValue2349 (mixedVector B) := by
    change mixedMoment B node2349 node2349Labels = _
    exact sound2349 B hB hF
  have h2429 : mixedVector B (Sum.inr 2429) = Sparse.eval nodeValue2429 (mixedVector B) := by
    change mixedMoment B node2429 node2429Labels = _
    exact sound2429 B hB hF
  have h2543 : mixedVector B (Sum.inr 2543) = Sparse.eval nodeValue2543 (mixedVector B) := by
    change mixedMoment B node2543 node2543Labels = _
    exact sound2543 B hB hF
  have h2556 : mixedVector B (Sum.inr 2556) = Sparse.eval nodeValue2556 (mixedVector B) := by
    change mixedMoment B node2556 node2556Labels = _
    exact sound2556 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1938, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1150, h2349, h2429, h2543, h2556, h4091, reducedSource1644] using sourceEq1938 B hB

theorem rowSound1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1644 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1644, numericCheck1644, reducedZero1644 B hB hF, mul_zero]

theorem reducedZero1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1645 (mixedVector B) = 0 := by
  have h2071 : mixedVector B (Sum.inr 2071) = Sparse.eval nodeValue2071 (mixedVector B) := by
    change mixedMoment B node2071 node2071Labels = _
    exact sound2071 B hB hF
  have h2073 : mixedVector B (Sum.inr 2073) = Sparse.eval nodeValue2073 (mixedVector B) := by
    change mixedMoment B node2073 node2073Labels = _
    exact sound2073 B hB hF
  have h2077 : mixedVector B (Sum.inr 2077) = Sparse.eval nodeValue2077 (mixedVector B) := by
    change mixedMoment B node2077 node2077Labels = _
    exact sound2077 B hB hF
  have h2086 : mixedVector B (Sum.inr 2086) = Sparse.eval nodeValue2086 (mixedVector B) := by
    change mixedMoment B node2086 node2086Labels = _
    exact sound2086 B hB hF
  have h2191 : mixedVector B (Sum.inr 2191) = Sparse.eval nodeValue2191 (mixedVector B) := by
    change mixedMoment B node2191 node2191Labels = _
    exact sound2191 B hB hF
  have h3558 : mixedVector B (Sum.inr 3558) = Sparse.eval nodeValue3558 (mixedVector B) := by
    change mixedMoment B node3558 node3558Labels = _
    exact sound3558 B hB hF
  have h4079 : mixedVector B (Sum.inr 4079) = Sparse.eval nodeValue4079 (mixedVector B) := by
    change mixedMoment B node4079 node4079Labels = _
    exact sound4079 B hB hF
  simpa only [sourceForm1939, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2071, h2073, h2077, h2086, h2191, h3558, h4079, reducedSource1645] using sourceEq1939 B hB

theorem rowSound1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1645 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1645, numericCheck1645, reducedZero1645 B hB hF, mul_zero]

theorem reducedZero1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1646 (mixedVector B) = 0 := by
  have h2454 : mixedVector B (Sum.inr 2454) = Sparse.eval nodeValue2454 (mixedVector B) := by
    change mixedMoment B node2454 node2454Labels = _
    exact sound2454 B hB hF
  have h2456 : mixedVector B (Sum.inr 2456) = Sparse.eval nodeValue2456 (mixedVector B) := by
    change mixedMoment B node2456 node2456Labels = _
    exact sound2456 B hB hF
  have h2462 : mixedVector B (Sum.inr 2462) = Sparse.eval nodeValue2462 (mixedVector B) := by
    change mixedMoment B node2462 node2462Labels = _
    exact sound2462 B hB hF
  have h2491 : mixedVector B (Sum.inr 2491) = Sparse.eval nodeValue2491 (mixedVector B) := by
    change mixedMoment B node2491 node2491Labels = _
    exact sound2491 B hB hF
  have h2698 : mixedVector B (Sum.inr 2698) = Sparse.eval nodeValue2698 (mixedVector B) := by
    change mixedMoment B node2698 node2698Labels = _
    exact sound2698 B hB hF
  have h3796 : mixedVector B (Sum.inr 3796) = Sparse.eval nodeValue3796 (mixedVector B) := by
    change mixedMoment B node3796 node3796Labels = _
    exact sound3796 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1940, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h2454, h2456, h2462, h2491, h2698, h3796, h4090, reducedSource1646] using sourceEq1940 B hB

theorem rowSound1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1646 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1646, numericCheck1646, reducedZero1646 B hB hF, mul_zero]

theorem reducedZero1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1647 (mixedVector B) = 0 := by
  have h1992 : mixedVector B (Sum.inr 1992) = Sparse.eval nodeValue1992 (mixedVector B) := by
    change mixedMoment B node1992 node1992Labels = _
    exact sound1992 B hB hF
  have h1994 : mixedVector B (Sum.inr 1994) = Sparse.eval nodeValue1994 (mixedVector B) := by
    change mixedMoment B node1994 node1994Labels = _
    exact sound1994 B hB hF
  have h2000 : mixedVector B (Sum.inr 2000) = Sparse.eval nodeValue2000 (mixedVector B) := by
    change mixedMoment B node2000 node2000Labels = _
    exact sound2000 B hB hF
  have h2031 : mixedVector B (Sum.inr 2031) = Sparse.eval nodeValue2031 (mixedVector B) := by
    change mixedMoment B node2031 node2031Labels = _
    exact sound2031 B hB hF
  have h2216 : mixedVector B (Sum.inr 2216) = Sparse.eval nodeValue2216 (mixedVector B) := by
    change mixedMoment B node2216 node2216Labels = _
    exact sound2216 B hB hF
  have h3517 : mixedVector B (Sum.inr 3517) = Sparse.eval nodeValue3517 (mixedVector B) := by
    change mixedMoment B node3517 node3517Labels = _
    exact sound3517 B hB hF
  have h4080 : mixedVector B (Sum.inr 4080) = Sparse.eval nodeValue4080 (mixedVector B) := by
    change mixedMoment B node4080 node4080Labels = _
    exact sound4080 B hB hF
  simpa only [sourceForm1942, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1992, h1994, h2000, h2031, h2216, h3517, h4080, reducedSource1647] using sourceEq1942 B hB

theorem rowSound1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1647 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1647, numericCheck1647, reducedZero1647 B hB hF, mul_zero]

theorem sourceRowsAt1632 : MixedData.sourceRows (1632 : Fin 2425) =
    MixedData.row1632 := by decide +kernel

theorem sourceRowsAt1633 : MixedData.sourceRows (1633 : Fin 2425) =
    MixedData.row1633 := by decide +kernel

theorem sourceRowsAt1634 : MixedData.sourceRows (1634 : Fin 2425) =
    MixedData.row1634 := by decide +kernel

theorem sourceRowsAt1635 : MixedData.sourceRows (1635 : Fin 2425) =
    MixedData.row1635 := by decide +kernel

theorem sourceRowsAt1636 : MixedData.sourceRows (1636 : Fin 2425) =
    MixedData.row1636 := by decide +kernel

theorem sourceRowsAt1637 : MixedData.sourceRows (1637 : Fin 2425) =
    MixedData.row1637 := by decide +kernel

theorem sourceRowsAt1638 : MixedData.sourceRows (1638 : Fin 2425) =
    MixedData.row1638 := by decide +kernel

theorem sourceRowsAt1639 : MixedData.sourceRows (1639 : Fin 2425) =
    MixedData.row1639 := by decide +kernel

theorem sourceRowsAt1640 : MixedData.sourceRows (1640 : Fin 2425) =
    MixedData.row1640 := by decide +kernel

theorem sourceRowsAt1641 : MixedData.sourceRows (1641 : Fin 2425) =
    MixedData.row1641 := by decide +kernel

theorem sourceRowsAt1642 : MixedData.sourceRows (1642 : Fin 2425) =
    MixedData.row1642 := by decide +kernel

theorem sourceRowsAt1643 : MixedData.sourceRows (1643 : Fin 2425) =
    MixedData.row1643 := by decide +kernel

theorem sourceRowsAt1644 : MixedData.sourceRows (1644 : Fin 2425) =
    MixedData.row1644 := by decide +kernel

theorem sourceRowsAt1645 : MixedData.sourceRows (1645 : Fin 2425) =
    MixedData.row1645 := by decide +kernel

theorem sourceRowsAt1646 : MixedData.sourceRows (1646 : Fin 2425) =
    MixedData.row1646 := by decide +kernel

theorem sourceRowsAt1647 : MixedData.sourceRows (1647 : Fin 2425) =
    MixedData.row1647 := by decide +kernel

theorem chunkSound102_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 102) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1632 ∨ k.val = 1633 ∨ k.val = 1634 ∨ k.val = 1635 ∨ k.val = 1636 ∨ k.val = 1637 ∨ k.val = 1638 ∨ k.val = 1639 ∨ k.val = 1640 ∨ k.val = 1641 ∨ k.val = 1642 ∨ k.val = 1643 ∨ k.val = 1644 ∨ k.val = 1645 ∨ k.val = 1646 ∨ k.val = 1647 := by omega
  rcases heq with h1632 | h1633 | h1634 | h1635 | h1636 | h1637 | h1638 | h1639 | h1640 | h1641 | h1642 | h1643 | h1644 | h1645 | h1646 | h1647
  · have he : k = (1632 : Fin 2425) := Fin.ext h1632
    subst k
    rw [sourceRowsAt1632]
    exact rowSound1632 B hB hF
  · have he : k = (1633 : Fin 2425) := Fin.ext h1633
    subst k
    rw [sourceRowsAt1633]
    exact rowSound1633 B hB hF
  · have he : k = (1634 : Fin 2425) := Fin.ext h1634
    subst k
    rw [sourceRowsAt1634]
    exact rowSound1634 B hB hF
  · have he : k = (1635 : Fin 2425) := Fin.ext h1635
    subst k
    rw [sourceRowsAt1635]
    exact rowSound1635 B hB hF
  · have he : k = (1636 : Fin 2425) := Fin.ext h1636
    subst k
    rw [sourceRowsAt1636]
    exact rowSound1636 B hB hF
  · have he : k = (1637 : Fin 2425) := Fin.ext h1637
    subst k
    rw [sourceRowsAt1637]
    exact rowSound1637 B hB hF
  · have he : k = (1638 : Fin 2425) := Fin.ext h1638
    subst k
    rw [sourceRowsAt1638]
    exact rowSound1638 B hB hF
  · have he : k = (1639 : Fin 2425) := Fin.ext h1639
    subst k
    rw [sourceRowsAt1639]
    exact rowSound1639 B hB hF
  · have he : k = (1640 : Fin 2425) := Fin.ext h1640
    subst k
    rw [sourceRowsAt1640]
    exact rowSound1640 B hB hF
  · have he : k = (1641 : Fin 2425) := Fin.ext h1641
    subst k
    rw [sourceRowsAt1641]
    exact rowSound1641 B hB hF
  · have he : k = (1642 : Fin 2425) := Fin.ext h1642
    subst k
    rw [sourceRowsAt1642]
    exact rowSound1642 B hB hF
  · have he : k = (1643 : Fin 2425) := Fin.ext h1643
    subst k
    rw [sourceRowsAt1643]
    exact rowSound1643 B hB hF
  · have he : k = (1644 : Fin 2425) := Fin.ext h1644
    subst k
    rw [sourceRowsAt1644]
    exact rowSound1644 B hB hF
  · have he : k = (1645 : Fin 2425) := Fin.ext h1645
    subst k
    rw [sourceRowsAt1645]
    exact rowSound1645 B hB hF
  · have he : k = (1646 : Fin 2425) := Fin.ext h1646
    subst k
    rw [sourceRowsAt1646]
    exact rowSound1646 B hB hF
  · have he : k = (1647 : Fin 2425) := Fin.ext h1647
    subst k
    rw [sourceRowsAt1647]
    exact rowSound1647 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound102_e_oai
