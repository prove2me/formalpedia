-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:44:42.153228+00:00
-- url     : https://prove2.me/submissions/b38ec09a-487d-4221-907a-6819e3b86856

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E088
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E192
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13064 raw13064Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13064 raw13064Labels = mixedMoment B raw13064step0 raw13064step0Labels := by
      have hz : ∀ j, raw13064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13064step0 = (fun i j => raw13064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13064step0 raw13064; decide +kernel
      have hl : raw13064step0Labels = raw13064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13064 raw13064Labels permutation265 hz
    mixedMoment B raw13064step0 raw13064step0Labels = mixedMoment B raw13064step1 raw13064step1Labels := by
      have ha : raw13064step1 = (fun i j => raw13064step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13064step1 raw13064step0; decide +kernel
      have hl : raw13064step1Labels = raw13064step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13064step0 raw13064step0Labels permutation56 permutation0
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

theorem canonical23801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23801 raw23801Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw23801 raw23801Labels = mixedMoment B raw23801step0 raw23801step0Labels := by
      have hz : ∀ j, raw23801 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23801step0 = (fun i j => raw23801 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23801step0 raw23801; decide +kernel
      have hl : raw23801step0Labels = raw23801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23801 raw23801Labels permutation265 hz
    mixedMoment B raw23801step0 raw23801step0Labels = mixedMoment B raw23801step1 raw23801step1Labels := by
      have ha : raw23801step1 = (fun i j => raw23801step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23801step1 raw23801step0; decide +kernel
      have hl : raw23801step1Labels = raw23801step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23801step0 raw23801step0Labels permutation42 permutation4
    mixedMoment B raw23801step1 raw23801step1Labels = mixedMoment B raw23801step2 raw23801step2Labels := by
      have ha : raw23801step2 = -raw23801step1 := by apply Matrix.ext; change ∀ i j, raw23801step2 i j = -(raw23801step1 i j); unfold raw23801step2 raw23801step1; decide +kernel
      have hl : raw23801step2Labels = raw23801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1714 node1714Labels := by rfl

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

theorem canonical23804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23804 raw23804Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw23804 raw23804Labels = mixedMoment B raw23804step0 raw23804step0Labels := by
      have hz : ∀ j, raw23804 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23804step0 = (fun i j => raw23804 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23804step0 raw23804; decide +kernel
      have hl : raw23804step0Labels = raw23804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23804 raw23804Labels permutation265 hz
    mixedMoment B raw23804step0 raw23804step0Labels = mixedMoment B raw23804step1 raw23804step1Labels := by
      have ha : raw23804step1 = (fun i j => raw23804step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23804step1 raw23804step0; decide +kernel
      have hl : raw23804step1Labels = raw23804step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23804step0 raw23804step0Labels permutation38 permutation2
    _ = mixedMoment B node604 node604Labels := by rfl

theorem canonical23805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23805 raw23805Labels = mixedMoment B node923 node923Labels := by
  calc
    mixedMoment B raw23805 raw23805Labels = mixedMoment B raw23805step0 raw23805step0Labels := by
      have ha : raw23805step0 = (fun i j => raw23805 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23805step0 raw23805; decide +kernel
      have hl : raw23805step0Labels = raw23805Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23805 raw23805Labels permutation158 permutation2
    _ = mixedMoment B node923 node923Labels := by rfl

theorem canonical23806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23806 raw23806Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw23806 raw23806Labels = mixedMoment B raw23806step0 raw23806step0Labels := by
      have hz : ∀ j, raw23806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23806step0 = (fun i j => raw23806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23806step0 raw23806; decide +kernel
      have hl : raw23806step0Labels = raw23806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23806 raw23806Labels permutation265 hz
    _ = mixedMoment B node1042 node1042Labels := by rfl

theorem canonical23807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23807 raw23807Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw23807 raw23807Labels = mixedMoment B raw23807step0 raw23807step0Labels := by
      have hz : ∀ j, raw23807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23807step0 = (fun i j => raw23807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23807step0 raw23807; decide +kernel
      have hl : raw23807step0Labels = raw23807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23807 raw23807Labels permutation434 hz
    mixedMoment B raw23807step0 raw23807step0Labels = mixedMoment B raw23807step1 raw23807step1Labels := by
      have hz : ∀ j, raw23807step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23807step1 = (fun i j => raw23807step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23807step1 raw23807step0; decide +kernel
      have hl : raw23807step1Labels = raw23807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23807step0 raw23807step0Labels permutation56 hz
    _ = mixedMoment B node1087 node1087Labels := by rfl

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

theorem canonical23808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23808 raw23808Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw23808 raw23808Labels = mixedMoment B raw23808step0 raw23808step0Labels := by
      have hz : ∀ j, raw23808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23808step0 = (fun i j => raw23808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23808step0 raw23808; decide +kernel
      have hl : raw23808step0Labels = raw23808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23808 raw23808Labels permutation265 hz
    mixedMoment B raw23808step0 raw23808step0Labels = mixedMoment B raw23808step1 raw23808step1Labels := by
      have ha : raw23808step1 = (fun i j => raw23808step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23808step1 raw23808step0; decide +kernel
      have hl : raw23808step1Labels = raw23808step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23808step0 raw23808step0Labels permutation46 permutation2
    _ = mixedMoment B node1058 node1058Labels := by rfl

theorem canonical23809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23809 raw23809Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw23809 raw23809Labels = mixedMoment B raw23809step0 raw23809step0Labels := by
      have hz : ∀ j, raw23809 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23809step0 = (fun i j => raw23809 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23809step0 raw23809; decide +kernel
      have hl : raw23809step0Labels = raw23809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23809 raw23809Labels permutation265 hz
    mixedMoment B raw23809step0 raw23809step0Labels = mixedMoment B raw23809step1 raw23809step1Labels := by
      have ha : raw23809step1 = (fun i j => raw23809step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23809step1 raw23809step0; decide +kernel
      have hl : raw23809step1Labels = raw23809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23809step0 raw23809step0Labels permutation42 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical23810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23810 raw23810Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23810 raw23810Labels = mixedMoment B raw23810step0 raw23810step0Labels := by
      have hz : ∀ j, raw23810 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw23810step0 = (fun i j => raw23810 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw23810step0 raw23810; decide +kernel
      have hl : raw23810step0Labels = raw23810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810 raw23810Labels permutation590 hz
    mixedMoment B raw23810step0 raw23810step0Labels = mixedMoment B raw23810step1 raw23810step1Labels := by
      have hz : ∀ j, raw23810step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23810step1 = (fun i j => raw23810step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23810step1 raw23810step0; decide +kernel
      have hl : raw23810step1Labels = raw23810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step0 raw23810step0Labels permutation104 hz
    mixedMoment B raw23810step1 raw23810step1Labels = mixedMoment B raw23810step2 raw23810step2Labels := by
      have hz : ∀ j, raw23810step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23810step2 = (fun i j => raw23810step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23810step2 raw23810step1; decide +kernel
      have hl : raw23810step2Labels = raw23810step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23810step1 raw23810step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23811 raw23811Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw23811 raw23811Labels = mixedMoment B raw23811step0 raw23811step0Labels := by
      have hz : ∀ j, raw23811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23811step0 = (fun i j => raw23811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23811step0 raw23811; decide +kernel
      have hl : raw23811step0Labels = raw23811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23811 raw23811Labels permutation265 hz
    mixedMoment B raw23811step0 raw23811step0Labels = mixedMoment B raw23811step1 raw23811step1Labels := by
      have ha : raw23811step1 = (fun i j => raw23811step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23811step1 raw23811step0; decide +kernel
      have hl : raw23811step1Labels = raw23811step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23811step0 raw23811step0Labels permutation34 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical23812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23812 raw23812Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw23812 raw23812Labels = mixedMoment B raw23812step0 raw23812step0Labels := by
      have ha : raw23812step0 = (fun i j => raw23812 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23812step0 raw23812; decide +kernel
      have hl : raw23812step0Labels = raw23812Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23812 raw23812Labels permutation188 permutation2
    _ = mixedMoment B node1335 node1335Labels := by rfl

theorem canonical23813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23813 raw23813Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw23813 raw23813Labels = mixedMoment B raw23813step0 raw23813step0Labels := by
      have hz : ∀ j, raw23813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23813step0 = (fun i j => raw23813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23813step0 raw23813; decide +kernel
      have hl : raw23813step0Labels = raw23813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23813 raw23813Labels permutation265 hz
    mixedMoment B raw23813step0 raw23813step0Labels = mixedMoment B raw23813step1 raw23813step1Labels := by
      have ha : raw23813step1 = (fun i j => raw23813step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23813step1 raw23813step0; decide +kernel
      have hl : raw23813step1Labels = raw23813step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23813step0 raw23813step0Labels permutation34 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

theorem canonical23814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23814 raw23814Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw23814 raw23814Labels = mixedMoment B raw23814step0 raw23814step0Labels := by
      have hz : ∀ j, raw23814 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23814step0 = (fun i j => raw23814 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23814step0 raw23814; decide +kernel
      have hl : raw23814step0Labels = raw23814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23814 raw23814Labels permutation265 hz
    mixedMoment B raw23814step0 raw23814step0Labels = mixedMoment B raw23814step1 raw23814step1Labels := by
      have ha : raw23814step1 = (fun i j => raw23814step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23814step1 raw23814step0; decide +kernel
      have hl : raw23814step1Labels = raw23814step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23814step0 raw23814step0Labels permutation34 permutation2
    _ = mixedMoment B node1338 node1338Labels := by rfl

theorem canonical23815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23815 raw23815Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw23815 raw23815Labels = mixedMoment B raw23815step0 raw23815step0Labels := by
      have hz : ∀ j, raw23815 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23815step0 = (fun i j => raw23815 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23815step0 raw23815; decide +kernel
      have hl : raw23815step0Labels = raw23815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23815 raw23815Labels permutation265 hz
    _ = mixedMoment B node1347 node1347Labels := by rfl

theorem canonical23816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23816 raw23816Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw23816 raw23816Labels = mixedMoment B raw23816step0 raw23816step0Labels := by
      have hz : ∀ j, raw23816 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23816step0 = (fun i j => raw23816 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23816step0 raw23816; decide +kernel
      have hl : raw23816step0Labels = raw23816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23816 raw23816Labels permutation265 hz
    mixedMoment B raw23816step0 raw23816step0Labels = mixedMoment B raw23816step1 raw23816step1Labels := by
      have ha : raw23816step1 = (fun i j => raw23816step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23816step1 raw23816step0; decide +kernel
      have hl : raw23816step1Labels = raw23816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23816step0 raw23816step0Labels permutation34 permutation2
    _ = mixedMoment B node1337 node1337Labels := by rfl

theorem canonical23817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23817 raw23817Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw23817 raw23817Labels = mixedMoment B raw23817step0 raw23817step0Labels := by
      have hz : ∀ j, raw23817 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23817step0 = (fun i j => raw23817 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23817step0 raw23817; decide +kernel
      have hl : raw23817step0Labels = raw23817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23817 raw23817Labels permutation265 hz
    mixedMoment B raw23817step0 raw23817step0Labels = mixedMoment B raw23817step1 raw23817step1Labels := by
      have ha : raw23817step1 = (fun i j => raw23817step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23817step1 raw23817step0; decide +kernel
      have hl : raw23817step1Labels = raw23817step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23817step0 raw23817step0Labels permutation140 permutation0
    mixedMoment B raw23817step1 raw23817step1Labels = mixedMoment B raw23817step2 raw23817step2Labels := by
      have ha : raw23817step2 = -raw23817step1 := by apply Matrix.ext; change ∀ i j, raw23817step2 i j = -(raw23817step1 i j); unfold raw23817step2 raw23817step1; decide +kernel
      have hl : raw23817step2Labels = raw23817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

theorem canonical23819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23819 raw23819Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw23819 raw23819Labels = mixedMoment B raw23819step0 raw23819step0Labels := by
      have hz : ∀ j, raw23819 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23819step0 = (fun i j => raw23819 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23819step0 raw23819; decide +kernel
      have hl : raw23819step0Labels = raw23819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23819 raw23819Labels permutation265 hz
    mixedMoment B raw23819step0 raw23819step0Labels = mixedMoment B raw23819step1 raw23819step1Labels := by
      have ha : raw23819step1 = (fun i j => raw23819step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23819step1 raw23819step0; decide +kernel
      have hl : raw23819step1Labels = raw23819step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23819step0 raw23819step0Labels permutation34 permutation2
    mixedMoment B raw23819step1 raw23819step1Labels = mixedMoment B raw23819step2 raw23819step2Labels := by
      have ha : raw23819step2 = -raw23819step1 := by apply Matrix.ext; change ∀ i j, raw23819step2 i j = -(raw23819step1 i j); unfold raw23819step2 raw23819step1; decide +kernel
      have hl : raw23819step2Labels = raw23819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3287 node3287Labels := by rfl

theorem canonical23820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23820 raw23820Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23820 raw23820Labels = mixedMoment B raw23820step0 raw23820step0Labels := by
      have hz : ∀ j, raw23820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23820step0 = (fun i j => raw23820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23820step0 raw23820; decide +kernel
      have hl : raw23820step0Labels = raw23820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23820 raw23820Labels permutation265 hz
    mixedMoment B raw23820step0 raw23820step0Labels = mixedMoment B raw23820step1 raw23820step1Labels := by
      have ha : raw23820step1 = (fun i j => raw23820step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23820step1 raw23820step0; decide +kernel
      have hl : raw23820step1Labels = raw23820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23820step0 raw23820step0Labels permutation34 permutation2
    mixedMoment B raw23820step1 raw23820step1Labels = mixedMoment B raw23820step2 raw23820step2Labels := by
      have ha : raw23820step2 = -raw23820step1 := by apply Matrix.ext; change ∀ i j, raw23820step2 i j = -(raw23820step1 i j); unfold raw23820step2 raw23820step1; decide +kernel
      have hl : raw23820step2Labels = raw23820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical23821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23821 raw23821Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw23821 raw23821Labels = mixedMoment B raw23821step0 raw23821step0Labels := by
      have hz : ∀ j, raw23821 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23821step0 = (fun i j => raw23821 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23821step0 raw23821; decide +kernel
      have hl : raw23821step0Labels = raw23821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23821 raw23821Labels permutation265 hz
    mixedMoment B raw23821step0 raw23821step0Labels = mixedMoment B raw23821step1 raw23821step1Labels := by
      have ha : raw23821step1 = (fun i j => raw23821step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23821step1 raw23821step0; decide +kernel
      have hl : raw23821step1Labels = raw23821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23821step0 raw23821step0Labels permutation145 permutation2
    _ = mixedMoment B node2502 node2502Labels := by rfl

theorem canonical23822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23822 raw23822Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw23822 raw23822Labels = mixedMoment B raw23822step0 raw23822step0Labels := by
      have hz : ∀ j, raw23822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23822step0 = (fun i j => raw23822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23822step0 raw23822; decide +kernel
      have hl : raw23822step0Labels = raw23822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23822 raw23822Labels permutation265 hz
    mixedMoment B raw23822step0 raw23822step0Labels = mixedMoment B raw23822step1 raw23822step1Labels := by
      have ha : raw23822step1 = (fun i j => raw23822step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23822step1 raw23822step0; decide +kernel
      have hl : raw23822step1Labels = raw23822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23822step0 raw23822step0Labels permutation50 permutation4
    mixedMoment B raw23822step1 raw23822step1Labels = mixedMoment B raw23822step2 raw23822step2Labels := by
      have ha : raw23822step2 = -raw23822step1 := by apply Matrix.ext; change ∀ i j, raw23822step2 i j = -(raw23822step1 i j); unfold raw23822step2 raw23822step1; decide +kernel
      have hl : raw23822step2Labels = raw23822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node824 node824Labels := by rfl

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

theorem canonical23824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23824 raw23824Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23824 raw23824Labels = mixedMoment B raw23824step0 raw23824step0Labels := by
      have hz : ∀ j, raw23824 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23824step0 = (fun i j => raw23824 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23824step0 raw23824; decide +kernel
      have hl : raw23824step0Labels = raw23824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23824 raw23824Labels permutation265 hz
    mixedMoment B raw23824step0 raw23824step0Labels = mixedMoment B raw23824step1 raw23824step1Labels := by
      have ha : raw23824step1 = (fun i j => raw23824step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23824step1 raw23824step0; decide +kernel
      have hl : raw23824step1Labels = raw23824step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23824step0 raw23824step0Labels permutation50 permutation4
    mixedMoment B raw23824step1 raw23824step1Labels = mixedMoment B raw23824step2 raw23824step2Labels := by
      have ha : raw23824step2 = -raw23824step1 := by apply Matrix.ext; change ∀ i j, raw23824step2 i j = -(raw23824step1 i j); unfold raw23824step2 raw23824step1; decide +kernel
      have hl : raw23824step2Labels = raw23824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical23825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23825 raw23825Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw23825 raw23825Labels = mixedMoment B raw23825step0 raw23825step0Labels := by
      have hz : ∀ j, raw23825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23825step0 = (fun i j => raw23825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23825step0 raw23825; decide +kernel
      have hl : raw23825step0Labels = raw23825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23825 raw23825Labels permutation265 hz
    mixedMoment B raw23825step0 raw23825step0Labels = mixedMoment B raw23825step1 raw23825step1Labels := by
      have ha : raw23825step1 = (fun i j => raw23825step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23825step1 raw23825step0; decide +kernel
      have hl : raw23825step1Labels = raw23825step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23825step0 raw23825step0Labels permutation50 permutation4
    mixedMoment B raw23825step1 raw23825step1Labels = mixedMoment B raw23825step2 raw23825step2Labels := by
      have ha : raw23825step2 = -raw23825step1 := by apply Matrix.ext; change ∀ i j, raw23825step2 i j = -(raw23825step1 i j); unfold raw23825step2 raw23825step1; decide +kernel
      have hl : raw23825step2Labels = raw23825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

theorem canonical23826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23826 raw23826Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw23826 raw23826Labels = mixedMoment B raw23826step0 raw23826step0Labels := by
      have ha : raw23826step0 = (fun i j => raw23826 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23826step0 raw23826; decide +kernel
      have hl : raw23826step0Labels = raw23826Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23826 raw23826Labels permutation218 permutation4
    mixedMoment B raw23826step0 raw23826step0Labels = mixedMoment B raw23826step1 raw23826step1Labels := by
      have ha : raw23826step1 = -raw23826step0 := by apply Matrix.ext; change ∀ i j, raw23826step1 i j = -(raw23826step0 i j); unfold raw23826step1 raw23826step0; decide +kernel
      have hl : raw23826step1Labels = raw23826step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical23827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23827 raw23827Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw23827 raw23827Labels = mixedMoment B raw23827step0 raw23827step0Labels := by
      have hz : ∀ j, raw23827 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23827step0 = (fun i j => raw23827 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23827step0 raw23827; decide +kernel
      have hl : raw23827step0Labels = raw23827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23827 raw23827Labels permutation265 hz
    mixedMoment B raw23827step0 raw23827step0Labels = mixedMoment B raw23827step1 raw23827step1Labels := by
      have ha : raw23827step1 = (fun i j => raw23827step0 (permutation43 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23827step1 raw23827step0; decide +kernel
      have hl : raw23827step1Labels = raw23827step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23827step0 raw23827step0Labels permutation43 permutation4
    mixedMoment B raw23827step1 raw23827step1Labels = mixedMoment B raw23827step2 raw23827step2Labels := by
      have ha : raw23827step2 = -raw23827step1 := by apply Matrix.ext; change ∀ i j, raw23827step2 i j = -(raw23827step1 i j); unfold raw23827step2 raw23827step1; decide +kernel
      have hl : raw23827step2Labels = raw23827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical23828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23828 raw23828Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23828 raw23828Labels = mixedMoment B raw23828step0 raw23828step0Labels := by
      have hz : ∀ j, raw23828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23828step0 = (fun i j => raw23828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23828step0 raw23828; decide +kernel
      have hl : raw23828step0Labels = raw23828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23828 raw23828Labels permutation265 hz
    mixedMoment B raw23828step0 raw23828step0Labels = mixedMoment B raw23828step1 raw23828step1Labels := by
      have ha : raw23828step1 = (fun i j => raw23828step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23828step1 raw23828step0; decide +kernel
      have hl : raw23828step1Labels = raw23828step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23828step0 raw23828step0Labels permutation38 permutation4
    mixedMoment B raw23828step1 raw23828step1Labels = mixedMoment B raw23828step2 raw23828step2Labels := by
      have ha : raw23828step2 = -raw23828step1 := by apply Matrix.ext; change ∀ i j, raw23828step2 i j = -(raw23828step1 i j); unfold raw23828step2 raw23828step1; decide +kernel
      have hl : raw23828step2Labels = raw23828step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical23829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23829 raw23829Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw23829 raw23829Labels = mixedMoment B raw23829step0 raw23829step0Labels := by
      have hz : ∀ j, raw23829 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23829step0 = (fun i j => raw23829 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23829step0 raw23829; decide +kernel
      have hl : raw23829step0Labels = raw23829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23829 raw23829Labels permutation265 hz
    mixedMoment B raw23829step0 raw23829step0Labels = mixedMoment B raw23829step1 raw23829step1Labels := by
      have ha : raw23829step1 = (fun i j => raw23829step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23829step1 raw23829step0; decide +kernel
      have hl : raw23829step1Labels = raw23829step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23829step0 raw23829step0Labels permutation39 permutation4
    mixedMoment B raw23829step1 raw23829step1Labels = mixedMoment B raw23829step2 raw23829step2Labels := by
      have ha : raw23829step2 = -raw23829step1 := by apply Matrix.ext; change ∀ i j, raw23829step2 i j = -(raw23829step1 i j); unfold raw23829step2 raw23829step1; decide +kernel
      have hl : raw23829step2Labels = raw23829step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node807 node807Labels := by rfl

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

theorem canonical23831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23831 raw23831Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw23831 raw23831Labels = mixedMoment B raw23831step0 raw23831step0Labels := by
      have hz : ∀ j, raw23831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23831step0 = (fun i j => raw23831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23831step0 raw23831; decide +kernel
      have hl : raw23831step0Labels = raw23831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23831 raw23831Labels permutation265 hz
    mixedMoment B raw23831step0 raw23831step0Labels = mixedMoment B raw23831step1 raw23831step1Labels := by
      have ha : raw23831step1 = (fun i j => raw23831step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23831step1 raw23831step0; decide +kernel
      have hl : raw23831step1Labels = raw23831step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23831step0 raw23831step0Labels permutation39 permutation4
    mixedMoment B raw23831step1 raw23831step1Labels = mixedMoment B raw23831step2 raw23831step2Labels := by
      have ha : raw23831step2 = -raw23831step1 := by apply Matrix.ext; change ∀ i j, raw23831step2 i j = -(raw23831step1 i j); unfold raw23831step2 raw23831step1; decide +kernel
      have hl : raw23831step2Labels = raw23831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1646 node1646Labels := by rfl

theorem canonical23832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23832 raw23832Labels = mixedMoment B node601 node601Labels := by
  calc
    mixedMoment B raw23832 raw23832Labels = mixedMoment B raw23832step0 raw23832step0Labels := by
      have hz : ∀ j, raw23832 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23832step0 = (fun i j => raw23832 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23832step0 raw23832; decide +kernel
      have hl : raw23832step0Labels = raw23832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23832 raw23832Labels permutation265 hz
    mixedMoment B raw23832step0 raw23832step0Labels = mixedMoment B raw23832step1 raw23832step1Labels := by
      have ha : raw23832step1 = (fun i j => raw23832step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23832step1 raw23832step0; decide +kernel
      have hl : raw23832step1Labels = raw23832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23832step0 raw23832step0Labels permutation40 permutation2
    _ = mixedMoment B node601 node601Labels := by rfl

theorem canonical23833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23833 raw23833Labels = mixedMoment B node920 node920Labels := by
  calc
    mixedMoment B raw23833 raw23833Labels = mixedMoment B raw23833step0 raw23833step0Labels := by
      have ha : raw23833step0 = (fun i j => raw23833 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23833step0 raw23833; decide +kernel
      have hl : raw23833step0Labels = raw23833Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23833 raw23833Labels permutation160 permutation2
    _ = mixedMoment B node920 node920Labels := by rfl

theorem canonical23834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23834 raw23834Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw23834 raw23834Labels = mixedMoment B raw23834step0 raw23834step0Labels := by
      have hz : ∀ j, raw23834 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23834step0 = (fun i j => raw23834 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23834step0 raw23834; decide +kernel
      have hl : raw23834step0Labels = raw23834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23834 raw23834Labels permutation265 hz
    _ = mixedMoment B node1057 node1057Labels := by rfl

theorem canonical23835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23835 raw23835Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23835 raw23835Labels = mixedMoment B raw23835step0 raw23835step0Labels := by
      have hz : ∀ j, raw23835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23835step0 = (fun i j => raw23835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23835step0 raw23835; decide +kernel
      have hl : raw23835step0Labels = raw23835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23835 raw23835Labels permutation434 hz
    mixedMoment B raw23835step0 raw23835step0Labels = mixedMoment B raw23835step1 raw23835step1Labels := by
      have hz : ∀ j, raw23835step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23835step1 = (fun i j => raw23835step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23835step1 raw23835step0; decide +kernel
      have hl : raw23835step1Labels = raw23835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23835step0 raw23835step0Labels permutation56 hz
    mixedMoment B raw23835step1 raw23835step1Labels = mixedMoment B raw23835step2 raw23835step2Labels := by
      have ha : raw23835step2 = (fun i j => raw23835step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23835step2 raw23835step1; decide +kernel
      have hl : raw23835step2Labels = raw23835step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23835step1 raw23835step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical23836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23836 raw23836Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw23836 raw23836Labels = mixedMoment B raw23836step0 raw23836step0Labels := by
      have hz : ∀ j, raw23836 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23836step0 = (fun i j => raw23836 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23836step0 raw23836; decide +kernel
      have hl : raw23836step0Labels = raw23836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23836 raw23836Labels permutation520 hz
    mixedMoment B raw23836step0 raw23836step0Labels = mixedMoment B raw23836step1 raw23836step1Labels := by
      have hz : ∀ j, raw23836step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23836step1 = (fun i j => raw23836step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23836step1 raw23836step0; decide +kernel
      have hl : raw23836step1Labels = raw23836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23836step0 raw23836step0Labels permutation56 hz
    mixedMoment B raw23836step1 raw23836step1Labels = mixedMoment B raw23836step2 raw23836step2Labels := by
      have ha : raw23836step2 = (fun i j => raw23836step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23836step2 raw23836step1; decide +kernel
      have hl : raw23836step2Labels = raw23836step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23836step1 raw23836step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

theorem canonical23837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23837 raw23837Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw23837 raw23837Labels = mixedMoment B raw23837step0 raw23837step0Labels := by
      have hz : ∀ j, raw23837 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23837step0 = (fun i j => raw23837 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23837step0 raw23837; decide +kernel
      have hl : raw23837step0Labels = raw23837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23837 raw23837Labels permutation265 hz
    mixedMoment B raw23837step0 raw23837step0Labels = mixedMoment B raw23837step1 raw23837step1Labels := by
      have ha : raw23837step1 = (fun i j => raw23837step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23837step1 raw23837step0; decide +kernel
      have hl : raw23837step1Labels = raw23837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23837step0 raw23837step0Labels permutation41 permutation2
    _ = mixedMoment B node1079 node1079Labels := by rfl

theorem canonical23838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23838 raw23838Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw23838 raw23838Labels = mixedMoment B raw23838step0 raw23838step0Labels := by
      have hz : ∀ j, raw23838 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23838step0 = (fun i j => raw23838 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23838step0 raw23838; decide +kernel
      have hl : raw23838step0Labels = raw23838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838 raw23838Labels permutation520 hz
    mixedMoment B raw23838step0 raw23838step0Labels = mixedMoment B raw23838step1 raw23838step1Labels := by
      have hz : ∀ j, raw23838step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw23838step1 = (fun i j => raw23838step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw23838step1 raw23838step0; decide +kernel
      have hl : raw23838step1Labels = raw23838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838step0 raw23838step0Labels permutation104 hz
    mixedMoment B raw23838step1 raw23838step1Labels = mixedMoment B raw23838step2 raw23838step2Labels := by
      have hz : ∀ j, raw23838step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23838step2 = (fun i j => raw23838step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23838step2 raw23838step1; decide +kernel
      have hl : raw23838step2Labels = raw23838step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23838step1 raw23838step1Labels permutation14 hz
    mixedMoment B raw23838step2 raw23838step2Labels = mixedMoment B raw23838step3 raw23838step3Labels := by
      have ha : raw23838step3 = (fun i j => raw23838step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23838step3 raw23838step2; decide +kernel
      have hl : raw23838step3Labels = raw23838step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23838step2 raw23838step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

theorem canonical23839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23839 raw23839Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw23839 raw23839Labels = mixedMoment B raw23839step0 raw23839step0Labels := by
      have hz : ∀ j, raw23839 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23839step0 = (fun i j => raw23839 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23839step0 raw23839; decide +kernel
      have hl : raw23839step0Labels = raw23839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23839 raw23839Labels permutation265 hz
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical23840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23840 raw23840Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw23840 raw23840Labels = mixedMoment B raw23840step0 raw23840step0Labels := by
      have ha : raw23840step0 = (fun i j => raw23840 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23840step0 raw23840; decide +kernel
      have hl : raw23840step0Labels = raw23840Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23840 raw23840Labels permutation176 permutation2
    _ = mixedMoment B node1316 node1316Labels := by rfl

theorem canonical23841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23841 raw23841Labels = mixedMoment B node1370 node1370Labels := by
  calc
    mixedMoment B raw23841 raw23841Labels = mixedMoment B raw23841step0 raw23841step0Labels := by
      have hz : ∀ j, raw23841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23841step0 = (fun i j => raw23841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23841step0 raw23841; decide +kernel
      have hl : raw23841step0Labels = raw23841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23841 raw23841Labels permutation265 hz
    _ = mixedMoment B node1370 node1370Labels := by rfl

theorem canonical23842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23842 raw23842Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw23842 raw23842Labels = mixedMoment B raw23842step0 raw23842step0Labels := by
      have hz : ∀ j, raw23842 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23842step0 = (fun i j => raw23842 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23842step0 raw23842; decide +kernel
      have hl : raw23842step0Labels = raw23842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23842 raw23842Labels permutation265 hz
    mixedMoment B raw23842step0 raw23842step0Labels = mixedMoment B raw23842step1 raw23842step1Labels := by
      have ha : raw23842step1 = (fun i j => raw23842step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23842step1 raw23842step0; decide +kernel
      have hl : raw23842step1Labels = raw23842step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23842step0 raw23842step0Labels permutation34 permutation2
    _ = mixedMoment B node1322 node1322Labels := by rfl

theorem canonical23843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23843 raw23843Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw23843 raw23843Labels = mixedMoment B raw23843step0 raw23843step0Labels := by
      have hz : ∀ j, raw23843 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23843step0 = (fun i j => raw23843 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23843step0 raw23843; decide +kernel
      have hl : raw23843step0Labels = raw23843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23843 raw23843Labels permutation265 hz
    _ = mixedMoment B node1322 node1322Labels := by rfl

theorem canonical23844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23844 raw23844Labels = mixedMoment B node1320 node1320Labels := by
  calc
    mixedMoment B raw23844 raw23844Labels = mixedMoment B raw23844step0 raw23844step0Labels := by
      have hz : ∀ j, raw23844 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23844step0 = (fun i j => raw23844 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23844step0 raw23844; decide +kernel
      have hl : raw23844step0Labels = raw23844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23844 raw23844Labels permutation265 hz
    _ = mixedMoment B node1320 node1320Labels := by rfl

theorem canonical23845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23845 raw23845Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw23845 raw23845Labels = mixedMoment B raw23845step0 raw23845step0Labels := by
      have hz : ∀ j, raw23845 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23845step0 = (fun i j => raw23845 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23845step0 raw23845; decide +kernel
      have hl : raw23845step0Labels = raw23845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23845 raw23845Labels permutation265 hz
    mixedMoment B raw23845step0 raw23845step0Labels = mixedMoment B raw23845step1 raw23845step1Labels := by
      have ha : raw23845step1 = (fun i j => raw23845step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23845step1 raw23845step0; decide +kernel
      have hl : raw23845step1Labels = raw23845step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23845step0 raw23845step0Labels permutation41 permutation4
    mixedMoment B raw23845step1 raw23845step1Labels = mixedMoment B raw23845step2 raw23845step2Labels := by
      have ha : raw23845step2 = -raw23845step1 := by apply Matrix.ext; change ∀ i j, raw23845step2 i j = -(raw23845step1 i j); unfold raw23845step2 raw23845step1; decide +kernel
      have hl : raw23845step2Labels = raw23845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1709 node1709Labels := by rfl

theorem canonical23846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23846 raw23846Labels = mixedMoment B node3241 node3241Labels := by
  calc
    mixedMoment B raw23846 raw23846Labels = mixedMoment B raw23846step0 raw23846step0Labels := by
      have ha : raw23846step0 = (fun i j => raw23846 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23846step0 raw23846; decide +kernel
      have hl : raw23846step0Labels = raw23846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23846 raw23846Labels permutation176 permutation2
    mixedMoment B raw23846step0 raw23846step0Labels = mixedMoment B raw23846step1 raw23846step1Labels := by
      have ha : raw23846step1 = -raw23846step0 := by apply Matrix.ext; change ∀ i j, raw23846step1 i j = -(raw23846step0 i j); unfold raw23846step1 raw23846step0; decide +kernel
      have hl : raw23846step1Labels = raw23846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3241 node3241Labels := by rfl

theorem canonical23847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23847 raw23847Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw23847 raw23847Labels = mixedMoment B raw23847step0 raw23847step0Labels := by
      have hz : ∀ j, raw23847 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23847step0 = (fun i j => raw23847 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23847step0 raw23847; decide +kernel
      have hl : raw23847step0Labels = raw23847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23847 raw23847Labels permutation265 hz
    mixedMoment B raw23847step0 raw23847step0Labels = mixedMoment B raw23847step1 raw23847step1Labels := by
      have ha : raw23847step1 = -raw23847step0 := by apply Matrix.ext; change ∀ i j, raw23847step1 i j = -(raw23847step0 i j); unfold raw23847step1 raw23847step0; decide +kernel
      have hl : raw23847step1Labels = raw23847step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical23848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23848 raw23848Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw23848 raw23848Labels = mixedMoment B raw23848step0 raw23848step0Labels := by
      have hz : ∀ j, raw23848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23848step0 = (fun i j => raw23848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23848step0 raw23848; decide +kernel
      have hl : raw23848step0Labels = raw23848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23848 raw23848Labels permutation265 hz
    mixedMoment B raw23848step0 raw23848step0Labels = mixedMoment B raw23848step1 raw23848step1Labels := by
      have ha : raw23848step1 = (fun i j => raw23848step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23848step1 raw23848step0; decide +kernel
      have hl : raw23848step1Labels = raw23848step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23848step0 raw23848step0Labels permutation35 permutation2
    mixedMoment B raw23848step1 raw23848step1Labels = mixedMoment B raw23848step2 raw23848step2Labels := by
      have ha : raw23848step2 = -raw23848step1 := by apply Matrix.ext; change ∀ i j, raw23848step2 i j = -(raw23848step1 i j); unfold raw23848step2 raw23848step1; decide +kernel
      have hl : raw23848step2Labels = raw23848step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3246 node3246Labels := by rfl

theorem canonical23849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23849 raw23849Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw23849 raw23849Labels = mixedMoment B raw23849step0 raw23849step0Labels := by
      have hz : ∀ j, raw23849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23849step0 = (fun i j => raw23849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23849step0 raw23849; decide +kernel
      have hl : raw23849step0Labels = raw23849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23849 raw23849Labels permutation265 hz
    mixedMoment B raw23849step0 raw23849step0Labels = mixedMoment B raw23849step1 raw23849step1Labels := by
      have ha : raw23849step1 = (fun i j => raw23849step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23849step1 raw23849step0; decide +kernel
      have hl : raw23849step1Labels = raw23849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23849step0 raw23849step0Labels permutation33 permutation2
    mixedMoment B raw23849step1 raw23849step1Labels = mixedMoment B raw23849step2 raw23849step2Labels := by
      have ha : raw23849step2 = -raw23849step1 := by apply Matrix.ext; change ∀ i j, raw23849step2 i j = -(raw23849step1 i j); unfold raw23849step2 raw23849step1; decide +kernel
      have hl : raw23849step2Labels = raw23849step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3246 node3246Labels := by rfl

theorem canonical23850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23850 raw23850Labels = mixedMoment B node3245 node3245Labels := by
  calc
    mixedMoment B raw23850 raw23850Labels = mixedMoment B raw23850step0 raw23850step0Labels := by
      have hz : ∀ j, raw23850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23850step0 = (fun i j => raw23850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23850step0 raw23850; decide +kernel
      have hl : raw23850step0Labels = raw23850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23850 raw23850Labels permutation265 hz
    mixedMoment B raw23850step0 raw23850step0Labels = mixedMoment B raw23850step1 raw23850step1Labels := by
      have ha : raw23850step1 = -raw23850step0 := by apply Matrix.ext; change ∀ i j, raw23850step1 i j = -(raw23850step0 i j); unfold raw23850step1 raw23850step0; decide +kernel
      have hl : raw23850step1Labels = raw23850step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3245 node3245Labels := by rfl

theorem canonical23851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23851 raw23851Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw23851 raw23851Labels = mixedMoment B raw23851step0 raw23851step0Labels := by
      have ha : raw23851step0 = (fun i j => raw23851 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23851step0 raw23851; decide +kernel
      have hl : raw23851step0Labels = raw23851Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23851 raw23851Labels permutation212 permutation4
    mixedMoment B raw23851step0 raw23851step0Labels = mixedMoment B raw23851step1 raw23851step1Labels := by
      have ha : raw23851step1 = -raw23851step0 := by apply Matrix.ext; change ∀ i j, raw23851step1 i j = -(raw23851step0 i j); unfold raw23851step1 raw23851step0; decide +kernel
      have hl : raw23851step1Labels = raw23851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1705 node1705Labels := by rfl

theorem canonical23852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23852 raw23852Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23852 raw23852Labels = mixedMoment B raw23852step0 raw23852step0Labels := by
      have hz : ∀ j, raw23852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23852step0 = (fun i j => raw23852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23852step0 raw23852; decide +kernel
      have hl : raw23852step0Labels = raw23852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23852 raw23852Labels permutation265 hz
    mixedMoment B raw23852step0 raw23852step0Labels = mixedMoment B raw23852step1 raw23852step1Labels := by
      have ha : raw23852step1 = (fun i j => raw23852step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23852step1 raw23852step0; decide +kernel
      have hl : raw23852step1Labels = raw23852step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23852step0 raw23852step0Labels permutation44 permutation4
    mixedMoment B raw23852step1 raw23852step1Labels = mixedMoment B raw23852step2 raw23852step2Labels := by
      have ha : raw23852step2 = -raw23852step1 := by apply Matrix.ext; change ∀ i j, raw23852step2 i j = -(raw23852step1 i j); unfold raw23852step2 raw23852step1; decide +kernel
      have hl : raw23852step2Labels = raw23852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical23853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23853 raw23853Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23853 raw23853Labels = mixedMoment B raw23853step0 raw23853step0Labels := by
      have hz : ∀ j, raw23853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23853step0 = (fun i j => raw23853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23853step0 raw23853; decide +kernel
      have hl : raw23853step0Labels = raw23853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23853 raw23853Labels permutation265 hz
    mixedMoment B raw23853step0 raw23853step0Labels = mixedMoment B raw23853step1 raw23853step1Labels := by
      have ha : raw23853step1 = (fun i j => raw23853step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23853step1 raw23853step0; decide +kernel
      have hl : raw23853step1Labels = raw23853step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23853step0 raw23853step0Labels permutation40 permutation4
    mixedMoment B raw23853step1 raw23853step1Labels = mixedMoment B raw23853step2 raw23853step2Labels := by
      have ha : raw23853step2 = -raw23853step1 := by apply Matrix.ext; change ∀ i j, raw23853step2 i j = -(raw23853step1 i j); unfold raw23853step2 raw23853step1; decide +kernel
      have hl : raw23853step2Labels = raw23853step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical23854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23854 raw23854Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw23854 raw23854Labels = mixedMoment B raw23854step0 raw23854step0Labels := by
      have hz : ∀ j, raw23854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23854step0 = (fun i j => raw23854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23854step0 raw23854; decide +kernel
      have hl : raw23854step0Labels = raw23854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23854 raw23854Labels permutation265 hz
    mixedMoment B raw23854step0 raw23854step0Labels = mixedMoment B raw23854step1 raw23854step1Labels := by
      have ha : raw23854step1 = (fun i j => raw23854step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23854step1 raw23854step0; decide +kernel
      have hl : raw23854step1Labels = raw23854step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23854step0 raw23854step0Labels permutation47 permutation4
    mixedMoment B raw23854step1 raw23854step1Labels = mixedMoment B raw23854step2 raw23854step2Labels := by
      have ha : raw23854step2 = -raw23854step1 := by apply Matrix.ext; change ∀ i j, raw23854step2 i j = -(raw23854step1 i j); unfold raw23854step2 raw23854step1; decide +kernel
      have hl : raw23854step2Labels = raw23854step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node811 node811Labels := by rfl

theorem canonical23855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23855 raw23855Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw23855 raw23855Labels = mixedMoment B raw23855step0 raw23855step0Labels := by
      have ha : raw23855step0 = (fun i j => raw23855 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23855step0 raw23855; decide +kernel
      have hl : raw23855step0Labels = raw23855Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23855 raw23855Labels permutation167 permutation4
    mixedMoment B raw23855step0 raw23855step0Labels = mixedMoment B raw23855step1 raw23855step1Labels := by
      have ha : raw23855step1 = -raw23855step0 := by apply Matrix.ext; change ∀ i j, raw23855step1 i j = -(raw23855step0 i j); unfold raw23855step1 raw23855step0; decide +kernel
      have hl : raw23855step1Labels = raw23855step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1601 node1601Labels := by rfl

theorem canonical23856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23856 raw23856Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw23856 raw23856Labels = mixedMoment B raw23856step0 raw23856step0Labels := by
      have hz : ∀ j, raw23856 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23856step0 = (fun i j => raw23856 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23856step0 raw23856; decide +kernel
      have hl : raw23856step0Labels = raw23856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23856 raw23856Labels permutation265 hz
    mixedMoment B raw23856step0 raw23856step0Labels = mixedMoment B raw23856step1 raw23856step1Labels := by
      have ha : raw23856step1 = (fun i j => raw23856step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23856step1 raw23856step0; decide +kernel
      have hl : raw23856step1Labels = raw23856step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23856step0 raw23856step0Labels permutation47 permutation4
    mixedMoment B raw23856step1 raw23856step1Labels = mixedMoment B raw23856step2 raw23856step2Labels := by
      have ha : raw23856step2 = -raw23856step1 := by apply Matrix.ext; change ∀ i j, raw23856step2 i j = -(raw23856step1 i j); unfold raw23856step2 raw23856step1; decide +kernel
      have hl : raw23856step2Labels = raw23856step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1649 node1649Labels := by rfl

theorem canonical23857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23857 raw23857Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw23857 raw23857Labels = mixedMoment B raw23857step0 raw23857step0Labels := by
      have hz : ∀ j, raw23857 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23857step0 = (fun i j => raw23857 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23857step0 raw23857; decide +kernel
      have hl : raw23857step0Labels = raw23857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23857 raw23857Labels permutation265 hz
    mixedMoment B raw23857step0 raw23857step0Labels = mixedMoment B raw23857step1 raw23857step1Labels := by
      have ha : raw23857step1 = (fun i j => raw23857step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23857step1 raw23857step0; decide +kernel
      have hl : raw23857step1Labels = raw23857step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23857step0 raw23857step0Labels permutation49 permutation4
    mixedMoment B raw23857step1 raw23857step1Labels = mixedMoment B raw23857step2 raw23857step2Labels := by
      have ha : raw23857step2 = -raw23857step1 := by apply Matrix.ext; change ∀ i j, raw23857step2 i j = -(raw23857step1 i j); unfold raw23857step2 raw23857step1; decide +kernel
      have hl : raw23857step2Labels = raw23857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical23860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23860 raw23860Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw23860 raw23860Labels = mixedMoment B raw23860step0 raw23860step0Labels := by
      have hz : ∀ j, raw23860 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23860step0 = (fun i j => raw23860 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23860step0 raw23860; decide +kernel
      have hl : raw23860step0Labels = raw23860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23860 raw23860Labels permutation265 hz
    mixedMoment B raw23860step0 raw23860step0Labels = mixedMoment B raw23860step1 raw23860step1Labels := by
      have ha : raw23860step1 = (fun i j => raw23860step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23860step1 raw23860step0; decide +kernel
      have hl : raw23860step1Labels = raw23860step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23860step0 raw23860step0Labels permutation34 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical23861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23861 raw23861Labels = mixedMoment B node1314 node1314Labels := by
  calc
    mixedMoment B raw23861 raw23861Labels = mixedMoment B raw23861step0 raw23861step0Labels := by
      have ha : raw23861step0 = (fun i j => raw23861 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23861step0 raw23861; decide +kernel
      have hl : raw23861step0Labels = raw23861Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23861 raw23861Labels permutation178 permutation2
    _ = mixedMoment B node1314 node1314Labels := by rfl

theorem canonical23862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23862 raw23862Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw23862 raw23862Labels = mixedMoment B raw23862step0 raw23862step0Labels := by
      have hz : ∀ j, raw23862 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23862step0 = (fun i j => raw23862 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23862step0 raw23862; decide +kernel
      have hl : raw23862step0Labels = raw23862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23862 raw23862Labels permutation265 hz
    mixedMoment B raw23862step0 raw23862step0Labels = mixedMoment B raw23862step1 raw23862step1Labels := by
      have ha : raw23862step1 = (fun i j => raw23862step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23862step1 raw23862step0; decide +kernel
      have hl : raw23862step1Labels = raw23862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23862step0 raw23862step0Labels permutation34 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

theorem canonical23863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23863 raw23863Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw23863 raw23863Labels = mixedMoment B raw23863step0 raw23863step0Labels := by
      have hz : ∀ j, raw23863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23863step0 = (fun i j => raw23863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23863step0 raw23863; decide +kernel
      have hl : raw23863step0Labels = raw23863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23863 raw23863Labels permutation265 hz
    mixedMoment B raw23863step0 raw23863step0Labels = mixedMoment B raw23863step1 raw23863step1Labels := by
      have ha : raw23863step1 = (fun i j => raw23863step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23863step1 raw23863step0; decide +kernel
      have hl : raw23863step1Labels = raw23863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23863step0 raw23863step0Labels permutation34 permutation2
    _ = mixedMoment B node1318 node1318Labels := by rfl

theorem canonical23864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23864 raw23864Labels = mixedMoment B node1321 node1321Labels := by
  calc
    mixedMoment B raw23864 raw23864Labels = mixedMoment B raw23864step0 raw23864step0Labels := by
      have hz : ∀ j, raw23864 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23864step0 = (fun i j => raw23864 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23864step0 raw23864; decide +kernel
      have hl : raw23864step0Labels = raw23864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23864 raw23864Labels permutation265 hz
    _ = mixedMoment B node1321 node1321Labels := by rfl

theorem canonical23865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23865 raw23865Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw23865 raw23865Labels = mixedMoment B raw23865step0 raw23865step0Labels := by
      have hz : ∀ j, raw23865 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23865step0 = (fun i j => raw23865 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23865step0 raw23865; decide +kernel
      have hl : raw23865step0Labels = raw23865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23865 raw23865Labels permutation265 hz
    mixedMoment B raw23865step0 raw23865step0Labels = mixedMoment B raw23865step1 raw23865step1Labels := by
      have ha : raw23865step1 = (fun i j => raw23865step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23865step1 raw23865step0; decide +kernel
      have hl : raw23865step1Labels = raw23865step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23865step0 raw23865step0Labels permutation34 permutation2
    _ = mixedMoment B node1317 node1317Labels := by rfl

theorem canonical23866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23866 raw23866Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw23866 raw23866Labels = mixedMoment B raw23866step0 raw23866step0Labels := by
      have hz : ∀ j, raw23866 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23866step0 = (fun i j => raw23866 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23866step0 raw23866; decide +kernel
      have hl : raw23866step0Labels = raw23866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23866 raw23866Labels permutation520 hz
    mixedMoment B raw23866step0 raw23866step0Labels = mixedMoment B raw23866step1 raw23866step1Labels := by
      have hz : ∀ j, raw23866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23866step1 = (fun i j => raw23866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23866step1 raw23866step0; decide +kernel
      have hl : raw23866step1Labels = raw23866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23866step0 raw23866step0Labels permutation56 hz
    mixedMoment B raw23866step1 raw23866step1Labels = mixedMoment B raw23866step2 raw23866step2Labels := by
      have ha : raw23866step2 = (fun i j => raw23866step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23866step2 raw23866step1; decide +kernel
      have hl : raw23866step2Labels = raw23866step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23866step1 raw23866step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

theorem canonical23867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23867 raw23867Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw23867 raw23867Labels = mixedMoment B raw23867step0 raw23867step0Labels := by
      have ha : raw23867step0 = (fun i j => raw23867 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23867step0 raw23867; decide +kernel
      have hl : raw23867step0Labels = raw23867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23867 raw23867Labels permutation188 permutation2
    mixedMoment B raw23867step0 raw23867step0Labels = mixedMoment B raw23867step1 raw23867step1Labels := by
      have ha : raw23867step1 = -raw23867step0 := by apply Matrix.ext; change ∀ i j, raw23867step1 i j = -(raw23867step0 i j); unfold raw23867step1 raw23867step0; decide +kernel
      have hl : raw23867step1Labels = raw23867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3238 node3238Labels := by rfl

theorem canonical23868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23868 raw23868Labels = mixedMoment B node3240 node3240Labels := by
  calc
    mixedMoment B raw23868 raw23868Labels = mixedMoment B raw23868step0 raw23868step0Labels := by
      have hz : ∀ j, raw23868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23868step0 = (fun i j => raw23868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23868step0 raw23868; decide +kernel
      have hl : raw23868step0Labels = raw23868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23868 raw23868Labels permutation265 hz
    mixedMoment B raw23868step0 raw23868step0Labels = mixedMoment B raw23868step1 raw23868step1Labels := by
      have ha : raw23868step1 = (fun i j => raw23868step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23868step1 raw23868step0; decide +kernel
      have hl : raw23868step1Labels = raw23868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23868step0 raw23868step0Labels permutation34 permutation2
    mixedMoment B raw23868step1 raw23868step1Labels = mixedMoment B raw23868step2 raw23868step2Labels := by
      have ha : raw23868step2 = -raw23868step1 := by apply Matrix.ext; change ∀ i j, raw23868step2 i j = -(raw23868step1 i j); unfold raw23868step2 raw23868step1; decide +kernel
      have hl : raw23868step2Labels = raw23868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3240 node3240Labels := by rfl

theorem canonical23869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23869 raw23869Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw23869 raw23869Labels = mixedMoment B raw23869step0 raw23869step0Labels := by
      have hz : ∀ j, raw23869 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23869step0 = (fun i j => raw23869 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23869step0 raw23869; decide +kernel
      have hl : raw23869step0Labels = raw23869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23869 raw23869Labels permutation265 hz
    mixedMoment B raw23869step0 raw23869step0Labels = mixedMoment B raw23869step1 raw23869step1Labels := by
      have ha : raw23869step1 = (fun i j => raw23869step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23869step1 raw23869step0; decide +kernel
      have hl : raw23869step1Labels = raw23869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23869step0 raw23869step0Labels permutation145 permutation2
    _ = mixedMoment B node2466 node2466Labels := by rfl

theorem canonical23870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23870 raw23870Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw23870 raw23870Labels = mixedMoment B raw23870step0 raw23870step0Labels := by
      have hz : ∀ j, raw23870 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23870step0 = (fun i j => raw23870 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23870step0 raw23870; decide +kernel
      have hl : raw23870step0Labels = raw23870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23870 raw23870Labels permutation265 hz
    mixedMoment B raw23870step0 raw23870step0Labels = mixedMoment B raw23870step1 raw23870step1Labels := by
      have ha : raw23870step1 = (fun i j => raw23870step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23870step1 raw23870step0; decide +kernel
      have hl : raw23870step1Labels = raw23870step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23870step0 raw23870step0Labels permutation53 permutation4
    mixedMoment B raw23870step1 raw23870step1Labels = mixedMoment B raw23870step2 raw23870step2Labels := by
      have ha : raw23870step2 = -raw23870step1 := by apply Matrix.ext; change ∀ i j, raw23870step2 i j = -(raw23870step1 i j); unfold raw23870step2 raw23870step1; decide +kernel
      have hl : raw23870step2Labels = raw23870step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node827 node827Labels := by rfl

theorem canonical23871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23871 raw23871Labels = mixedMoment B node1609 node1609Labels := by
  calc
    mixedMoment B raw23871 raw23871Labels = mixedMoment B raw23871step0 raw23871step0Labels := by
      have ha : raw23871step0 = (fun i j => raw23871 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23871step0 raw23871; decide +kernel
      have hl : raw23871step0Labels = raw23871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23871 raw23871Labels permutation173 permutation4
    mixedMoment B raw23871step0 raw23871step0Labels = mixedMoment B raw23871step1 raw23871step1Labels := by
      have ha : raw23871step1 = -raw23871step0 := by apply Matrix.ext; change ∀ i j, raw23871step1 i j = -(raw23871step0 i j); unfold raw23871step1 raw23871step0; decide +kernel
      have hl : raw23871step1Labels = raw23871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1609 node1609Labels := by rfl

theorem canonical23872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23872 raw23872Labels = mixedMoment B node1658 node1658Labels := by
  calc
    mixedMoment B raw23872 raw23872Labels = mixedMoment B raw23872step0 raw23872step0Labels := by
      have hz : ∀ j, raw23872 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23872step0 = (fun i j => raw23872 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23872step0 raw23872; decide +kernel
      have hl : raw23872step0Labels = raw23872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23872 raw23872Labels permutation265 hz
    mixedMoment B raw23872step0 raw23872step0Labels = mixedMoment B raw23872step1 raw23872step1Labels := by
      have ha : raw23872step1 = (fun i j => raw23872step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23872step1 raw23872step0; decide +kernel
      have hl : raw23872step1Labels = raw23872step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23872step0 raw23872step0Labels permutation53 permutation4
    mixedMoment B raw23872step1 raw23872step1Labels = mixedMoment B raw23872step2 raw23872step2Labels := by
      have ha : raw23872step2 = -raw23872step1 := by apply Matrix.ext; change ∀ i j, raw23872step2 i j = -(raw23872step1 i j); unfold raw23872step2 raw23872step1; decide +kernel
      have hl : raw23872step2Labels = raw23872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1658 node1658Labels := by rfl

theorem canonical23880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23880 raw23880Labels = mixedMoment B node578 node578Labels := by
  calc
    mixedMoment B raw23880 raw23880Labels = mixedMoment B raw23880step0 raw23880step0Labels := by
      have ha : raw23880step0 = (fun i j => raw23880 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23880step0 raw23880; decide +kernel
      have hl : raw23880step0Labels = raw23880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23880 raw23880Labels permutation184 permutation2
    _ = mixedMoment B node578 node578Labels := by rfl

theorem canonical23881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23881 raw23881Labels = mixedMoment B node942 node942Labels := by
  calc
    mixedMoment B raw23881 raw23881Labels = mixedMoment B raw23881step0 raw23881step0Labels := by
      have ha : raw23881step0 = (fun i j => raw23881 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23881step0 raw23881; decide +kernel
      have hl : raw23881step0Labels = raw23881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23881 raw23881Labels permutation184 permutation2
    _ = mixedMoment B node942 node942Labels := by rfl

theorem canonical23882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23882 raw23882Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw23882 raw23882Labels = mixedMoment B raw23882step0 raw23882step0Labels := by
      have hz : ∀ j, raw23882 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23882step0 = (fun i j => raw23882 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23882step0 raw23882; decide +kernel
      have hl : raw23882step0Labels = raw23882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23882 raw23882Labels permutation520 hz
    mixedMoment B raw23882step0 raw23882step0Labels = mixedMoment B raw23882step1 raw23882step1Labels := by
      have ha : raw23882step1 = (fun i j => raw23882step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23882step1 raw23882step0; decide +kernel
      have hl : raw23882step1Labels = raw23882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23882step0 raw23882step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical23883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23883 raw23883Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw23883 raw23883Labels = mixedMoment B raw23883step0 raw23883step0Labels := by
      have ha : raw23883step0 = (fun i j => raw23883 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23883step0 raw23883; decide +kernel
      have hl : raw23883step0Labels = raw23883Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23883 raw23883Labels permutation184 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical23884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23884 raw23884Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw23884 raw23884Labels = mixedMoment B raw23884step0 raw23884step0Labels := by
      have hz : ∀ j, raw23884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23884step0 = (fun i j => raw23884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23884step0 raw23884; decide +kernel
      have hl : raw23884step0Labels = raw23884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23884 raw23884Labels permutation346 hz
    mixedMoment B raw23884step0 raw23884step0Labels = mixedMoment B raw23884step1 raw23884step1Labels := by
      have ha : raw23884step1 = -raw23884step0 := by apply Matrix.ext; change ∀ i j, raw23884step1 i j = -(raw23884step0 i j); unfold raw23884step1 raw23884step0; decide +kernel
      have hl : raw23884step1Labels = raw23884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3299 node3299Labels := by rfl

theorem canonical23885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23885 raw23885Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw23885 raw23885Labels = mixedMoment B raw23885step0 raw23885step0Labels := by
      have ha : raw23885step0 = (fun i j => raw23885 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23885step0 raw23885; decide +kernel
      have hl : raw23885step0Labels = raw23885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23885 raw23885Labels permutation155 permutation2
    mixedMoment B raw23885step0 raw23885step0Labels = mixedMoment B raw23885step1 raw23885step1Labels := by
      have ha : raw23885step1 = -raw23885step0 := by apply Matrix.ext; change ∀ i j, raw23885step1 i j = -(raw23885step0 i j); unfold raw23885step1 raw23885step0; decide +kernel
      have hl : raw23885step1Labels = raw23885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3282 node3282Labels := by rfl

theorem canonical23886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23886 raw23886Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw23886 raw23886Labels = mixedMoment B raw23886step0 raw23886step0Labels := by
      have ha : raw23886step0 = (fun i j => raw23886 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23886step0 raw23886; decide +kernel
      have hl : raw23886step0Labels = raw23886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23886 raw23886Labels permutation153 permutation2
    mixedMoment B raw23886step0 raw23886step0Labels = mixedMoment B raw23886step1 raw23886step1Labels := by
      have ha : raw23886step1 = -raw23886step0 := by apply Matrix.ext; change ∀ i j, raw23886step1 i j = -(raw23886step0 i j); unfold raw23886step1 raw23886step0; decide +kernel
      have hl : raw23886step1Labels = raw23886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3282 node3282Labels := by rfl

theorem canonical23887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23887 raw23887Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw23887 raw23887Labels = mixedMoment B raw23887step0 raw23887step0Labels := by
      have ha : raw23887step0 = -raw23887 := by apply Matrix.ext; change ∀ i j, raw23887step0 i j = -(raw23887 i j); unfold raw23887step0 raw23887; decide +kernel
      have hl : raw23887step0Labels = raw23887Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3281 node3281Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical88
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11298 raw11298Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11298 raw11298Labels = mixedMoment B raw11298step0 raw11298step0Labels := by
      have hz : ∀ j, raw11298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw11298step0 = (fun i j => raw11298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw11298step0 raw11298; decide +kernel
      have hl : raw11298step0Labels = raw11298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298 raw11298Labels permutation520 hz
    mixedMoment B raw11298step0 raw11298step0Labels = mixedMoment B raw11298step1 raw11298step1Labels := by
      have hz : ∀ j, raw11298step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11298step1 = (fun i j => raw11298step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11298step1 raw11298step0; decide +kernel
      have hl : raw11298step1Labels = raw11298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11298step0 raw11298step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11299 raw11299Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw11299 raw11299Labels = mixedMoment B raw11299step0 raw11299step0Labels := by
      have hz : ∀ j, raw11299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11299step0 = (fun i j => raw11299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11299step0 raw11299; decide +kernel
      have hl : raw11299step0Labels = raw11299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11299 raw11299Labels permutation434 hz
    mixedMoment B raw11299step0 raw11299step0Labels = mixedMoment B raw11299step1 raw11299step1Labels := by
      have ha : raw11299step1 = (fun i j => raw11299step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11299step1 raw11299step0; decide +kernel
      have hl : raw11299step1Labels = raw11299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11299step0 raw11299step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

theorem canonical11301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11301 raw11301Labels = mixedMoment B node1020 node1020Labels := by
  calc
    _ = mixedMoment B node1020 node1020Labels := by rfl

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

theorem sound807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node807 node807Labels = Sparse.eval nodeValue807 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 807) = mixedMoment B node807 node807Labels := rfl
  simpa [nodeValue807, Sparse.eval] using hc.symm

theorem sound811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node811 node811Labels = Sparse.eval nodeValue811 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 811) = mixedMoment B node811 node811Labels := rfl
  simpa [nodeValue811, Sparse.eval] using hc.symm

theorem sound824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node824 node824Labels = Sparse.eval nodeValue824 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 824) = mixedMoment B node824 node824Labels := rfl
  simpa [nodeValue824, Sparse.eval] using hc.symm

theorem sound827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node827 node827Labels = Sparse.eval nodeValue827 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 827) = mixedMoment B node827 node827Labels := rfl
  simpa [nodeValue827, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node920 node920Labels = 0 := by
  exact mixedMoment_alpha B hF node920 node920Labels 1 permutation160
    (by decide +kernel)

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

theorem sound920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node920 node920Labels = Sparse.eval nodeValue920 (mixedVector B) := by
  simpa only [nodeValue920, Sparse.eval_nil] using zero920 B _hB _hF

theorem sound923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node923 node923Labels = Sparse.eval nodeValue923 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 923) = mixedMoment B node923 node923Labels := rfl
  simpa [nodeValue923, Sparse.eval] using hc.symm

theorem sound942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node942 node942Labels = Sparse.eval nodeValue942 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 942) = mixedMoment B node942 node942Labels := rfl
  simpa [nodeValue942, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = 0 := by
  exact mixedMoment_alpha B hF node1020 node1020Labels 1 permutation152
    (by decide +kernel)

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

theorem sound1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1020 node1020Labels = Sparse.eval nodeValue1020 (mixedVector B) := by
  simpa only [nodeValue1020, Sparse.eval_nil] using zero1020 B _hB _hF

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

theorem sound1039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1039 node1039Labels = Sparse.eval nodeValue1039 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1039) = mixedMoment B node1039 node1039Labels := rfl
  simpa [nodeValue1039, Sparse.eval] using hc.symm

theorem sound1041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1041 node1041Labels = Sparse.eval nodeValue1041 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1041) = mixedMoment B node1041 node1041Labels := rfl
  simpa [nodeValue1041, Sparse.eval] using hc.symm

theorem sound1042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1042 node1042Labels = Sparse.eval nodeValue1042 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1042) = mixedMoment B node1042 node1042Labels := rfl
  simpa [nodeValue1042, Sparse.eval] using hc.symm

theorem sound1057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1057 node1057Labels = Sparse.eval nodeValue1057 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1057) = mixedMoment B node1057 node1057Labels := rfl
  simpa [nodeValue1057, Sparse.eval] using hc.symm

theorem sound1058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1058 node1058Labels = Sparse.eval nodeValue1058 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1058) = mixedMoment B node1058 node1058Labels := rfl
  simpa [nodeValue1058, Sparse.eval] using hc.symm

theorem sound1079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1079 node1079Labels = Sparse.eval nodeValue1079 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1079) = mixedMoment B node1079 node1079Labels := rfl
  simpa [nodeValue1079, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1314 node1314Labels = Sparse.eval nodeValue1314 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1314) = mixedMoment B node1314 node1314Labels := rfl
  simpa [nodeValue1314, Sparse.eval] using hc.symm

theorem sound1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1316 node1316Labels = Sparse.eval nodeValue1316 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1316) = mixedMoment B node1316 node1316Labels := rfl
  simpa [nodeValue1316, Sparse.eval] using hc.symm

theorem sound1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1317 node1317Labels = Sparse.eval nodeValue1317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1317) = mixedMoment B node1317 node1317Labels := rfl
  simpa [nodeValue1317, Sparse.eval] using hc.symm

theorem sound1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1318 node1318Labels = Sparse.eval nodeValue1318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1318) = mixedMoment B node1318 node1318Labels := rfl
  simpa [nodeValue1318, Sparse.eval] using hc.symm

theorem sound1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1320 node1320Labels = Sparse.eval nodeValue1320 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1320) = mixedMoment B node1320 node1320Labels := rfl
  simpa [nodeValue1320, Sparse.eval] using hc.symm

theorem sound1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1321 node1321Labels = Sparse.eval nodeValue1321 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1321) = mixedMoment B node1321 node1321Labels := rfl
  simpa [nodeValue1321, Sparse.eval] using hc.symm

theorem sound1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1322 node1322Labels = Sparse.eval nodeValue1322 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1322) = mixedMoment B node1322 node1322Labels := rfl
  simpa [nodeValue1322, Sparse.eval] using hc.symm

theorem sound1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1335 node1335Labels = Sparse.eval nodeValue1335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1335) = mixedMoment B node1335 node1335Labels := rfl
  simpa [nodeValue1335, Sparse.eval] using hc.symm

theorem sound1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1337 node1337Labels = Sparse.eval nodeValue1337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1337) = mixedMoment B node1337 node1337Labels := rfl
  simpa [nodeValue1337, Sparse.eval] using hc.symm

theorem sound1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1338 node1338Labels = Sparse.eval nodeValue1338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1338) = mixedMoment B node1338 node1338Labels := rfl
  simpa [nodeValue1338, Sparse.eval] using hc.symm

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

theorem sound1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1367 node1367Labels = Sparse.eval nodeValue1367 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1367) = mixedMoment B node1367 node1367Labels := rfl
  simpa [nodeValue1367, Sparse.eval] using hc.symm

theorem sound1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1370 node1370Labels = Sparse.eval nodeValue1370 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1370) = mixedMoment B node1370 node1370Labels := rfl
  simpa [nodeValue1370, Sparse.eval] using hc.symm

theorem sound1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1406 node1406Labels = Sparse.eval nodeValue1406 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1406) = mixedMoment B node1406 node1406Labels := rfl
  simpa [nodeValue1406, Sparse.eval] using hc.symm

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

theorem sound1601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1601 node1601Labels = Sparse.eval nodeValue1601 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1601) = mixedMoment B node1601 node1601Labels := rfl
  simpa [nodeValue1601, Sparse.eval] using hc.symm

theorem sound1607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1607 node1607Labels = Sparse.eval nodeValue1607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1607) = mixedMoment B node1607 node1607Labels := rfl
  simpa [nodeValue1607, Sparse.eval] using hc.symm

theorem sound1609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1609 node1609Labels = Sparse.eval nodeValue1609 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1609) = mixedMoment B node1609 node1609Labels := rfl
  simpa [nodeValue1609, Sparse.eval] using hc.symm

theorem sound1646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1646 node1646Labels = Sparse.eval nodeValue1646 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1646) = mixedMoment B node1646 node1646Labels := rfl
  simpa [nodeValue1646, Sparse.eval] using hc.symm

theorem sound1649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1649 node1649Labels = Sparse.eval nodeValue1649 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1649) = mixedMoment B node1649 node1649Labels := rfl
  simpa [nodeValue1649, Sparse.eval] using hc.symm

theorem sound1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1656 node1656Labels = Sparse.eval nodeValue1656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1656) = mixedMoment B node1656 node1656Labels := rfl
  simpa [nodeValue1656, Sparse.eval] using hc.symm

theorem sound1658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1658 node1658Labels = Sparse.eval nodeValue1658 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1658) = mixedMoment B node1658 node1658Labels := rfl
  simpa [nodeValue1658, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Zeros26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem zero1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = 0 := by
  exact mixedMoment_alpha B hF node1705 node1705Labels 1 permutation437
    (by decide +kernel)

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

theorem sound1705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1705 node1705Labels = Sparse.eval nodeValue1705 (mixedVector B) := by
  simpa only [nodeValue1705, Sparse.eval_nil] using zero1705 B _hB _hF

theorem sound1707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1707 node1707Labels = Sparse.eval nodeValue1707 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1707) = mixedMoment B node1707 node1707Labels := rfl
  simpa [nodeValue1707, Sparse.eval] using hc.symm

theorem sound1709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1709 node1709Labels = Sparse.eval nodeValue1709 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1709) = mixedMoment B node1709 node1709Labels := rfl
  simpa [nodeValue1709, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

theorem sound1714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1714 node1714Labels = Sparse.eval nodeValue1714 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1714) = mixedMoment B node1714 node1714Labels := rfl
  simpa [nodeValue1714, Sparse.eval] using hc.symm

theorem sound1715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1715 node1715Labels = Sparse.eval nodeValue1715 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1715) = mixedMoment B node1715 node1715Labels := rfl
  simpa [nodeValue1715, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

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

theorem sound2466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2466 node2466Labels = Sparse.eval nodeValue2466 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2466) = mixedMoment B node2466 node2466Labels := rfl
  simpa [nodeValue2466, Sparse.eval] using hc.symm

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

theorem sound2502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2502 node2502Labels = Sparse.eval nodeValue2502 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2502) = mixedMoment B node2502 node2502Labels := rfl
  simpa [nodeValue2502, Sparse.eval] using hc.symm

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

theorem sound2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2884 node2884Labels = Sparse.eval nodeValue2884 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2884) = mixedMoment B node2884 node2884Labels := rfl
  simpa [nodeValue2884, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3238 node3238Labels = Sparse.eval nodeValue3238 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3238) = mixedMoment B node3238 node3238Labels := rfl
  simpa [nodeValue3238, Sparse.eval] using hc.symm

theorem sound3240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3240 node3240Labels = Sparse.eval nodeValue3240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3240) = mixedMoment B node3240 node3240Labels := rfl
  simpa [nodeValue3240, Sparse.eval] using hc.symm

theorem sound3241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3241 node3241Labels = Sparse.eval nodeValue3241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3241) = mixedMoment B node3241 node3241Labels := rfl
  simpa [nodeValue3241, Sparse.eval] using hc.symm

theorem sound3245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3245 node3245Labels = Sparse.eval nodeValue3245 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3245) = mixedMoment B node3245 node3245Labels := rfl
  simpa [nodeValue3245, Sparse.eval] using hc.symm

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

theorem sound3281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3281 node3281Labels = Sparse.eval nodeValue3281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3281) = mixedMoment B node3281 node3281Labels := rfl
  simpa [nodeValue3281, Sparse.eval] using hc.symm

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

theorem sound3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3293 node3293Labels = Sparse.eval nodeValue3293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3293) = mixedMoment B node3293 node3293Labels := rfl
  simpa [nodeValue3293, Sparse.eval] using hc.symm

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

theorem sound578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node578 node578Labels = Sparse.eval nodeValue578 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 578) = mixedMoment B node578 node578Labels := rfl
  simpa [nodeValue578, Sparse.eval] using hc.symm

theorem sound601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node601 node601Labels = Sparse.eval nodeValue601 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 601) = mixedMoment B node601 node601Labels := rfl
  simpa [nodeValue601, Sparse.eval] using hc.symm

theorem sound604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node604 node604Labels = Sparse.eval nodeValue604 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 604) = mixedMoment B node604 node604Labels := rfl
  simpa [nodeValue604, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources49
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1578 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 0) (sourceB1578 + difference 0 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 604) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 0) (sourceB1578 + difference 0 2) sourceC1578) = raw23804 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23804; decide +kernel
    rw [ha]
    exact (canonical23804 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 1) (sourceB1578 + difference 1 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 923) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 1) (sourceB1578 + difference 1 2) sourceC1578) = raw23805 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23805; decide +kernel
    rw [ha]
    exact (canonical23805 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 2) (sourceB1578 + difference 2 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1042) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 2) (sourceB1578 + difference 2 2) sourceC1578) = raw23806 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23806; decide +kernel
    rw [ha]
    exact (canonical23806 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 3) (sourceB1578 + difference 3 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1087) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 3) (sourceB1578 + difference 3 2) sourceC1578) = raw23807 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23807; decide +kernel
    rw [ha]
    exact (canonical23807 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 4) (sourceB1578 + difference 4 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1058) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 4) (sourceB1578 + difference 4 2) sourceC1578) = raw23808 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23808; decide +kernel
    rw [ha]
    exact (canonical23808 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1578 + difference 2 5) (sourceB1578 + difference 5 2) sourceC1578) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1578 + difference 2 5) (sourceB1578 + difference 5 2) sourceC1578) = raw23809 := by
      apply Matrix.ext; unfold tripleCharges sourceA1578 sourceB1578 sourceC1578 difference raw23809; decide +kernel
    rw [ha]
    exact (canonical23809 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1578 + sourceB1578) sourceC1578) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1578 + sourceB1578) sourceC1578) = raw23810 := by
      apply Matrix.ext; unfold doubleCharges sourceA1578 sourceB1578 sourceC1578 raw23810; decide +kernel
    rw [ha]
    exact (canonical23810 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1578 sourceB1578 sourceC1578
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1578, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1579 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1579 + difference 0 2) (sourceB1579 + difference 2 0) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2954) := by
    have ha : (tripleCharges (sourceA1579 + difference 0 2) (sourceB1579 + difference 2 0) sourceC1579) = raw23811 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23811; decide +kernel
    rw [ha]
    exact (canonical23811 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1579 + difference 1 2) (sourceB1579 + difference 2 1) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1335) := by
    have ha : (tripleCharges (sourceA1579 + difference 1 2) (sourceB1579 + difference 2 1) sourceC1579) = raw23812 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23812; decide +kernel
    rw [ha]
    exact (canonical23812 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1579 + difference 2 2) (sourceB1579 + difference 2 2) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1406) := by
    have ha : (tripleCharges (sourceA1579 + difference 2 2) (sourceB1579 + difference 2 2) sourceC1579) = raw23813 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23813; decide +kernel
    rw [ha]
    exact (canonical23813 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1579 + difference 3 2) (sourceB1579 + difference 2 3) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1338) := by
    have ha : (tripleCharges (sourceA1579 + difference 3 2) (sourceB1579 + difference 2 3) sourceC1579) = raw23814 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23814; decide +kernel
    rw [ha]
    exact (canonical23814 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1579 + difference 4 2) (sourceB1579 + difference 2 4) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1347) := by
    have ha : (tripleCharges (sourceA1579 + difference 4 2) (sourceB1579 + difference 2 4) sourceC1579) = raw23815 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23815; decide +kernel
    rw [ha]
    exact (canonical23815 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1579 + difference 5 2) (sourceB1579 + difference 2 5) sourceC1579) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1337) := by
    have ha : (tripleCharges (sourceA1579 + difference 5 2) (sourceB1579 + difference 2 5) sourceC1579) = raw23816 := by
      apply Matrix.ext; unfold tripleCharges sourceA1579 sourceB1579 sourceC1579 difference raw23816; decide +kernel
    rw [ha]
    exact (canonical23816 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1579 + sourceB1579) sourceC1579) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1579 + sourceB1579) sourceC1579) = raw23817 := by
      apply Matrix.ext; unfold doubleCharges sourceA1579 sourceB1579 sourceC1579 raw23817; decide +kernel
    rw [ha]
    exact (canonical23817 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1579 sourceB1579 sourceC1579
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1579, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1580 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 0) (sourceB1580 + difference 0 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 0) (sourceB1580 + difference 0 0) sourceC1580) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 1) (sourceB1580 + difference 1 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 1) (sourceB1580 + difference 1 0) sourceC1580) = raw23818 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23818; decide +kernel
    rw [ha]
    exact (canonical23818 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 2) (sourceB1580 + difference 2 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 2) (sourceB1580 + difference 2 0) sourceC1580) = raw23797 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23797; decide +kernel
    rw [ha]
    exact (canonical23797 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 3) (sourceB1580 + difference 3 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 3) (sourceB1580 + difference 3 0) sourceC1580) = raw23819 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23819; decide +kernel
    rw [ha]
    exact (canonical23819 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 4) (sourceB1580 + difference 4 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 4) (sourceB1580 + difference 4 0) sourceC1580) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1580 + difference 0 5) (sourceB1580 + difference 5 0) sourceC1580) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1580 + difference 0 5) (sourceB1580 + difference 5 0) sourceC1580) = raw23821 := by
      apply Matrix.ext; unfold tripleCharges sourceA1580 sourceB1580 sourceC1580 difference raw23821; decide +kernel
    rw [ha]
    exact (canonical23821 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1580 + sourceB1580) sourceC1580) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1580 + sourceB1580) sourceC1580) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1580 sourceB1580 sourceC1580 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1580 sourceB1580 sourceC1580
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1580, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1581 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 0) (sourceB1581 + difference 0 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 824) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 0) (sourceB1581 + difference 0 3) sourceC1581) = raw23822 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23822; decide +kernel
    rw [ha]
    exact (canonical23822 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 1) (sourceB1581 + difference 1 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 1) (sourceB1581 + difference 1 3) sourceC1581) = raw23823 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23823; decide +kernel
    rw [ha]
    exact (canonical23823 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 2) (sourceB1581 + difference 2 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 2) (sourceB1581 + difference 2 3) sourceC1581) = raw23802 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23802; decide +kernel
    rw [ha]
    exact (canonical23802 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 3) (sourceB1581 + difference 3 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 3) (sourceB1581 + difference 3 3) sourceC1581) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 4) (sourceB1581 + difference 4 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 4) (sourceB1581 + difference 4 3) sourceC1581) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1581 + difference 3 5) (sourceB1581 + difference 5 3) sourceC1581) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1581 + difference 3 5) (sourceB1581 + difference 5 3) sourceC1581) = raw23825 := by
      apply Matrix.ext; unfold tripleCharges sourceA1581 sourceB1581 sourceC1581 difference raw23825; decide +kernel
    rw [ha]
    exact (canonical23825 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1581 + sourceB1581) sourceC1581) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1581 + sourceB1581) sourceC1581) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1581 sourceB1581 sourceC1581 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1581 sourceB1581 sourceC1581
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1581, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1582 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1582 + difference 0 4) (sourceB1582 + difference 4 0) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1582 + difference 0 4) (sourceB1582 + difference 4 0) sourceC1582) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1582 + difference 1 4) (sourceB1582 + difference 4 1) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1582 + difference 1 4) (sourceB1582 + difference 4 1) sourceC1582) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1582 + difference 2 4) (sourceB1582 + difference 4 2) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1582 + difference 2 4) (sourceB1582 + difference 4 2) sourceC1582) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1582 + difference 3 4) (sourceB1582 + difference 4 3) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1582 + difference 3 4) (sourceB1582 + difference 4 3) sourceC1582) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1582 + difference 4 4) (sourceB1582 + difference 4 4) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1582 + difference 4 4) (sourceB1582 + difference 4 4) sourceC1582) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1582 + difference 5 4) (sourceB1582 + difference 4 5) sourceC1582) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1582 + difference 5 4) (sourceB1582 + difference 4 5) sourceC1582) = raw23828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1582 sourceB1582 sourceC1582 difference raw23828; decide +kernel
    rw [ha]
    exact (canonical23828 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1582 + sourceB1582) sourceC1582) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1582 + sourceB1582) sourceC1582) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1582 sourceB1582 sourceC1582 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1582 sourceB1582 sourceC1582
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1582, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1583 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 0) (sourceB1583 + difference 0 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 807) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 0) (sourceB1583 + difference 0 5) sourceC1583) = raw23829 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23829; decide +kernel
    rw [ha]
    exact (canonical23829 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 1) (sourceB1583 + difference 1 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1598) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 1) (sourceB1583 + difference 1 5) sourceC1583) = raw23830 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23830; decide +kernel
    rw [ha]
    exact (canonical23830 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 2) (sourceB1583 + difference 2 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 2) (sourceB1583 + difference 2 5) sourceC1583) = raw23803 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23803; decide +kernel
    rw [ha]
    exact (canonical23803 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 3) (sourceB1583 + difference 3 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 3) (sourceB1583 + difference 3 5) sourceC1583) = raw23831 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23831; decide +kernel
    rw [ha]
    exact (canonical23831 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 4) (sourceB1583 + difference 4 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 4) (sourceB1583 + difference 4 5) sourceC1583) = raw23828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23828; decide +kernel
    rw [ha]
    exact (canonical23828 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1583 + difference 5 5) (sourceB1583 + difference 5 5) sourceC1583) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1714) := by
    have ha : (tripleCharges (sourceA1583 + difference 5 5) (sourceB1583 + difference 5 5) sourceC1583) = raw23801 := by
      apply Matrix.ext; unfold tripleCharges sourceA1583 sourceB1583 sourceC1583 difference raw23801; decide +kernel
    rw [ha]
    exact (canonical23801 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1583 + sourceB1583) sourceC1583) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1583 + sourceB1583) sourceC1583) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1583 sourceB1583 sourceC1583 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1583 sourceB1583 sourceC1583
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1583, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1584 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 0) (sourceB1584 + difference 0 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 601) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 0) (sourceB1584 + difference 0 2) sourceC1584) = raw23832 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23832; decide +kernel
    rw [ha]
    exact (canonical23832 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 1) (sourceB1584 + difference 1 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 920) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 1) (sourceB1584 + difference 1 2) sourceC1584) = raw23833 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23833; decide +kernel
    rw [ha]
    exact (canonical23833 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 2) (sourceB1584 + difference 2 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1057) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 2) (sourceB1584 + difference 2 2) sourceC1584) = raw23834 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23834; decide +kernel
    rw [ha]
    exact (canonical23834 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 3) (sourceB1584 + difference 3 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 3) (sourceB1584 + difference 3 2) sourceC1584) = raw23835 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23835; decide +kernel
    rw [ha]
    exact (canonical23835 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 4) (sourceB1584 + difference 4 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1083) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 4) (sourceB1584 + difference 4 2) sourceC1584) = raw23836 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23836; decide +kernel
    rw [ha]
    exact (canonical23836 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1584 + difference 2 5) (sourceB1584 + difference 5 2) sourceC1584) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1079) := by
    have ha : (tripleCharges (sourceA1584 + difference 2 5) (sourceB1584 + difference 5 2) sourceC1584) = raw23837 := by
      apply Matrix.ext; unfold tripleCharges sourceA1584 sourceB1584 sourceC1584 difference raw23837; decide +kernel
    rw [ha]
    exact (canonical23837 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1584 + sourceB1584) sourceC1584) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1584 + sourceB1584) sourceC1584) = raw23838 := by
      apply Matrix.ext; unfold doubleCharges sourceA1584 sourceB1584 sourceC1584 raw23838; decide +kernel
    rw [ha]
    exact (canonical23838 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1584 sourceB1584 sourceC1584
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1584, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1585 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1585 + difference 0 2) (sourceB1585 + difference 2 0) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2884) := by
    have ha : (tripleCharges (sourceA1585 + difference 0 2) (sourceB1585 + difference 2 0) sourceC1585) = raw23839 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23839; decide +kernel
    rw [ha]
    exact (canonical23839 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1585 + difference 1 2) (sourceB1585 + difference 2 1) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1316) := by
    have ha : (tripleCharges (sourceA1585 + difference 1 2) (sourceB1585 + difference 2 1) sourceC1585) = raw23840 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23840; decide +kernel
    rw [ha]
    exact (canonical23840 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1585 + difference 2 2) (sourceB1585 + difference 2 2) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1370) := by
    have ha : (tripleCharges (sourceA1585 + difference 2 2) (sourceB1585 + difference 2 2) sourceC1585) = raw23841 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23841; decide +kernel
    rw [ha]
    exact (canonical23841 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1585 + difference 3 2) (sourceB1585 + difference 2 3) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1585 + difference 3 2) (sourceB1585 + difference 2 3) sourceC1585) = raw23842 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23842; decide +kernel
    rw [ha]
    exact (canonical23842 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1585 + difference 4 2) (sourceB1585 + difference 2 4) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1322) := by
    have ha : (tripleCharges (sourceA1585 + difference 4 2) (sourceB1585 + difference 2 4) sourceC1585) = raw23843 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23843; decide +kernel
    rw [ha]
    exact (canonical23843 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1585 + difference 5 2) (sourceB1585 + difference 2 5) sourceC1585) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1320) := by
    have ha : (tripleCharges (sourceA1585 + difference 5 2) (sourceB1585 + difference 2 5) sourceC1585) = raw23844 := by
      apply Matrix.ext; unfold tripleCharges sourceA1585 sourceB1585 sourceC1585 difference raw23844; decide +kernel
    rw [ha]
    exact (canonical23844 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1585 + sourceB1585) sourceC1585) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1585 + sourceB1585) sourceC1585) = raw13064 := by
      apply Matrix.ext; unfold doubleCharges sourceA1585 sourceB1585 sourceC1585 raw13064; decide +kernel
    rw [ha]
    exact (canonical13064 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1585 sourceB1585 sourceC1585
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1585, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1586 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 0) (sourceB1586 + difference 0 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 0) (sourceB1586 + difference 0 0) sourceC1586) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 1) (sourceB1586 + difference 1 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 1) (sourceB1586 + difference 1 0) sourceC1586) = raw23846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23846; decide +kernel
    rw [ha]
    exact (canonical23846 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 2) (sourceB1586 + difference 2 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 2) (sourceB1586 + difference 2 0) sourceC1586) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 3) (sourceB1586 + difference 3 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 3) (sourceB1586 + difference 3 0) sourceC1586) = raw23848 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23848; decide +kernel
    rw [ha]
    exact (canonical23848 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 4) (sourceB1586 + difference 4 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3246) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 4) (sourceB1586 + difference 4 0) sourceC1586) = raw23849 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23849; decide +kernel
    rw [ha]
    exact (canonical23849 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1586 + difference 0 5) (sourceB1586 + difference 5 0) sourceC1586) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3245) := by
    have ha : (tripleCharges (sourceA1586 + difference 0 5) (sourceB1586 + difference 5 0) sourceC1586) = raw23850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1586 sourceB1586 sourceC1586 difference raw23850; decide +kernel
    rw [ha]
    exact (canonical23850 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1586 + sourceB1586) sourceC1586) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1586 + sourceB1586) sourceC1586) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1586 sourceB1586 sourceC1586 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1586 sourceB1586 sourceC1586
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1586, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1587 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1587 + difference 0 2) (sourceB1587 + difference 2 0) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1587 + difference 0 2) (sourceB1587 + difference 2 0) sourceC1587) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1587 + difference 1 2) (sourceB1587 + difference 2 1) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1587 + difference 1 2) (sourceB1587 + difference 2 1) sourceC1587) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1587 + difference 2 2) (sourceB1587 + difference 2 2) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1587 + difference 2 2) (sourceB1587 + difference 2 2) sourceC1587) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1587 + difference 3 2) (sourceB1587 + difference 2 3) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1587 + difference 3 2) (sourceB1587 + difference 2 3) sourceC1587) = raw23852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23852; decide +kernel
    rw [ha]
    exact (canonical23852 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1587 + difference 4 2) (sourceB1587 + difference 2 4) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1587 + difference 4 2) (sourceB1587 + difference 2 4) sourceC1587) = raw23828 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23828; decide +kernel
    rw [ha]
    exact (canonical23828 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1587 + difference 5 2) (sourceB1587 + difference 2 5) sourceC1587) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1587 + difference 5 2) (sourceB1587 + difference 2 5) sourceC1587) = raw23853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1587 sourceB1587 sourceC1587 difference raw23853; decide +kernel
    rw [ha]
    exact (canonical23853 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1587 + sourceB1587) sourceC1587) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1587 + sourceB1587) sourceC1587) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1587 sourceB1587 sourceC1587 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1587 sourceB1587 sourceC1587
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1587, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1588 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 0) (sourceB1588 + difference 0 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 811) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 0) (sourceB1588 + difference 0 3) sourceC1588) = raw23854 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23854; decide +kernel
    rw [ha]
    exact (canonical23854 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 1) (sourceB1588 + difference 1 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 1) (sourceB1588 + difference 1 3) sourceC1588) = raw23855 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23855; decide +kernel
    rw [ha]
    exact (canonical23855 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 2) (sourceB1588 + difference 2 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 2) (sourceB1588 + difference 2 3) sourceC1588) = raw23852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23852; decide +kernel
    rw [ha]
    exact (canonical23852 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 3) (sourceB1588 + difference 3 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1709) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 3) (sourceB1588 + difference 3 3) sourceC1588) = raw23845 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23845; decide +kernel
    rw [ha]
    exact (canonical23845 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 4) (sourceB1588 + difference 4 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 4) (sourceB1588 + difference 4 3) sourceC1588) = raw23856 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23856; decide +kernel
    rw [ha]
    exact (canonical23856 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1588 + difference 3 5) (sourceB1588 + difference 5 3) sourceC1588) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1588 + difference 3 5) (sourceB1588 + difference 5 3) sourceC1588) = raw23857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1588 sourceB1588 sourceC1588 difference raw23857; decide +kernel
    rw [ha]
    exact (canonical23857 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1588 + sourceB1588) sourceC1588) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1588 + sourceB1588) sourceC1588) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1588 sourceB1588 sourceC1588 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1588 sourceB1588 sourceC1588
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1588, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1590 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1590 + difference 0 2) (sourceB1590 + difference 2 0) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2881) := by
    have ha : (tripleCharges (sourceA1590 + difference 0 2) (sourceB1590 + difference 2 0) sourceC1590) = raw23860 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23860; decide +kernel
    rw [ha]
    exact (canonical23860 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1590 + difference 1 2) (sourceB1590 + difference 2 1) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1314) := by
    have ha : (tripleCharges (sourceA1590 + difference 1 2) (sourceB1590 + difference 2 1) sourceC1590) = raw23861 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23861; decide +kernel
    rw [ha]
    exact (canonical23861 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1590 + difference 2 2) (sourceB1590 + difference 2 2) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1367) := by
    have ha : (tripleCharges (sourceA1590 + difference 2 2) (sourceB1590 + difference 2 2) sourceC1590) = raw23862 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23862; decide +kernel
    rw [ha]
    exact (canonical23862 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1590 + difference 3 2) (sourceB1590 + difference 2 3) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1318) := by
    have ha : (tripleCharges (sourceA1590 + difference 3 2) (sourceB1590 + difference 2 3) sourceC1590) = raw23863 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23863; decide +kernel
    rw [ha]
    exact (canonical23863 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1590 + difference 4 2) (sourceB1590 + difference 2 4) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1321) := by
    have ha : (tripleCharges (sourceA1590 + difference 4 2) (sourceB1590 + difference 2 4) sourceC1590) = raw23864 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23864; decide +kernel
    rw [ha]
    exact (canonical23864 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1590 + difference 5 2) (sourceB1590 + difference 2 5) sourceC1590) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1317) := by
    have ha : (tripleCharges (sourceA1590 + difference 5 2) (sourceB1590 + difference 2 5) sourceC1590) = raw23865 := by
      apply Matrix.ext; unfold tripleCharges sourceA1590 sourceB1590 sourceC1590 difference raw23865; decide +kernel
    rw [ha]
    exact (canonical23865 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1590 + sourceB1590) sourceC1590) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1590 + sourceB1590) sourceC1590) = raw23866 := by
      apply Matrix.ext; unfold doubleCharges sourceA1590 sourceB1590 sourceC1590 raw23866; decide +kernel
    rw [ha]
    exact (canonical23866 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1590 sourceB1590 sourceC1590
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1590, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1591 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 0) (sourceB1591 + difference 0 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 0) (sourceB1591 + difference 0 0) sourceC1591) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 1) (sourceB1591 + difference 1 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 1) (sourceB1591 + difference 1 0) sourceC1591) = raw23867 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23867; decide +kernel
    rw [ha]
    exact (canonical23867 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 2) (sourceB1591 + difference 2 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 2) (sourceB1591 + difference 2 0) sourceC1591) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 3) (sourceB1591 + difference 3 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3240) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 3) (sourceB1591 + difference 3 0) sourceC1591) = raw23868 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23868; decide +kernel
    rw [ha]
    exact (canonical23868 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 4) (sourceB1591 + difference 4 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3245) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 4) (sourceB1591 + difference 4 0) sourceC1591) = raw23850 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23850; decide +kernel
    rw [ha]
    exact (canonical23850 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1591 + difference 0 5) (sourceB1591 + difference 5 0) sourceC1591) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA1591 + difference 0 5) (sourceB1591 + difference 5 0) sourceC1591) = raw23869 := by
      apply Matrix.ext; unfold tripleCharges sourceA1591 sourceB1591 sourceC1591 difference raw23869; decide +kernel
    rw [ha]
    exact (canonical23869 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1591 + sourceB1591) sourceC1591) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1591 + sourceB1591) sourceC1591) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1591 sourceB1591 sourceC1591 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1591 sourceB1591 sourceC1591
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1591, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1592 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 0) (sourceB1592 + difference 0 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 827) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 0) (sourceB1592 + difference 0 3) sourceC1592) = raw23870 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23870; decide +kernel
    rw [ha]
    exact (canonical23870 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 1) (sourceB1592 + difference 1 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1609) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 1) (sourceB1592 + difference 1 3) sourceC1592) = raw23871 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23871; decide +kernel
    rw [ha]
    exact (canonical23871 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 2) (sourceB1592 + difference 2 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 2) (sourceB1592 + difference 2 3) sourceC1592) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 3) (sourceB1592 + difference 3 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 3) (sourceB1592 + difference 3 3) sourceC1592) = raw23827 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23827; decide +kernel
    rw [ha]
    exact (canonical23827 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 4) (sourceB1592 + difference 4 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1715) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 4) (sourceB1592 + difference 4 3) sourceC1592) = raw23857 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23857; decide +kernel
    rw [ha]
    exact (canonical23857 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1592 + difference 3 5) (sourceB1592 + difference 5 3) sourceC1592) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1658) := by
    have ha : (tripleCharges (sourceA1592 + difference 3 5) (sourceB1592 + difference 5 3) sourceC1592) = raw23872 := by
      apply Matrix.ext; unfold tripleCharges sourceA1592 sourceB1592 sourceC1592 difference raw23872; decide +kernel
    rw [ha]
    exact (canonical23872 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1592 + sourceB1592) sourceC1592) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1592 + sourceB1592) sourceC1592) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1592 sourceB1592 sourceC1592 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1592 sourceB1592 sourceC1592
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1592, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1594 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 0) (sourceB1594 + difference 0 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 578) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 0) (sourceB1594 + difference 0 1) sourceC1594) = raw23880 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23880; decide +kernel
    rw [ha]
    exact (canonical23880 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 1) (sourceB1594 + difference 1 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1020) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 1) (sourceB1594 + difference 1 1) sourceC1594) = raw11301 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw11301; decide +kernel
    rw [ha]
    exact (canonical11301 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 2) (sourceB1594 + difference 2 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 942) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 2) (sourceB1594 + difference 2 1) sourceC1594) = raw23881 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23881; decide +kernel
    rw [ha]
    exact (canonical23881 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 3) (sourceB1594 + difference 3 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 3) (sourceB1594 + difference 3 1) sourceC1594) = raw11299 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw11299; decide +kernel
    rw [ha]
    exact (canonical11299 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 4) (sourceB1594 + difference 4 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1041) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 4) (sourceB1594 + difference 4 1) sourceC1594) = raw23882 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23882; decide +kernel
    rw [ha]
    exact (canonical23882 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1594 + difference 1 5) (sourceB1594 + difference 5 1) sourceC1594) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1594 + difference 1 5) (sourceB1594 + difference 5 1) sourceC1594) = raw23883 := by
      apply Matrix.ext; unfold tripleCharges sourceA1594 sourceB1594 sourceC1594 difference raw23883; decide +kernel
    rw [ha]
    exact (canonical23883 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1594 + sourceB1594) sourceC1594) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1594 + sourceB1594) sourceC1594) = raw11298 := by
      apply Matrix.ext; unfold doubleCharges sourceA1594 sourceB1594 sourceC1594 raw11298; decide +kernel
    rw [ha]
    exact (canonical11298 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1594 sourceB1594 sourceC1594
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1594, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1595 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 0) (sourceB1595 + difference 0 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 0) (sourceB1595 + difference 0 0) sourceC1595) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 1) (sourceB1595 + difference 1 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 1) (sourceB1595 + difference 1 0) sourceC1595) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 2) (sourceB1595 + difference 2 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 2) (sourceB1595 + difference 2 0) sourceC1595) = raw23884 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23884; decide +kernel
    rw [ha]
    exact (canonical23884 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 3) (sourceB1595 + difference 3 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 3) (sourceB1595 + difference 3 0) sourceC1595) = raw23885 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23885; decide +kernel
    rw [ha]
    exact (canonical23885 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 4) (sourceB1595 + difference 4 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3282) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 4) (sourceB1595 + difference 4 0) sourceC1595) = raw23886 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23886; decide +kernel
    rw [ha]
    exact (canonical23886 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1595 + difference 0 5) (sourceB1595 + difference 5 0) sourceC1595) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3281) := by
    have ha : (tripleCharges (sourceA1595 + difference 0 5) (sourceB1595 + difference 5 0) sourceC1595) = raw23887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1595 sourceB1595 sourceC1595 difference raw23887; decide +kernel
    rw [ha]
    exact (canonical23887 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1595 + sourceB1595) sourceC1595) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1595 + sourceB1595) sourceC1595) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1595 sourceB1595 sourceC1595 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1595 sourceB1595 sourceC1595
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1595, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1344 : Integer.Sparse.reindex keyMap MixedData.row1344 = numericRow1344 := by decide +kernel

theorem numericCheck1344 (x : Master → ℝ) : Integer.Sparse.eval numericRow1344 x =
    (1 : ℝ) * reducedSource1344 x := by
  norm_num [numericRow1344, reducedSource1344, Integer.Sparse.eval, Sparse.eval, nodeValue604, nodeValue923, nodeValue1042, nodeValue1058, nodeValue1079, nodeValue1087, nodeValue4084]

theorem reindexCheck1345 : Integer.Sparse.reindex keyMap MixedData.row1345 = numericRow1345 := by decide +kernel

theorem numericCheck1345 (x : Master → ℝ) : Integer.Sparse.eval numericRow1345 x =
    (1 : ℝ) * reducedSource1345 x := by
  norm_num [numericRow1345, reducedSource1345, Integer.Sparse.eval, Sparse.eval, nodeValue1335, nodeValue1337, nodeValue1338, nodeValue1347, nodeValue1406, nodeValue2954, nodeValue4091]

theorem reindexCheck1346 : Integer.Sparse.reindex keyMap MixedData.row1346 = numericRow1346 := by decide +kernel

theorem numericCheck1346 (x : Master → ℝ) : Integer.Sparse.eval numericRow1346 x =
    (1 : ℝ) * reducedSource1346 x := by
  norm_num [numericRow1346, reducedSource1346, Integer.Sparse.eval, Sparse.eval, nodeValue1714, nodeValue2502, nodeValue3285, nodeValue3287, nodeValue3293, nodeValue3305, nodeValue4069]

theorem reindexCheck1347 : Integer.Sparse.reindex keyMap MixedData.row1347 = numericRow1347 := by decide +kernel

theorem numericCheck1347 (x : Master → ℝ) : Integer.Sparse.eval numericRow1347 x =
    (1 : ℝ) * reducedSource1347 x := by
  norm_num [numericRow1347, reducedSource1347, Integer.Sparse.eval, Sparse.eval, nodeValue824, nodeValue1607, nodeValue1656, nodeValue1714, nodeValue1737, nodeValue1739, nodeValue4069]

theorem reindexCheck1348 : Integer.Sparse.reindex keyMap MixedData.row1348 = numericRow1348 := by decide +kernel

theorem numericCheck1348 (x : Master → ℝ) : Integer.Sparse.eval numericRow1348 x =
    (1 : ℝ) * reducedSource1348 x := by
  norm_num [numericRow1348, reducedSource1348, Integer.Sparse.eval, Sparse.eval, nodeValue1713, nodeValue1714, nodeValue1715, nodeValue1724, nodeValue1737, nodeValue3293, nodeValue4069]

theorem reindexCheck1349 : Integer.Sparse.reindex keyMap MixedData.row1349 = numericRow1349 := by decide +kernel

theorem numericCheck1349 (x : Master → ℝ) : Integer.Sparse.eval numericRow1349 x =
    (1 : ℝ) * reducedSource1349 x := by
  norm_num [numericRow1349, reducedSource1349, Integer.Sparse.eval, Sparse.eval, nodeValue807, nodeValue1598, nodeValue1646, nodeValue1714, nodeValue1724, nodeValue1728, nodeValue4069]

theorem reindexCheck1350 : Integer.Sparse.reindex keyMap MixedData.row1350 = numericRow1350 := by decide +kernel

theorem numericCheck1350 (x : Master → ℝ) : Integer.Sparse.eval numericRow1350 x =
    (1 : ℝ) * reducedSource1350 x := by
  norm_num [numericRow1350, reducedSource1350, Integer.Sparse.eval, Sparse.eval, nodeValue601, nodeValue920, nodeValue1057, nodeValue1079, nodeValue1083, nodeValue4084]

theorem reindexCheck1351 : Integer.Sparse.reindex keyMap MixedData.row1351 = numericRow1351 := by decide +kernel

theorem numericCheck1351 (x : Master → ℝ) : Integer.Sparse.eval numericRow1351 x =
    (1 : ℝ) * reducedSource1351 x := by
  norm_num [numericRow1351, reducedSource1351, Integer.Sparse.eval, Sparse.eval, nodeValue1316, nodeValue1320, nodeValue1322, nodeValue1370, nodeValue2884, nodeValue4091]

theorem reindexCheck1352 : Integer.Sparse.reindex keyMap MixedData.row1352 = numericRow1352 := by decide +kernel

theorem numericCheck1352 (x : Master → ℝ) : Integer.Sparse.eval numericRow1352 x =
    (1 : ℝ) * reducedSource1352 x := by
  norm_num [numericRow1352, reducedSource1352, Integer.Sparse.eval, Sparse.eval, nodeValue1709, nodeValue3241, nodeValue3245, nodeValue3246, nodeValue3299, nodeValue4069]

theorem reindexCheck1353 : Integer.Sparse.reindex keyMap MixedData.row1353 = numericRow1353 := by decide +kernel

theorem numericCheck1353 (x : Master → ℝ) : Integer.Sparse.eval numericRow1353 x =
    (1 : ℝ) * reducedSource1353 x := by
  norm_num [numericRow1353, reducedSource1353, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue1707, nodeValue1709, nodeValue1724, nodeValue3299, nodeValue4069]

theorem reindexCheck1354 : Integer.Sparse.reindex keyMap MixedData.row1354 = numericRow1354 := by decide +kernel

theorem numericCheck1354 (x : Master → ℝ) : Integer.Sparse.eval numericRow1354 x =
    (1 : ℝ) * reducedSource1354 x := by
  norm_num [numericRow1354, reducedSource1354, Integer.Sparse.eval, Sparse.eval, nodeValue811, nodeValue1601, nodeValue1649, nodeValue1709, nodeValue1715, nodeValue1724, nodeValue4069]

theorem reindexCheck1355 : Integer.Sparse.reindex keyMap MixedData.row1355 = numericRow1355 := by decide +kernel

theorem numericCheck1355 (x : Master → ℝ) : Integer.Sparse.eval numericRow1355 x =
    (1 : ℝ) * reducedSource1355 x := by
  norm_num [numericRow1355, reducedSource1355, Integer.Sparse.eval, Sparse.eval, nodeValue1314, nodeValue1317, nodeValue1318, nodeValue1321, nodeValue1367, nodeValue2881, nodeValue4092]

theorem reindexCheck1356 : Integer.Sparse.reindex keyMap MixedData.row1356 = numericRow1356 := by decide +kernel

theorem numericCheck1356 (x : Master → ℝ) : Integer.Sparse.eval numericRow1356 x =
    (1 : ℝ) * reducedSource1356 x := by
  norm_num [numericRow1356, reducedSource1356, Integer.Sparse.eval, Sparse.eval, nodeValue1715, nodeValue2466, nodeValue3238, nodeValue3240, nodeValue3245, nodeValue3293, nodeValue4069]

theorem reindexCheck1357 : Integer.Sparse.reindex keyMap MixedData.row1357 = numericRow1357 := by decide +kernel

theorem numericCheck1357 (x : Master → ℝ) : Integer.Sparse.eval numericRow1357 x =
    (1 : ℝ) * reducedSource1357 x := by
  norm_num [numericRow1357, reducedSource1357, Integer.Sparse.eval, Sparse.eval, nodeValue827, nodeValue1609, nodeValue1658, nodeValue1715, nodeValue1737, nodeValue4069]

theorem reindexCheck1358 : Integer.Sparse.reindex keyMap MixedData.row1358 = numericRow1358 := by decide +kernel

theorem numericCheck1358 (x : Master → ℝ) : Integer.Sparse.eval numericRow1358 x =
    (1 : ℝ) * reducedSource1358 x := by
  norm_num [numericRow1358, reducedSource1358, Integer.Sparse.eval, Sparse.eval, nodeValue578, nodeValue942, nodeValue1020, nodeValue1039, nodeValue1041, nodeValue4083]

theorem reindexCheck1359 : Integer.Sparse.reindex keyMap MixedData.row1359 = numericRow1359 := by decide +kernel

theorem numericCheck1359 (x : Master → ℝ) : Integer.Sparse.eval numericRow1359 x =
    (1 : ℝ) * reducedSource1359 x := by
  norm_num [numericRow1359, reducedSource1359, Integer.Sparse.eval, Sparse.eval, nodeValue1705, nodeValue3281, nodeValue3282, nodeValue3299, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows84
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1344 (mixedVector B) = 0 := by
  have h604 : mixedVector B (Sum.inr 604) = Sparse.eval nodeValue604 (mixedVector B) := by
    change mixedMoment B node604 node604Labels = _
    exact sound604 B hB hF
  have h923 : mixedVector B (Sum.inr 923) = Sparse.eval nodeValue923 (mixedVector B) := by
    change mixedMoment B node923 node923Labels = _
    exact sound923 B hB hF
  have h1042 : mixedVector B (Sum.inr 1042) = Sparse.eval nodeValue1042 (mixedVector B) := by
    change mixedMoment B node1042 node1042Labels = _
    exact sound1042 B hB hF
  have h1058 : mixedVector B (Sum.inr 1058) = Sparse.eval nodeValue1058 (mixedVector B) := by
    change mixedMoment B node1058 node1058Labels = _
    exact sound1058 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1087 : mixedVector B (Sum.inr 1087) = Sparse.eval nodeValue1087 (mixedVector B) := by
    change mixedMoment B node1087 node1087Labels = _
    exact sound1087 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1578, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h604, h923, h1042, h1058, h1079, h1087, h4084, reducedSource1344] using sourceEq1578 B hB

theorem rowSound1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1344 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1344, numericCheck1344, reducedZero1344 B hB hF, mul_zero]

theorem reducedZero1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1345 (mixedVector B) = 0 := by
  have h1335 : mixedVector B (Sum.inr 1335) = Sparse.eval nodeValue1335 (mixedVector B) := by
    change mixedMoment B node1335 node1335Labels = _
    exact sound1335 B hB hF
  have h1337 : mixedVector B (Sum.inr 1337) = Sparse.eval nodeValue1337 (mixedVector B) := by
    change mixedMoment B node1337 node1337Labels = _
    exact sound1337 B hB hF
  have h1338 : mixedVector B (Sum.inr 1338) = Sparse.eval nodeValue1338 (mixedVector B) := by
    change mixedMoment B node1338 node1338Labels = _
    exact sound1338 B hB hF
  have h1347 : mixedVector B (Sum.inr 1347) = Sparse.eval nodeValue1347 (mixedVector B) := by
    change mixedMoment B node1347 node1347Labels = _
    exact sound1347 B hB hF
  have h1406 : mixedVector B (Sum.inr 1406) = Sparse.eval nodeValue1406 (mixedVector B) := by
    change mixedMoment B node1406 node1406Labels = _
    exact sound1406 B hB hF
  have h2954 : mixedVector B (Sum.inr 2954) = Sparse.eval nodeValue2954 (mixedVector B) := by
    change mixedMoment B node2954 node2954Labels = _
    exact sound2954 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1579, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1335, h1337, h1338, h1347, h1406, h2954, h4091, reducedSource1345] using sourceEq1579 B hB

theorem rowSound1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1345 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1345, numericCheck1345, reducedZero1345 B hB hF, mul_zero]

theorem reducedZero1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1346 (mixedVector B) = 0 := by
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1580, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1714, h2502, h3285, h3287, h3293, h3305, h4069, reducedSource1346] using sourceEq1580 B hB

theorem rowSound1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1346 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1346, numericCheck1346, reducedZero1346 B hB hF, mul_zero]

theorem reducedZero1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1347 (mixedVector B) = 0 := by
  have h824 : mixedVector B (Sum.inr 824) = Sparse.eval nodeValue824 (mixedVector B) := by
    change mixedMoment B node824 node824Labels = _
    exact sound824 B hB hF
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1581, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h824, h1607, h1656, h1714, h1737, h1739, h4069, reducedSource1347] using sourceEq1581 B hB

theorem rowSound1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1347 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1347, numericCheck1347, reducedZero1347 B hB hF, mul_zero]

theorem reducedZero1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1348 (mixedVector B) = 0 := by
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1582, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1713, h1714, h1715, h1724, h1737, h3293, h4069, reducedSource1348] using sourceEq1582 B hB

theorem rowSound1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1348 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1348, numericCheck1348, reducedZero1348 B hB hF, mul_zero]

theorem reducedZero1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1349 (mixedVector B) = 0 := by
  have h807 : mixedVector B (Sum.inr 807) = Sparse.eval nodeValue807 (mixedVector B) := by
    change mixedMoment B node807 node807Labels = _
    exact sound807 B hB hF
  have h1598 : mixedVector B (Sum.inr 1598) = Sparse.eval nodeValue1598 (mixedVector B) := by
    change mixedMoment B node1598 node1598Labels = _
    exact sound1598 B hB hF
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1714 : mixedVector B (Sum.inr 1714) = Sparse.eval nodeValue1714 (mixedVector B) := by
    change mixedMoment B node1714 node1714Labels = _
    exact sound1714 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1583, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h807, h1598, h1646, h1714, h1724, h1728, h4069, reducedSource1349] using sourceEq1583 B hB

theorem rowSound1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1349 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1349, numericCheck1349, reducedZero1349 B hB hF, mul_zero]

theorem reducedZero1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1350 (mixedVector B) = 0 := by
  have h601 : mixedVector B (Sum.inr 601) = Sparse.eval nodeValue601 (mixedVector B) := by
    change mixedMoment B node601 node601Labels = _
    exact sound601 B hB hF
  have h920 : mixedVector B (Sum.inr 920) = Sparse.eval nodeValue920 (mixedVector B) := by
    change mixedMoment B node920 node920Labels = _
    exact sound920 B hB hF
  have h1057 : mixedVector B (Sum.inr 1057) = Sparse.eval nodeValue1057 (mixedVector B) := by
    change mixedMoment B node1057 node1057Labels = _
    exact sound1057 B hB hF
  have h1079 : mixedVector B (Sum.inr 1079) = Sparse.eval nodeValue1079 (mixedVector B) := by
    change mixedMoment B node1079 node1079Labels = _
    exact sound1079 B hB hF
  have h1083 : mixedVector B (Sum.inr 1083) = Sparse.eval nodeValue1083 (mixedVector B) := by
    change mixedMoment B node1083 node1083Labels = _
    exact sound1083 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1584, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h601, h920, h1057, h1079, h1083, h4084, reducedSource1350] using sourceEq1584 B hB

theorem rowSound1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1350 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1350, numericCheck1350, reducedZero1350 B hB hF, mul_zero]

theorem reducedZero1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1351 (mixedVector B) = 0 := by
  have h1316 : mixedVector B (Sum.inr 1316) = Sparse.eval nodeValue1316 (mixedVector B) := by
    change mixedMoment B node1316 node1316Labels = _
    exact sound1316 B hB hF
  have h1320 : mixedVector B (Sum.inr 1320) = Sparse.eval nodeValue1320 (mixedVector B) := by
    change mixedMoment B node1320 node1320Labels = _
    exact sound1320 B hB hF
  have h1322 : mixedVector B (Sum.inr 1322) = Sparse.eval nodeValue1322 (mixedVector B) := by
    change mixedMoment B node1322 node1322Labels = _
    exact sound1322 B hB hF
  have h1370 : mixedVector B (Sum.inr 1370) = Sparse.eval nodeValue1370 (mixedVector B) := by
    change mixedMoment B node1370 node1370Labels = _
    exact sound1370 B hB hF
  have h2884 : mixedVector B (Sum.inr 2884) = Sparse.eval nodeValue2884 (mixedVector B) := by
    change mixedMoment B node2884 node2884Labels = _
    exact sound2884 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1585, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1316, h1320, h1322, h1370, h2884, h4091, reducedSource1351] using sourceEq1585 B hB

theorem rowSound1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1351 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1351, numericCheck1351, reducedZero1351 B hB hF, mul_zero]

theorem reducedZero1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1352 (mixedVector B) = 0 := by
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3245 : mixedVector B (Sum.inr 3245) = Sparse.eval nodeValue3245 (mixedVector B) := by
    change mixedMoment B node3245 node3245Labels = _
    exact sound3245 B hB hF
  have h3246 : mixedVector B (Sum.inr 3246) = Sparse.eval nodeValue3246 (mixedVector B) := by
    change mixedMoment B node3246 node3246Labels = _
    exact sound3246 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1586, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1709, h3241, h3245, h3246, h3299, h4069, reducedSource1352] using sourceEq1586 B hB

theorem rowSound1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1352 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1352, numericCheck1352, reducedZero1352 B hB hF, mul_zero]

theorem reducedZero1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1353 (mixedVector B) = 0 := by
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1587, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1705, h1707, h1709, h1724, h3299, h4069, reducedSource1353] using sourceEq1587 B hB

theorem rowSound1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1353 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1353, numericCheck1353, reducedZero1353 B hB hF, mul_zero]

theorem reducedZero1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1354 (mixedVector B) = 0 := by
  have h811 : mixedVector B (Sum.inr 811) = Sparse.eval nodeValue811 (mixedVector B) := by
    change mixedMoment B node811 node811Labels = _
    exact sound811 B hB hF
  have h1601 : mixedVector B (Sum.inr 1601) = Sparse.eval nodeValue1601 (mixedVector B) := by
    change mixedMoment B node1601 node1601Labels = _
    exact sound1601 B hB hF
  have h1649 : mixedVector B (Sum.inr 1649) = Sparse.eval nodeValue1649 (mixedVector B) := by
    change mixedMoment B node1649 node1649Labels = _
    exact sound1649 B hB hF
  have h1709 : mixedVector B (Sum.inr 1709) = Sparse.eval nodeValue1709 (mixedVector B) := by
    change mixedMoment B node1709 node1709Labels = _
    exact sound1709 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1588, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h811, h1601, h1649, h1709, h1715, h1724, h4069, reducedSource1354] using sourceEq1588 B hB

theorem rowSound1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1354 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1354, numericCheck1354, reducedZero1354 B hB hF, mul_zero]

theorem reducedZero1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1355 (mixedVector B) = 0 := by
  have h1314 : mixedVector B (Sum.inr 1314) = Sparse.eval nodeValue1314 (mixedVector B) := by
    change mixedMoment B node1314 node1314Labels = _
    exact sound1314 B hB hF
  have h1317 : mixedVector B (Sum.inr 1317) = Sparse.eval nodeValue1317 (mixedVector B) := by
    change mixedMoment B node1317 node1317Labels = _
    exact sound1317 B hB hF
  have h1318 : mixedVector B (Sum.inr 1318) = Sparse.eval nodeValue1318 (mixedVector B) := by
    change mixedMoment B node1318 node1318Labels = _
    exact sound1318 B hB hF
  have h1321 : mixedVector B (Sum.inr 1321) = Sparse.eval nodeValue1321 (mixedVector B) := by
    change mixedMoment B node1321 node1321Labels = _
    exact sound1321 B hB hF
  have h1367 : mixedVector B (Sum.inr 1367) = Sparse.eval nodeValue1367 (mixedVector B) := by
    change mixedMoment B node1367 node1367Labels = _
    exact sound1367 B hB hF
  have h2881 : mixedVector B (Sum.inr 2881) = Sparse.eval nodeValue2881 (mixedVector B) := by
    change mixedMoment B node2881 node2881Labels = _
    exact sound2881 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1590, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1314, h1317, h1318, h1321, h1367, h2881, h4092, reducedSource1355] using sourceEq1590 B hB

theorem rowSound1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1355 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1355, numericCheck1355, reducedZero1355 B hB hF, mul_zero]

theorem reducedZero1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1356 (mixedVector B) = 0 := by
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3240 : mixedVector B (Sum.inr 3240) = Sparse.eval nodeValue3240 (mixedVector B) := by
    change mixedMoment B node3240 node3240Labels = _
    exact sound3240 B hB hF
  have h3245 : mixedVector B (Sum.inr 3245) = Sparse.eval nodeValue3245 (mixedVector B) := by
    change mixedMoment B node3245 node3245Labels = _
    exact sound3245 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1591, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1715, h2466, h3238, h3240, h3245, h3293, h4069, reducedSource1356] using sourceEq1591 B hB

theorem rowSound1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1356 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1356, numericCheck1356, reducedZero1356 B hB hF, mul_zero]

theorem reducedZero1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1357 (mixedVector B) = 0 := by
  have h827 : mixedVector B (Sum.inr 827) = Sparse.eval nodeValue827 (mixedVector B) := by
    change mixedMoment B node827 node827Labels = _
    exact sound827 B hB hF
  have h1609 : mixedVector B (Sum.inr 1609) = Sparse.eval nodeValue1609 (mixedVector B) := by
    change mixedMoment B node1609 node1609Labels = _
    exact sound1609 B hB hF
  have h1658 : mixedVector B (Sum.inr 1658) = Sparse.eval nodeValue1658 (mixedVector B) := by
    change mixedMoment B node1658 node1658Labels = _
    exact sound1658 B hB hF
  have h1715 : mixedVector B (Sum.inr 1715) = Sparse.eval nodeValue1715 (mixedVector B) := by
    change mixedMoment B node1715 node1715Labels = _
    exact sound1715 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1592, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h827, h1609, h1658, h1715, h1737, h4069, reducedSource1357] using sourceEq1592 B hB

theorem rowSound1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1357 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1357, numericCheck1357, reducedZero1357 B hB hF, mul_zero]

theorem reducedZero1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1358 (mixedVector B) = 0 := by
  have h578 : mixedVector B (Sum.inr 578) = Sparse.eval nodeValue578 (mixedVector B) := by
    change mixedMoment B node578 node578Labels = _
    exact sound578 B hB hF
  have h942 : mixedVector B (Sum.inr 942) = Sparse.eval nodeValue942 (mixedVector B) := by
    change mixedMoment B node942 node942Labels = _
    exact sound942 B hB hF
  have h1020 : mixedVector B (Sum.inr 1020) = Sparse.eval nodeValue1020 (mixedVector B) := by
    change mixedMoment B node1020 node1020Labels = _
    exact sound1020 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1041 : mixedVector B (Sum.inr 1041) = Sparse.eval nodeValue1041 (mixedVector B) := by
    change mixedMoment B node1041 node1041Labels = _
    exact sound1041 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1594, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h578, h942, h1020, h1039, h1041, h4083, reducedSource1358] using sourceEq1594 B hB

theorem rowSound1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1358 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1358, numericCheck1358, reducedZero1358 B hB hF, mul_zero]

theorem reducedZero1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1359 (mixedVector B) = 0 := by
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h3281 : mixedVector B (Sum.inr 3281) = Sparse.eval nodeValue3281 (mixedVector B) := by
    change mixedMoment B node3281 node3281Labels = _
    exact sound3281 B hB hF
  have h3282 : mixedVector B (Sum.inr 3282) = Sparse.eval nodeValue3282 (mixedVector B) := by
    change mixedMoment B node3282 node3282Labels = _
    exact sound3282 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1595, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1705, h3281, h3282, h3299, h4069, reducedSource1359] using sourceEq1595 B hB

theorem rowSound1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1359 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1359, numericCheck1359, reducedZero1359 B hB hF, mul_zero]

theorem sourceRowsAt1344 : MixedData.sourceRows (1344 : Fin 2425) =
    MixedData.row1344 := by decide +kernel

theorem sourceRowsAt1345 : MixedData.sourceRows (1345 : Fin 2425) =
    MixedData.row1345 := by decide +kernel

theorem sourceRowsAt1346 : MixedData.sourceRows (1346 : Fin 2425) =
    MixedData.row1346 := by decide +kernel

theorem sourceRowsAt1347 : MixedData.sourceRows (1347 : Fin 2425) =
    MixedData.row1347 := by decide +kernel

theorem sourceRowsAt1348 : MixedData.sourceRows (1348 : Fin 2425) =
    MixedData.row1348 := by decide +kernel

theorem sourceRowsAt1349 : MixedData.sourceRows (1349 : Fin 2425) =
    MixedData.row1349 := by decide +kernel

theorem sourceRowsAt1350 : MixedData.sourceRows (1350 : Fin 2425) =
    MixedData.row1350 := by decide +kernel

theorem sourceRowsAt1351 : MixedData.sourceRows (1351 : Fin 2425) =
    MixedData.row1351 := by decide +kernel

theorem sourceRowsAt1352 : MixedData.sourceRows (1352 : Fin 2425) =
    MixedData.row1352 := by decide +kernel

theorem sourceRowsAt1353 : MixedData.sourceRows (1353 : Fin 2425) =
    MixedData.row1353 := by decide +kernel

theorem sourceRowsAt1354 : MixedData.sourceRows (1354 : Fin 2425) =
    MixedData.row1354 := by decide +kernel

theorem sourceRowsAt1355 : MixedData.sourceRows (1355 : Fin 2425) =
    MixedData.row1355 := by decide +kernel

theorem sourceRowsAt1356 : MixedData.sourceRows (1356 : Fin 2425) =
    MixedData.row1356 := by decide +kernel

theorem sourceRowsAt1357 : MixedData.sourceRows (1357 : Fin 2425) =
    MixedData.row1357 := by decide +kernel

theorem sourceRowsAt1358 : MixedData.sourceRows (1358 : Fin 2425) =
    MixedData.row1358 := by decide +kernel

theorem sourceRowsAt1359 : MixedData.sourceRows (1359 : Fin 2425) =
    MixedData.row1359 := by decide +kernel

theorem chunkSound84_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 84) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1344 ∨ k.val = 1345 ∨ k.val = 1346 ∨ k.val = 1347 ∨ k.val = 1348 ∨ k.val = 1349 ∨ k.val = 1350 ∨ k.val = 1351 ∨ k.val = 1352 ∨ k.val = 1353 ∨ k.val = 1354 ∨ k.val = 1355 ∨ k.val = 1356 ∨ k.val = 1357 ∨ k.val = 1358 ∨ k.val = 1359 := by omega
  rcases heq with h1344 | h1345 | h1346 | h1347 | h1348 | h1349 | h1350 | h1351 | h1352 | h1353 | h1354 | h1355 | h1356 | h1357 | h1358 | h1359
  · have he : k = (1344 : Fin 2425) := Fin.ext h1344
    subst k
    rw [sourceRowsAt1344]
    exact rowSound1344 B hB hF
  · have he : k = (1345 : Fin 2425) := Fin.ext h1345
    subst k
    rw [sourceRowsAt1345]
    exact rowSound1345 B hB hF
  · have he : k = (1346 : Fin 2425) := Fin.ext h1346
    subst k
    rw [sourceRowsAt1346]
    exact rowSound1346 B hB hF
  · have he : k = (1347 : Fin 2425) := Fin.ext h1347
    subst k
    rw [sourceRowsAt1347]
    exact rowSound1347 B hB hF
  · have he : k = (1348 : Fin 2425) := Fin.ext h1348
    subst k
    rw [sourceRowsAt1348]
    exact rowSound1348 B hB hF
  · have he : k = (1349 : Fin 2425) := Fin.ext h1349
    subst k
    rw [sourceRowsAt1349]
    exact rowSound1349 B hB hF
  · have he : k = (1350 : Fin 2425) := Fin.ext h1350
    subst k
    rw [sourceRowsAt1350]
    exact rowSound1350 B hB hF
  · have he : k = (1351 : Fin 2425) := Fin.ext h1351
    subst k
    rw [sourceRowsAt1351]
    exact rowSound1351 B hB hF
  · have he : k = (1352 : Fin 2425) := Fin.ext h1352
    subst k
    rw [sourceRowsAt1352]
    exact rowSound1352 B hB hF
  · have he : k = (1353 : Fin 2425) := Fin.ext h1353
    subst k
    rw [sourceRowsAt1353]
    exact rowSound1353 B hB hF
  · have he : k = (1354 : Fin 2425) := Fin.ext h1354
    subst k
    rw [sourceRowsAt1354]
    exact rowSound1354 B hB hF
  · have he : k = (1355 : Fin 2425) := Fin.ext h1355
    subst k
    rw [sourceRowsAt1355]
    exact rowSound1355 B hB hF
  · have he : k = (1356 : Fin 2425) := Fin.ext h1356
    subst k
    rw [sourceRowsAt1356]
    exact rowSound1356 B hB hF
  · have he : k = (1357 : Fin 2425) := Fin.ext h1357
    subst k
    rw [sourceRowsAt1357]
    exact rowSound1357 B hB hF
  · have he : k = (1358 : Fin 2425) := Fin.ext h1358
    subst k
    rw [sourceRowsAt1358]
    exact rowSound1358 B hB hF
  · have he : k = (1359 : Fin 2425) := Fin.ext h1359
    subst k
    rw [sourceRowsAt1359]
    exact rowSound1359 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound84_e_oai
