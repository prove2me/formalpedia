-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:39:38.822847+00:00
-- url     : https://prove2.me/submissions/ec17ac42-537d-468c-85b2-8c20ffbf684d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E090
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E193
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

theorem canonical23940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23940 raw23940Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw23940 raw23940Labels = mixedMoment B raw23940step0 raw23940step0Labels := by
      have hz : ∀ j, raw23940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23940step0 = (fun i j => raw23940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23940step0 raw23940; decide +kernel
      have hl : raw23940step0Labels = raw23940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23940 raw23940Labels permutation346 hz
    mixedMoment B raw23940step0 raw23940step0Labels = mixedMoment B raw23940step1 raw23940step1Labels := by
      have ha : raw23940step1 = (fun i j => raw23940step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23940step1 raw23940step0; decide +kernel
      have hl : raw23940step1Labels = raw23940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23940step0 raw23940step0Labels permutation51 permutation2
    mixedMoment B raw23940step1 raw23940step1Labels = mixedMoment B raw23940step2 raw23940step2Labels := by
      have ha : raw23940step2 = -raw23940step1 := by apply Matrix.ext; change ∀ i j, raw23940step2 i j = -(raw23940step1 i j); unfold raw23940step2 raw23940step1; decide +kernel
      have hl : raw23940step2Labels = raw23940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

theorem canonical23942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23942 raw23942Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23942 raw23942Labels = mixedMoment B raw23942step0 raw23942step0Labels := by
      have hz : ∀ j, raw23942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23942step0 = (fun i j => raw23942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23942step0 raw23942; decide +kernel
      have hl : raw23942step0Labels = raw23942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23942 raw23942Labels permutation346 hz
    mixedMoment B raw23942step0 raw23942step0Labels = mixedMoment B raw23942step1 raw23942step1Labels := by
      have ha : raw23942step1 = (fun i j => raw23942step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23942step1 raw23942step0; decide +kernel
      have hl : raw23942step1Labels = raw23942step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23942step0 raw23942step0Labels permutation50 permutation2
    mixedMoment B raw23942step1 raw23942step1Labels = mixedMoment B raw23942step2 raw23942step2Labels := by
      have ha : raw23942step2 = -raw23942step1 := by apply Matrix.ext; change ∀ i j, raw23942step2 i j = -(raw23942step1 i j); unfold raw23942step2 raw23942step1; decide +kernel
      have hl : raw23942step2Labels = raw23942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical23945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23945 raw23945Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw23945 raw23945Labels = mixedMoment B raw23945step0 raw23945step0Labels := by
      have hz : ∀ j, raw23945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23945step0 = (fun i j => raw23945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23945step0 raw23945; decide +kernel
      have hl : raw23945step0Labels = raw23945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23945 raw23945Labels permutation346 hz
    mixedMoment B raw23945step0 raw23945step0Labels = mixedMoment B raw23945step1 raw23945step1Labels := by
      have hz : ∀ j, raw23945step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23945step1 = (fun i j => raw23945step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23945step1 raw23945step0; decide +kernel
      have hl : raw23945step1Labels = raw23945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23945step0 raw23945step0Labels permutation56 hz
    mixedMoment B raw23945step1 raw23945step1Labels = mixedMoment B raw23945step2 raw23945step2Labels := by
      have ha : raw23945step2 = (fun i j => raw23945step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23945step2 raw23945step1; decide +kernel
      have hl : raw23945step2Labels = raw23945step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23945step1 raw23945step1Labels permutation31 permutation4
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical23952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23952 raw23952Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23952 raw23952Labels = mixedMoment B raw23952step0 raw23952step0Labels := by
      have hz : ∀ j, raw23952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23952step0 = (fun i j => raw23952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23952step0 raw23952; decide +kernel
      have hl : raw23952step0Labels = raw23952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23952 raw23952Labels permutation346 hz
    mixedMoment B raw23952step0 raw23952step0Labels = mixedMoment B raw23952step1 raw23952step1Labels := by
      have ha : raw23952step1 = (fun i j => raw23952step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23952step1 raw23952step0; decide +kernel
      have hl : raw23952step1Labels = raw23952step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23952step0 raw23952step0Labels permutation34 permutation4
    mixedMoment B raw23952step1 raw23952step1Labels = mixedMoment B raw23952step2 raw23952step2Labels := by
      have ha : raw23952step2 = -raw23952step1 := by apply Matrix.ext; change ∀ i j, raw23952step2 i j = -(raw23952step1 i j); unfold raw23952step2 raw23952step1; decide +kernel
      have hl : raw23952step2Labels = raw23952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical23953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23953 raw23953Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw23953 raw23953Labels = mixedMoment B raw23953step0 raw23953step0Labels := by
      have ha : raw23953step0 = (fun i j => raw23953 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23953step0 raw23953; decide +kernel
      have hl : raw23953step0Labels = raw23953Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23953 raw23953Labels permutation160 permutation4
    mixedMoment B raw23953step0 raw23953step0Labels = mixedMoment B raw23953step1 raw23953step1Labels := by
      have ha : raw23953step1 = -raw23953step0 := by apply Matrix.ext; change ∀ i j, raw23953step1 i j = -(raw23953step0 i j); unfold raw23953step1 raw23953step0; decide +kernel
      have hl : raw23953step1Labels = raw23953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical23969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23969 raw23969Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw23969 raw23969Labels = mixedMoment B raw23969step0 raw23969step0Labels := by
      have hz : ∀ j, raw23969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23969step0 = (fun i j => raw23969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23969step0 raw23969; decide +kernel
      have hl : raw23969step0Labels = raw23969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23969 raw23969Labels permutation346 hz
    mixedMoment B raw23969step0 raw23969step0Labels = mixedMoment B raw23969step1 raw23969step1Labels := by
      have ha : raw23969step1 = (fun i j => raw23969step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23969step1 raw23969step0; decide +kernel
      have hl : raw23969step1Labels = raw23969step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23969step0 raw23969step0Labels permutation45 permutation2
    mixedMoment B raw23969step1 raw23969step1Labels = mixedMoment B raw23969step2 raw23969step2Labels := by
      have ha : raw23969step2 = -raw23969step1 := by apply Matrix.ext; change ∀ i j, raw23969step2 i j = -(raw23969step1 i j); unfold raw23969step2 raw23969step1; decide +kernel
      have hl : raw23969step2Labels = raw23969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1646 node1646Labels := by rfl

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

theorem canonical24024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24024 raw24024Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw24024 raw24024Labels = mixedMoment B raw24024step0 raw24024step0Labels := by
      have ha : raw24024step0 = (fun i j => raw24024 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24024step0 raw24024; decide +kernel
      have hl : raw24024step0Labels = raw24024Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24024 raw24024Labels permutation176 permutation2
    _ = mixedMoment B node2483 node2483Labels := by rfl

theorem canonical24025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24025 raw24025Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24025 raw24025Labels = mixedMoment B raw24025step0 raw24025step0Labels := by
      have ha : raw24025step0 = (fun i j => raw24025 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24025step0 raw24025; decide +kernel
      have hl : raw24025step0Labels = raw24025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24025 raw24025Labels permutation179 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

theorem canonical24026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24026 raw24026Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24026 raw24026Labels = mixedMoment B raw24026step0 raw24026step0Labels := by
      have ha : raw24026step0 = (fun i j => raw24026 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24026step0 raw24026; decide +kernel
      have hl : raw24026step0Labels = raw24026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24026 raw24026Labels permutation177 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

theorem canonical24027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24027 raw24027Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw24027 raw24027Labels = mixedMoment B raw24027step0 raw24027step0Labels := by
      have ha : raw24027step0 = (fun i j => raw24027 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24027step0 raw24027; decide +kernel
      have hl : raw24027step0Labels = raw24027Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24027 raw24027Labels permutation176 permutation2
    _ = mixedMoment B node1116 node1116Labels := by rfl

theorem canonical24028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24028 raw24028Labels = mixedMoment B node1609 node1609Labels := by
  calc
    mixedMoment B raw24028 raw24028Labels = mixedMoment B raw24028step0 raw24028step0Labels := by
      have ha : raw24028step0 = (fun i j => raw24028 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24028step0 raw24028; decide +kernel
      have hl : raw24028step0Labels = raw24028Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24028 raw24028Labels permutation197 permutation2
    mixedMoment B raw24028step0 raw24028step0Labels = mixedMoment B raw24028step1 raw24028step1Labels := by
      have ha : raw24028step1 = -raw24028step0 := by apply Matrix.ext; change ∀ i j, raw24028step1 i j = -(raw24028step0 i j); unfold raw24028step1 raw24028step0; decide +kernel
      have hl : raw24028step1Labels = raw24028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1609 node1609Labels := by rfl

theorem canonical24029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24029 raw24029Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw24029 raw24029Labels = mixedMoment B raw24029step0 raw24029step0Labels := by
      have ha : raw24029step0 = (fun i j => raw24029 (permutation195 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24029step0 raw24029; decide +kernel
      have hl : raw24029step0Labels = raw24029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24029 raw24029Labels permutation195 permutation2
    mixedMoment B raw24029step0 raw24029step0Labels = mixedMoment B raw24029step1 raw24029step1Labels := by
      have ha : raw24029step1 = -raw24029step0 := by apply Matrix.ext; change ∀ i j, raw24029step1 i j = -(raw24029step0 i j); unfold raw24029step1 raw24029step0; decide +kernel
      have hl : raw24029step1Labels = raw24029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1607 node1607Labels := by rfl

theorem canonical24030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24030 raw24030Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw24030 raw24030Labels = mixedMoment B raw24030step0 raw24030step0Labels := by
      have ha : raw24030step0 = (fun i j => raw24030 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24030step0 raw24030; decide +kernel
      have hl : raw24030step0Labels = raw24030Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24030 raw24030Labels permutation194 permutation2
    mixedMoment B raw24030step0 raw24030step0Labels = mixedMoment B raw24030step1 raw24030step1Labels := by
      have ha : raw24030step1 = -raw24030step0 := by apply Matrix.ext; change ∀ i j, raw24030step1 i j = -(raw24030step0 i j); unfold raw24030step1 raw24030step0; decide +kernel
      have hl : raw24030step1Labels = raw24030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1607 node1607Labels := by rfl

theorem canonical24031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24031 raw24031Labels = mixedMoment B node1616 node1616Labels := by
  calc
    mixedMoment B raw24031 raw24031Labels = mixedMoment B raw24031step0 raw24031step0Labels := by
      have ha : raw24031step0 = (fun i j => raw24031 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24031step0 raw24031; decide +kernel
      have hl : raw24031step0Labels = raw24031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24031 raw24031Labels permutation176 permutation2
    mixedMoment B raw24031step0 raw24031step0Labels = mixedMoment B raw24031step1 raw24031step1Labels := by
      have ha : raw24031step1 = -raw24031step0 := by apply Matrix.ext; change ∀ i j, raw24031step1 i j = -(raw24031step0 i j); unfold raw24031step1 raw24031step0; decide +kernel
      have hl : raw24031step1Labels = raw24031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1616 node1616Labels := by rfl

theorem canonical24032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24032 raw24032Labels = mixedMoment B node1594 node1594Labels := by
  calc
    mixedMoment B raw24032 raw24032Labels = mixedMoment B raw24032step0 raw24032step0Labels := by
      have ha : raw24032step0 = (fun i j => raw24032 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24032step0 raw24032; decide +kernel
      have hl : raw24032step0Labels = raw24032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24032 raw24032Labels permutation160 permutation4
    mixedMoment B raw24032step0 raw24032step0Labels = mixedMoment B raw24032step1 raw24032step1Labels := by
      have ha : raw24032step1 = -raw24032step0 := by apply Matrix.ext; change ∀ i j, raw24032step1 i j = -(raw24032step0 i j); unfold raw24032step1 raw24032step0; decide +kernel
      have hl : raw24032step1Labels = raw24032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1594 node1594Labels := by rfl

theorem canonical24033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24033 raw24033Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw24033 raw24033Labels = mixedMoment B raw24033step0 raw24033step0Labels := by
      have ha : raw24033step0 = (fun i j => raw24033 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24033step0 raw24033; decide +kernel
      have hl : raw24033step0Labels = raw24033Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24033 raw24033Labels permutation164 permutation4
    mixedMoment B raw24033step0 raw24033step0Labels = mixedMoment B raw24033step1 raw24033step1Labels := by
      have ha : raw24033step1 = -raw24033step0 := by apply Matrix.ext; change ∀ i j, raw24033step1 i j = -(raw24033step0 i j); unfold raw24033step1 raw24033step0; decide +kernel
      have hl : raw24033step1Labels = raw24033step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

theorem canonical24034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24034 raw24034Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw24034 raw24034Labels = mixedMoment B raw24034step0 raw24034step0Labels := by
      have ha : raw24034step0 = (fun i j => raw24034 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24034step0 raw24034; decide +kernel
      have hl : raw24034step0Labels = raw24034Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24034 raw24034Labels permutation158 permutation4
    mixedMoment B raw24034step0 raw24034step0Labels = mixedMoment B raw24034step1 raw24034step1Labels := by
      have ha : raw24034step1 = -raw24034step0 := by apply Matrix.ext; change ∀ i j, raw24034step1 i j = -(raw24034step0 i j); unfold raw24034step1 raw24034step0; decide +kernel
      have hl : raw24034step1Labels = raw24034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

theorem canonical24035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24035 raw24035Labels = mixedMoment B node1592 node1592Labels := by
  calc
    mixedMoment B raw24035 raw24035Labels = mixedMoment B raw24035step0 raw24035step0Labels := by
      have ha : raw24035step0 = (fun i j => raw24035 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24035step0 raw24035; decide +kernel
      have hl : raw24035step0Labels = raw24035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24035 raw24035Labels permutation160 permutation4
    mixedMoment B raw24035step0 raw24035step0Labels = mixedMoment B raw24035step1 raw24035step1Labels := by
      have ha : raw24035step1 = -raw24035step0 := by apply Matrix.ext; change ∀ i j, raw24035step1 i j = -(raw24035step0 i j); unfold raw24035step1 raw24035step0; decide +kernel
      have hl : raw24035step1Labels = raw24035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1592 node1592Labels := by rfl

theorem canonical24036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24036 raw24036Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw24036 raw24036Labels = mixedMoment B raw24036step0 raw24036step0Labels := by
      have ha : raw24036step0 = (fun i j => raw24036 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24036step0 raw24036; decide +kernel
      have hl : raw24036step0Labels = raw24036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24036 raw24036Labels permutation164 permutation4
    mixedMoment B raw24036step0 raw24036step0Labels = mixedMoment B raw24036step1 raw24036step1Labels := by
      have ha : raw24036step1 = -raw24036step0 := by apply Matrix.ext; change ∀ i j, raw24036step1 i j = -(raw24036step0 i j); unfold raw24036step1 raw24036step0; decide +kernel
      have hl : raw24036step1Labels = raw24036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3238 node3238Labels := by rfl

theorem canonical24037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24037 raw24037Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw24037 raw24037Labels = mixedMoment B raw24037step0 raw24037step0Labels := by
      have ha : raw24037step0 = (fun i j => raw24037 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24037step0 raw24037; decide +kernel
      have hl : raw24037step0Labels = raw24037Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24037 raw24037Labels permutation164 permutation4
    mixedMoment B raw24037step0 raw24037step0Labels = mixedMoment B raw24037step1 raw24037step1Labels := by
      have ha : raw24037step1 = -raw24037step0 := by apply Matrix.ext; change ∀ i j, raw24037step1 i j = -(raw24037step0 i j); unfold raw24037step1 raw24037step0; decide +kernel
      have hl : raw24037step1Labels = raw24037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3285 node3285Labels := by rfl

theorem canonical24038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24038 raw24038Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw24038 raw24038Labels = mixedMoment B raw24038step0 raw24038step0Labels := by
      have ha : raw24038step0 = (fun i j => raw24038 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24038step0 raw24038; decide +kernel
      have hl : raw24038step0Labels = raw24038Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24038 raw24038Labels permutation182 permutation2
    mixedMoment B raw24038step0 raw24038step0Labels = mixedMoment B raw24038step1 raw24038step1Labels := by
      have ha : raw24038step1 = -raw24038step0 := by apply Matrix.ext; change ∀ i j, raw24038step1 i j = -(raw24038step0 i j); unfold raw24038step1 raw24038step0; decide +kernel
      have hl : raw24038step1Labels = raw24038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3290 node3290Labels := by rfl

theorem canonical24039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24039 raw24039Labels = mixedMoment B node2480 node2480Labels := by
  calc
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical24040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24040 raw24040Labels = mixedMoment B node1213 node1213Labels := by
  calc
    _ = mixedMoment B node1213 node1213Labels := by rfl

theorem canonical24041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24041 raw24041Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw24041 raw24041Labels = mixedMoment B raw24041step0 raw24041step0Labels := by
      have ha : raw24041step0 = (fun i j => raw24041 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24041step0 raw24041; decide +kernel
      have hl : raw24041step0Labels = raw24041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24041 raw24041Labels permutation158 permutation2
    _ = mixedMoment B node1129 node1129Labels := by rfl

theorem canonical24042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24042 raw24042Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw24042 raw24042Labels = mixedMoment B raw24042step0 raw24042step0Labels := by
      have ha : raw24042step0 = (fun i j => raw24042 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24042step0 raw24042; decide +kernel
      have hl : raw24042step0Labels = raw24042Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24042 raw24042Labels permutation154 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

theorem canonical24043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24043 raw24043Labels = mixedMoment B node1114 node1114Labels := by
  calc
    _ = mixedMoment B node1114 node1114Labels := by rfl

theorem canonical24044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24044 raw24044Labels = mixedMoment B node1112 node1112Labels := by
  calc
    _ = mixedMoment B node1112 node1112Labels := by rfl

theorem canonical24045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24045 raw24045Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw24045 raw24045Labels = mixedMoment B raw24045step0 raw24045step0Labels := by
      have hz : ∀ j, raw24045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24045step0 = (fun i j => raw24045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24045step0 raw24045; decide +kernel
      have hl : raw24045step0Labels = raw24045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24045 raw24045Labels permutation434 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical24046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24046 raw24046Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw24046 raw24046Labels = mixedMoment B raw24046step0 raw24046step0Labels := by
      have ha : raw24046step0 = (fun i j => raw24046 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24046step0 raw24046; decide +kernel
      have hl : raw24046step0Labels = raw24046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24046 raw24046Labels permutation158 permutation2
    _ = mixedMoment B node625 node625Labels := by rfl

theorem canonical24047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24047 raw24047Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24047 raw24047Labels = mixedMoment B raw24047step0 raw24047step0Labels := by
      have hz : ∀ j, raw24047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24047step0 = (fun i j => raw24047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24047step0 raw24047; decide +kernel
      have hl : raw24047step0Labels = raw24047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24047 raw24047Labels permutation434 hz
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical24048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24048 raw24048Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw24048 raw24048Labels = mixedMoment B raw24048step0 raw24048step0Labels := by
      have ha : raw24048step0 = (fun i j => raw24048 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24048step0 raw24048; decide +kernel
      have hl : raw24048step0Labels = raw24048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24048 raw24048Labels permutation166 permutation2
    _ = mixedMoment B node1213 node1213Labels := by rfl

theorem canonical24049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24049 raw24049Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw24049 raw24049Labels = mixedMoment B raw24049step0 raw24049step0Labels := by
      have ha : raw24049step0 = (fun i j => raw24049 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24049step0 raw24049; decide +kernel
      have hl : raw24049step0Labels = raw24049Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24049 raw24049Labels permutation158 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical24050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24050 raw24050Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw24050 raw24050Labels = mixedMoment B raw24050step0 raw24050step0Labels := by
      have ha : raw24050step0 = (fun i j => raw24050 (permutation191 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24050step0 raw24050; decide +kernel
      have hl : raw24050step0Labels = raw24050Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24050 raw24050Labels permutation191 permutation2
    mixedMoment B raw24050step0 raw24050step0Labels = mixedMoment B raw24050step1 raw24050step1Labels := by
      have ha : raw24050step1 = -raw24050step0 := by apply Matrix.ext; change ∀ i j, raw24050step1 i j = -(raw24050step0 i j); unfold raw24050step1 raw24050step0; decide +kernel
      have hl : raw24050step1Labels = raw24050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1601 node1601Labels := by rfl

theorem canonical24051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24051 raw24051Labels = mixedMoment B node1598 node1598Labels := by
  calc
    mixedMoment B raw24051 raw24051Labels = mixedMoment B raw24051step0 raw24051step0Labels := by
      have ha : raw24051step0 = (fun i j => raw24051 (permutation189 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24051step0 raw24051; decide +kernel
      have hl : raw24051step0Labels = raw24051Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24051 raw24051Labels permutation189 permutation2
    mixedMoment B raw24051step0 raw24051step0Labels = mixedMoment B raw24051step1 raw24051step1Labels := by
      have ha : raw24051step1 = -raw24051step0 := by apply Matrix.ext; change ∀ i j, raw24051step1 i j = -(raw24051step0 i j); unfold raw24051step1 raw24051step0; decide +kernel
      have hl : raw24051step1Labels = raw24051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1598 node1598Labels := by rfl

theorem canonical24052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24052 raw24052Labels = mixedMoment B node1597 node1597Labels := by
  calc
    mixedMoment B raw24052 raw24052Labels = mixedMoment B raw24052step0 raw24052step0Labels := by
      have ha : raw24052step0 = (fun i j => raw24052 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24052step0 raw24052; decide +kernel
      have hl : raw24052step0Labels = raw24052Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24052 raw24052Labels permutation188 permutation2
    mixedMoment B raw24052step0 raw24052step0Labels = mixedMoment B raw24052step1 raw24052step1Labels := by
      have ha : raw24052step1 = -raw24052step0 := by apply Matrix.ext; change ∀ i j, raw24052step1 i j = -(raw24052step0 i j); unfold raw24052step1 raw24052step0; decide +kernel
      have hl : raw24052step1Labels = raw24052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1597 node1597Labels := by rfl

theorem canonical24053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24053 raw24053Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw24053 raw24053Labels = mixedMoment B raw24053step0 raw24053step0Labels := by
      have ha : raw24053step0 = (fun i j => raw24053 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24053step0 raw24053; decide +kernel
      have hl : raw24053step0Labels = raw24053Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24053 raw24053Labels permutation178 permutation2
    _ = mixedMoment B node1210 node1210Labels := by rfl

theorem canonical24054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24054 raw24054Labels = mixedMoment B node2613 node2613Labels := by
  calc
    mixedMoment B raw24054 raw24054Labels = mixedMoment B raw24054step0 raw24054step0Labels := by
      have ha : raw24054step0 = (fun i j => raw24054 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24054step0 raw24054; decide +kernel
      have hl : raw24054step0Labels = raw24054Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24054 raw24054Labels permutation154 permutation2
    _ = mixedMoment B node2613 node2613Labels := by rfl

theorem canonical24055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24055 raw24055Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw24055 raw24055Labels = mixedMoment B raw24055step0 raw24055step0Labels := by
      have ha : raw24055step0 = (fun i j => raw24055 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24055step0 raw24055; decide +kernel
      have hl : raw24055step0Labels = raw24055Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24055 raw24055Labels permutation178 permutation2
    _ = mixedMoment B node2477 node2477Labels := by rfl

theorem canonical24056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24056 raw24056Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw24056 raw24056Labels = mixedMoment B raw24056step0 raw24056step0Labels := by
      have ha : raw24056step0 = (fun i j => raw24056 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24056step0 raw24056; decide +kernel
      have hl : raw24056step0Labels = raw24056Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24056 raw24056Labels permutation176 permutation2
    _ = mixedMoment B node2708 node2708Labels := by rfl

theorem canonical24057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24057 raw24057Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw24057 raw24057Labels = mixedMoment B raw24057step0 raw24057step0Labels := by
      have ha : raw24057step0 = (fun i j => raw24057 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24057step0 raw24057; decide +kernel
      have hl : raw24057step0Labels = raw24057Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24057 raw24057Labels permutation188 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

theorem canonical24058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24058 raw24058Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw24058 raw24058Labels = mixedMoment B raw24058step0 raw24058step0Labels := by
      have ha : raw24058step0 = (fun i j => raw24058 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24058step0 raw24058; decide +kernel
      have hl : raw24058step0Labels = raw24058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24058 raw24058Labels permutation178 permutation2
    _ = mixedMoment B node2718 node2718Labels := by rfl

theorem canonical24059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24059 raw24059Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw24059 raw24059Labels = mixedMoment B raw24059step0 raw24059step0Labels := by
      have ha : raw24059step0 = (fun i j => raw24059 (permutation188 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24059step0 raw24059; decide +kernel
      have hl : raw24059step0Labels = raw24059Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24059 raw24059Labels permutation188 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

theorem canonical24060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24060 raw24060Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24060 raw24060Labels = mixedMoment B raw24060step0 raw24060step0Labels := by
      have ha : raw24060step0 = (fun i j => raw24060 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24060step0 raw24060; decide +kernel
      have hl : raw24060step0Labels = raw24060Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24060 raw24060Labels permutation176 permutation2
    _ = mixedMoment B node1180 node1180Labels := by rfl

theorem canonical24061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24061 raw24061Labels = mixedMoment B node2607 node2607Labels := by
  calc
    _ = mixedMoment B node2607 node2607Labels := by rfl

theorem canonical24062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24062 raw24062Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw24062 raw24062Labels = mixedMoment B raw24062step0 raw24062step0Labels := by
      have ha : raw24062step0 = (fun i j => raw24062 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24062step0 raw24062; decide +kernel
      have hl : raw24062step0Labels = raw24062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24062 raw24062Labels permutation176 permutation2
    _ = mixedMoment B node2383 node2383Labels := by rfl

theorem canonical24063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24063 raw24063Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw24063 raw24063Labels = mixedMoment B raw24063step0 raw24063step0Labels := by
      have ha : raw24063step0 = (fun i j => raw24063 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24063step0 raw24063; decide +kernel
      have hl : raw24063step0Labels = raw24063Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24063 raw24063Labels permutation176 permutation2
    _ = mixedMoment B node2662 node2662Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical188
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical24064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24064 raw24064Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw24064 raw24064Labels = mixedMoment B raw24064step0 raw24064step0Labels := by
      have ha : raw24064step0 = (fun i j => raw24064 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24064step0 raw24064; decide +kernel
      have hl : raw24064step0Labels = raw24064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24064 raw24064Labels permutation178 permutation2
    _ = mixedMoment B node2662 node2662Labels := by rfl

theorem canonical24065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24065 raw24065Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw24065 raw24065Labels = mixedMoment B raw24065step0 raw24065step0Labels := by
      have ha : raw24065step0 = (fun i j => raw24065 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24065step0 raw24065; decide +kernel
      have hl : raw24065step0Labels = raw24065Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24065 raw24065Labels permutation176 permutation2
    _ = mixedMoment B node2671 node2671Labels := by rfl

theorem canonical24066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24066 raw24066Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw24066 raw24066Labels = mixedMoment B raw24066step0 raw24066step0Labels := by
      have ha : raw24066step0 = (fun i j => raw24066 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24066step0 raw24066; decide +kernel
      have hl : raw24066step0Labels = raw24066Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24066 raw24066Labels permutation176 permutation0
    _ = mixedMoment B node4087 node4087Labels := by rfl

theorem canonical24067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24067 raw24067Labels = mixedMoment B node1187 node1187Labels := by
  calc
    mixedMoment B raw24067 raw24067Labels = mixedMoment B raw24067step0 raw24067step0Labels := by
      have ha : raw24067step0 = (fun i j => raw24067 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24067step0 raw24067; decide +kernel
      have hl : raw24067step0Labels = raw24067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24067 raw24067Labels permutation176 permutation2
    _ = mixedMoment B node1187 node1187Labels := by rfl

theorem canonical24068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24068 raw24068Labels = mixedMoment B node1256 node1256Labels := by
  calc
    _ = mixedMoment B node1256 node1256Labels := by rfl

theorem canonical24069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24069 raw24069Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24069 raw24069Labels = mixedMoment B raw24069step0 raw24069step0Labels := by
      have ha : raw24069step0 = (fun i j => raw24069 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24069step0 raw24069; decide +kernel
      have hl : raw24069step0Labels = raw24069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24069 raw24069Labels permutation179 permutation2
    _ = mixedMoment B node1180 node1180Labels := by rfl

theorem canonical24070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24070 raw24070Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw24070 raw24070Labels = mixedMoment B raw24070step0 raw24070step0Labels := by
      have ha : raw24070step0 = (fun i j => raw24070 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24070step0 raw24070; decide +kernel
      have hl : raw24070step0Labels = raw24070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24070 raw24070Labels permutation177 permutation2
    _ = mixedMoment B node1180 node1180Labels := by rfl

theorem canonical24071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24071 raw24071Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw24071 raw24071Labels = mixedMoment B raw24071step0 raw24071step0Labels := by
      have ha : raw24071step0 = (fun i j => raw24071 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24071step0 raw24071; decide +kernel
      have hl : raw24071step0Labels = raw24071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24071 raw24071Labels permutation178 permutation2
    _ = mixedMoment B node1178 node1178Labels := by rfl

theorem canonical24072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24072 raw24072Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw24072 raw24072Labels = mixedMoment B raw24072step0 raw24072step0Labels := by
      have ha : raw24072step0 = (fun i j => raw24072 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24072step0 raw24072; decide +kernel
      have hl : raw24072step0Labels = raw24072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24072 raw24072Labels permutation154 permutation2
    _ = mixedMoment B node2606 node2606Labels := by rfl

theorem canonical24073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24073 raw24073Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw24073 raw24073Labels = mixedMoment B raw24073step0 raw24073step0Labels := by
      have ha : raw24073step0 = (fun i j => raw24073 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24073step0 raw24073; decide +kernel
      have hl : raw24073step0Labels = raw24073Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24073 raw24073Labels permutation178 permutation2
    _ = mixedMoment B node2382 node2382Labels := by rfl

theorem canonical24074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24074 raw24074Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw24074 raw24074Labels = mixedMoment B raw24074step0 raw24074step0Labels := by
      have ha : raw24074step0 = (fun i j => raw24074 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24074step0 raw24074; decide +kernel
      have hl : raw24074step0Labels = raw24074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24074 raw24074Labels permutation176 permutation2
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical24075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24075 raw24075Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw24075 raw24075Labels = mixedMoment B raw24075step0 raw24075step0Labels := by
      have hz : ∀ j, raw24075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24075step0 = (fun i j => raw24075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24075step0 raw24075; decide +kernel
      have hl : raw24075step0Labels = raw24075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24075 raw24075Labels permutation520 hz
    mixedMoment B raw24075step0 raw24075step0Labels = mixedMoment B raw24075step1 raw24075step1Labels := by
      have ha : raw24075step1 = (fun i j => raw24075step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24075step1 raw24075step0; decide +kernel
      have hl : raw24075step1Labels = raw24075step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24075step0 raw24075step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

theorem canonical24076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24076 raw24076Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw24076 raw24076Labels = mixedMoment B raw24076step0 raw24076step0Labels := by
      have ha : raw24076step0 = (fun i j => raw24076 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24076step0 raw24076; decide +kernel
      have hl : raw24076step0Labels = raw24076Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24076 raw24076Labels permutation178 permutation2
    _ = mixedMoment B node2669 node2669Labels := by rfl

theorem canonical24077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24077 raw24077Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw24077 raw24077Labels = mixedMoment B raw24077step0 raw24077step0Labels := by
      have hz : ∀ j, raw24077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24077step0 = (fun i j => raw24077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24077step0 raw24077; decide +kernel
      have hl : raw24077step0Labels = raw24077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24077 raw24077Labels permutation520 hz
    mixedMoment B raw24077step0 raw24077step0Labels = mixedMoment B raw24077step1 raw24077step1Labels := by
      have ha : raw24077step1 = (fun i j => raw24077step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24077step1 raw24077step0; decide +kernel
      have hl : raw24077step1Labels = raw24077step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24077step0 raw24077step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

theorem canonical24078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24078 raw24078Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw24078 raw24078Labels = mixedMoment B raw24078step0 raw24078step0Labels := by
      have hz : ∀ j, raw24078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24078step0 = (fun i j => raw24078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24078step0 raw24078; decide +kernel
      have hl : raw24078step0Labels = raw24078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24078 raw24078Labels permutation265 hz
    mixedMoment B raw24078step0 raw24078step0Labels = mixedMoment B raw24078step1 raw24078step1Labels := by
      have ha : raw24078step1 = (fun i j => raw24078step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24078step1 raw24078step0; decide +kernel
      have hl : raw24078step1Labels = raw24078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24078step0 raw24078step0Labels permutation51 permutation2
    mixedMoment B raw24078step1 raw24078step1Labels = mixedMoment B raw24078step2 raw24078step2Labels := by
      have ha : raw24078step2 = -raw24078step1 := by apply Matrix.ext; change ∀ i j, raw24078step2 i j = -(raw24078step1 i j); unfold raw24078step2 raw24078step1; decide +kernel
      have hl : raw24078step2Labels = raw24078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1656 node1656Labels := by rfl

theorem canonical24079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24079 raw24079Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw24079 raw24079Labels = mixedMoment B raw24079step0 raw24079step0Labels := by
      have hz : ∀ j, raw24079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24079step0 = (fun i j => raw24079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24079step0 raw24079; decide +kernel
      have hl : raw24079step0Labels = raw24079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24079 raw24079Labels permutation346 hz
    mixedMoment B raw24079step0 raw24079step0Labels = mixedMoment B raw24079step1 raw24079step1Labels := by
      have hz : ∀ j, raw24079step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24079step1 = (fun i j => raw24079step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24079step1 raw24079step0; decide +kernel
      have hl : raw24079step1Labels = raw24079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24079step0 raw24079step0Labels permutation56 hz
    mixedMoment B raw24079step1 raw24079step1Labels = mixedMoment B raw24079step2 raw24079step2Labels := by
      have ha : raw24079step2 = (fun i j => raw24079step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24079step2 raw24079step1; decide +kernel
      have hl : raw24079step2Labels = raw24079step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24079step1 raw24079step1Labels permutation13 permutation2
    mixedMoment B raw24079step2 raw24079step2Labels = mixedMoment B raw24079step3 raw24079step3Labels := by
      have ha : raw24079step3 = -raw24079step2 := by apply Matrix.ext; change ∀ i j, raw24079step3 i j = -(raw24079step2 i j); unfold raw24079step3 raw24079step2; decide +kernel
      have hl : raw24079step3Labels = raw24079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1659 node1659Labels := by rfl

theorem canonical24080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24080 raw24080Labels = mixedMoment B node1661 node1661Labels := by
  calc
    mixedMoment B raw24080 raw24080Labels = mixedMoment B raw24080step0 raw24080step0Labels := by
      have hz : ∀ j, raw24080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24080step0 = (fun i j => raw24080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24080step0 raw24080; decide +kernel
      have hl : raw24080step0Labels = raw24080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24080 raw24080Labels permutation346 hz
    mixedMoment B raw24080step0 raw24080step0Labels = mixedMoment B raw24080step1 raw24080step1Labels := by
      have hz : ∀ j, raw24080step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24080step1 = (fun i j => raw24080step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24080step1 raw24080step0; decide +kernel
      have hl : raw24080step1Labels = raw24080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24080step0 raw24080step0Labels permutation56 hz
    mixedMoment B raw24080step1 raw24080step1Labels = mixedMoment B raw24080step2 raw24080step2Labels := by
      have ha : raw24080step2 = (fun i j => raw24080step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24080step2 raw24080step1; decide +kernel
      have hl : raw24080step2Labels = raw24080step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24080step1 raw24080step1Labels permutation12 permutation2
    mixedMoment B raw24080step2 raw24080step2Labels = mixedMoment B raw24080step3 raw24080step3Labels := by
      have ha : raw24080step3 = -raw24080step2 := by apply Matrix.ext; change ∀ i j, raw24080step3 i j = -(raw24080step2 i j); unfold raw24080step3 raw24080step2; decide +kernel
      have hl : raw24080step3Labels = raw24080step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1661 node1661Labels := by rfl

theorem canonical24081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24081 raw24081Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw24081 raw24081Labels = mixedMoment B raw24081step0 raw24081step0Labels := by
      have hz : ∀ j, raw24081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24081step0 = (fun i j => raw24081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24081step0 raw24081; decide +kernel
      have hl : raw24081step0Labels = raw24081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24081 raw24081Labels permutation346 hz
    mixedMoment B raw24081step0 raw24081step0Labels = mixedMoment B raw24081step1 raw24081step1Labels := by
      have hz : ∀ j, raw24081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24081step1 = (fun i j => raw24081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24081step1 raw24081step0; decide +kernel
      have hl : raw24081step1Labels = raw24081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24081step0 raw24081step0Labels permutation56 hz
    mixedMoment B raw24081step1 raw24081step1Labels = mixedMoment B raw24081step2 raw24081step2Labels := by
      have ha : raw24081step2 = (fun i j => raw24081step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24081step2 raw24081step1; decide +kernel
      have hl : raw24081step2Labels = raw24081step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24081step1 raw24081step1Labels permutation13 permutation2
    mixedMoment B raw24081step2 raw24081step2Labels = mixedMoment B raw24081step3 raw24081step3Labels := by
      have ha : raw24081step3 = -raw24081step2 := by apply Matrix.ext; change ∀ i j, raw24081step3 i j = -(raw24081step2 i j); unfold raw24081step3 raw24081step2; decide +kernel
      have hl : raw24081step3Labels = raw24081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1739 node1739Labels := by rfl

theorem canonical24082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24082 raw24082Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw24082 raw24082Labels = mixedMoment B raw24082step0 raw24082step0Labels := by
      have hz : ∀ j, raw24082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24082step0 = (fun i j => raw24082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24082step0 raw24082; decide +kernel
      have hl : raw24082step0Labels = raw24082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24082 raw24082Labels permutation346 hz
    mixedMoment B raw24082step0 raw24082step0Labels = mixedMoment B raw24082step1 raw24082step1Labels := by
      have hz : ∀ j, raw24082step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24082step1 = (fun i j => raw24082step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24082step1 raw24082step0; decide +kernel
      have hl : raw24082step1Labels = raw24082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24082step0 raw24082step0Labels permutation56 hz
    mixedMoment B raw24082step1 raw24082step1Labels = mixedMoment B raw24082step2 raw24082step2Labels := by
      have ha : raw24082step2 = (fun i j => raw24082step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24082step2 raw24082step1; decide +kernel
      have hl : raw24082step2Labels = raw24082step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24082step1 raw24082step1Labels permutation8 permutation4
    mixedMoment B raw24082step2 raw24082step2Labels = mixedMoment B raw24082step3 raw24082step3Labels := by
      have ha : raw24082step3 = -raw24082step2 := by apply Matrix.ext; change ∀ i j, raw24082step3 i j = -(raw24082step2 i j); unfold raw24082step3 raw24082step2; decide +kernel
      have hl : raw24082step3Labels = raw24082step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1650 node1650Labels := by rfl

theorem canonical24083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24083 raw24083Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw24083 raw24083Labels = mixedMoment B raw24083step0 raw24083step0Labels := by
      have hz : ∀ j, raw24083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24083step0 = (fun i j => raw24083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24083step0 raw24083; decide +kernel
      have hl : raw24083step0Labels = raw24083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24083 raw24083Labels permutation346 hz
    mixedMoment B raw24083step0 raw24083step0Labels = mixedMoment B raw24083step1 raw24083step1Labels := by
      have ha : raw24083step1 = (fun i j => raw24083step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24083step1 raw24083step0; decide +kernel
      have hl : raw24083step1Labels = raw24083step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24083step0 raw24083step0Labels permutation151 permutation4
    _ = mixedMoment B node2502 node2502Labels := by rfl

theorem canonical24084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24084 raw24084Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw24084 raw24084Labels = mixedMoment B raw24084step0 raw24084step0Labels := by
      have hz : ∀ j, raw24084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24084step0 = (fun i j => raw24084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24084step0 raw24084; decide +kernel
      have hl : raw24084step0Labels = raw24084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24084 raw24084Labels permutation265 hz
    mixedMoment B raw24084step0 raw24084step0Labels = mixedMoment B raw24084step1 raw24084step1Labels := by
      have ha : raw24084step1 = (fun i j => raw24084step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24084step1 raw24084step0; decide +kernel
      have hl : raw24084step1Labels = raw24084step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24084step0 raw24084step0Labels permutation151 permutation4
    _ = mixedMoment B node2502 node2502Labels := by rfl

theorem canonical24085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24085 raw24085Labels = mixedMoment B node2521 node2521Labels := by
  calc
    mixedMoment B raw24085 raw24085Labels = mixedMoment B raw24085step0 raw24085step0Labels := by
      have hz : ∀ j, raw24085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24085step0 = (fun i j => raw24085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24085step0 raw24085; decide +kernel
      have hl : raw24085step0Labels = raw24085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24085 raw24085Labels permutation346 hz
    mixedMoment B raw24085step0 raw24085step0Labels = mixedMoment B raw24085step1 raw24085step1Labels := by
      have hz : ∀ j, raw24085step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24085step1 = (fun i j => raw24085step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24085step1 raw24085step0; decide +kernel
      have hl : raw24085step1Labels = raw24085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24085step0 raw24085step0Labels permutation56 hz
    mixedMoment B raw24085step1 raw24085step1Labels = mixedMoment B raw24085step2 raw24085step2Labels := by
      have ha : raw24085step2 = (fun i j => raw24085step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24085step2 raw24085step1; decide +kernel
      have hl : raw24085step2Labels = raw24085step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24085step1 raw24085step1Labels permutation31 permutation4
    _ = mixedMoment B node2521 node2521Labels := by rfl

theorem canonical24086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24086 raw24086Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw24086 raw24086Labels = mixedMoment B raw24086step0 raw24086step0Labels := by
      have hz : ∀ j, raw24086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24086step0 = (fun i j => raw24086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24086step0 raw24086; decide +kernel
      have hl : raw24086step0Labels = raw24086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24086 raw24086Labels permutation346 hz
    mixedMoment B raw24086step0 raw24086step0Labels = mixedMoment B raw24086step1 raw24086step1Labels := by
      have hz : ∀ j, raw24086step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24086step1 = (fun i j => raw24086step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24086step1 raw24086step0; decide +kernel
      have hl : raw24086step1Labels = raw24086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24086step0 raw24086step0Labels permutation56 hz
    mixedMoment B raw24086step1 raw24086step1Labels = mixedMoment B raw24086step2 raw24086step2Labels := by
      have ha : raw24086step2 = (fun i j => raw24086step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24086step2 raw24086step1; decide +kernel
      have hl : raw24086step2Labels = raw24086step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24086step1 raw24086step1Labels permutation8 permutation4
    mixedMoment B raw24086step2 raw24086step2Labels = mixedMoment B raw24086step3 raw24086step3Labels := by
      have ha : raw24086step3 = -raw24086step2 := by apply Matrix.ext; change ∀ i j, raw24086step3 i j = -(raw24086step2 i j); unfold raw24086step3 raw24086step2; decide +kernel
      have hl : raw24086step3Labels = raw24086step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3305 node3305Labels := by rfl

theorem canonical24087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24087 raw24087Labels = mixedMoment B node1646 node1646Labels := by
  calc
    mixedMoment B raw24087 raw24087Labels = mixedMoment B raw24087step0 raw24087step0Labels := by
      have hz : ∀ j, raw24087 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24087step0 = (fun i j => raw24087 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24087step0 raw24087; decide +kernel
      have hl : raw24087step0Labels = raw24087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24087 raw24087Labels permutation265 hz
    mixedMoment B raw24087step0 raw24087step0Labels = mixedMoment B raw24087step1 raw24087step1Labels := by
      have ha : raw24087step1 = (fun i j => raw24087step0 (permutation45 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24087step1 raw24087step0; decide +kernel
      have hl : raw24087step1Labels = raw24087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24087step0 raw24087step0Labels permutation45 permutation2
    mixedMoment B raw24087step1 raw24087step1Labels = mixedMoment B raw24087step2 raw24087step2Labels := by
      have ha : raw24087step2 = -raw24087step1 := by apply Matrix.ext; change ∀ i j, raw24087step2 i j = -(raw24087step1 i j); unfold raw24087step2 raw24087step1; decide +kernel
      have hl : raw24087step2Labels = raw24087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1646 node1646Labels := by rfl

theorem canonical24088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24088 raw24088Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw24088 raw24088Labels = mixedMoment B raw24088step0 raw24088step0Labels := by
      have hz : ∀ j, raw24088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24088step0 = (fun i j => raw24088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24088step0 raw24088; decide +kernel
      have hl : raw24088step0Labels = raw24088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24088 raw24088Labels permutation346 hz
    mixedMoment B raw24088step0 raw24088step0Labels = mixedMoment B raw24088step1 raw24088step1Labels := by
      have hz : ∀ j, raw24088step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24088step1 = (fun i j => raw24088step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24088step1 raw24088step0; decide +kernel
      have hl : raw24088step1Labels = raw24088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24088step0 raw24088step0Labels permutation56 hz
    mixedMoment B raw24088step1 raw24088step1Labels = mixedMoment B raw24088step2 raw24088step2Labels := by
      have ha : raw24088step2 = (fun i j => raw24088step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24088step2 raw24088step1; decide +kernel
      have hl : raw24088step2Labels = raw24088step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24088step1 raw24088step1Labels permutation11 permutation2
    mixedMoment B raw24088step2 raw24088step2Labels = mixedMoment B raw24088step3 raw24088step3Labels := by
      have ha : raw24088step3 = -raw24088step2 := by apply Matrix.ext; change ∀ i j, raw24088step3 i j = -(raw24088step2 i j); unfold raw24088step3 raw24088step2; decide +kernel
      have hl : raw24088step3Labels = raw24088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1651 node1651Labels := by rfl

theorem canonical24089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24089 raw24089Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw24089 raw24089Labels = mixedMoment B raw24089step0 raw24089step0Labels := by
      have hz : ∀ j, raw24089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24089step0 = (fun i j => raw24089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24089step0 raw24089; decide +kernel
      have hl : raw24089step0Labels = raw24089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24089 raw24089Labels permutation346 hz
    mixedMoment B raw24089step0 raw24089step0Labels = mixedMoment B raw24089step1 raw24089step1Labels := by
      have hz : ∀ j, raw24089step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24089step1 = (fun i j => raw24089step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24089step1 raw24089step0; decide +kernel
      have hl : raw24089step1Labels = raw24089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24089step0 raw24089step0Labels permutation56 hz
    mixedMoment B raw24089step1 raw24089step1Labels = mixedMoment B raw24089step2 raw24089step2Labels := by
      have ha : raw24089step2 = (fun i j => raw24089step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24089step2 raw24089step1; decide +kernel
      have hl : raw24089step2Labels = raw24089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24089step1 raw24089step1Labels permutation11 permutation2
    mixedMoment B raw24089step2 raw24089step2Labels = mixedMoment B raw24089step3 raw24089step3Labels := by
      have ha : raw24089step3 = -raw24089step2 := by apply Matrix.ext; change ∀ i j, raw24089step3 i j = -(raw24089step2 i j); unfold raw24089step3 raw24089step2; decide +kernel
      have hl : raw24089step3Labels = raw24089step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1728 node1728Labels := by rfl

theorem canonical24090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24090 raw24090Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw24090 raw24090Labels = mixedMoment B raw24090step0 raw24090step0Labels := by
      have hz : ∀ j, raw24090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24090step0 = (fun i j => raw24090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24090step0 raw24090; decide +kernel
      have hl : raw24090step0Labels = raw24090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24090 raw24090Labels permutation346 hz
    mixedMoment B raw24090step0 raw24090step0Labels = mixedMoment B raw24090step1 raw24090step1Labels := by
      have hz : ∀ j, raw24090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24090step1 = (fun i j => raw24090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24090step1 raw24090step0; decide +kernel
      have hl : raw24090step1Labels = raw24090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24090step0 raw24090step0Labels permutation56 hz
    mixedMoment B raw24090step1 raw24090step1Labels = mixedMoment B raw24090step2 raw24090step2Labels := by
      have ha : raw24090step2 = (fun i j => raw24090step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24090step2 raw24090step1; decide +kernel
      have hl : raw24090step2Labels = raw24090step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24090step1 raw24090step1Labels permutation10 permutation2
    mixedMoment B raw24090step2 raw24090step2Labels = mixedMoment B raw24090step3 raw24090step3Labels := by
      have ha : raw24090step3 = -raw24090step2 := by apply Matrix.ext; change ∀ i j, raw24090step3 i j = -(raw24090step2 i j); unfold raw24090step3 raw24090step2; decide +kernel
      have hl : raw24090step3Labels = raw24090step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1653 node1653Labels := by rfl

theorem canonical24091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24091 raw24091Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw24091 raw24091Labels = mixedMoment B raw24091step0 raw24091step0Labels := by
      have hz : ∀ j, raw24091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24091step0 = (fun i j => raw24091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24091step0 raw24091; decide +kernel
      have hl : raw24091step0Labels = raw24091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24091 raw24091Labels permutation346 hz
    mixedMoment B raw24091step0 raw24091step0Labels = mixedMoment B raw24091step1 raw24091step1Labels := by
      have hz : ∀ j, raw24091step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24091step1 = (fun i j => raw24091step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24091step1 raw24091step0; decide +kernel
      have hl : raw24091step1Labels = raw24091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24091step0 raw24091step0Labels permutation56 hz
    mixedMoment B raw24091step1 raw24091step1Labels = mixedMoment B raw24091step2 raw24091step2Labels := by
      have ha : raw24091step2 = (fun i j => raw24091step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24091step2 raw24091step1; decide +kernel
      have hl : raw24091step2Labels = raw24091step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24091step1 raw24091step1Labels permutation8 permutation4
    mixedMoment B raw24091step2 raw24091step2Labels = mixedMoment B raw24091step3 raw24091step3Labels := by
      have ha : raw24091step3 = -raw24091step2 := by apply Matrix.ext; change ∀ i j, raw24091step3 i j = -(raw24091step2 i j); unfold raw24091step3 raw24091step2; decide +kernel
      have hl : raw24091step3Labels = raw24091step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1653 node1653Labels := by rfl

theorem canonical24092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24092 raw24092Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw24092 raw24092Labels = mixedMoment B raw24092step0 raw24092step0Labels := by
      have hz : ∀ j, raw24092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24092step0 = (fun i j => raw24092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24092step0 raw24092; decide +kernel
      have hl : raw24092step0Labels = raw24092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24092 raw24092Labels permutation265 hz
    mixedMoment B raw24092step0 raw24092step0Labels = mixedMoment B raw24092step1 raw24092step1Labels := by
      have ha : raw24092step1 = (fun i j => raw24092step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw24092step1 raw24092step0; decide +kernel
      have hl : raw24092step1Labels = raw24092step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24092step0 raw24092step0Labels permutation32 permutation4
    mixedMoment B raw24092step1 raw24092step1Labels = mixedMoment B raw24092step2 raw24092step2Labels := by
      have ha : raw24092step2 = -raw24092step1 := by apply Matrix.ext; change ∀ i j, raw24092step2 i j = -(raw24092step1 i j); unfold raw24092step2 raw24092step1; decide +kernel
      have hl : raw24092step2Labels = raw24092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3287 node3287Labels := by rfl

theorem canonical24093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24093 raw24093Labels = mixedMoment B node3049 node3049Labels := by
  calc
    mixedMoment B raw24093 raw24093Labels = mixedMoment B raw24093step0 raw24093step0Labels := by
      have hz : ∀ j, raw24093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24093step0 = (fun i j => raw24093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24093step0 raw24093; decide +kernel
      have hl : raw24093step0Labels = raw24093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24093 raw24093Labels permutation346 hz
    mixedMoment B raw24093step0 raw24093step0Labels = mixedMoment B raw24093step1 raw24093step1Labels := by
      have hz : ∀ j, raw24093step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24093step1 = (fun i j => raw24093step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24093step1 raw24093step0; decide +kernel
      have hl : raw24093step1Labels = raw24093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24093step0 raw24093step0Labels permutation56 hz
    mixedMoment B raw24093step1 raw24093step1Labels = mixedMoment B raw24093step2 raw24093step2Labels := by
      have ha : raw24093step2 = (fun i j => raw24093step1 (permutation19 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24093step2 raw24093step1; decide +kernel
      have hl : raw24093step2Labels = raw24093step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24093step1 raw24093step1Labels permutation19 permutation2
    _ = mixedMoment B node3049 node3049Labels := by rfl

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

theorem sound1112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1112 node1112Labels = Sparse.eval nodeValue1112 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1112) = mixedMoment B node1112 node1112Labels := rfl
  simpa [nodeValue1112, Sparse.eval] using hc.symm

theorem sound1114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1114 node1114Labels = Sparse.eval nodeValue1114 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1114) = mixedMoment B node1114 node1114Labels := rfl
  simpa [nodeValue1114, Sparse.eval] using hc.symm

theorem sound1116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1116 node1116Labels = Sparse.eval nodeValue1116 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1116) = mixedMoment B node1116 node1116Labels := rfl
  simpa [nodeValue1116, Sparse.eval] using hc.symm

theorem sound1117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1117 node1117Labels = Sparse.eval nodeValue1117 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1117) = mixedMoment B node1117 node1117Labels := rfl
  simpa [nodeValue1117, Sparse.eval] using hc.symm

theorem sound1129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1129 node1129Labels = Sparse.eval nodeValue1129 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1129) = mixedMoment B node1129 node1129Labels := rfl
  simpa [nodeValue1129, Sparse.eval] using hc.symm

theorem sound1135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1135 node1135Labels = Sparse.eval nodeValue1135 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1135) = mixedMoment B node1135 node1135Labels := rfl
  simpa [nodeValue1135, Sparse.eval] using hc.symm

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

theorem sound1178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1178 node1178Labels = Sparse.eval nodeValue1178 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1178) = mixedMoment B node1178 node1178Labels := rfl
  simpa [nodeValue1178, Sparse.eval] using hc.symm

theorem sound1180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1180 node1180Labels = Sparse.eval nodeValue1180 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1180) = mixedMoment B node1180 node1180Labels := rfl
  simpa [nodeValue1180, Sparse.eval] using hc.symm

theorem sound1187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1187 node1187Labels = Sparse.eval nodeValue1187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1187) = mixedMoment B node1187 node1187Labels := rfl
  simpa [nodeValue1187, Sparse.eval] using hc.symm

theorem sound1210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1210 node1210Labels = Sparse.eval nodeValue1210 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1210) = mixedMoment B node1210 node1210Labels := rfl
  simpa [nodeValue1210, Sparse.eval] using hc.symm

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

theorem sound1216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1216 node1216Labels = Sparse.eval nodeValue1216 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1216) = mixedMoment B node1216 node1216Labels := rfl
  simpa [nodeValue1216, Sparse.eval] using hc.symm

theorem sound1235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1235 node1235Labels = Sparse.eval nodeValue1235 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1235) = mixedMoment B node1235 node1235Labels := rfl
  simpa [nodeValue1235, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1256 node1256Labels = Sparse.eval nodeValue1256 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1256) = mixedMoment B node1256 node1256Labels := rfl
  simpa [nodeValue1256, Sparse.eval] using hc.symm

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

theorem zero1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = 0 := by
  exact mixedMoment_alpha B hF node1592 node1592Labels 1 permutation434
    (by decide +kernel)

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

theorem sound1592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1592 node1592Labels = Sparse.eval nodeValue1592 (mixedVector B) := by
  simpa only [nodeValue1592, Sparse.eval_nil] using zero1592 B _hB _hF

theorem sound1594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1594 node1594Labels = Sparse.eval nodeValue1594 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1594) = mixedMoment B node1594 node1594Labels := rfl
  simpa [nodeValue1594, Sparse.eval] using hc.symm

theorem sound1597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1597 node1597Labels = Sparse.eval nodeValue1597 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1597) = mixedMoment B node1597 node1597Labels := rfl
  simpa [nodeValue1597, Sparse.eval] using hc.symm

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

theorem sound1616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1616 node1616Labels = Sparse.eval nodeValue1616 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1616) = mixedMoment B node1616 node1616Labels := rfl
  simpa [nodeValue1616, Sparse.eval] using hc.symm

theorem sound1646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1646 node1646Labels = Sparse.eval nodeValue1646 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1646) = mixedMoment B node1646 node1646Labels := rfl
  simpa [nodeValue1646, Sparse.eval] using hc.symm

theorem sound1650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1650 node1650Labels = Sparse.eval nodeValue1650 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1650) = mixedMoment B node1650 node1650Labels := rfl
  simpa [nodeValue1650, Sparse.eval] using hc.symm

theorem sound1651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1651 node1651Labels = Sparse.eval nodeValue1651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1651) = mixedMoment B node1651 node1651Labels := rfl
  simpa [nodeValue1651, Sparse.eval] using hc.symm

theorem sound1653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1653 node1653Labels = Sparse.eval nodeValue1653 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1653) = mixedMoment B node1653 node1653Labels := rfl
  simpa [nodeValue1653, Sparse.eval] using hc.symm

theorem sound1656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1656 node1656Labels = Sparse.eval nodeValue1656 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1656) = mixedMoment B node1656 node1656Labels := rfl
  simpa [nodeValue1656, Sparse.eval] using hc.symm

theorem sound1659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1659 node1659Labels = Sparse.eval nodeValue1659 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1659) = mixedMoment B node1659 node1659Labels := rfl
  simpa [nodeValue1659, Sparse.eval] using hc.symm

theorem sound1661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1661 node1661Labels = Sparse.eval nodeValue1661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1661) = mixedMoment B node1661 node1661Labels := rfl
  simpa [nodeValue1661, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound2382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2382 node2382Labels = Sparse.eval nodeValue2382 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2382) = mixedMoment B node2382 node2382Labels := rfl
  simpa [nodeValue2382, Sparse.eval] using hc.symm

theorem sound2383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2383 node2383Labels = Sparse.eval nodeValue2383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2383) = mixedMoment B node2383 node2383Labels := rfl
  simpa [nodeValue2383, Sparse.eval] using hc.symm

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

theorem sound2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2477 node2477Labels = Sparse.eval nodeValue2477 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2477) = mixedMoment B node2477 node2477Labels := rfl
  simpa [nodeValue2477, Sparse.eval] using hc.symm

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

theorem sound2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2521 node2521Labels = Sparse.eval nodeValue2521 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2521) = mixedMoment B node2521 node2521Labels := rfl
  simpa [nodeValue2521, Sparse.eval] using hc.symm

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

theorem sound2606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2606 node2606Labels = Sparse.eval nodeValue2606 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2606) = mixedMoment B node2606 node2606Labels := rfl
  simpa [nodeValue2606, Sparse.eval] using hc.symm

theorem sound2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2607 node2607Labels = Sparse.eval nodeValue2607 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2607) = mixedMoment B node2607 node2607Labels := rfl
  simpa [nodeValue2607, Sparse.eval] using hc.symm

theorem sound2613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2613 node2613Labels = Sparse.eval nodeValue2613 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2613) = mixedMoment B node2613 node2613Labels := rfl
  simpa [nodeValue2613, Sparse.eval] using hc.symm

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

theorem sound2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2661 node2661Labels = Sparse.eval nodeValue2661 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2661) = mixedMoment B node2661 node2661Labels := rfl
  simpa [nodeValue2661, Sparse.eval] using hc.symm

theorem sound2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2662 node2662Labels = Sparse.eval nodeValue2662 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2662) = mixedMoment B node2662 node2662Labels := rfl
  simpa [nodeValue2662, Sparse.eval] using hc.symm

theorem sound2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2669 node2669Labels = Sparse.eval nodeValue2669 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2669) = mixedMoment B node2669 node2669Labels := rfl
  simpa [nodeValue2669, Sparse.eval] using hc.symm

theorem sound2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2671 node2671Labels = Sparse.eval nodeValue2671 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2671) = mixedMoment B node2671 node2671Labels := rfl
  simpa [nodeValue2671, Sparse.eval] using hc.symm

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

theorem sound2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2694 node2694Labels = Sparse.eval nodeValue2694 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2694) = mixedMoment B node2694 node2694Labels := rfl
  simpa [nodeValue2694, Sparse.eval] using hc.symm

theorem sound2708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2708 node2708Labels = Sparse.eval nodeValue2708 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2708) = mixedMoment B node2708 node2708Labels := rfl
  simpa [nodeValue2708, Sparse.eval] using hc.symm

theorem sound2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2718 node2718Labels = Sparse.eval nodeValue2718 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2718) = mixedMoment B node2718 node2718Labels := rfl
  simpa [nodeValue2718, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

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

theorem sound3049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3049 node3049Labels = Sparse.eval nodeValue3049 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3049) = mixedMoment B node3049 node3049Labels := rfl
  simpa [nodeValue3049, Sparse.eval] using hc.symm

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

theorem sound3241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3241 node3241Labels = Sparse.eval nodeValue3241 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3241) = mixedMoment B node3241 node3241Labels := rfl
  simpa [nodeValue3241, Sparse.eval] using hc.symm

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

theorem sound4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4087 node4087Labels = Sparse.eval nodeValue4087 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4087) = mixedMoment B node4087 node4087Labels := rfl
  simpa [nodeValue4087, Sparse.eval] using hc.symm

theorem sound4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node4088 node4088Labels = Sparse.eval nodeValue4088 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 4088) = mixedMoment B node4088 node4088Labels := rfl
  simpa [nodeValue4088, Sparse.eval] using hc.symm

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

theorem sound625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node625 node625Labels = Sparse.eval nodeValue625 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 625) = mixedMoment B node625 node625Labels := rfl
  simpa [nodeValue625, Sparse.eval] using hc.symm

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

theorem sourceEq1631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1631 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1631 + difference 0 2) (sourceB1631 + difference 2 0) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2483) := by
    have ha : (tripleCharges (sourceA1631 + difference 0 2) (sourceB1631 + difference 2 0) sourceC1631) = raw24024 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24024; decide +kernel
    rw [ha]
    exact (canonical24024 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1631 + difference 1 2) (sourceB1631 + difference 2 1) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1135) := by
    have ha : (tripleCharges (sourceA1631 + difference 1 2) (sourceB1631 + difference 2 1) sourceC1631) = raw24021 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24021; decide +kernel
    rw [ha]
    exact (canonical24021 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1631 + difference 2 2) (sourceB1631 + difference 2 2) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1216) := by
    have ha : (tripleCharges (sourceA1631 + difference 2 2) (sourceB1631 + difference 2 2) sourceC1631) = raw24020 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24020; decide +kernel
    rw [ha]
    exact (canonical24020 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1631 + difference 3 2) (sourceB1631 + difference 2 3) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1631 + difference 3 2) (sourceB1631 + difference 2 3) sourceC1631) = raw24025 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24025; decide +kernel
    rw [ha]
    exact (canonical24025 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1631 + difference 4 2) (sourceB1631 + difference 2 4) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1631 + difference 4 2) (sourceB1631 + difference 2 4) sourceC1631) = raw24026 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24026; decide +kernel
    rw [ha]
    exact (canonical24026 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1631 + difference 5 2) (sourceB1631 + difference 2 5) sourceC1631) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1116) := by
    have ha : (tripleCharges (sourceA1631 + difference 5 2) (sourceB1631 + difference 2 5) sourceC1631) = raw24027 := by
      apply Matrix.ext; unfold tripleCharges sourceA1631 sourceB1631 sourceC1631 difference raw24027; decide +kernel
    rw [ha]
    exact (canonical24027 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1631 + sourceB1631) sourceC1631) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1631 + sourceB1631) sourceC1631) = raw13769 := by
      apply Matrix.ext; unfold doubleCharges sourceA1631 sourceB1631 sourceC1631 raw13769; decide +kernel
    rw [ha]
    exact (canonical13769 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1631 sourceB1631 sourceC1631
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1631, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sources51
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1632 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 0) (sourceB1632 + difference 0 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 0) (sourceB1632 + difference 0 0) sourceC1632) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 1) (sourceB1632 + difference 1 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1609) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 1) (sourceB1632 + difference 1 0) sourceC1632) = raw24028 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24028; decide +kernel
    rw [ha]
    exact (canonical24028 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 2) (sourceB1632 + difference 2 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 2) (sourceB1632 + difference 2 0) sourceC1632) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 3) (sourceB1632 + difference 3 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 3) (sourceB1632 + difference 3 0) sourceC1632) = raw24029 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24029; decide +kernel
    rw [ha]
    exact (canonical24029 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 4) (sourceB1632 + difference 4 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1607) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 4) (sourceB1632 + difference 4 0) sourceC1632) = raw24030 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24030; decide +kernel
    rw [ha]
    exact (canonical24030 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1632 + difference 0 5) (sourceB1632 + difference 5 0) sourceC1632) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1632 + difference 0 5) (sourceB1632 + difference 5 0) sourceC1632) = raw24031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1632 sourceB1632 sourceC1632 difference raw24031; decide +kernel
    rw [ha]
    exact (canonical24031 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1632 + sourceB1632) sourceC1632) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1632 + sourceB1632) sourceC1632) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1632 sourceB1632 sourceC1632 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1632 sourceB1632 sourceC1632
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1632, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1633 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1633 + difference 0 0) (sourceB1633 + difference 0 0) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1633 + difference 0 0) (sourceB1633 + difference 0 0) sourceC1633) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1633 + difference 1 0) (sourceB1633 + difference 0 1) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1633 + difference 1 0) (sourceB1633 + difference 0 1) sourceC1633) = raw23853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw23853; decide +kernel
    rw [ha]
    exact (canonical23853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1633 + difference 2 0) (sourceB1633 + difference 0 2) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1594) := by
    have ha : (tripleCharges (sourceA1633 + difference 2 0) (sourceB1633 + difference 0 2) sourceC1633) = raw24032 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24032; decide +kernel
    rw [ha]
    exact (canonical24032 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1633 + difference 3 0) (sourceB1633 + difference 0 3) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1633 + difference 3 0) (sourceB1633 + difference 0 3) sourceC1633) = raw24033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24033; decide +kernel
    rw [ha]
    exact (canonical24033 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1633 + difference 4 0) (sourceB1633 + difference 0 4) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1633 + difference 4 0) (sourceB1633 + difference 0 4) sourceC1633) = raw24034 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24034; decide +kernel
    rw [ha]
    exact (canonical24034 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1633 + difference 5 0) (sourceB1633 + difference 0 5) sourceC1633) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1592) := by
    have ha : (tripleCharges (sourceA1633 + difference 5 0) (sourceB1633 + difference 0 5) sourceC1633) = raw24035 := by
      apply Matrix.ext; unfold tripleCharges sourceA1633 sourceB1633 sourceC1633 difference raw24035; decide +kernel
    rw [ha]
    exact (canonical24035 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1633 + sourceB1633) sourceC1633) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1633 + sourceB1633) sourceC1633) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1633 sourceB1633 sourceC1633 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1633 sourceB1633 sourceC1633
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1633, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1634 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 0) (sourceB1634 + difference 0 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 0) (sourceB1634 + difference 0 3) sourceC1634) = raw24033 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24033; decide +kernel
    rw [ha]
    exact (canonical24033 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 1) (sourceB1634 + difference 1 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3238) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 1) (sourceB1634 + difference 1 3) sourceC1634) = raw24036 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24036; decide +kernel
    rw [ha]
    exact (canonical24036 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 2) (sourceB1634 + difference 2 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 2) (sourceB1634 + difference 2 3) sourceC1634) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 3) (sourceB1634 + difference 3 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 3) (sourceB1634 + difference 3 3) sourceC1634) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 4) (sourceB1634 + difference 4 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3285) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 4) (sourceB1634 + difference 4 3) sourceC1634) = raw24037 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24037; decide +kernel
    rw [ha]
    exact (canonical24037 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1634 + difference 3 5) (sourceB1634 + difference 5 3) sourceC1634) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1634 + difference 3 5) (sourceB1634 + difference 5 3) sourceC1634) = raw24038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1634 sourceB1634 sourceC1634 difference raw24038; decide +kernel
    rw [ha]
    exact (canonical24038 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1634 + sourceB1634) sourceC1634) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1634 + sourceB1634) sourceC1634) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1634 sourceB1634 sourceC1634 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1634 sourceB1634 sourceC1634
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1634, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1635 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1635 + difference 0 5) (sourceB1635 + difference 5 0) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1635 + difference 0 5) (sourceB1635 + difference 5 0) sourceC1635) = raw24031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw24031; decide +kernel
    rw [ha]
    exact (canonical24031 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1635 + difference 1 5) (sourceB1635 + difference 5 1) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3299) := by
    have ha : (tripleCharges (sourceA1635 + difference 1 5) (sourceB1635 + difference 5 1) sourceC1635) = raw23847 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23847; decide +kernel
    rw [ha]
    exact (canonical23847 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1635 + difference 2 5) (sourceB1635 + difference 5 2) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3241) := by
    have ha : (tripleCharges (sourceA1635 + difference 2 5) (sourceB1635 + difference 5 2) sourceC1635) = raw23846 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23846; decide +kernel
    rw [ha]
    exact (canonical23846 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1635 + difference 3 5) (sourceB1635 + difference 5 3) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1635 + difference 3 5) (sourceB1635 + difference 5 3) sourceC1635) = raw24038 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw24038; decide +kernel
    rw [ha]
    exact (canonical24038 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1635 + difference 4 5) (sourceB1635 + difference 5 4) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1635 + difference 4 5) (sourceB1635 + difference 5 4) sourceC1635) = raw23982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23982; decide +kernel
    rw [ha]
    exact (canonical23982 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1635 + difference 5 5) (sourceB1635 + difference 5 5) sourceC1635) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1635 + difference 5 5) (sourceB1635 + difference 5 5) sourceC1635) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1635 sourceB1635 sourceC1635 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1635 + sourceB1635) sourceC1635) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1635 + sourceB1635) sourceC1635) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1635 sourceB1635 sourceC1635 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1635 sourceB1635 sourceC1635
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1635, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1636 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1636 + difference 0 1) (sourceB1636 + difference 1 0) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2480) := by
    have ha : (tripleCharges (sourceA1636 + difference 0 1) (sourceB1636 + difference 1 0) sourceC1636) = raw24039 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24039; decide +kernel
    rw [ha]
    exact (canonical24039 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1636 + difference 1 1) (sourceB1636 + difference 1 1) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1636 + difference 1 1) (sourceB1636 + difference 1 1) sourceC1636) = raw24040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24040; decide +kernel
    rw [ha]
    exact (canonical24040 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1636 + difference 2 1) (sourceB1636 + difference 1 2) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1636 + difference 2 1) (sourceB1636 + difference 1 2) sourceC1636) = raw24041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24041; decide +kernel
    rw [ha]
    exact (canonical24041 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1636 + difference 3 1) (sourceB1636 + difference 1 3) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1117) := by
    have ha : (tripleCharges (sourceA1636 + difference 3 1) (sourceB1636 + difference 1 3) sourceC1636) = raw24042 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24042; decide +kernel
    rw [ha]
    exact (canonical24042 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1636 + difference 4 1) (sourceB1636 + difference 1 4) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1114) := by
    have ha : (tripleCharges (sourceA1636 + difference 4 1) (sourceB1636 + difference 1 4) sourceC1636) = raw24043 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24043; decide +kernel
    rw [ha]
    exact (canonical24043 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1636 + difference 5 1) (sourceB1636 + difference 1 5) sourceC1636) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1112) := by
    have ha : (tripleCharges (sourceA1636 + difference 5 1) (sourceB1636 + difference 1 5) sourceC1636) = raw24044 := by
      apply Matrix.ext; unfold tripleCharges sourceA1636 sourceB1636 sourceC1636 difference raw24044; decide +kernel
    rw [ha]
    exact (canonical24044 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1636 + sourceB1636) sourceC1636) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1636 + sourceB1636) sourceC1636) = raw24045 := by
      apply Matrix.ext; unfold doubleCharges sourceA1636 sourceB1636 sourceC1636 raw24045; decide +kernel
    rw [ha]
    exact (canonical24045 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1636 sourceB1636 sourceC1636
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1636, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1637 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 0) (sourceB1637 + difference 0 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 625) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 0) (sourceB1637 + difference 0 2) sourceC1637) = raw24046 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24046; decide +kernel
    rw [ha]
    exact (canonical24046 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 1) (sourceB1637 + difference 1 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1129) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 1) (sourceB1637 + difference 1 2) sourceC1637) = raw24041 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24041; decide +kernel
    rw [ha]
    exact (canonical24041 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 2) (sourceB1637 + difference 2 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 2) (sourceB1637 + difference 2 2) sourceC1637) = raw24040 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24040; decide +kernel
    rw [ha]
    exact (canonical24040 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 3) (sourceB1637 + difference 3 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 3) (sourceB1637 + difference 3 2) sourceC1637) = raw24047 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24047; decide +kernel
    rw [ha]
    exact (canonical24047 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 4) (sourceB1637 + difference 4 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1213) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 4) (sourceB1637 + difference 4 2) sourceC1637) = raw24048 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24048; decide +kernel
    rw [ha]
    exact (canonical24048 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1637 + difference 2 5) (sourceB1637 + difference 5 2) sourceC1637) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1235) := by
    have ha : (tripleCharges (sourceA1637 + difference 2 5) (sourceB1637 + difference 5 2) sourceC1637) = raw24049 := by
      apply Matrix.ext; unfold tripleCharges sourceA1637 sourceB1637 sourceC1637 difference raw24049; decide +kernel
    rw [ha]
    exact (canonical24049 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1637 + sourceB1637) sourceC1637) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1637 + sourceB1637) sourceC1637) = raw24045 := by
      apply Matrix.ext; unfold doubleCharges sourceA1637 sourceB1637 sourceC1637 raw24045; decide +kernel
    rw [ha]
    exact (canonical24045 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1637 sourceB1637 sourceC1637
    (0 : Fin 2) 1 (2 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1637, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1638 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 0) (sourceB1638 + difference 0 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3290) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 0) (sourceB1638 + difference 0 0) sourceC1638) = raw23982 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw23982; decide +kernel
    rw [ha]
    exact (canonical23982 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 1) (sourceB1638 + difference 1 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1601) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 1) (sourceB1638 + difference 1 0) sourceC1638) = raw24050 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24050; decide +kernel
    rw [ha]
    exact (canonical24050 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 2) (sourceB1638 + difference 2 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 2) (sourceB1638 + difference 2 0) sourceC1638) = raw23970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw23970; decide +kernel
    rw [ha]
    exact (canonical23970 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 3) (sourceB1638 + difference 3 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1598) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 3) (sourceB1638 + difference 3 0) sourceC1638) = raw24051 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24051; decide +kernel
    rw [ha]
    exact (canonical24051 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 4) (sourceB1638 + difference 4 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1616) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 4) (sourceB1638 + difference 4 0) sourceC1638) = raw24031 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24031; decide +kernel
    rw [ha]
    exact (canonical24031 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1638 + difference 0 5) (sourceB1638 + difference 5 0) sourceC1638) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1597) := by
    have ha : (tripleCharges (sourceA1638 + difference 0 5) (sourceB1638 + difference 5 0) sourceC1638) = raw24052 := by
      apply Matrix.ext; unfold tripleCharges sourceA1638 sourceB1638 sourceC1638 difference raw24052; decide +kernel
    rw [ha]
    exact (canonical24052 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1638 + sourceB1638) sourceC1638) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1638 + sourceB1638) sourceC1638) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1638 sourceB1638 sourceC1638 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1638 sourceB1638 sourceC1638
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1638, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1639 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 0) (sourceB1639 + difference 0 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1210) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 0) (sourceB1639 + difference 0 0) sourceC1639) = raw24053 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24053; decide +kernel
    rw [ha]
    exact (canonical24053 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 1) (sourceB1639 + difference 1 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2613) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 1) (sourceB1639 + difference 1 0) sourceC1639) = raw24054 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24054; decide +kernel
    rw [ha]
    exact (canonical24054 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 2) (sourceB1639 + difference 2 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2477) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 2) (sourceB1639 + difference 2 0) sourceC1639) = raw24055 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24055; decide +kernel
    rw [ha]
    exact (canonical24055 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 3) (sourceB1639 + difference 3 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2708) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 3) (sourceB1639 + difference 3 0) sourceC1639) = raw24056 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24056; decide +kernel
    rw [ha]
    exact (canonical24056 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 4) (sourceB1639 + difference 4 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2694) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 4) (sourceB1639 + difference 4 0) sourceC1639) = raw24057 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24057; decide +kernel
    rw [ha]
    exact (canonical24057 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1639 + difference 0 5) (sourceB1639 + difference 5 0) sourceC1639) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2718) := by
    have ha : (tripleCharges (sourceA1639 + difference 0 5) (sourceB1639 + difference 5 0) sourceC1639) = raw24058 := by
      apply Matrix.ext; unfold tripleCharges sourceA1639 sourceB1639 sourceC1639 difference raw24058; decide +kernel
    rw [ha]
    exact (canonical24058 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1639 + sourceB1639) sourceC1639) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4090) := by
    have ha : (doubleCharges (sourceA1639 + sourceB1639) sourceC1639) = raw24059 := by
      apply Matrix.ext; unfold doubleCharges sourceA1639 sourceB1639 sourceC1639 raw24059; decide +kernel
    rw [ha]
    exact (canonical24059 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1639 sourceB1639 sourceC1639
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1639, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1640 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 0) (sourceB1640 + difference 0 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 0) (sourceB1640 + difference 0 0) sourceC1640) = raw24060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24060; decide +kernel
    rw [ha]
    exact (canonical24060 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 1) (sourceB1640 + difference 1 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2607) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 1) (sourceB1640 + difference 1 0) sourceC1640) = raw24061 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24061; decide +kernel
    rw [ha]
    exact (canonical24061 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 2) (sourceB1640 + difference 2 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2383) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 2) (sourceB1640 + difference 2 0) sourceC1640) = raw24062 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24062; decide +kernel
    rw [ha]
    exact (canonical24062 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 3) (sourceB1640 + difference 3 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 3) (sourceB1640 + difference 3 0) sourceC1640) = raw24063 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24063; decide +kernel
    rw [ha]
    exact (canonical24063 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 4) (sourceB1640 + difference 4 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2662) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 4) (sourceB1640 + difference 4 0) sourceC1640) = raw24064 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24064; decide +kernel
    rw [ha]
    exact (canonical24064 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1640 + difference 0 5) (sourceB1640 + difference 5 0) sourceC1640) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1640 + difference 0 5) (sourceB1640 + difference 5 0) sourceC1640) = raw24065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1640 sourceB1640 sourceC1640 difference raw24065; decide +kernel
    rw [ha]
    exact (canonical24065 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1640 + sourceB1640) sourceC1640) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1640 + sourceB1640) sourceC1640) = raw24066 := by
      apply Matrix.ext; unfold doubleCharges sourceA1640 sourceB1640 sourceC1640 raw24066; decide +kernel
    rw [ha]
    exact (canonical24066 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1640 sourceB1640 sourceC1640
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1640, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1641 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1641 + difference 0 5) (sourceB1641 + difference 5 0) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2671) := by
    have ha : (tripleCharges (sourceA1641 + difference 0 5) (sourceB1641 + difference 5 0) sourceC1641) = raw24065 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24065; decide +kernel
    rw [ha]
    exact (canonical24065 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1641 + difference 1 5) (sourceB1641 + difference 5 1) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1187) := by
    have ha : (tripleCharges (sourceA1641 + difference 1 5) (sourceB1641 + difference 5 1) sourceC1641) = raw24067 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24067; decide +kernel
    rw [ha]
    exact (canonical24067 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1641 + difference 2 5) (sourceB1641 + difference 5 2) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1256) := by
    have ha : (tripleCharges (sourceA1641 + difference 2 5) (sourceB1641 + difference 5 2) sourceC1641) = raw24068 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24068; decide +kernel
    rw [ha]
    exact (canonical24068 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1641 + difference 3 5) (sourceB1641 + difference 5 3) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1641 + difference 3 5) (sourceB1641 + difference 5 3) sourceC1641) = raw24069 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24069; decide +kernel
    rw [ha]
    exact (canonical24069 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1641 + difference 4 5) (sourceB1641 + difference 5 4) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1641 + difference 4 5) (sourceB1641 + difference 5 4) sourceC1641) = raw24070 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24070; decide +kernel
    rw [ha]
    exact (canonical24070 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1641 + difference 5 5) (sourceB1641 + difference 5 5) sourceC1641) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1180) := by
    have ha : (tripleCharges (sourceA1641 + difference 5 5) (sourceB1641 + difference 5 5) sourceC1641) = raw24060 := by
      apply Matrix.ext; unfold tripleCharges sourceA1641 sourceB1641 sourceC1641 difference raw24060; decide +kernel
    rw [ha]
    exact (canonical24060 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1641 + sourceB1641) sourceC1641) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4087) := by
    have ha : (doubleCharges (sourceA1641 + sourceB1641) sourceC1641) = raw24066 := by
      apply Matrix.ext; unfold doubleCharges sourceA1641 sourceB1641 sourceC1641 raw24066; decide +kernel
    rw [ha]
    exact (canonical24066 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1641 sourceB1641 sourceC1641
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1641, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1642 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 0) (sourceB1642 + difference 0 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1178) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 0) (sourceB1642 + difference 0 0) sourceC1642) = raw24071 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24071; decide +kernel
    rw [ha]
    exact (canonical24071 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 1) (sourceB1642 + difference 1 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2606) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 1) (sourceB1642 + difference 1 0) sourceC1642) = raw24072 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24072; decide +kernel
    rw [ha]
    exact (canonical24072 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 2) (sourceB1642 + difference 2 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2382) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 2) (sourceB1642 + difference 2 0) sourceC1642) = raw24073 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24073; decide +kernel
    rw [ha]
    exact (canonical24073 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 3) (sourceB1642 + difference 3 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2661) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 3) (sourceB1642 + difference 3 0) sourceC1642) = raw24074 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24074; decide +kernel
    rw [ha]
    exact (canonical24074 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 4) (sourceB1642 + difference 4 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2672) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 4) (sourceB1642 + difference 4 0) sourceC1642) = raw24075 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24075; decide +kernel
    rw [ha]
    exact (canonical24075 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1642 + difference 0 5) (sourceB1642 + difference 5 0) sourceC1642) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2669) := by
    have ha : (tripleCharges (sourceA1642 + difference 0 5) (sourceB1642 + difference 5 0) sourceC1642) = raw24076 := by
      apply Matrix.ext; unfold tripleCharges sourceA1642 sourceB1642 sourceC1642 difference raw24076; decide +kernel
    rw [ha]
    exact (canonical24076 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1642 + sourceB1642) sourceC1642) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4088) := by
    have ha : (doubleCharges (sourceA1642 + sourceB1642) sourceC1642) = raw24077 := by
      apply Matrix.ext; unfold doubleCharges sourceA1642 sourceB1642 sourceC1642 raw24077; decide +kernel
    rw [ha]
    exact (canonical24077 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1642 sourceB1642 sourceC1642
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1642, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1643 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 0) (sourceB1643 + difference 0 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 0) (sourceB1643 + difference 0 0) sourceC1643) = raw23945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw23945; decide +kernel
    rw [ha]
    exact (canonical23945 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 1) (sourceB1643 + difference 1 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 1) (sourceB1643 + difference 1 0) sourceC1643) = raw23940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw23940; decide +kernel
    rw [ha]
    exact (canonical23940 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 2) (sourceB1643 + difference 2 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 2) (sourceB1643 + difference 2 0) sourceC1643) = raw24078 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24078; decide +kernel
    rw [ha]
    exact (canonical24078 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 3) (sourceB1643 + difference 3 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1659) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 3) (sourceB1643 + difference 3 0) sourceC1643) = raw24079 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24079; decide +kernel
    rw [ha]
    exact (canonical24079 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 4) (sourceB1643 + difference 4 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1661) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 4) (sourceB1643 + difference 4 0) sourceC1643) = raw24080 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24080; decide +kernel
    rw [ha]
    exact (canonical24080 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1643 + difference 0 5) (sourceB1643 + difference 5 0) sourceC1643) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1739) := by
    have ha : (tripleCharges (sourceA1643 + difference 0 5) (sourceB1643 + difference 5 0) sourceC1643) = raw24081 := by
      apply Matrix.ext; unfold tripleCharges sourceA1643 sourceB1643 sourceC1643 difference raw24081; decide +kernel
    rw [ha]
    exact (canonical24081 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1643 + sourceB1643) sourceC1643) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1643 + sourceB1643) sourceC1643) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1643 sourceB1643 sourceC1643 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1643 sourceB1643 sourceC1643
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1643, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1644 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 0) (sourceB1644 + difference 0 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1650) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 0) (sourceB1644 + difference 0 4) sourceC1644) = raw24082 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24082; decide +kernel
    rw [ha]
    exact (canonical24082 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 1) (sourceB1644 + difference 1 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 1) (sourceB1644 + difference 1 4) sourceC1644) = raw24083 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24083; decide +kernel
    rw [ha]
    exact (canonical24083 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 2) (sourceB1644 + difference 2 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 2) (sourceB1644 + difference 2 4) sourceC1644) = raw24084 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24084; decide +kernel
    rw [ha]
    exact (canonical24084 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 3) (sourceB1644 + difference 3 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2521) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 3) (sourceB1644 + difference 3 4) sourceC1644) = raw24085 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24085; decide +kernel
    rw [ha]
    exact (canonical24085 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 4) (sourceB1644 + difference 4 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 4) (sourceB1644 + difference 4 4) sourceC1644) = raw23945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw23945; decide +kernel
    rw [ha]
    exact (canonical23945 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1644 + difference 4 5) (sourceB1644 + difference 5 4) sourceC1644) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1644 + difference 4 5) (sourceB1644 + difference 5 4) sourceC1644) = raw24086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1644 sourceB1644 sourceC1644 difference raw24086; decide +kernel
    rw [ha]
    exact (canonical24086 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1644 + sourceB1644) sourceC1644) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1644 + sourceB1644) sourceC1644) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1644 sourceB1644 sourceC1644 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1644 sourceB1644 sourceC1644
    (0 : Fin 2) 1 (4 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1644, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1645 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 0) (sourceB1645 + difference 0 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 0) (sourceB1645 + difference 0 0) sourceC1645) = raw23976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw23976; decide +kernel
    rw [ha]
    exact (canonical23976 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 1) (sourceB1645 + difference 1 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 1) (sourceB1645 + difference 1 0) sourceC1645) = raw23969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw23969; decide +kernel
    rw [ha]
    exact (canonical23969 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 2) (sourceB1645 + difference 2 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 2) (sourceB1645 + difference 2 0) sourceC1645) = raw24087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24087; decide +kernel
    rw [ha]
    exact (canonical24087 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 3) (sourceB1645 + difference 3 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1651) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 3) (sourceB1645 + difference 3 0) sourceC1645) = raw24088 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24088; decide +kernel
    rw [ha]
    exact (canonical24088 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 4) (sourceB1645 + difference 4 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1728) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 4) (sourceB1645 + difference 4 0) sourceC1645) = raw24089 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24089; decide +kernel
    rw [ha]
    exact (canonical24089 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1645 + difference 0 5) (sourceB1645 + difference 5 0) sourceC1645) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1645 + difference 0 5) (sourceB1645 + difference 5 0) sourceC1645) = raw24090 := by
      apply Matrix.ext; unfold tripleCharges sourceA1645 sourceB1645 sourceC1645 difference raw24090; decide +kernel
    rw [ha]
    exact (canonical24090 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1645 + sourceB1645) sourceC1645) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1645 + sourceB1645) sourceC1645) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1645 sourceB1645 sourceC1645 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1645 sourceB1645 sourceC1645
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1645, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1646 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 0) (sourceB1646 + difference 0 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1653) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 0) (sourceB1646 + difference 0 5) sourceC1646) = raw24091 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24091; decide +kernel
    rw [ha]
    exact (canonical24091 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 1) (sourceB1646 + difference 1 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 1) (sourceB1646 + difference 1 5) sourceC1646) = raw23985 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw23985; decide +kernel
    rw [ha]
    exact (canonical23985 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 2) (sourceB1646 + difference 2 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3287) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 2) (sourceB1646 + difference 2 5) sourceC1646) = raw24092 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24092; decide +kernel
    rw [ha]
    exact (canonical24092 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 3) (sourceB1646 + difference 3 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3049) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 3) (sourceB1646 + difference 3 5) sourceC1646) = raw24093 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24093; decide +kernel
    rw [ha]
    exact (canonical24093 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 4) (sourceB1646 + difference 4 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3305) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 4) (sourceB1646 + difference 4 5) sourceC1646) = raw24086 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw24086; decide +kernel
    rw [ha]
    exact (canonical24086 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1646 + difference 5 5) (sourceB1646 + difference 5 5) sourceC1646) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3306) := by
    have ha : (tripleCharges (sourceA1646 + difference 5 5) (sourceB1646 + difference 5 5) sourceC1646) = raw23976 := by
      apply Matrix.ext; unfold tripleCharges sourceA1646 sourceB1646 sourceC1646 difference raw23976; decide +kernel
    rw [ha]
    exact (canonical23976 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1646 + sourceB1646) sourceC1646) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1646 + sourceB1646) sourceC1646) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1646 sourceB1646 sourceC1646 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1646 sourceB1646 sourceC1646
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1646, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1392 : Integer.Sparse.reindex keyMap MixedData.row1392 = numericRow1392 := by decide +kernel

theorem numericCheck1392 (x : Master → ℝ) : Integer.Sparse.eval numericRow1392 x =
    (1 : ℝ) * reducedSource1392 x := by
  norm_num [numericRow1392, reducedSource1392, Integer.Sparse.eval, Sparse.eval, nodeValue1116, nodeValue1117, nodeValue1135, nodeValue1216, nodeValue2483, nodeValue4091]

theorem reindexCheck1393 : Integer.Sparse.reindex keyMap MixedData.row1393 = numericRow1393 := by decide +kernel

theorem numericCheck1393 (x : Master → ℝ) : Integer.Sparse.eval numericRow1393 x =
    (1 : ℝ) * reducedSource1393 x := by
  norm_num [numericRow1393, reducedSource1393, Integer.Sparse.eval, Sparse.eval, nodeValue1607, nodeValue1609, nodeValue1616, nodeValue1737, nodeValue3288, nodeValue4069]

theorem reindexCheck1394 : Integer.Sparse.reindex keyMap MixedData.row1394 = numericRow1394 := by decide +kernel

theorem numericCheck1394 (x : Master → ℝ) : Integer.Sparse.eval numericRow1394 x =
    (1 : ℝ) * reducedSource1394 x := by
  norm_num [numericRow1394, reducedSource1394, Integer.Sparse.eval, Sparse.eval, nodeValue1592, nodeValue1594, nodeValue1597, nodeValue1707, nodeValue3288, nodeValue4069]

theorem reindexCheck1395 : Integer.Sparse.reindex keyMap MixedData.row1395 = numericRow1395 := by decide +kernel

theorem numericCheck1395 (x : Master → ℝ) : Integer.Sparse.eval numericRow1395 x =
    (1 : ℝ) * reducedSource1395 x := by
  norm_num [numericRow1395, reducedSource1395, Integer.Sparse.eval, Sparse.eval, nodeValue1597, nodeValue3238, nodeValue3285, nodeValue3288, nodeValue3290, nodeValue3293, nodeValue4069]

theorem reindexCheck1396 : Integer.Sparse.reindex keyMap MixedData.row1396 = numericRow1396 := by decide +kernel

theorem numericCheck1396 (x : Master → ℝ) : Integer.Sparse.eval numericRow1396 x =
    (1 : ℝ) * reducedSource1396 x := by
  norm_num [numericRow1396, reducedSource1396, Integer.Sparse.eval, Sparse.eval, nodeValue1616, nodeValue3241, nodeValue3288, nodeValue3290, nodeValue3299, nodeValue4069]

theorem reindexCheck1397 : Integer.Sparse.reindex keyMap MixedData.row1397 = numericRow1397 := by decide +kernel

theorem numericCheck1397 (x : Master → ℝ) : Integer.Sparse.eval numericRow1397 x =
    (1 : ℝ) * reducedSource1397 x := by
  norm_num [numericRow1397, reducedSource1397, Integer.Sparse.eval, Sparse.eval, nodeValue1112, nodeValue1114, nodeValue1117, nodeValue1129, nodeValue1213, nodeValue2480, nodeValue4091]

theorem reindexCheck1398 : Integer.Sparse.reindex keyMap MixedData.row1398 = numericRow1398 := by decide +kernel

theorem numericCheck1398 (x : Master → ℝ) : Integer.Sparse.eval numericRow1398 x =
    (1 : ℝ) * reducedSource1398 x := by
  norm_num [numericRow1398, reducedSource1398, Integer.Sparse.eval, Sparse.eval, nodeValue625, nodeValue1129, nodeValue1213, nodeValue1235, nodeValue1240, nodeValue4091]

theorem reindexCheck1399 : Integer.Sparse.reindex keyMap MixedData.row1399 = numericRow1399 := by decide +kernel

theorem numericCheck1399 (x : Master → ℝ) : Integer.Sparse.eval numericRow1399 x =
    (1 : ℝ) * reducedSource1399 x := by
  norm_num [numericRow1399, reducedSource1399, Integer.Sparse.eval, Sparse.eval, nodeValue1597, nodeValue1598, nodeValue1601, nodeValue1616, nodeValue1724, nodeValue3290, nodeValue4069]

theorem reindexCheck1400 : Integer.Sparse.reindex keyMap MixedData.row1400 = numericRow1400 := by decide +kernel

theorem numericCheck1400 (x : Master → ℝ) : Integer.Sparse.eval numericRow1400 x =
    (1 : ℝ) * reducedSource1400 x := by
  norm_num [numericRow1400, reducedSource1400, Integer.Sparse.eval, Sparse.eval, nodeValue1210, nodeValue2477, nodeValue2613, nodeValue2694, nodeValue2708, nodeValue2718, nodeValue4090]

theorem reindexCheck1401 : Integer.Sparse.reindex keyMap MixedData.row1401 = numericRow1401 := by decide +kernel

theorem numericCheck1401 (x : Master → ℝ) : Integer.Sparse.eval numericRow1401 x =
    (1 : ℝ) * reducedSource1401 x := by
  norm_num [numericRow1401, reducedSource1401, Integer.Sparse.eval, Sparse.eval, nodeValue1180, nodeValue2383, nodeValue2607, nodeValue2662, nodeValue2671, nodeValue4087]

theorem reindexCheck1402 : Integer.Sparse.reindex keyMap MixedData.row1402 = numericRow1402 := by decide +kernel

theorem numericCheck1402 (x : Master → ℝ) : Integer.Sparse.eval numericRow1402 x =
    (1 : ℝ) * reducedSource1402 x := by
  norm_num [numericRow1402, reducedSource1402, Integer.Sparse.eval, Sparse.eval, nodeValue1180, nodeValue1187, nodeValue1256, nodeValue2671, nodeValue4087]

theorem reindexCheck1403 : Integer.Sparse.reindex keyMap MixedData.row1403 = numericRow1403 := by decide +kernel

theorem numericCheck1403 (x : Master → ℝ) : Integer.Sparse.eval numericRow1403 x =
    (1 : ℝ) * reducedSource1403 x := by
  norm_num [numericRow1403, reducedSource1403, Integer.Sparse.eval, Sparse.eval, nodeValue1178, nodeValue2382, nodeValue2606, nodeValue2661, nodeValue2669, nodeValue2672, nodeValue4088]

theorem reindexCheck1404 : Integer.Sparse.reindex keyMap MixedData.row1404 = numericRow1404 := by decide +kernel

theorem numericCheck1404 (x : Master → ℝ) : Integer.Sparse.eval numericRow1404 x =
    (1 : ℝ) * reducedSource1404 x := by
  norm_num [numericRow1404, reducedSource1404, Integer.Sparse.eval, Sparse.eval, nodeValue1656, nodeValue1659, nodeValue1661, nodeValue1739, nodeValue2737, nodeValue4069]

theorem reindexCheck1405 : Integer.Sparse.reindex keyMap MixedData.row1405 = numericRow1405 := by decide +kernel

theorem numericCheck1405 (x : Master → ℝ) : Integer.Sparse.eval numericRow1405 x =
    (1 : ℝ) * reducedSource1405 x := by
  norm_num [numericRow1405, reducedSource1405, Integer.Sparse.eval, Sparse.eval, nodeValue1650, nodeValue2502, nodeValue2521, nodeValue2737, nodeValue3305, nodeValue4069]

theorem reindexCheck1406 : Integer.Sparse.reindex keyMap MixedData.row1406 = numericRow1406 := by decide +kernel

theorem numericCheck1406 (x : Master → ℝ) : Integer.Sparse.eval numericRow1406 x =
    (1 : ℝ) * reducedSource1406 x := by
  norm_num [numericRow1406, reducedSource1406, Integer.Sparse.eval, Sparse.eval, nodeValue1646, nodeValue1651, nodeValue1653, nodeValue1728, nodeValue3306, nodeValue4069]

theorem reindexCheck1407 : Integer.Sparse.reindex keyMap MixedData.row1407 = numericRow1407 := by decide +kernel

theorem numericCheck1407 (x : Master → ℝ) : Integer.Sparse.eval numericRow1407 x =
    (1 : ℝ) * reducedSource1407 x := by
  norm_num [numericRow1407, reducedSource1407, Integer.Sparse.eval, Sparse.eval, nodeValue1653, nodeValue3049, nodeValue3287, nodeValue3305, nodeValue3306, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows87
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1392 (mixedVector B) = 0 := by
  have h1116 : mixedVector B (Sum.inr 1116) = Sparse.eval nodeValue1116 (mixedVector B) := by
    change mixedMoment B node1116 node1116Labels = _
    exact sound1116 B hB hF
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1135 : mixedVector B (Sum.inr 1135) = Sparse.eval nodeValue1135 (mixedVector B) := by
    change mixedMoment B node1135 node1135Labels = _
    exact sound1135 B hB hF
  have h1216 : mixedVector B (Sum.inr 1216) = Sparse.eval nodeValue1216 (mixedVector B) := by
    change mixedMoment B node1216 node1216Labels = _
    exact sound1216 B hB hF
  have h2483 : mixedVector B (Sum.inr 2483) = Sparse.eval nodeValue2483 (mixedVector B) := by
    change mixedMoment B node2483 node2483Labels = _
    exact sound2483 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1631, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1116, h1117, h1135, h1216, h2483, h4091, reducedSource1392] using sourceEq1631 B hB

theorem rowSound1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1392 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1392, numericCheck1392, reducedZero1392 B hB hF, mul_zero]

theorem reducedZero1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1393 (mixedVector B) = 0 := by
  have h1607 : mixedVector B (Sum.inr 1607) = Sparse.eval nodeValue1607 (mixedVector B) := by
    change mixedMoment B node1607 node1607Labels = _
    exact sound1607 B hB hF
  have h1609 : mixedVector B (Sum.inr 1609) = Sparse.eval nodeValue1609 (mixedVector B) := by
    change mixedMoment B node1609 node1609Labels = _
    exact sound1609 B hB hF
  have h1616 : mixedVector B (Sum.inr 1616) = Sparse.eval nodeValue1616 (mixedVector B) := by
    change mixedMoment B node1616 node1616Labels = _
    exact sound1616 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1632, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1607, h1609, h1616, h1737, h3288, h4069, reducedSource1393] using sourceEq1632 B hB

theorem rowSound1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1393 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1393, numericCheck1393, reducedZero1393 B hB hF, mul_zero]

theorem reducedZero1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1394 (mixedVector B) = 0 := by
  have h1592 : mixedVector B (Sum.inr 1592) = Sparse.eval nodeValue1592 (mixedVector B) := by
    change mixedMoment B node1592 node1592Labels = _
    exact sound1592 B hB hF
  have h1594 : mixedVector B (Sum.inr 1594) = Sparse.eval nodeValue1594 (mixedVector B) := by
    change mixedMoment B node1594 node1594Labels = _
    exact sound1594 B hB hF
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1633, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1592, h1594, h1597, h1707, h3288, h4069, reducedSource1394] using sourceEq1633 B hB

theorem rowSound1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1394 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1394, numericCheck1394, reducedZero1394 B hB hF, mul_zero]

theorem reducedZero1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1395 (mixedVector B) = 0 := by
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h3238 : mixedVector B (Sum.inr 3238) = Sparse.eval nodeValue3238 (mixedVector B) := by
    change mixedMoment B node3238 node3238Labels = _
    exact sound3238 B hB hF
  have h3285 : mixedVector B (Sum.inr 3285) = Sparse.eval nodeValue3285 (mixedVector B) := by
    change mixedMoment B node3285 node3285Labels = _
    exact sound3285 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1634, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1597, h3238, h3285, h3288, h3290, h3293, h4069, reducedSource1395] using sourceEq1634 B hB

theorem rowSound1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1395 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1395, numericCheck1395, reducedZero1395 B hB hF, mul_zero]

theorem reducedZero1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1396 (mixedVector B) = 0 := by
  have h1616 : mixedVector B (Sum.inr 1616) = Sparse.eval nodeValue1616 (mixedVector B) := by
    change mixedMoment B node1616 node1616Labels = _
    exact sound1616 B hB hF
  have h3241 : mixedVector B (Sum.inr 3241) = Sparse.eval nodeValue3241 (mixedVector B) := by
    change mixedMoment B node3241 node3241Labels = _
    exact sound3241 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h3299 : mixedVector B (Sum.inr 3299) = Sparse.eval nodeValue3299 (mixedVector B) := by
    change mixedMoment B node3299 node3299Labels = _
    exact sound3299 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1635, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1616, h3241, h3288, h3290, h3299, h4069, reducedSource1396] using sourceEq1635 B hB

theorem rowSound1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1396 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1396, numericCheck1396, reducedZero1396 B hB hF, mul_zero]

theorem reducedZero1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1397 (mixedVector B) = 0 := by
  have h1112 : mixedVector B (Sum.inr 1112) = Sparse.eval nodeValue1112 (mixedVector B) := by
    change mixedMoment B node1112 node1112Labels = _
    exact sound1112 B hB hF
  have h1114 : mixedVector B (Sum.inr 1114) = Sparse.eval nodeValue1114 (mixedVector B) := by
    change mixedMoment B node1114 node1114Labels = _
    exact sound1114 B hB hF
  have h1117 : mixedVector B (Sum.inr 1117) = Sparse.eval nodeValue1117 (mixedVector B) := by
    change mixedMoment B node1117 node1117Labels = _
    exact sound1117 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h2480 : mixedVector B (Sum.inr 2480) = Sparse.eval nodeValue2480 (mixedVector B) := by
    change mixedMoment B node2480 node2480Labels = _
    exact sound2480 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1636, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1112, h1114, h1117, h1129, h1213, h2480, h4091, reducedSource1397] using sourceEq1636 B hB

theorem rowSound1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1397 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1397, numericCheck1397, reducedZero1397 B hB hF, mul_zero]

theorem reducedZero1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1398 (mixedVector B) = 0 := by
  have h625 : mixedVector B (Sum.inr 625) = Sparse.eval nodeValue625 (mixedVector B) := by
    change mixedMoment B node625 node625Labels = _
    exact sound625 B hB hF
  have h1129 : mixedVector B (Sum.inr 1129) = Sparse.eval nodeValue1129 (mixedVector B) := by
    change mixedMoment B node1129 node1129Labels = _
    exact sound1129 B hB hF
  have h1213 : mixedVector B (Sum.inr 1213) = Sparse.eval nodeValue1213 (mixedVector B) := by
    change mixedMoment B node1213 node1213Labels = _
    exact sound1213 B hB hF
  have h1235 : mixedVector B (Sum.inr 1235) = Sparse.eval nodeValue1235 (mixedVector B) := by
    change mixedMoment B node1235 node1235Labels = _
    exact sound1235 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1637, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h625, h1129, h1213, h1235, h1240, h4091, reducedSource1398] using sourceEq1637 B hB

theorem rowSound1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1398 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1398, numericCheck1398, reducedZero1398 B hB hF, mul_zero]

theorem reducedZero1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1399 (mixedVector B) = 0 := by
  have h1597 : mixedVector B (Sum.inr 1597) = Sparse.eval nodeValue1597 (mixedVector B) := by
    change mixedMoment B node1597 node1597Labels = _
    exact sound1597 B hB hF
  have h1598 : mixedVector B (Sum.inr 1598) = Sparse.eval nodeValue1598 (mixedVector B) := by
    change mixedMoment B node1598 node1598Labels = _
    exact sound1598 B hB hF
  have h1601 : mixedVector B (Sum.inr 1601) = Sparse.eval nodeValue1601 (mixedVector B) := by
    change mixedMoment B node1601 node1601Labels = _
    exact sound1601 B hB hF
  have h1616 : mixedVector B (Sum.inr 1616) = Sparse.eval nodeValue1616 (mixedVector B) := by
    change mixedMoment B node1616 node1616Labels = _
    exact sound1616 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3290 : mixedVector B (Sum.inr 3290) = Sparse.eval nodeValue3290 (mixedVector B) := by
    change mixedMoment B node3290 node3290Labels = _
    exact sound3290 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1638, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1597, h1598, h1601, h1616, h1724, h3290, h4069, reducedSource1399] using sourceEq1638 B hB

theorem rowSound1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1399 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1399, numericCheck1399, reducedZero1399 B hB hF, mul_zero]

theorem reducedZero1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1400 (mixedVector B) = 0 := by
  have h1210 : mixedVector B (Sum.inr 1210) = Sparse.eval nodeValue1210 (mixedVector B) := by
    change mixedMoment B node1210 node1210Labels = _
    exact sound1210 B hB hF
  have h2477 : mixedVector B (Sum.inr 2477) = Sparse.eval nodeValue2477 (mixedVector B) := by
    change mixedMoment B node2477 node2477Labels = _
    exact sound2477 B hB hF
  have h2613 : mixedVector B (Sum.inr 2613) = Sparse.eval nodeValue2613 (mixedVector B) := by
    change mixedMoment B node2613 node2613Labels = _
    exact sound2613 B hB hF
  have h2694 : mixedVector B (Sum.inr 2694) = Sparse.eval nodeValue2694 (mixedVector B) := by
    change mixedMoment B node2694 node2694Labels = _
    exact sound2694 B hB hF
  have h2708 : mixedVector B (Sum.inr 2708) = Sparse.eval nodeValue2708 (mixedVector B) := by
    change mixedMoment B node2708 node2708Labels = _
    exact sound2708 B hB hF
  have h2718 : mixedVector B (Sum.inr 2718) = Sparse.eval nodeValue2718 (mixedVector B) := by
    change mixedMoment B node2718 node2718Labels = _
    exact sound2718 B hB hF
  have h4090 : mixedVector B (Sum.inr 4090) = Sparse.eval nodeValue4090 (mixedVector B) := by
    change mixedMoment B node4090 node4090Labels = _
    exact sound4090 B hB hF
  simpa only [sourceForm1639, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1210, h2477, h2613, h2694, h2708, h2718, h4090, reducedSource1400] using sourceEq1639 B hB

theorem rowSound1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1400 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1400, numericCheck1400, reducedZero1400 B hB hF, mul_zero]

theorem reducedZero1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1401 (mixedVector B) = 0 := by
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h2383 : mixedVector B (Sum.inr 2383) = Sparse.eval nodeValue2383 (mixedVector B) := by
    change mixedMoment B node2383 node2383Labels = _
    exact sound2383 B hB hF
  have h2607 : mixedVector B (Sum.inr 2607) = Sparse.eval nodeValue2607 (mixedVector B) := by
    change mixedMoment B node2607 node2607Labels = _
    exact sound2607 B hB hF
  have h2662 : mixedVector B (Sum.inr 2662) = Sparse.eval nodeValue2662 (mixedVector B) := by
    change mixedMoment B node2662 node2662Labels = _
    exact sound2662 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1640, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1180, h2383, h2607, h2662, h2671, h4087, reducedSource1401] using sourceEq1640 B hB

theorem rowSound1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1401 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1401, numericCheck1401, reducedZero1401 B hB hF, mul_zero]

theorem reducedZero1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1402 (mixedVector B) = 0 := by
  have h1180 : mixedVector B (Sum.inr 1180) = Sparse.eval nodeValue1180 (mixedVector B) := by
    change mixedMoment B node1180 node1180Labels = _
    exact sound1180 B hB hF
  have h1187 : mixedVector B (Sum.inr 1187) = Sparse.eval nodeValue1187 (mixedVector B) := by
    change mixedMoment B node1187 node1187Labels = _
    exact sound1187 B hB hF
  have h1256 : mixedVector B (Sum.inr 1256) = Sparse.eval nodeValue1256 (mixedVector B) := by
    change mixedMoment B node1256 node1256Labels = _
    exact sound1256 B hB hF
  have h2671 : mixedVector B (Sum.inr 2671) = Sparse.eval nodeValue2671 (mixedVector B) := by
    change mixedMoment B node2671 node2671Labels = _
    exact sound2671 B hB hF
  have h4087 : mixedVector B (Sum.inr 4087) = Sparse.eval nodeValue4087 (mixedVector B) := by
    change mixedMoment B node4087 node4087Labels = _
    exact sound4087 B hB hF
  simpa only [sourceForm1641, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1180, h1187, h1256, h2671, h4087, reducedSource1402] using sourceEq1641 B hB

theorem rowSound1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1402 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1402, numericCheck1402, reducedZero1402 B hB hF, mul_zero]

theorem reducedZero1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1403 (mixedVector B) = 0 := by
  have h1178 : mixedVector B (Sum.inr 1178) = Sparse.eval nodeValue1178 (mixedVector B) := by
    change mixedMoment B node1178 node1178Labels = _
    exact sound1178 B hB hF
  have h2382 : mixedVector B (Sum.inr 2382) = Sparse.eval nodeValue2382 (mixedVector B) := by
    change mixedMoment B node2382 node2382Labels = _
    exact sound2382 B hB hF
  have h2606 : mixedVector B (Sum.inr 2606) = Sparse.eval nodeValue2606 (mixedVector B) := by
    change mixedMoment B node2606 node2606Labels = _
    exact sound2606 B hB hF
  have h2661 : mixedVector B (Sum.inr 2661) = Sparse.eval nodeValue2661 (mixedVector B) := by
    change mixedMoment B node2661 node2661Labels = _
    exact sound2661 B hB hF
  have h2669 : mixedVector B (Sum.inr 2669) = Sparse.eval nodeValue2669 (mixedVector B) := by
    change mixedMoment B node2669 node2669Labels = _
    exact sound2669 B hB hF
  have h2672 : mixedVector B (Sum.inr 2672) = Sparse.eval nodeValue2672 (mixedVector B) := by
    change mixedMoment B node2672 node2672Labels = _
    exact sound2672 B hB hF
  have h4088 : mixedVector B (Sum.inr 4088) = Sparse.eval nodeValue4088 (mixedVector B) := by
    change mixedMoment B node4088 node4088Labels = _
    exact sound4088 B hB hF
  simpa only [sourceForm1642, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1178, h2382, h2606, h2661, h2669, h2672, h4088, reducedSource1403] using sourceEq1642 B hB

theorem rowSound1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1403 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1403, numericCheck1403, reducedZero1403 B hB hF, mul_zero]

theorem reducedZero1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1404 (mixedVector B) = 0 := by
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1659 : mixedVector B (Sum.inr 1659) = Sparse.eval nodeValue1659 (mixedVector B) := by
    change mixedMoment B node1659 node1659Labels = _
    exact sound1659 B hB hF
  have h1661 : mixedVector B (Sum.inr 1661) = Sparse.eval nodeValue1661 (mixedVector B) := by
    change mixedMoment B node1661 node1661Labels = _
    exact sound1661 B hB hF
  have h1739 : mixedVector B (Sum.inr 1739) = Sparse.eval nodeValue1739 (mixedVector B) := by
    change mixedMoment B node1739 node1739Labels = _
    exact sound1739 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1643, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1656, h1659, h1661, h1739, h2737, h4069, reducedSource1404] using sourceEq1643 B hB

theorem rowSound1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1404 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1404, numericCheck1404, reducedZero1404 B hB hF, mul_zero]

theorem reducedZero1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1405 (mixedVector B) = 0 := by
  have h1650 : mixedVector B (Sum.inr 1650) = Sparse.eval nodeValue1650 (mixedVector B) := by
    change mixedMoment B node1650 node1650Labels = _
    exact sound1650 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h2521 : mixedVector B (Sum.inr 2521) = Sparse.eval nodeValue2521 (mixedVector B) := by
    change mixedMoment B node2521 node2521Labels = _
    exact sound2521 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1644, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1650, h2502, h2521, h2737, h3305, h4069, reducedSource1405] using sourceEq1644 B hB

theorem rowSound1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1405 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1405, numericCheck1405, reducedZero1405 B hB hF, mul_zero]

theorem reducedZero1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1406 (mixedVector B) = 0 := by
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1651 : mixedVector B (Sum.inr 1651) = Sparse.eval nodeValue1651 (mixedVector B) := by
    change mixedMoment B node1651 node1651Labels = _
    exact sound1651 B hB hF
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h1728 : mixedVector B (Sum.inr 1728) = Sparse.eval nodeValue1728 (mixedVector B) := by
    change mixedMoment B node1728 node1728Labels = _
    exact sound1728 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1645, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1646, h1651, h1653, h1728, h3306, h4069, reducedSource1406] using sourceEq1645 B hB

theorem rowSound1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1406 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1406, numericCheck1406, reducedZero1406 B hB hF, mul_zero]

theorem reducedZero1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1407 (mixedVector B) = 0 := by
  have h1653 : mixedVector B (Sum.inr 1653) = Sparse.eval nodeValue1653 (mixedVector B) := by
    change mixedMoment B node1653 node1653Labels = _
    exact sound1653 B hB hF
  have h3049 : mixedVector B (Sum.inr 3049) = Sparse.eval nodeValue3049 (mixedVector B) := by
    change mixedMoment B node3049 node3049Labels = _
    exact sound3049 B hB hF
  have h3287 : mixedVector B (Sum.inr 3287) = Sparse.eval nodeValue3287 (mixedVector B) := by
    change mixedMoment B node3287 node3287Labels = _
    exact sound3287 B hB hF
  have h3305 : mixedVector B (Sum.inr 3305) = Sparse.eval nodeValue3305 (mixedVector B) := by
    change mixedMoment B node3305 node3305Labels = _
    exact sound3305 B hB hF
  have h3306 : mixedVector B (Sum.inr 3306) = Sparse.eval nodeValue3306 (mixedVector B) := by
    change mixedMoment B node3306 node3306Labels = _
    exact sound3306 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1646, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1653, h3049, h3287, h3305, h3306, h4069, reducedSource1407] using sourceEq1646 B hB

theorem rowSound1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1407 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1407, numericCheck1407, reducedZero1407 B hB hF, mul_zero]

theorem sourceRowsAt1392 : MixedData.sourceRows (1392 : Fin 2425) =
    MixedData.row1392 := by decide +kernel

theorem sourceRowsAt1393 : MixedData.sourceRows (1393 : Fin 2425) =
    MixedData.row1393 := by decide +kernel

theorem sourceRowsAt1394 : MixedData.sourceRows (1394 : Fin 2425) =
    MixedData.row1394 := by decide +kernel

theorem sourceRowsAt1395 : MixedData.sourceRows (1395 : Fin 2425) =
    MixedData.row1395 := by decide +kernel

theorem sourceRowsAt1396 : MixedData.sourceRows (1396 : Fin 2425) =
    MixedData.row1396 := by decide +kernel

theorem sourceRowsAt1397 : MixedData.sourceRows (1397 : Fin 2425) =
    MixedData.row1397 := by decide +kernel

theorem sourceRowsAt1398 : MixedData.sourceRows (1398 : Fin 2425) =
    MixedData.row1398 := by decide +kernel

theorem sourceRowsAt1399 : MixedData.sourceRows (1399 : Fin 2425) =
    MixedData.row1399 := by decide +kernel

theorem sourceRowsAt1400 : MixedData.sourceRows (1400 : Fin 2425) =
    MixedData.row1400 := by decide +kernel

theorem sourceRowsAt1401 : MixedData.sourceRows (1401 : Fin 2425) =
    MixedData.row1401 := by decide +kernel

theorem sourceRowsAt1402 : MixedData.sourceRows (1402 : Fin 2425) =
    MixedData.row1402 := by decide +kernel

theorem sourceRowsAt1403 : MixedData.sourceRows (1403 : Fin 2425) =
    MixedData.row1403 := by decide +kernel

theorem sourceRowsAt1404 : MixedData.sourceRows (1404 : Fin 2425) =
    MixedData.row1404 := by decide +kernel

theorem sourceRowsAt1405 : MixedData.sourceRows (1405 : Fin 2425) =
    MixedData.row1405 := by decide +kernel

theorem sourceRowsAt1406 : MixedData.sourceRows (1406 : Fin 2425) =
    MixedData.row1406 := by decide +kernel

theorem sourceRowsAt1407 : MixedData.sourceRows (1407 : Fin 2425) =
    MixedData.row1407 := by decide +kernel

theorem chunkSound87_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 87) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1392 ∨ k.val = 1393 ∨ k.val = 1394 ∨ k.val = 1395 ∨ k.val = 1396 ∨ k.val = 1397 ∨ k.val = 1398 ∨ k.val = 1399 ∨ k.val = 1400 ∨ k.val = 1401 ∨ k.val = 1402 ∨ k.val = 1403 ∨ k.val = 1404 ∨ k.val = 1405 ∨ k.val = 1406 ∨ k.val = 1407 := by omega
  rcases heq with h1392 | h1393 | h1394 | h1395 | h1396 | h1397 | h1398 | h1399 | h1400 | h1401 | h1402 | h1403 | h1404 | h1405 | h1406 | h1407
  · have he : k = (1392 : Fin 2425) := Fin.ext h1392
    subst k
    rw [sourceRowsAt1392]
    exact rowSound1392 B hB hF
  · have he : k = (1393 : Fin 2425) := Fin.ext h1393
    subst k
    rw [sourceRowsAt1393]
    exact rowSound1393 B hB hF
  · have he : k = (1394 : Fin 2425) := Fin.ext h1394
    subst k
    rw [sourceRowsAt1394]
    exact rowSound1394 B hB hF
  · have he : k = (1395 : Fin 2425) := Fin.ext h1395
    subst k
    rw [sourceRowsAt1395]
    exact rowSound1395 B hB hF
  · have he : k = (1396 : Fin 2425) := Fin.ext h1396
    subst k
    rw [sourceRowsAt1396]
    exact rowSound1396 B hB hF
  · have he : k = (1397 : Fin 2425) := Fin.ext h1397
    subst k
    rw [sourceRowsAt1397]
    exact rowSound1397 B hB hF
  · have he : k = (1398 : Fin 2425) := Fin.ext h1398
    subst k
    rw [sourceRowsAt1398]
    exact rowSound1398 B hB hF
  · have he : k = (1399 : Fin 2425) := Fin.ext h1399
    subst k
    rw [sourceRowsAt1399]
    exact rowSound1399 B hB hF
  · have he : k = (1400 : Fin 2425) := Fin.ext h1400
    subst k
    rw [sourceRowsAt1400]
    exact rowSound1400 B hB hF
  · have he : k = (1401 : Fin 2425) := Fin.ext h1401
    subst k
    rw [sourceRowsAt1401]
    exact rowSound1401 B hB hF
  · have he : k = (1402 : Fin 2425) := Fin.ext h1402
    subst k
    rw [sourceRowsAt1402]
    exact rowSound1402 B hB hF
  · have he : k = (1403 : Fin 2425) := Fin.ext h1403
    subst k
    rw [sourceRowsAt1403]
    exact rowSound1403 B hB hF
  · have he : k = (1404 : Fin 2425) := Fin.ext h1404
    subst k
    rw [sourceRowsAt1404]
    exact rowSound1404 B hB hF
  · have he : k = (1405 : Fin 2425) := Fin.ext h1405
    subst k
    rw [sourceRowsAt1405]
    exact rowSound1405 B hB hF
  · have he : k = (1406 : Fin 2425) := Fin.ext h1406
    subst k
    rw [sourceRowsAt1406]
    exact rowSound1406 B hB hF
  · have he : k = (1407 : Fin 2425) := Fin.ext h1407
    subst k
    rw [sourceRowsAt1407]
    exact rowSound1407 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound87_e_oai
