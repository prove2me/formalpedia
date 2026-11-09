-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:37:22.920207+00:00
-- url     : https://prove2.me/submissions/a3a3b117-7928-41c9-a035-434183ef944c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E077
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E087
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E092
import Definitions.Def_OAIQ106E096
import Definitions.Def_OAIQ106E098
import Definitions.Def_OAIQ106E192
import Definitions.Def_OAIQ106E111
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13559 raw13559Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13559 raw13559Labels = mixedMoment B raw13559step0 raw13559step0Labels := by
      have hz : ∀ j, raw13559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13559step0 = (fun i j => raw13559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13559step0 raw13559; decide +kernel
      have hl : raw13559step0Labels = raw13559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13559 raw13559Labels permutation346 hz
    mixedMoment B raw13559step0 raw13559step0Labels = mixedMoment B raw13559step1 raw13559step1Labels := by
      have ha : raw13559step1 = (fun i j => raw13559step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13559step1 raw13559step0; decide +kernel
      have hl : raw13559step1Labels = raw13559step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13559step0 raw13559step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical13560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13560 raw13560Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw13560 raw13560Labels = mixedMoment B raw13560step0 raw13560step0Labels := by
      have hz : ∀ j, raw13560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13560step0 = (fun i j => raw13560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13560step0 raw13560; decide +kernel
      have hl : raw13560step0Labels = raw13560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13560 raw13560Labels permutation346 hz
    mixedMoment B raw13560step0 raw13560step0Labels = mixedMoment B raw13560step1 raw13560step1Labels := by
      have ha : raw13560step1 = (fun i j => raw13560step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13560step1 raw13560step0; decide +kernel
      have hl : raw13560step1Labels = raw13560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13560step0 raw13560step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

theorem canonical13564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13564 raw13564Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw13564 raw13564Labels = mixedMoment B raw13564step0 raw13564step0Labels := by
      have hz : ∀ j, raw13564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13564step0 = (fun i j => raw13564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13564step0 raw13564; decide +kernel
      have hl : raw13564step0Labels = raw13564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13564 raw13564Labels permutation346 hz
    _ = mixedMoment B node1270 node1270Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical128
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16433 raw16433Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw16433 raw16433Labels = mixedMoment B raw16433step0 raw16433step0Labels := by
      have hz : ∀ j, raw16433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16433step0 = (fun i j => raw16433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16433step0 raw16433; decide +kernel
      have hl : raw16433step0Labels = raw16433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16433 raw16433Labels permutation346 hz
    mixedMoment B raw16433step0 raw16433step0Labels = mixedMoment B raw16433step1 raw16433step1Labels := by
      have ha : raw16433step1 = (fun i j => raw16433step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw16433step1 raw16433step0; decide +kernel
      have hl : raw16433step1Labels = raw16433step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16433step0 raw16433step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical174
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical22395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22395 raw22395Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw22395 raw22395Labels = mixedMoment B raw22395step0 raw22395step0Labels := by
      have hz : ∀ j, raw22395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22395step0 = (fun i j => raw22395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22395step0 raw22395; decide +kernel
      have hl : raw22395step0Labels = raw22395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22395 raw22395Labels permutation346 hz
    _ = mixedMoment B node1133 node1133Labels := by rfl

theorem canonical22398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22398 raw22398Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw22398 raw22398Labels = mixedMoment B raw22398step0 raw22398step0Labels := by
      have hz : ∀ j, raw22398 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22398step0 = (fun i j => raw22398 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22398step0 raw22398; decide +kernel
      have hl : raw22398step0Labels = raw22398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398 raw22398Labels permutation520 hz
    mixedMoment B raw22398step0 raw22398step0Labels = mixedMoment B raw22398step1 raw22398step1Labels := by
      have hz : ∀ j, raw22398step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22398step1 = (fun i j => raw22398step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22398step1 raw22398step0; decide +kernel
      have hl : raw22398step1Labels = raw22398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398step0 raw22398step0Labels permutation104 hz
    mixedMoment B raw22398step1 raw22398step1Labels = mixedMoment B raw22398step2 raw22398step2Labels := by
      have hz : ∀ j, raw22398step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22398step2 = (fun i j => raw22398step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22398step2 raw22398step1; decide +kernel
      have hl : raw22398step2Labels = raw22398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398step1 raw22398step1Labels permutation20 hz
    mixedMoment B raw22398step2 raw22398step2Labels = mixedMoment B raw22398step3 raw22398step3Labels := by
      have ha : raw22398step3 = (fun i j => raw22398step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22398step3 raw22398step2; decide +kernel
      have hl : raw22398step3Labels = raw22398step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22398step2 raw22398step2Labels permutation7 permutation0
    mixedMoment B raw22398step3 raw22398step3Labels = mixedMoment B raw22398step4 raw22398step4Labels := by
      have ha : raw22398step4 = -raw22398step3 := by apply Matrix.ext; change ∀ i j, raw22398step4 i j = -(raw22398step3 i j); unfold raw22398step4 raw22398step3; decide +kernel
      have hl : raw22398step4Labels = raw22398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

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

theorem canonical23887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23887 raw23887Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw23887 raw23887Labels = mixedMoment B raw23887step0 raw23887step0Labels := by
      have ha : raw23887step0 = -raw23887 := by apply Matrix.ext; change ∀ i j, raw23887step0 i j = -(raw23887 i j); unfold raw23887step0 raw23887; decide +kernel
      have hl : raw23887step0Labels = raw23887Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3281 node3281Labels := by rfl

theorem canonical23888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23888 raw23888Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw23888 raw23888Labels = mixedMoment B raw23888step0 raw23888step0Labels := by
      have ha : raw23888step0 = (fun i j => raw23888 (permutation215 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23888step0 raw23888; decide +kernel
      have hl : raw23888step0Labels = raw23888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23888 raw23888Labels permutation215 permutation4
    mixedMoment B raw23888step0 raw23888step0Labels = mixedMoment B raw23888step1 raw23888step1Labels := by
      have ha : raw23888step1 = -raw23888step0 := by apply Matrix.ext; change ∀ i j, raw23888step1 i j = -(raw23888step0 i j); unfold raw23888step1 raw23888step0; decide +kernel
      have hl : raw23888step1Labels = raw23888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node784 node784Labels := by rfl

theorem canonical23889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23889 raw23889Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw23889 raw23889Labels = mixedMoment B raw23889step0 raw23889step0Labels := by
      have ha : raw23889step0 = (fun i j => raw23889 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23889step0 raw23889; decide +kernel
      have hl : raw23889step0Labels = raw23889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23889 raw23889Labels permutation213 permutation4
    mixedMoment B raw23889step0 raw23889step0Labels = mixedMoment B raw23889step1 raw23889step1Labels := by
      have ha : raw23889step1 = -raw23889step0 := by apply Matrix.ext; change ∀ i j, raw23889step1 i j = -(raw23889step0 i j); unfold raw23889step1 raw23889step0; decide +kernel
      have hl : raw23889step1Labels = raw23889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node784 node784Labels := by rfl

theorem canonical23890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23890 raw23890Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw23890 raw23890Labels = mixedMoment B raw23890step0 raw23890step0Labels := by
      have ha : raw23890step0 = (fun i j => raw23890 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23890step0 raw23890; decide +kernel
      have hl : raw23890step0Labels = raw23890Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23890 raw23890Labels permutation224 permutation4
    mixedMoment B raw23890step0 raw23890step0Labels = mixedMoment B raw23890step1 raw23890step1Labels := by
      have ha : raw23890step1 = -raw23890step0 := by apply Matrix.ext; change ∀ i j, raw23890step1 i j = -(raw23890step0 i j); unfold raw23890step1 raw23890step0; decide +kernel
      have hl : raw23890step1Labels = raw23890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical23891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23891 raw23891Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw23891 raw23891Labels = mixedMoment B raw23891step0 raw23891step0Labels := by
      have ha : raw23891step0 = (fun i j => raw23891 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23891step0 raw23891; decide +kernel
      have hl : raw23891step0Labels = raw23891Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23891 raw23891Labels permutation200 permutation4
    mixedMoment B raw23891step0 raw23891step0Labels = mixedMoment B raw23891step1 raw23891step1Labels := by
      have ha : raw23891step1 = -raw23891step0 := by apply Matrix.ext; change ∀ i j, raw23891step1 i j = -(raw23891step0 i j); unfold raw23891step1 raw23891step0; decide +kernel
      have hl : raw23891step1Labels = raw23891step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node803 node803Labels := by rfl

theorem canonical23892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23892 raw23892Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw23892 raw23892Labels = mixedMoment B raw23892step0 raw23892step0Labels := by
      have ha : raw23892step0 = (fun i j => raw23892 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23892step0 raw23892; decide +kernel
      have hl : raw23892step0Labels = raw23892Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23892 raw23892Labels permutation212 permutation4
    mixedMoment B raw23892step0 raw23892step0Labels = mixedMoment B raw23892step1 raw23892step1Labels := by
      have ha : raw23892step1 = -raw23892step0 := by apply Matrix.ext; change ∀ i j, raw23892step1 i j = -(raw23892step0 i j); unfold raw23892step1 raw23892step0; decide +kernel
      have hl : raw23892step1Labels = raw23892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node782 node782Labels := by rfl

theorem canonical23893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23893 raw23893Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw23893 raw23893Labels = mixedMoment B raw23893step0 raw23893step0Labels := by
      have hz : ∀ j, raw23893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23893step0 = (fun i j => raw23893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23893step0 raw23893; decide +kernel
      have hl : raw23893step0Labels = raw23893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23893 raw23893Labels permutation346 hz
    mixedMoment B raw23893step0 raw23893step0Labels = mixedMoment B raw23893step1 raw23893step1Labels := by
      have ha : raw23893step1 = (fun i j => raw23893step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23893step1 raw23893step0; decide +kernel
      have hl : raw23893step1Labels = raw23893step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23893step0 raw23893step0Labels permutation44 permutation4
    mixedMoment B raw23893step1 raw23893step1Labels = mixedMoment B raw23893step2 raw23893step2Labels := by
      have ha : raw23893step2 = -raw23893step1 := by apply Matrix.ext; change ∀ i j, raw23893step2 i j = -(raw23893step1 i j); unfold raw23893step2 raw23893step1; decide +kernel
      have hl : raw23893step2Labels = raw23893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1724 node1724Labels := by rfl

theorem canonical23894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23894 raw23894Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw23894 raw23894Labels = mixedMoment B raw23894step0 raw23894step0Labels := by
      have ha : raw23894step0 = (fun i j => raw23894 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23894step0 raw23894; decide +kernel
      have hl : raw23894step0Labels = raw23894Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23894 raw23894Labels permutation224 permutation4
    mixedMoment B raw23894step0 raw23894step0Labels = mixedMoment B raw23894step1 raw23894step1Labels := by
      have ha : raw23894step1 = -raw23894step0 := by apply Matrix.ext; change ∀ i j, raw23894step1 i j = -(raw23894step0 i j); unfold raw23894step1 raw23894step0; decide +kernel
      have hl : raw23894step1Labels = raw23894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1642 node1642Labels := by rfl

theorem canonical23895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23895 raw23895Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw23895 raw23895Labels = mixedMoment B raw23895step0 raw23895step0Labels := by
      have ha : raw23895step0 = (fun i j => raw23895 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23895step0 raw23895; decide +kernel
      have hl : raw23895step0Labels = raw23895Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23895 raw23895Labels permutation240 permutation4
    mixedMoment B raw23895step0 raw23895step0Labels = mixedMoment B raw23895step1 raw23895step1Labels := by
      have ha : raw23895step1 = -raw23895step0 := by apply Matrix.ext; change ∀ i j, raw23895step1 i j = -(raw23895step0 i j); unfold raw23895step1 raw23895step0; decide +kernel
      have hl : raw23895step1Labels = raw23895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical23896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23896 raw23896Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw23896 raw23896Labels = mixedMoment B raw23896step0 raw23896step0Labels := by
      have hz : ∀ j, raw23896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23896step0 = (fun i j => raw23896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23896step0 raw23896; decide +kernel
      have hl : raw23896step0Labels = raw23896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23896 raw23896Labels permutation346 hz
    mixedMoment B raw23896step0 raw23896step0Labels = mixedMoment B raw23896step1 raw23896step1Labels := by
      have ha : raw23896step1 = (fun i j => raw23896step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23896step1 raw23896step0; decide +kernel
      have hl : raw23896step1Labels = raw23896step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23896step0 raw23896step0Labels permutation40 permutation4
    mixedMoment B raw23896step1 raw23896step1Labels = mixedMoment B raw23896step2 raw23896step2Labels := by
      have ha : raw23896step2 = -raw23896step1 := by apply Matrix.ext; change ∀ i j, raw23896step2 i j = -(raw23896step1 i j); unfold raw23896step2 raw23896step1; decide +kernel
      have hl : raw23896step2Labels = raw23896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1707 node1707Labels := by rfl

theorem canonical23897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23897 raw23897Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw23897 raw23897Labels = mixedMoment B raw23897step0 raw23897step0Labels := by
      have ha : raw23897step0 = (fun i j => raw23897 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23897step0 raw23897; decide +kernel
      have hl : raw23897step0Labels = raw23897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23897 raw23897Labels permutation212 permutation4
    mixedMoment B raw23897step0 raw23897step0Labels = mixedMoment B raw23897step1 raw23897step1Labels := by
      have ha : raw23897step1 = -raw23897step0 := by apply Matrix.ext; change ∀ i j, raw23897step1 i j = -(raw23897step0 i j); unfold raw23897step1 raw23897step0; decide +kernel
      have hl : raw23897step1Labels = raw23897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1635 node1635Labels := by rfl

theorem canonical23898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23898 raw23898Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw23898 raw23898Labels = mixedMoment B raw23898step0 raw23898step0Labels := by
      have ha : raw23898step0 = (fun i j => raw23898 (permutation234 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23898step0 raw23898; decide +kernel
      have hl : raw23898step0Labels = raw23898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23898 raw23898Labels permutation234 permutation4
    mixedMoment B raw23898step0 raw23898step0Labels = mixedMoment B raw23898step1 raw23898step1Labels := by
      have ha : raw23898step1 = -raw23898step0 := by apply Matrix.ext; change ∀ i j, raw23898step1 i j = -(raw23898step0 i j); unfold raw23898step1 raw23898step0; decide +kernel
      have hl : raw23898step1Labels = raw23898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1635 node1635Labels := by rfl

theorem canonical23900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23900 raw23900Labels = mixedMoment B node580 node580Labels := by
  calc
    mixedMoment B raw23900 raw23900Labels = mixedMoment B raw23900step0 raw23900step0Labels := by
      have ha : raw23900step0 = (fun i j => raw23900 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23900step0 raw23900; decide +kernel
      have hl : raw23900step0Labels = raw23900Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23900 raw23900Labels permutation182 permutation2
    _ = mixedMoment B node580 node580Labels := by rfl

theorem canonical23901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23901 raw23901Labels = mixedMoment B node1021 node1021Labels := by
  calc
    _ = mixedMoment B node1021 node1021Labels := by rfl

theorem canonical23902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23902 raw23902Labels = mixedMoment B node944 node944Labels := by
  calc
    mixedMoment B raw23902 raw23902Labels = mixedMoment B raw23902step0 raw23902step0Labels := by
      have ha : raw23902step0 = (fun i j => raw23902 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23902step0 raw23902; decide +kernel
      have hl : raw23902step0Labels = raw23902Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23902 raw23902Labels permutation182 permutation2
    _ = mixedMoment B node944 node944Labels := by rfl

theorem canonical23903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23903 raw23903Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw23903 raw23903Labels = mixedMoment B raw23903step0 raw23903step0Labels := by
      have ha : raw23903step0 = (fun i j => raw23903 (permutation190 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23903step0 raw23903; decide +kernel
      have hl : raw23903step0Labels = raw23903Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23903 raw23903Labels permutation190 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

theorem canonical23904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23904 raw23904Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw23904 raw23904Labels = mixedMoment B raw23904step0 raw23904step0Labels := by
      have ha : raw23904step0 = (fun i j => raw23904 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23904step0 raw23904; decide +kernel
      have hl : raw23904step0Labels = raw23904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23904 raw23904Labels permutation186 permutation2
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical23905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23905 raw23905Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw23905 raw23905Labels = mixedMoment B raw23905step0 raw23905step0Labels := by
      have ha : raw23905step0 = (fun i j => raw23905 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23905step0 raw23905; decide +kernel
      have hl : raw23905step0Labels = raw23905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23905 raw23905Labels permutation154 permutation2
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical23906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23906 raw23906Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw23906 raw23906Labels = mixedMoment B raw23906step0 raw23906step0Labels := by
      have ha : raw23906step0 = (fun i j => raw23906 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23906step0 raw23906; decide +kernel
      have hl : raw23906step0Labels = raw23906Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23906 raw23906Labels permutation154 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

theorem canonical23907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23907 raw23907Labels = mixedMoment B node1335 node1335Labels := by
  calc
    mixedMoment B raw23907 raw23907Labels = mixedMoment B raw23907step0 raw23907step0Labels := by
      have ha : raw23907step0 = (fun i j => raw23907 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23907step0 raw23907; decide +kernel
      have hl : raw23907step0Labels = raw23907Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23907 raw23907Labels permutation154 permutation2
    _ = mixedMoment B node1335 node1335Labels := by rfl

theorem canonical23908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23908 raw23908Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw23908 raw23908Labels = mixedMoment B raw23908step0 raw23908step0Labels := by
      have ha : raw23908step0 = (fun i j => raw23908 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23908step0 raw23908; decide +kernel
      have hl : raw23908step0Labels = raw23908Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23908 raw23908Labels permutation154 permutation2
    _ = mixedMoment B node1328 node1328Labels := by rfl

theorem canonical23909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23909 raw23909Labels = mixedMoment B node1330 node1330Labels := by
  calc
    _ = mixedMoment B node1330 node1330Labels := by rfl

theorem canonical23910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23910 raw23910Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw23910 raw23910Labels = mixedMoment B raw23910step0 raw23910step0Labels := by
      have ha : raw23910step0 = (fun i j => raw23910 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23910step0 raw23910; decide +kernel
      have hl : raw23910step0Labels = raw23910Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23910 raw23910Labels permutation154 permutation2
    _ = mixedMoment B node1327 node1327Labels := by rfl

theorem canonical23911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23911 raw23911Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw23911 raw23911Labels = mixedMoment B raw23911step0 raw23911step0Labels := by
      have hz : ∀ j, raw23911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw23911step0 = (fun i j => raw23911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw23911step0 raw23911; decide +kernel
      have hl : raw23911step0Labels = raw23911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23911 raw23911Labels permutation520 hz
    mixedMoment B raw23911step0 raw23911step0Labels = mixedMoment B raw23911step1 raw23911step1Labels := by
      have ha : raw23911step1 = (fun i j => raw23911step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw23911step1 raw23911step0; decide +kernel
      have hl : raw23911step1Labels = raw23911step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23911step0 raw23911step0Labels permutation146 permutation0
    mixedMoment B raw23911step1 raw23911step1Labels = mixedMoment B raw23911step2 raw23911step2Labels := by
      have ha : raw23911step2 = -raw23911step1 := by apply Matrix.ext; change ∀ i j, raw23911step2 i j = -(raw23911step1 i j); unfold raw23911step2 raw23911step1; decide +kernel
      have hl : raw23911step2Labels = raw23911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

theorem canonical23912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23912 raw23912Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw23912 raw23912Labels = mixedMoment B raw23912step0 raw23912step0Labels := by
      have hz : ∀ j, raw23912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23912step0 = (fun i j => raw23912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23912step0 raw23912; decide +kernel
      have hl : raw23912step0Labels = raw23912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23912 raw23912Labels permutation346 hz
    mixedMoment B raw23912step0 raw23912step0Labels = mixedMoment B raw23912step1 raw23912step1Labels := by
      have ha : raw23912step1 = (fun i j => raw23912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23912step1 raw23912step0; decide +kernel
      have hl : raw23912step1Labels = raw23912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23912step0 raw23912step0Labels permutation34 permutation2
    mixedMoment B raw23912step1 raw23912step1Labels = mixedMoment B raw23912step2 raw23912step2Labels := by
      have ha : raw23912step2 = -raw23912step1 := by apply Matrix.ext; change ∀ i j, raw23912step2 i j = -(raw23912step1 i j); unfold raw23912step2 raw23912step1; decide +kernel
      have hl : raw23912step2Labels = raw23912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3293 node3293Labels := by rfl

theorem canonical23913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23913 raw23913Labels = mixedMoment B node3278 node3278Labels := by
  calc
    mixedMoment B raw23913 raw23913Labels = mixedMoment B raw23913step0 raw23913step0Labels := by
      have ha : raw23913step0 = (fun i j => raw23913 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23913step0 raw23913; decide +kernel
      have hl : raw23913step0Labels = raw23913Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23913 raw23913Labels permutation154 permutation2
    mixedMoment B raw23913step0 raw23913step0Labels = mixedMoment B raw23913step1 raw23913step1Labels := by
      have ha : raw23913step1 = -raw23913step0 := by apply Matrix.ext; change ∀ i j, raw23913step1 i j = -(raw23913step0 i j); unfold raw23913step1 raw23913step0; decide +kernel
      have hl : raw23913step1Labels = raw23913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3278 node3278Labels := by rfl

theorem canonical23914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23914 raw23914Labels = mixedMoment B node2457 node2457Labels := by
  calc
    mixedMoment B raw23914 raw23914Labels = mixedMoment B raw23914step0 raw23914step0Labels := by
      have ha : raw23914step0 = (fun i j => raw23914 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23914step0 raw23914; decide +kernel
      have hl : raw23914step0Labels = raw23914Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23914 raw23914Labels permutation662 permutation2
    _ = mixedMoment B node2457 node2457Labels := by rfl

theorem canonical23917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23917 raw23917Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw23917 raw23917Labels = mixedMoment B raw23917step0 raw23917step0Labels := by
      have ha : raw23917step0 = (fun i j => raw23917 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23917step0 raw23917; decide +kernel
      have hl : raw23917step0Labels = raw23917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23917 raw23917Labels permutation246 permutation4
    mixedMoment B raw23917step0 raw23917step0Labels = mixedMoment B raw23917step1 raw23917step1Labels := by
      have ha : raw23917step1 = -raw23917step0 := by apply Matrix.ext; change ∀ i j, raw23917step1 i j = -(raw23917step0 i j); unfold raw23917step1 raw23917step0; decide +kernel
      have hl : raw23917step1Labels = raw23917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node822 node822Labels := by rfl

theorem canonical23919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23919 raw23919Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw23919 raw23919Labels = mixedMoment B raw23919step0 raw23919step0Labels := by
      have hz : ∀ j, raw23919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23919step0 = (fun i j => raw23919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23919step0 raw23919; decide +kernel
      have hl : raw23919step0Labels = raw23919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23919 raw23919Labels permutation346 hz
    mixedMoment B raw23919step0 raw23919step0Labels = mixedMoment B raw23919step1 raw23919step1Labels := by
      have ha : raw23919step1 = (fun i j => raw23919step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23919step1 raw23919step0; decide +kernel
      have hl : raw23919step1Labels = raw23919step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23919step0 raw23919step0Labels permutation50 permutation4
    mixedMoment B raw23919step1 raw23919step1Labels = mixedMoment B raw23919step2 raw23919step2Labels := by
      have ha : raw23919step2 = -raw23919step1 := by apply Matrix.ext; change ∀ i j, raw23919step2 i j = -(raw23919step1 i j); unfold raw23919step2 raw23919step1; decide +kernel
      have hl : raw23919step2Labels = raw23919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1737 node1737Labels := by rfl

theorem canonical23920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23920 raw23920Labels = mixedMoment B node1654 node1654Labels := by
  calc
    mixedMoment B raw23920 raw23920Labels = mixedMoment B raw23920step0 raw23920step0Labels := by
      have ha : raw23920step0 = (fun i j => raw23920 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23920step0 raw23920; decide +kernel
      have hl : raw23920step0Labels = raw23920Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23920 raw23920Labels permutation246 permutation4
    mixedMoment B raw23920step0 raw23920step0Labels = mixedMoment B raw23920step1 raw23920step1Labels := by
      have ha : raw23920step1 = -raw23920step0 := by apply Matrix.ext; change ∀ i j, raw23920step1 i j = -(raw23920step0 i j); unfold raw23920step1 raw23920step0; decide +kernel
      have hl : raw23920step1Labels = raw23920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1654 node1654Labels := by rfl

theorem canonical23928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23928 raw23928Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw23928 raw23928Labels = mixedMoment B raw23928step0 raw23928step0Labels := by
      have hz : ∀ j, raw23928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23928step0 = (fun i j => raw23928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23928step0 raw23928; decide +kernel
      have hl : raw23928step0Labels = raw23928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23928 raw23928Labels permutation346 hz
    _ = mixedMoment B node2509 node2509Labels := by rfl

theorem canonical23929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23929 raw23929Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw23929 raw23929Labels = mixedMoment B raw23929step0 raw23929step0Labels := by
      have hz : ∀ j, raw23929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23929step0 = (fun i j => raw23929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23929step0 raw23929; decide +kernel
      have hl : raw23929step0Labels = raw23929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23929 raw23929Labels permutation346 hz
    _ = mixedMoment B node1234 node1234Labels := by rfl

theorem canonical23930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23930 raw23930Labels = mixedMoment B node1125 node1125Labels := by
  calc
    _ = mixedMoment B node1125 node1125Labels := by rfl

theorem canonical23931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23931 raw23931Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw23931 raw23931Labels = mixedMoment B raw23931step0 raw23931step0Labels := by
      have hz : ∀ j, raw23931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23931step0 = (fun i j => raw23931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23931step0 raw23931; decide +kernel
      have hl : raw23931step0Labels = raw23931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23931 raw23931Labels permutation346 hz
    mixedMoment B raw23931step0 raw23931step0Labels = mixedMoment B raw23931step1 raw23931step1Labels := by
      have ha : raw23931step1 = (fun i j => raw23931step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23931step1 raw23931step0; decide +kernel
      have hl : raw23931step1Labels = raw23931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23931step0 raw23931step0Labels permutation34 permutation2
    _ = mixedMoment B node1133 node1133Labels := by rfl

theorem canonical23932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23932 raw23932Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw23932 raw23932Labels = mixedMoment B raw23932step0 raw23932step0Labels := by
      have hz : ∀ j, raw23932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23932step0 = (fun i j => raw23932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23932step0 raw23932; decide +kernel
      have hl : raw23932step0Labels = raw23932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23932 raw23932Labels permutation346 hz
    _ = mixedMoment B node1128 node1128Labels := by rfl

theorem canonical23933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23933 raw23933Labels = mixedMoment B node651 node651Labels := by
  calc
    mixedMoment B raw23933 raw23933Labels = mixedMoment B raw23933step0 raw23933step0Labels := by
      have hz : ∀ j, raw23933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23933step0 = (fun i j => raw23933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23933step0 raw23933; decide +kernel
      have hl : raw23933step0Labels = raw23933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23933 raw23933Labels permutation346 hz
    _ = mixedMoment B node651 node651Labels := by rfl

theorem canonical23934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23934 raw23934Labels = mixedMoment B node1169 node1169Labels := by
  calc
    mixedMoment B raw23934 raw23934Labels = mixedMoment B raw23934step0 raw23934step0Labels := by
      have ha : raw23934step0 = (fun i j => raw23934 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23934step0 raw23934; decide +kernel
      have hl : raw23934step0Labels = raw23934Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23934 raw23934Labels permutation176 permutation2
    _ = mixedMoment B node1169 node1169Labels := by rfl

theorem canonical23935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23935 raw23935Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw23935 raw23935Labels = mixedMoment B raw23935step0 raw23935step0Labels := by
      have hz : ∀ j, raw23935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23935step0 = (fun i j => raw23935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23935step0 raw23935; decide +kernel
      have hl : raw23935step0Labels = raw23935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23935 raw23935Labels permutation346 hz
    mixedMoment B raw23935step0 raw23935step0Labels = mixedMoment B raw23935step1 raw23935step1Labels := by
      have ha : raw23935step1 = (fun i j => raw23935step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23935step1 raw23935step0; decide +kernel
      have hl : raw23935step1Labels = raw23935step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23935step0 raw23935step0Labels permutation38 permutation2
    _ = mixedMoment B node1270 node1270Labels := by rfl

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

theorem canonical23936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23936 raw23936Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw23936 raw23936Labels = mixedMoment B raw23936step0 raw23936step0Labels := by
      have hz : ∀ j, raw23936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23936step0 = (fun i j => raw23936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23936step0 raw23936; decide +kernel
      have hl : raw23936step0Labels = raw23936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23936 raw23936Labels permutation346 hz
    mixedMoment B raw23936step0 raw23936step0Labels = mixedMoment B raw23936step1 raw23936step1Labels := by
      have ha : raw23936step1 = (fun i j => raw23936step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23936step1 raw23936step0; decide +kernel
      have hl : raw23936step1Labels = raw23936step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23936step0 raw23936step0Labels permutation44 permutation2
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical23937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23937 raw23937Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw23937 raw23937Labels = mixedMoment B raw23937step0 raw23937step0Labels := by
      have hz : ∀ j, raw23937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23937step0 = (fun i j => raw23937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23937step0 raw23937; decide +kernel
      have hl : raw23937step0Labels = raw23937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23937 raw23937Labels permutation346 hz
    mixedMoment B raw23937step0 raw23937step0Labels = mixedMoment B raw23937step1 raw23937step1Labels := by
      have ha : raw23937step1 = (fun i j => raw23937step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23937step1 raw23937step0; decide +kernel
      have hl : raw23937step1Labels = raw23937step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23937step0 raw23937step0Labels permutation145 permutation4
    _ = mixedMoment B node2702 node2702Labels := by rfl

theorem canonical23938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23938 raw23938Labels = mixedMoment B node1658 node1658Labels := by
  calc
    mixedMoment B raw23938 raw23938Labels = mixedMoment B raw23938step0 raw23938step0Labels := by
      have hz : ∀ j, raw23938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23938step0 = (fun i j => raw23938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23938step0 raw23938; decide +kernel
      have hl : raw23938step0Labels = raw23938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23938 raw23938Labels permutation346 hz
    mixedMoment B raw23938step0 raw23938step0Labels = mixedMoment B raw23938step1 raw23938step1Labels := by
      have ha : raw23938step1 = (fun i j => raw23938step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23938step1 raw23938step0; decide +kernel
      have hl : raw23938step1Labels = raw23938step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23938step0 raw23938step0Labels permutation53 permutation2
    mixedMoment B raw23938step1 raw23938step1Labels = mixedMoment B raw23938step2 raw23938step2Labels := by
      have ha : raw23938step2 = -raw23938step1 := by apply Matrix.ext; change ∀ i j, raw23938step2 i j = -(raw23938step1 i j); unfold raw23938step2 raw23938step1; decide +kernel
      have hl : raw23938step2Labels = raw23938step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1658 node1658Labels := by rfl

theorem canonical23939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23939 raw23939Labels = mixedMoment B node1654 node1654Labels := by
  calc
    mixedMoment B raw23939 raw23939Labels = mixedMoment B raw23939step0 raw23939step0Labels := by
      have ha : raw23939step0 = (fun i j => raw23939 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23939step0 raw23939; decide +kernel
      have hl : raw23939step0Labels = raw23939Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23939 raw23939Labels permutation246 permutation2
    mixedMoment B raw23939step0 raw23939step0Labels = mixedMoment B raw23939step1 raw23939step1Labels := by
      have ha : raw23939step1 = -raw23939step0 := by apply Matrix.ext; change ∀ i j, raw23939step1 i j = -(raw23939step0 i j); unfold raw23939step1 raw23939step0; decide +kernel
      have hl : raw23939step1Labels = raw23939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1654 node1654Labels := by rfl

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

theorem canonical23941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23941 raw23941Labels = mixedMoment B node1656 node1656Labels := by
  calc
    mixedMoment B raw23941 raw23941Labels = mixedMoment B raw23941step0 raw23941step0Labels := by
      have hz : ∀ j, raw23941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23941step0 = (fun i j => raw23941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23941step0 raw23941; decide +kernel
      have hl : raw23941step0Labels = raw23941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23941 raw23941Labels permutation346 hz
    mixedMoment B raw23941step0 raw23941step0Labels = mixedMoment B raw23941step1 raw23941step1Labels := by
      have ha : raw23941step1 = (fun i j => raw23941step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23941step1 raw23941step0; decide +kernel
      have hl : raw23941step1Labels = raw23941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23941step0 raw23941step0Labels permutation50 permutation2
    mixedMoment B raw23941step1 raw23941step1Labels = mixedMoment B raw23941step2 raw23941step2Labels := by
      have ha : raw23941step2 = -raw23941step1 := by apply Matrix.ext; change ∀ i j, raw23941step2 i j = -(raw23941step1 i j); unfold raw23941step2 raw23941step1; decide +kernel
      have hl : raw23941step2Labels = raw23941step1Labels := by decide +kernel
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

theorem canonical23943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23943 raw23943Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw23943 raw23943Labels = mixedMoment B raw23943step0 raw23943step0Labels := by
      have hz : ∀ j, raw23943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23943step0 = (fun i j => raw23943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23943step0 raw23943; decide +kernel
      have hl : raw23943step0Labels = raw23943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23943 raw23943Labels permutation346 hz
    mixedMoment B raw23943step0 raw23943step0Labels = mixedMoment B raw23943step1 raw23943step1Labels := by
      have hz : ∀ j, raw23943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23943step1 = (fun i j => raw23943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23943step1 raw23943step0; decide +kernel
      have hl : raw23943step1Labels = raw23943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23943step0 raw23943step0Labels permutation56 hz
    mixedMoment B raw23943step1 raw23943step1Labels = mixedMoment B raw23943step2 raw23943step2Labels := by
      have ha : raw23943step2 = (fun i j => raw23943step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23943step2 raw23943step1; decide +kernel
      have hl : raw23943step2Labels = raw23943step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23943step1 raw23943step1Labels permutation8 permutation4
    mixedMoment B raw23943step2 raw23943step2Labels = mixedMoment B raw23943step3 raw23943step3Labels := by
      have ha : raw23943step3 = -raw23943step2 := by apply Matrix.ext; change ∀ i j, raw23943step3 i j = -(raw23943step2 i j); unfold raw23943step3 raw23943step2; decide +kernel
      have hl : raw23943step3Labels = raw23943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

theorem canonical23944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23944 raw23944Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw23944 raw23944Labels = mixedMoment B raw23944step0 raw23944step0Labels := by
      have hz : ∀ j, raw23944 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw23944step0 = (fun i j => raw23944 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw23944step0 raw23944; decide +kernel
      have hl : raw23944step0Labels = raw23944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23944 raw23944Labels permutation265 hz
    mixedMoment B raw23944step0 raw23944step0Labels = mixedMoment B raw23944step1 raw23944step1Labels := by
      have ha : raw23944step1 = (fun i j => raw23944step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23944step1 raw23944step0; decide +kernel
      have hl : raw23944step1Labels = raw23944step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23944step0 raw23944step0Labels permutation145 permutation4
    _ = mixedMoment B node2702 node2702Labels := by rfl

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

theorem canonical23946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23946 raw23946Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw23946 raw23946Labels = mixedMoment B raw23946step0 raw23946step0Labels := by
      have hz : ∀ j, raw23946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23946step0 = (fun i j => raw23946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23946step0 raw23946; decide +kernel
      have hl : raw23946step0Labels = raw23946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23946 raw23946Labels permutation346 hz
    mixedMoment B raw23946step0 raw23946step0Labels = mixedMoment B raw23946step1 raw23946step1Labels := by
      have hz : ∀ j, raw23946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23946step1 = (fun i j => raw23946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23946step1 raw23946step0; decide +kernel
      have hl : raw23946step1Labels = raw23946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23946step0 raw23946step0Labels permutation56 hz
    mixedMoment B raw23946step1 raw23946step1Labels = mixedMoment B raw23946step2 raw23946step2Labels := by
      have ha : raw23946step2 = (fun i j => raw23946step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23946step2 raw23946step1; decide +kernel
      have hl : raw23946step2Labels = raw23946step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23946step1 raw23946step1Labels permutation29 permutation4
    _ = mixedMoment B node2737 node2737Labels := by rfl

theorem canonical23947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23947 raw23947Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw23947 raw23947Labels = mixedMoment B raw23947step0 raw23947step0Labels := by
      have hz : ∀ j, raw23947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23947step0 = (fun i j => raw23947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23947step0 raw23947; decide +kernel
      have hl : raw23947step0Labels = raw23947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23947 raw23947Labels permutation346 hz
    mixedMoment B raw23947step0 raw23947step0Labels = mixedMoment B raw23947step1 raw23947step1Labels := by
      have hz : ∀ j, raw23947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23947step1 = (fun i j => raw23947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23947step1 raw23947step0; decide +kernel
      have hl : raw23947step1Labels = raw23947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23947step0 raw23947step0Labels permutation56 hz
    mixedMoment B raw23947step1 raw23947step1Labels = mixedMoment B raw23947step2 raw23947step2Labels := by
      have ha : raw23947step2 = (fun i j => raw23947step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23947step2 raw23947step1; decide +kernel
      have hl : raw23947step2Labels = raw23947step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23947step1 raw23947step1Labels permutation8 permutation4
    mixedMoment B raw23947step2 raw23947step2Labels = mixedMoment B raw23947step3 raw23947step3Labels := by
      have ha : raw23947step3 = -raw23947step2 := by apply Matrix.ext; change ∀ i j, raw23947step3 i j = -(raw23947step2 i j); unfold raw23947step3 raw23947step2; decide +kernel
      have hl : raw23947step3Labels = raw23947step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3308 node3308Labels := by rfl

theorem canonical23948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23948 raw23948Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw23948 raw23948Labels = mixedMoment B raw23948step0 raw23948step0Labels := by
      have hz : ∀ j, raw23948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23948step0 = (fun i j => raw23948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23948step0 raw23948; decide +kernel
      have hl : raw23948step0Labels = raw23948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23948 raw23948Labels permutation346 hz
    mixedMoment B raw23948step0 raw23948step0Labels = mixedMoment B raw23948step1 raw23948step1Labels := by
      have ha : raw23948step1 = (fun i j => raw23948step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23948step1 raw23948step0; decide +kernel
      have hl : raw23948step1Labels = raw23948step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23948step0 raw23948step0Labels permutation34 permutation4
    mixedMoment B raw23948step1 raw23948step1Labels = mixedMoment B raw23948step2 raw23948step2Labels := by
      have ha : raw23948step2 = -raw23948step1 := by apply Matrix.ext; change ∀ i j, raw23948step2 i j = -(raw23948step1 i j); unfold raw23948step2 raw23948step1; decide +kernel
      have hl : raw23948step2Labels = raw23948step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

theorem canonical23949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23949 raw23949Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw23949 raw23949Labels = mixedMoment B raw23949step0 raw23949step0Labels := by
      have hz : ∀ j, raw23949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23949step0 = (fun i j => raw23949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23949step0 raw23949; decide +kernel
      have hl : raw23949step0Labels = raw23949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23949 raw23949Labels permutation346 hz
    mixedMoment B raw23949step0 raw23949step0Labels = mixedMoment B raw23949step1 raw23949step1Labels := by
      have ha : raw23949step1 = (fun i j => raw23949step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23949step1 raw23949step0; decide +kernel
      have hl : raw23949step1Labels = raw23949step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23949step0 raw23949step0Labels permutation145 permutation4
    _ = mixedMoment B node2466 node2466Labels := by rfl

theorem canonical23950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23950 raw23950Labels = mixedMoment B node2457 node2457Labels := by
  calc
    mixedMoment B raw23950 raw23950Labels = mixedMoment B raw23950step0 raw23950step0Labels := by
      have ha : raw23950step0 = (fun i j => raw23950 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23950step0 raw23950; decide +kernel
      have hl : raw23950step0Labels = raw23950Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23950 raw23950Labels permutation662 permutation4
    _ = mixedMoment B node2457 node2457Labels := by rfl

theorem canonical23951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23951 raw23951Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw23951 raw23951Labels = mixedMoment B raw23951step0 raw23951step0Labels := by
      have hz : ∀ j, raw23951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23951step0 = (fun i j => raw23951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23951step0 raw23951; decide +kernel
      have hl : raw23951step0Labels = raw23951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23951 raw23951Labels permutation346 hz
    mixedMoment B raw23951step0 raw23951step0Labels = mixedMoment B raw23951step1 raw23951step1Labels := by
      have ha : raw23951step1 = (fun i j => raw23951step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23951step1 raw23951step0; decide +kernel
      have hl : raw23951step1Labels = raw23951step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23951step0 raw23951step0Labels permutation145 permutation4
    _ = mixedMoment B node2502 node2502Labels := by rfl

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

theorem canonical23955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23955 raw23955Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw23955 raw23955Labels = mixedMoment B raw23955step0 raw23955step0Labels := by
      have hz : ∀ j, raw23955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23955step0 = (fun i j => raw23955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23955step0 raw23955; decide +kernel
      have hl : raw23955step0Labels = raw23955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23955 raw23955Labels permutation346 hz
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical23956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23956 raw23956Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw23956 raw23956Labels = mixedMoment B raw23956step0 raw23956step0Labels := by
      have hz : ∀ j, raw23956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23956step0 = (fun i j => raw23956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23956step0 raw23956; decide +kernel
      have hl : raw23956step0Labels = raw23956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23956 raw23956Labels permutation346 hz
    _ = mixedMoment B node1237 node1237Labels := by rfl

theorem canonical23957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23957 raw23957Labels = mixedMoment B node1127 node1127Labels := by
  calc
    _ = mixedMoment B node1127 node1127Labels := by rfl

theorem canonical23958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23958 raw23958Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw23958 raw23958Labels = mixedMoment B raw23958step0 raw23958step0Labels := by
      have hz : ∀ j, raw23958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23958step0 = (fun i j => raw23958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23958step0 raw23958; decide +kernel
      have hl : raw23958step0Labels = raw23958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23958 raw23958Labels permutation346 hz
    mixedMoment B raw23958step0 raw23958step0Labels = mixedMoment B raw23958step1 raw23958step1Labels := by
      have ha : raw23958step1 = (fun i j => raw23958step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23958step1 raw23958step0; decide +kernel
      have hl : raw23958step1Labels = raw23958step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23958step0 raw23958step0Labels permutation34 permutation2
    _ = mixedMoment B node1141 node1141Labels := by rfl

theorem canonical23959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23959 raw23959Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw23959 raw23959Labels = mixedMoment B raw23959step0 raw23959step0Labels := by
      have hz : ∀ j, raw23959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23959step0 = (fun i j => raw23959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23959step0 raw23959; decide +kernel
      have hl : raw23959step0Labels = raw23959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23959 raw23959Labels permutation346 hz
    mixedMoment B raw23959step0 raw23959step0Labels = mixedMoment B raw23959step1 raw23959step1Labels := by
      have ha : raw23959step1 = (fun i j => raw23959step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23959step1 raw23959step0; decide +kernel
      have hl : raw23959step1Labels = raw23959step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23959step0 raw23959step0Labels permutation33 permutation2
    _ = mixedMoment B node1134 node1134Labels := by rfl

theorem canonical23960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23960 raw23960Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw23960 raw23960Labels = mixedMoment B raw23960step0 raw23960step0Labels := by
      have hz : ∀ j, raw23960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23960step0 = (fun i j => raw23960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23960step0 raw23960; decide +kernel
      have hl : raw23960step0Labels = raw23960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23960 raw23960Labels permutation346 hz
    mixedMoment B raw23960step0 raw23960step0Labels = mixedMoment B raw23960step1 raw23960step1Labels := by
      have ha : raw23960step1 = (fun i j => raw23960step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23960step1 raw23960step0; decide +kernel
      have hl : raw23960step1Labels = raw23960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23960step0 raw23960step0Labels permutation44 permutation2
    _ = mixedMoment B node640 node640Labels := by rfl

theorem canonical23961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23961 raw23961Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw23961 raw23961Labels = mixedMoment B raw23961step0 raw23961step0Labels := by
      have hz : ∀ j, raw23961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23961step0 = (fun i j => raw23961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23961step0 raw23961; decide +kernel
      have hl : raw23961step0Labels = raw23961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23961 raw23961Labels permutation346 hz
    mixedMoment B raw23961step0 raw23961step0Labels = mixedMoment B raw23961step1 raw23961step1Labels := by
      have ha : raw23961step1 = (fun i j => raw23961step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23961step1 raw23961step0; decide +kernel
      have hl : raw23961step1Labels = raw23961step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23961step0 raw23961step0Labels permutation34 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical23962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23962 raw23962Labels = mixedMoment B node1158 node1158Labels := by
  calc
    mixedMoment B raw23962 raw23962Labels = mixedMoment B raw23962step0 raw23962step0Labels := by
      have ha : raw23962step0 = (fun i j => raw23962 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23962step0 raw23962; decide +kernel
      have hl : raw23962step0Labels = raw23962Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23962 raw23962Labels permutation188 permutation2
    _ = mixedMoment B node1158 node1158Labels := by rfl

theorem canonical23963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23963 raw23963Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw23963 raw23963Labels = mixedMoment B raw23963step0 raw23963step0Labels := by
      have hz : ∀ j, raw23963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23963step0 = (fun i j => raw23963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23963step0 raw23963; decide +kernel
      have hl : raw23963step0Labels = raw23963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23963 raw23963Labels permutation346 hz
    mixedMoment B raw23963step0 raw23963step0Labels = mixedMoment B raw23963step1 raw23963step1Labels := by
      have ha : raw23963step1 = (fun i j => raw23963step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23963step1 raw23963step0; decide +kernel
      have hl : raw23963step1Labels = raw23963step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23963step0 raw23963step0Labels permutation40 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical23964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23964 raw23964Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw23964 raw23964Labels = mixedMoment B raw23964step0 raw23964step0Labels := by
      have hz : ∀ j, raw23964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23964step0 = (fun i j => raw23964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23964step0 raw23964; decide +kernel
      have hl : raw23964step0Labels = raw23964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23964 raw23964Labels permutation346 hz
    mixedMoment B raw23964step0 raw23964step0Labels = mixedMoment B raw23964step1 raw23964step1Labels := by
      have ha : raw23964step1 = (fun i j => raw23964step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23964step1 raw23964step0; decide +kernel
      have hl : raw23964step1Labels = raw23964step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23964step0 raw23964step0Labels permutation44 permutation2
    _ = mixedMoment B node1240 node1240Labels := by rfl

theorem canonical23965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23965 raw23965Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw23965 raw23965Labels = mixedMoment B raw23965step0 raw23965step0Labels := by
      have hz : ∀ j, raw23965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23965step0 = (fun i j => raw23965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23965step0 raw23965; decide +kernel
      have hl : raw23965step0Labels = raw23965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23965 raw23965Labels permutation346 hz
    mixedMoment B raw23965step0 raw23965step0Labels = mixedMoment B raw23965step1 raw23965step1Labels := by
      have ha : raw23965step1 = (fun i j => raw23965step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23965step1 raw23965step0; decide +kernel
      have hl : raw23965step1Labels = raw23965step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23965step0 raw23965step0Labels permutation44 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

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

theorem canonical23967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23967 raw23967Labels = mixedMoment B node1649 node1649Labels := by
  calc
    mixedMoment B raw23967 raw23967Labels = mixedMoment B raw23967step0 raw23967step0Labels := by
      have hz : ∀ j, raw23967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23967step0 = (fun i j => raw23967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23967step0 raw23967; decide +kernel
      have hl : raw23967step0Labels = raw23967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23967 raw23967Labels permutation346 hz
    mixedMoment B raw23967step0 raw23967step0Labels = mixedMoment B raw23967step1 raw23967step1Labels := by
      have ha : raw23967step1 = (fun i j => raw23967step0 (permutation47 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23967step1 raw23967step0; decide +kernel
      have hl : raw23967step1Labels = raw23967step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23967step0 raw23967step0Labels permutation47 permutation2
    mixedMoment B raw23967step1 raw23967step1Labels = mixedMoment B raw23967step2 raw23967step2Labels := by
      have ha : raw23967step2 = -raw23967step1 := by apply Matrix.ext; change ∀ i j, raw23967step2 i j = -(raw23967step1 i j); unfold raw23967step2 raw23967step1; decide +kernel
      have hl : raw23967step2Labels = raw23967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1649 node1649Labels := by rfl

theorem canonical23968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23968 raw23968Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw23968 raw23968Labels = mixedMoment B raw23968step0 raw23968step0Labels := by
      have ha : raw23968step0 = (fun i j => raw23968 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23968step0 raw23968; decide +kernel
      have hl : raw23968step0Labels = raw23968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23968 raw23968Labels permutation224 permutation2
    mixedMoment B raw23968step0 raw23968step0Labels = mixedMoment B raw23968step1 raw23968step1Labels := by
      have ha : raw23968step1 = -raw23968step0 := by apply Matrix.ext; change ∀ i j, raw23968step1 i j = -(raw23968step0 i j); unfold raw23968step1 raw23968step0; decide +kernel
      have hl : raw23968step1Labels = raw23968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1642 node1642Labels := by rfl

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

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical86
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical11086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11086 raw11086Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw11086 raw11086Labels = mixedMoment B raw11086step0 raw11086step0Labels := by
      have hz : ∀ j, raw11086 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11086step0 = (fun i j => raw11086 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11086step0 raw11086; decide +kernel
      have hl : raw11086step0Labels = raw11086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086 raw11086Labels permutation590 hz
    mixedMoment B raw11086step0 raw11086step0Labels = mixedMoment B raw11086step1 raw11086step1Labels := by
      have hz : ∀ j, raw11086step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw11086step1 = (fun i j => raw11086step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw11086step1 raw11086step0; decide +kernel
      have hl : raw11086step1Labels = raw11086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11086step0 raw11086step0Labels permutation104 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

theorem canonical11087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11087 raw11087Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw11087 raw11087Labels = mixedMoment B raw11087step0 raw11087step0Labels := by
      have hz : ∀ j, raw11087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw11087step0 = (fun i j => raw11087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw11087step0 raw11087; decide +kernel
      have hl : raw11087step0Labels = raw11087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11087 raw11087Labels permutation434 hz
    mixedMoment B raw11087step0 raw11087step0Labels = mixedMoment B raw11087step1 raw11087step1Labels := by
      have ha : raw11087step1 = (fun i j => raw11087step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11087step1 raw11087step0; decide +kernel
      have hl : raw11087step1Labels = raw11087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11087step0 raw11087step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

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

theorem sound640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node640 node640Labels = Sparse.eval nodeValue640 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 640) = mixedMoment B node640 node640Labels := rfl
  simpa [nodeValue640, Sparse.eval] using hc.symm

theorem sound651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node651 node651Labels = Sparse.eval nodeValue651 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 651) = mixedMoment B node651 node651Labels := rfl
  simpa [nodeValue651, Sparse.eval] using hc.symm

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

theorem sound782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node782 node782Labels = Sparse.eval nodeValue782 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 782) = mixedMoment B node782 node782Labels := rfl
  simpa [nodeValue782, Sparse.eval] using hc.symm

theorem sound784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node784 node784Labels = Sparse.eval nodeValue784 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 784) = mixedMoment B node784 node784Labels := rfl
  simpa [nodeValue784, Sparse.eval] using hc.symm

theorem sound803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node803 node803Labels = Sparse.eval nodeValue803 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 803) = mixedMoment B node803 node803Labels := rfl
  simpa [nodeValue803, Sparse.eval] using hc.symm

theorem sound822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node822 node822Labels = Sparse.eval nodeValue822 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 822) = mixedMoment B node822 node822Labels := rfl
  simpa [nodeValue822, Sparse.eval] using hc.symm

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

theorem sound944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node944 node944Labels = Sparse.eval nodeValue944 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 944) = mixedMoment B node944 node944Labels := rfl
  simpa [nodeValue944, Sparse.eval] using hc.symm

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

theorem sound1021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1021 node1021Labels = Sparse.eval nodeValue1021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1021) = mixedMoment B node1021 node1021Labels := rfl
  simpa [nodeValue1021, Sparse.eval] using hc.symm

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

theorem sound1044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1044 node1044Labels = Sparse.eval nodeValue1044 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1044) = mixedMoment B node1044 node1044Labels := rfl
  simpa [nodeValue1044, Sparse.eval] using hc.symm

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

theorem sound1125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1125 node1125Labels = Sparse.eval nodeValue1125 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1125) = mixedMoment B node1125 node1125Labels := rfl
  simpa [nodeValue1125, Sparse.eval] using hc.symm

theorem sound1127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1127 node1127Labels = Sparse.eval nodeValue1127 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1127) = mixedMoment B node1127 node1127Labels := rfl
  simpa [nodeValue1127, Sparse.eval] using hc.symm

theorem sound1128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1128 node1128Labels = Sparse.eval nodeValue1128 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1128) = mixedMoment B node1128 node1128Labels := rfl
  simpa [nodeValue1128, Sparse.eval] using hc.symm

theorem sound1132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1132 node1132Labels = Sparse.eval nodeValue1132 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1132) = mixedMoment B node1132 node1132Labels := rfl
  simpa [nodeValue1132, Sparse.eval] using hc.symm

theorem sound1133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1133 node1133Labels = Sparse.eval nodeValue1133 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1133) = mixedMoment B node1133 node1133Labels := rfl
  simpa [nodeValue1133, Sparse.eval] using hc.symm

theorem sound1134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1134 node1134Labels = Sparse.eval nodeValue1134 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1134) = mixedMoment B node1134 node1134Labels := rfl
  simpa [nodeValue1134, Sparse.eval] using hc.symm

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

theorem sound1158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1158 node1158Labels = Sparse.eval nodeValue1158 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1158) = mixedMoment B node1158 node1158Labels := rfl
  simpa [nodeValue1158, Sparse.eval] using hc.symm

theorem sound1169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1169 node1169Labels = Sparse.eval nodeValue1169 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1169) = mixedMoment B node1169 node1169Labels := rfl
  simpa [nodeValue1169, Sparse.eval] using hc.symm

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

theorem sound1234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1234 node1234Labels = Sparse.eval nodeValue1234 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1234) = mixedMoment B node1234 node1234Labels := rfl
  simpa [nodeValue1234, Sparse.eval] using hc.symm

theorem sound1237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1237 node1237Labels = Sparse.eval nodeValue1237 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1237) = mixedMoment B node1237 node1237Labels := rfl
  simpa [nodeValue1237, Sparse.eval] using hc.symm

theorem sound1240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1240 node1240Labels = Sparse.eval nodeValue1240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1240) = mixedMoment B node1240 node1240Labels := rfl
  simpa [nodeValue1240, Sparse.eval] using hc.symm

theorem sound1262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1262 node1262Labels = Sparse.eval nodeValue1262 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1262) = mixedMoment B node1262 node1262Labels := rfl
  simpa [nodeValue1262, Sparse.eval] using hc.symm

theorem sound1270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1270 node1270Labels = Sparse.eval nodeValue1270 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1270) = mixedMoment B node1270 node1270Labels := rfl
  simpa [nodeValue1270, Sparse.eval] using hc.symm

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

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

theorem sound1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1327 node1327Labels = Sparse.eval nodeValue1327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1327) = mixedMoment B node1327 node1327Labels := rfl
  simpa [nodeValue1327, Sparse.eval] using hc.symm

theorem sound1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1328 node1328Labels = Sparse.eval nodeValue1328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1328) = mixedMoment B node1328 node1328Labels := rfl
  simpa [nodeValue1328, Sparse.eval] using hc.symm

theorem sound1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1330 node1330Labels = Sparse.eval nodeValue1330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1330) = mixedMoment B node1330 node1330Labels := rfl
  simpa [nodeValue1330, Sparse.eval] using hc.symm

theorem sound1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1335 node1335Labels = Sparse.eval nodeValue1335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1335) = mixedMoment B node1335 node1335Labels := rfl
  simpa [nodeValue1335, Sparse.eval] using hc.symm

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

theorem sound1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1383 node1383Labels = Sparse.eval nodeValue1383 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1383) = mixedMoment B node1383 node1383Labels := rfl
  simpa [nodeValue1383, Sparse.eval] using hc.symm

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

theorem sound1602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1602 node1602Labels = Sparse.eval nodeValue1602 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1602) = mixedMoment B node1602 node1602Labels := rfl
  simpa [nodeValue1602, Sparse.eval] using hc.symm

theorem sound1635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1635 node1635Labels = Sparse.eval nodeValue1635 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1635) = mixedMoment B node1635 node1635Labels := rfl
  simpa [nodeValue1635, Sparse.eval] using hc.symm

theorem sound1642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1642 node1642Labels = Sparse.eval nodeValue1642 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1642) = mixedMoment B node1642 node1642Labels := rfl
  simpa [nodeValue1642, Sparse.eval] using hc.symm

theorem sound1645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1645 node1645Labels = Sparse.eval nodeValue1645 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1645) = mixedMoment B node1645 node1645Labels := rfl
  simpa [nodeValue1645, Sparse.eval] using hc.symm

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

theorem sound1654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1654 node1654Labels = Sparse.eval nodeValue1654 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1654) = mixedMoment B node1654 node1654Labels := rfl
  simpa [nodeValue1654, Sparse.eval] using hc.symm

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

theorem sound1710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1710 node1710Labels = Sparse.eval nodeValue1710 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1710) = mixedMoment B node1710 node1710Labels := rfl
  simpa [nodeValue1710, Sparse.eval] using hc.symm

theorem sound1713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1713 node1713Labels = Sparse.eval nodeValue1713 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1713) = mixedMoment B node1713 node1713Labels := rfl
  simpa [nodeValue1713, Sparse.eval] using hc.symm

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

theorem sound1737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1737 node1737Labels = Sparse.eval nodeValue1737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1737) = mixedMoment B node1737 node1737Labels := rfl
  simpa [nodeValue1737, Sparse.eval] using hc.symm

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

theorem sound2457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2457 node2457Labels = Sparse.eval nodeValue2457 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2457) = mixedMoment B node2457 node2457Labels := rfl
  simpa [nodeValue2457, Sparse.eval] using hc.symm

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

theorem sound2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2509 node2509Labels = Sparse.eval nodeValue2509 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2509) = mixedMoment B node2509 node2509Labels := rfl
  simpa [nodeValue2509, Sparse.eval] using hc.symm

theorem sound2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2512 node2512Labels = Sparse.eval nodeValue2512 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2512) = mixedMoment B node2512 node2512Labels := rfl
  simpa [nodeValue2512, Sparse.eval] using hc.symm

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

theorem sound2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2702 node2702Labels = Sparse.eval nodeValue2702 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2702) = mixedMoment B node2702 node2702Labels := rfl
  simpa [nodeValue2702, Sparse.eval] using hc.symm

theorem sound2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2737 node2737Labels = Sparse.eval nodeValue2737 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2737) = mixedMoment B node2737 node2737Labels := rfl
  simpa [nodeValue2737, Sparse.eval] using hc.symm

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

theorem sound3281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3281 node3281Labels = Sparse.eval nodeValue3281 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3281) = mixedMoment B node3281 node3281Labels := rfl
  simpa [nodeValue3281, Sparse.eval] using hc.symm

theorem sound3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3288 node3288Labels = Sparse.eval nodeValue3288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3288) = mixedMoment B node3288 node3288Labels := rfl
  simpa [nodeValue3288, Sparse.eval] using hc.symm

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

theorem sound3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3308 node3308Labels = Sparse.eval nodeValue3308 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3308) = mixedMoment B node3308 node3308Labels := rfl
  simpa [nodeValue3308, Sparse.eval] using hc.symm

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

theorem sound580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node580 node580Labels = Sparse.eval nodeValue580 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 580) = mixedMoment B node580 node580Labels := rfl
  simpa [nodeValue580, Sparse.eval] using hc.symm

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

theorem sourceEq1596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1596 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1596 + difference 0 0) (sourceB1596 + difference 0 0) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1596 + difference 0 0) (sourceB1596 + difference 0 0) sourceC1596) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1596 + difference 1 0) (sourceB1596 + difference 0 1) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA1596 + difference 1 0) (sourceB1596 + difference 0 1) sourceC1596) = raw23888 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23888; decide +kernel
    rw [ha]
    exact (canonical23888 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1596 + difference 2 0) (sourceB1596 + difference 0 2) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA1596 + difference 2 0) (sourceB1596 + difference 0 2) sourceC1596) = raw23889 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23889; decide +kernel
    rw [ha]
    exact (canonical23889 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1596 + difference 3 0) (sourceB1596 + difference 0 3) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1596 + difference 3 0) (sourceB1596 + difference 0 3) sourceC1596) = raw23890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23890; decide +kernel
    rw [ha]
    exact (canonical23890 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1596 + difference 4 0) (sourceB1596 + difference 0 4) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1596 + difference 4 0) (sourceB1596 + difference 0 4) sourceC1596) = raw23891 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23891; decide +kernel
    rw [ha]
    exact (canonical23891 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1596 + difference 5 0) (sourceB1596 + difference 0 5) sourceC1596) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 782) := by
    have ha : (tripleCharges (sourceA1596 + difference 5 0) (sourceB1596 + difference 0 5) sourceC1596) = raw23892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1596 sourceB1596 sourceC1596 difference raw23892; decide +kernel
    rw [ha]
    exact (canonical23892 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1596 + sourceB1596) sourceC1596) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1596 + sourceB1596) sourceC1596) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1596 sourceB1596 sourceC1596 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1596 sourceB1596 sourceC1596
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1596, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1597 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 0) (sourceB1597 + difference 0 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 803) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 0) (sourceB1597 + difference 0 3) sourceC1597) = raw23890 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23890; decide +kernel
    rw [ha]
    exact (canonical23890 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 1) (sourceB1597 + difference 1 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 1) (sourceB1597 + difference 1 3) sourceC1597) = raw23852 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23852; decide +kernel
    rw [ha]
    exact (canonical23852 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 2) (sourceB1597 + difference 2 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 2) (sourceB1597 + difference 2 3) sourceC1597) = raw23893 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23893; decide +kernel
    rw [ha]
    exact (canonical23893 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 3) (sourceB1597 + difference 3 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 3) (sourceB1597 + difference 3 3) sourceC1597) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 4) (sourceB1597 + difference 4 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 4) (sourceB1597 + difference 4 3) sourceC1597) = raw23894 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23894; decide +kernel
    rw [ha]
    exact (canonical23894 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1597 + difference 3 5) (sourceB1597 + difference 5 3) sourceC1597) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1597 + difference 3 5) (sourceB1597 + difference 5 3) sourceC1597) = raw23895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1597 sourceB1597 sourceC1597 difference raw23895; decide +kernel
    rw [ha]
    exact (canonical23895 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1597 + sourceB1597) sourceC1597) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1597 + sourceB1597) sourceC1597) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1597 sourceB1597 sourceC1597 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1597 sourceB1597 sourceC1597
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1597, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1598 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 0) (sourceB1598 + difference 0 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 782) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 0) (sourceB1598 + difference 0 5) sourceC1598) = raw23892 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23892; decide +kernel
    rw [ha]
    exact (canonical23892 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 1) (sourceB1598 + difference 1 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 1) (sourceB1598 + difference 1 5) sourceC1598) = raw23853 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23853; decide +kernel
    rw [ha]
    exact (canonical23853 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 2) (sourceB1598 + difference 2 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1707) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 2) (sourceB1598 + difference 2 5) sourceC1598) = raw23896 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23896; decide +kernel
    rw [ha]
    exact (canonical23896 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 3) (sourceB1598 + difference 3 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 3) (sourceB1598 + difference 3 5) sourceC1598) = raw23897 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23897; decide +kernel
    rw [ha]
    exact (canonical23897 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 4) (sourceB1598 + difference 4 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1635) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 4) (sourceB1598 + difference 4 5) sourceC1598) = raw23898 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23898; decide +kernel
    rw [ha]
    exact (canonical23898 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1598 + difference 5 5) (sourceB1598 + difference 5 5) sourceC1598) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1705) := by
    have ha : (tripleCharges (sourceA1598 + difference 5 5) (sourceB1598 + difference 5 5) sourceC1598) = raw23851 := by
      apply Matrix.ext; unfold tripleCharges sourceA1598 sourceB1598 sourceC1598 difference raw23851; decide +kernel
    rw [ha]
    exact (canonical23851 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1598 + sourceB1598) sourceC1598) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1598 + sourceB1598) sourceC1598) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1598 sourceB1598 sourceC1598 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1598 sourceB1598 sourceC1598
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1598, Integer.Sparse.eval]
  linarith only [hs]

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

theorem sourceEq1600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1600 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 0) (sourceB1600 + difference 0 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 580) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 0) (sourceB1600 + difference 0 1) sourceC1600) = raw23900 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23900; decide +kernel
    rw [ha]
    exact (canonical23900 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 1) (sourceB1600 + difference 1 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 1) (sourceB1600 + difference 1 1) sourceC1600) = raw23901 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23901; decide +kernel
    rw [ha]
    exact (canonical23901 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 2) (sourceB1600 + difference 2 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 944) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 2) (sourceB1600 + difference 2 1) sourceC1600) = raw23902 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23902; decide +kernel
    rw [ha]
    exact (canonical23902 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 3) (sourceB1600 + difference 3 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1044) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 3) (sourceB1600 + difference 3 1) sourceC1600) = raw11087 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw11087; decide +kernel
    rw [ha]
    exact (canonical11087 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 4) (sourceB1600 + difference 4 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1021) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 4) (sourceB1600 + difference 4 1) sourceC1600) = raw23903 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23903; decide +kernel
    rw [ha]
    exact (canonical23903 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1600 + difference 1 5) (sourceB1600 + difference 5 1) sourceC1600) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1039) := by
    have ha : (tripleCharges (sourceA1600 + difference 1 5) (sourceB1600 + difference 5 1) sourceC1600) = raw23904 := by
      apply Matrix.ext; unfold tripleCharges sourceA1600 sourceB1600 sourceC1600 difference raw23904; decide +kernel
    rw [ha]
    exact (canonical23904 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1600 + sourceB1600) sourceC1600) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4083) := by
    have ha : (doubleCharges (sourceA1600 + sourceB1600) sourceC1600) = raw11086 := by
      apply Matrix.ext; unfold doubleCharges sourceA1600 sourceB1600 sourceC1600 raw11086; decide +kernel
    rw [ha]
    exact (canonical11086 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1600 sourceB1600 sourceC1600
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1600, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1601 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1601 + difference 0 1) (sourceB1601 + difference 1 0) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2924) := by
    have ha : (tripleCharges (sourceA1601 + difference 0 1) (sourceB1601 + difference 1 0) sourceC1601) = raw23905 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23905; decide +kernel
    rw [ha]
    exact (canonical23905 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1601 + difference 1 1) (sourceB1601 + difference 1 1) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1383) := by
    have ha : (tripleCharges (sourceA1601 + difference 1 1) (sourceB1601 + difference 1 1) sourceC1601) = raw23906 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23906; decide +kernel
    rw [ha]
    exact (canonical23906 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1601 + difference 2 1) (sourceB1601 + difference 1 2) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1335) := by
    have ha : (tripleCharges (sourceA1601 + difference 2 1) (sourceB1601 + difference 1 2) sourceC1601) = raw23907 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23907; decide +kernel
    rw [ha]
    exact (canonical23907 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1601 + difference 3 1) (sourceB1601 + difference 1 3) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1328) := by
    have ha : (tripleCharges (sourceA1601 + difference 3 1) (sourceB1601 + difference 1 3) sourceC1601) = raw23908 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23908; decide +kernel
    rw [ha]
    exact (canonical23908 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1601 + difference 4 1) (sourceB1601 + difference 1 4) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1330) := by
    have ha : (tripleCharges (sourceA1601 + difference 4 1) (sourceB1601 + difference 1 4) sourceC1601) = raw23909 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23909; decide +kernel
    rw [ha]
    exact (canonical23909 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1601 + difference 5 1) (sourceB1601 + difference 1 5) sourceC1601) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1327) := by
    have ha : (tripleCharges (sourceA1601 + difference 5 1) (sourceB1601 + difference 1 5) sourceC1601) = raw23910 := by
      apply Matrix.ext; unfold tripleCharges sourceA1601 sourceB1601 sourceC1601 difference raw23910; decide +kernel
    rw [ha]
    exact (canonical23910 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1601 + sourceB1601) sourceC1601) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1601 + sourceB1601) sourceC1601) = raw23911 := by
      apply Matrix.ext; unfold doubleCharges sourceA1601 sourceB1601 sourceC1601 raw23911; decide +kernel
    rw [ha]
    exact (canonical23911 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1601 sourceB1601 sourceC1601
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1601, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1602 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 0) (sourceB1602 + difference 0 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 0) (sourceB1602 + difference 0 0) sourceC1602) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 1) (sourceB1602 + difference 1 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 1) (sourceB1602 + difference 1 0) sourceC1602) = raw23820 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23820; decide +kernel
    rw [ha]
    exact (canonical23820 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 2) (sourceB1602 + difference 2 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 2) (sourceB1602 + difference 2 0) sourceC1602) = raw23912 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23912; decide +kernel
    rw [ha]
    exact (canonical23912 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 3) (sourceB1602 + difference 3 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3278) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 3) (sourceB1602 + difference 3 0) sourceC1602) = raw23913 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23913; decide +kernel
    rw [ha]
    exact (canonical23913 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 4) (sourceB1602 + difference 4 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3281) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 4) (sourceB1602 + difference 4 0) sourceC1602) = raw23887 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23887; decide +kernel
    rw [ha]
    exact (canonical23887 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1602 + difference 0 5) (sourceB1602 + difference 5 0) sourceC1602) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2457) := by
    have ha : (tripleCharges (sourceA1602 + difference 0 5) (sourceB1602 + difference 5 0) sourceC1602) = raw23914 := by
      apply Matrix.ext; unfold tripleCharges sourceA1602 sourceB1602 sourceC1602 difference raw23914; decide +kernel
    rw [ha]
    exact (canonical23914 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1602 + sourceB1602) sourceC1602) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1602 + sourceB1602) sourceC1602) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1602 sourceB1602 sourceC1602 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1602 sourceB1602 sourceC1602
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1602, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1604 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 0) (sourceB1604 + difference 0 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 822) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 0) (sourceB1604 + difference 0 3) sourceC1604) = raw23917 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23917; decide +kernel
    rw [ha]
    exact (canonical23917 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 1) (sourceB1604 + difference 1 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 1) (sourceB1604 + difference 1 3) sourceC1604) = raw23824 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23824; decide +kernel
    rw [ha]
    exact (canonical23824 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 2) (sourceB1604 + difference 2 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 2) (sourceB1604 + difference 2 3) sourceC1604) = raw23919 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23919; decide +kernel
    rw [ha]
    exact (canonical23919 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 3) (sourceB1604 + difference 3 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 3) (sourceB1604 + difference 3 3) sourceC1604) = raw23826 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23826; decide +kernel
    rw [ha]
    exact (canonical23826 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 4) (sourceB1604 + difference 4 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1713) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 4) (sourceB1604 + difference 4 3) sourceC1604) = raw23895 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23895; decide +kernel
    rw [ha]
    exact (canonical23895 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1604 + difference 3 5) (sourceB1604 + difference 5 3) sourceC1604) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1654) := by
    have ha : (tripleCharges (sourceA1604 + difference 3 5) (sourceB1604 + difference 5 3) sourceC1604) = raw23920 := by
      apply Matrix.ext; unfold tripleCharges sourceA1604 sourceB1604 sourceC1604 difference raw23920; decide +kernel
    rw [ha]
    exact (canonical23920 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1604 + sourceB1604) sourceC1604) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1604 + sourceB1604) sourceC1604) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1604 sourceB1604 sourceC1604 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1604 sourceB1604 sourceC1604
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1604, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1606 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1606 + difference 0 1) (sourceB1606 + difference 1 0) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2509) := by
    have ha : (tripleCharges (sourceA1606 + difference 0 1) (sourceB1606 + difference 1 0) sourceC1606) = raw23928 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23928; decide +kernel
    rw [ha]
    exact (canonical23928 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1606 + difference 1 1) (sourceB1606 + difference 1 1) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1234) := by
    have ha : (tripleCharges (sourceA1606 + difference 1 1) (sourceB1606 + difference 1 1) sourceC1606) = raw23929 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23929; decide +kernel
    rw [ha]
    exact (canonical23929 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1606 + difference 2 1) (sourceB1606 + difference 1 2) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1125) := by
    have ha : (tripleCharges (sourceA1606 + difference 2 1) (sourceB1606 + difference 1 2) sourceC1606) = raw23930 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23930; decide +kernel
    rw [ha]
    exact (canonical23930 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1606 + difference 3 1) (sourceB1606 + difference 1 3) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1606 + difference 3 1) (sourceB1606 + difference 1 3) sourceC1606) = raw23931 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23931; decide +kernel
    rw [ha]
    exact (canonical23931 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1606 + difference 4 1) (sourceB1606 + difference 1 4) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1133) := by
    have ha : (tripleCharges (sourceA1606 + difference 4 1) (sourceB1606 + difference 1 4) sourceC1606) = raw22395 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw22395; decide +kernel
    rw [ha]
    exact (canonical22395 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1606 + difference 5 1) (sourceB1606 + difference 1 5) sourceC1606) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1128) := by
    have ha : (tripleCharges (sourceA1606 + difference 5 1) (sourceB1606 + difference 1 5) sourceC1606) = raw23932 := by
      apply Matrix.ext; unfold tripleCharges sourceA1606 sourceB1606 sourceC1606 difference raw23932; decide +kernel
    rw [ha]
    exact (canonical23932 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1606 + sourceB1606) sourceC1606) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4084) := by
    have ha : (doubleCharges (sourceA1606 + sourceB1606) sourceC1606) = raw22398 := by
      apply Matrix.ext; unfold doubleCharges sourceA1606 sourceB1606 sourceC1606 raw22398; decide +kernel
    rw [ha]
    exact (canonical22398 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1606 sourceB1606 sourceC1606
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1606, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1607 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 0) (sourceB1607 + difference 0 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 651) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 0) (sourceB1607 + difference 0 1) sourceC1607) = raw23933 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23933; decide +kernel
    rw [ha]
    exact (canonical23933 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 1) (sourceB1607 + difference 1 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 1) (sourceB1607 + difference 1 1) sourceC1607) = raw13564 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw13564; decide +kernel
    rw [ha]
    exact (canonical13564 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 2) (sourceB1607 + difference 2 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1169) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 2) (sourceB1607 + difference 2 1) sourceC1607) = raw23934 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23934; decide +kernel
    rw [ha]
    exact (canonical23934 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 3) (sourceB1607 + difference 3 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 3) (sourceB1607 + difference 3 1) sourceC1607) = raw23935 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23935; decide +kernel
    rw [ha]
    exact (canonical23935 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 4) (sourceB1607 + difference 4 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1270) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 4) (sourceB1607 + difference 4 1) sourceC1607) = raw23936 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw23936; decide +kernel
    rw [ha]
    exact (canonical23936 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1607 + difference 1 5) (sourceB1607 + difference 5 1) sourceC1607) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1607 + difference 1 5) (sourceB1607 + difference 5 1) sourceC1607) = raw13560 := by
      apply Matrix.ext; unfold tripleCharges sourceA1607 sourceB1607 sourceC1607 difference raw13560; decide +kernel
    rw [ha]
    exact (canonical13560 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1607 + sourceB1607) sourceC1607) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1607 + sourceB1607) sourceC1607) = raw13559 := by
      apply Matrix.ext; unfold doubleCharges sourceA1607 sourceB1607 sourceC1607 raw13559; decide +kernel
    rw [ha]
    exact (canonical13559 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1607 sourceB1607 sourceC1607
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1607, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1608 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 0) (sourceB1608 + difference 0 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 0) (sourceB1608 + difference 0 0) sourceC1608) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 1) (sourceB1608 + difference 1 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1658) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 1) (sourceB1608 + difference 1 0) sourceC1608) = raw23938 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23938; decide +kernel
    rw [ha]
    exact (canonical23938 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 2) (sourceB1608 + difference 2 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1654) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 2) (sourceB1608 + difference 2 0) sourceC1608) = raw23939 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23939; decide +kernel
    rw [ha]
    exact (canonical23939 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 3) (sourceB1608 + difference 3 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 3) (sourceB1608 + difference 3 0) sourceC1608) = raw23940 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23940; decide +kernel
    rw [ha]
    exact (canonical23940 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 4) (sourceB1608 + difference 4 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1656) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 4) (sourceB1608 + difference 4 0) sourceC1608) = raw23941 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23941; decide +kernel
    rw [ha]
    exact (canonical23941 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1608 + difference 0 5) (sourceB1608 + difference 5 0) sourceC1608) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1608 + difference 0 5) (sourceB1608 + difference 5 0) sourceC1608) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1608 sourceB1608 sourceC1608 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1608 + sourceB1608) sourceC1608) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1608 + sourceB1608) sourceC1608) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1608 sourceB1608 sourceC1608 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1608 sourceB1608 sourceC1608
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1608, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1609 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 0) (sourceB1609 + difference 0 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1710) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 0) (sourceB1609 + difference 0 1) sourceC1609) = raw23943 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23943; decide +kernel
    rw [ha]
    exact (canonical23943 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 1) (sourceB1609 + difference 1 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 1) (sourceB1609 + difference 1 1) sourceC1609) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 2) (sourceB1609 + difference 2 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 2) (sourceB1609 + difference 2 1) sourceC1609) = raw23944 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23944; decide +kernel
    rw [ha]
    exact (canonical23944 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 3) (sourceB1609 + difference 3 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 3) (sourceB1609 + difference 3 1) sourceC1609) = raw23945 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23945; decide +kernel
    rw [ha]
    exact (canonical23945 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 4) (sourceB1609 + difference 4 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2737) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 4) (sourceB1609 + difference 4 1) sourceC1609) = raw23946 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23946; decide +kernel
    rw [ha]
    exact (canonical23946 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1609 + difference 1 5) (sourceB1609 + difference 5 1) sourceC1609) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1609 + difference 1 5) (sourceB1609 + difference 5 1) sourceC1609) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1609 sourceB1609 sourceC1609 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1609 + sourceB1609) sourceC1609) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1609 + sourceB1609) sourceC1609) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1609 sourceB1609 sourceC1609 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1609 sourceB1609 sourceC1609
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1609, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1610 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 0) (sourceB1610 + difference 0 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1602) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 0) (sourceB1610 + difference 0 3) sourceC1610) = raw23948 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23948; decide +kernel
    rw [ha]
    exact (canonical23948 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 1) (sourceB1610 + difference 1 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2466) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 1) (sourceB1610 + difference 1 3) sourceC1610) = raw23949 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23949; decide +kernel
    rw [ha]
    exact (canonical23949 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 2) (sourceB1610 + difference 2 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2457) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 2) (sourceB1610 + difference 2 3) sourceC1610) = raw23950 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23950; decide +kernel
    rw [ha]
    exact (canonical23950 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 3) (sourceB1610 + difference 3 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 3) (sourceB1610 + difference 3 3) sourceC1610) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 4) (sourceB1610 + difference 4 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2502) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 4) (sourceB1610 + difference 4 3) sourceC1610) = raw23951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23951; decide +kernel
    rw [ha]
    exact (canonical23951 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1610 + difference 3 5) (sourceB1610 + difference 5 3) sourceC1610) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1610 + difference 3 5) (sourceB1610 + difference 5 3) sourceC1610) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1610 sourceB1610 sourceC1610 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1610 + sourceB1610) sourceC1610) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1610 + sourceB1610) sourceC1610) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1610 sourceB1610 sourceC1610 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1610 sourceB1610 sourceC1610
    (0 : Fin 2) 1 (3 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1610, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1611 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1611 + difference 0 5) (sourceB1611 + difference 5 0) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1737) := by
    have ha : (tripleCharges (sourceA1611 + difference 0 5) (sourceB1611 + difference 5 0) sourceC1611) = raw23942 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23942; decide +kernel
    rw [ha]
    exact (canonical23942 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1611 + difference 1 5) (sourceB1611 + difference 5 1) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3308) := by
    have ha : (tripleCharges (sourceA1611 + difference 1 5) (sourceB1611 + difference 5 1) sourceC1611) = raw23947 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23947; decide +kernel
    rw [ha]
    exact (canonical23947 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1611 + difference 2 5) (sourceB1611 + difference 5 2) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3288) := by
    have ha : (tripleCharges (sourceA1611 + difference 2 5) (sourceB1611 + difference 5 2) sourceC1611) = raw23953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23953; decide +kernel
    rw [ha]
    exact (canonical23953 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1611 + difference 3 5) (sourceB1611 + difference 5 3) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1611 + difference 3 5) (sourceB1611 + difference 5 3) sourceC1611) = raw23952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23952; decide +kernel
    rw [ha]
    exact (canonical23952 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1611 + difference 4 5) (sourceB1611 + difference 5 4) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3293) := by
    have ha : (tripleCharges (sourceA1611 + difference 4 5) (sourceB1611 + difference 5 4) sourceC1611) = raw23954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23954; decide +kernel
    rw [ha]
    exact (canonical23954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1611 + difference 5 5) (sourceB1611 + difference 5 5) sourceC1611) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2702) := by
    have ha : (tripleCharges (sourceA1611 + difference 5 5) (sourceB1611 + difference 5 5) sourceC1611) = raw23937 := by
      apply Matrix.ext; unfold tripleCharges sourceA1611 sourceB1611 sourceC1611 difference raw23937; decide +kernel
    rw [ha]
    exact (canonical23937 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1611 + sourceB1611) sourceC1611) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1611 + sourceB1611) sourceC1611) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1611 sourceB1611 sourceC1611 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1611 sourceB1611 sourceC1611
    (0 : Fin 2) 1 (5 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1611, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1612 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1612 + difference 0 1) (sourceB1612 + difference 1 0) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2512) := by
    have ha : (tripleCharges (sourceA1612 + difference 0 1) (sourceB1612 + difference 1 0) sourceC1612) = raw23955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23955; decide +kernel
    rw [ha]
    exact (canonical23955 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1612 + difference 1 1) (sourceB1612 + difference 1 1) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1237) := by
    have ha : (tripleCharges (sourceA1612 + difference 1 1) (sourceB1612 + difference 1 1) sourceC1612) = raw23956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23956; decide +kernel
    rw [ha]
    exact (canonical23956 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1612 + difference 2 1) (sourceB1612 + difference 1 2) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1127) := by
    have ha : (tripleCharges (sourceA1612 + difference 2 1) (sourceB1612 + difference 1 2) sourceC1612) = raw23957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23957; decide +kernel
    rw [ha]
    exact (canonical23957 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1612 + difference 3 1) (sourceB1612 + difference 1 3) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1141) := by
    have ha : (tripleCharges (sourceA1612 + difference 3 1) (sourceB1612 + difference 1 3) sourceC1612) = raw23958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23958; decide +kernel
    rw [ha]
    exact (canonical23958 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1612 + difference 4 1) (sourceB1612 + difference 1 4) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1134) := by
    have ha : (tripleCharges (sourceA1612 + difference 4 1) (sourceB1612 + difference 1 4) sourceC1612) = raw23959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw23959; decide +kernel
    rw [ha]
    exact (canonical23959 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1612 + difference 5 1) (sourceB1612 + difference 1 5) sourceC1612) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1132) := by
    have ha : (tripleCharges (sourceA1612 + difference 5 1) (sourceB1612 + difference 1 5) sourceC1612) = raw20245 := by
      apply Matrix.ext; unfold tripleCharges sourceA1612 sourceB1612 sourceC1612 difference raw20245; decide +kernel
    rw [ha]
    exact (canonical20245 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1612 + sourceB1612) sourceC1612) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4092) := by
    have ha : (doubleCharges (sourceA1612 + sourceB1612) sourceC1612) = raw4008 := by
      apply Matrix.ext; unfold doubleCharges sourceA1612 sourceB1612 sourceC1612 raw4008; decide +kernel
    rw [ha]
    exact (canonical4008 B hB).trans rfl
  have hs := mixedMoment_same_reversed B hB sourceA1612 sourceB1612 sourceC1612
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1612, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1613 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 0) (sourceB1613 + difference 0 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 640) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 0) (sourceB1613 + difference 0 1) sourceC1613) = raw23960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23960; decide +kernel
    rw [ha]
    exact (canonical23960 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 1) (sourceB1613 + difference 1 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 1) (sourceB1613 + difference 1 1) sourceC1613) = raw23961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23961; decide +kernel
    rw [ha]
    exact (canonical23961 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 2) (sourceB1613 + difference 2 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1158) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 2) (sourceB1613 + difference 2 1) sourceC1613) = raw23962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23962; decide +kernel
    rw [ha]
    exact (canonical23962 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 3) (sourceB1613 + difference 3 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1262) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 3) (sourceB1613 + difference 3 1) sourceC1613) = raw23963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23963; decide +kernel
    rw [ha]
    exact (canonical23963 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 4) (sourceB1613 + difference 4 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1240) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 4) (sourceB1613 + difference 4 1) sourceC1613) = raw23964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23964; decide +kernel
    rw [ha]
    exact (canonical23964 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1613 + difference 1 5) (sourceB1613 + difference 5 1) sourceC1613) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1293) := by
    have ha : (tripleCharges (sourceA1613 + difference 1 5) (sourceB1613 + difference 5 1) sourceC1613) = raw23965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1613 sourceB1613 sourceC1613 difference raw23965; decide +kernel
    rw [ha]
    exact (canonical23965 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1613 + sourceB1613) sourceC1613) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4091) := by
    have ha : (doubleCharges (sourceA1613 + sourceB1613) sourceC1613) = raw16433 := by
      apply Matrix.ext; unfold doubleCharges sourceA1613 sourceB1613 sourceC1613 raw16433; decide +kernel
    rw [ha]
    exact (canonical16433 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1613 sourceB1613 sourceC1613
    (0 : Fin 2) 1 (1 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1613, Integer.Sparse.eval]
  linarith only [hs]

theorem sourceEq1614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1614 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 0) (sourceB1614 + difference 0 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3294) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 0) (sourceB1614 + difference 0 0) sourceC1614) = raw23966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23966; decide +kernel
    rw [ha]
    exact (canonical23966 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 1) (sourceB1614 + difference 1 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1649) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 1) (sourceB1614 + difference 1 0) sourceC1614) = raw23967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23967; decide +kernel
    rw [ha]
    exact (canonical23967 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 2) (sourceB1614 + difference 2 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1642) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 2) (sourceB1614 + difference 2 0) sourceC1614) = raw23968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23968; decide +kernel
    rw [ha]
    exact (canonical23968 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 3) (sourceB1614 + difference 3 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1646) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 3) (sourceB1614 + difference 3 0) sourceC1614) = raw23969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23969; decide +kernel
    rw [ha]
    exact (canonical23969 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 4) (sourceB1614 + difference 4 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1724) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 4) (sourceB1614 + difference 4 0) sourceC1614) = raw23970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23970; decide +kernel
    rw [ha]
    exact (canonical23970 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1614 + difference 0 5) (sourceB1614 + difference 5 0) sourceC1614) (![0, 0, 1] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 1645) := by
    have ha : (tripleCharges (sourceA1614 + difference 0 5) (sourceB1614 + difference 5 0) sourceC1614) = raw23971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1614 sourceB1614 sourceC1614 difference raw23971; decide +kernel
    rw [ha]
    exact (canonical23971 B hB).trans rfl
  have hm6 : mixedMoment B (doubleCharges (sourceA1614 + sourceB1614) sourceC1614) (![0, 1] : Fin 2 → Fin 2) =
      mixedVector B (Sum.inr 4069) := by
    have ha : (doubleCharges (sourceA1614 + sourceB1614) sourceC1614) = raw23799 := by
      apply Matrix.ext; unfold doubleCharges sourceA1614 sourceB1614 sourceC1614 raw23799; decide +kernel
    rw [ha]
    exact (canonical23799 B hB).trans rfl
  have hs := mixedMoment_same B hB sourceA1614 sourceB1614 sourceC1614
    (0 : Fin 2) 1 (0 : Coord)
  rw [sum_fin_six] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6] at hs
  norm_num [sourceForm1614, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Arithmetic85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck1360 : Integer.Sparse.reindex keyMap MixedData.row1360 = numericRow1360 := by decide +kernel

theorem numericCheck1360 (x : Master → ℝ) : Integer.Sparse.eval numericRow1360 x =
    (1 : ℝ) * reducedSource1360 x := by
  norm_num [numericRow1360, reducedSource1360, Integer.Sparse.eval, Sparse.eval, nodeValue782, nodeValue784, nodeValue803, nodeValue1705, nodeValue4069]

theorem reindexCheck1361 : Integer.Sparse.reindex keyMap MixedData.row1361 = numericRow1361 := by decide +kernel

theorem numericCheck1361 (x : Master → ℝ) : Integer.Sparse.eval numericRow1361 x =
    (1 : ℝ) * reducedSource1361 x := by
  norm_num [numericRow1361, reducedSource1361, Integer.Sparse.eval, Sparse.eval, nodeValue803, nodeValue1642, nodeValue1705, nodeValue1713, nodeValue1724, nodeValue4069]

theorem reindexCheck1362 : Integer.Sparse.reindex keyMap MixedData.row1362 = numericRow1362 := by decide +kernel

theorem numericCheck1362 (x : Master → ℝ) : Integer.Sparse.eval numericRow1362 x =
    (1 : ℝ) * reducedSource1362 x := by
  norm_num [numericRow1362, reducedSource1362, Integer.Sparse.eval, Sparse.eval, nodeValue782, nodeValue1635, nodeValue1705, nodeValue1707, nodeValue4069]

theorem reindexCheck1363 : Integer.Sparse.reindex keyMap MixedData.row1363 = numericRow1363 := by decide +kernel

theorem numericCheck1363 (x : Master → ℝ) : Integer.Sparse.eval numericRow1363 x =
    (1 : ℝ) * reducedSource1363 x := by
  norm_num [numericRow1363, reducedSource1363, Integer.Sparse.eval, Sparse.eval, nodeValue580, nodeValue944, nodeValue1021, nodeValue1039, nodeValue1044, nodeValue4083]

theorem reindexCheck1364 : Integer.Sparse.reindex keyMap MixedData.row1364 = numericRow1364 := by decide +kernel

theorem numericCheck1364 (x : Master → ℝ) : Integer.Sparse.eval numericRow1364 x =
    (1 : ℝ) * reducedSource1364 x := by
  norm_num [numericRow1364, reducedSource1364, Integer.Sparse.eval, Sparse.eval, nodeValue1327, nodeValue1328, nodeValue1330, nodeValue1335, nodeValue1383, nodeValue2924, nodeValue4091]

theorem reindexCheck1365 : Integer.Sparse.reindex keyMap MixedData.row1365 = numericRow1365 := by decide +kernel

theorem numericCheck1365 (x : Master → ℝ) : Integer.Sparse.eval numericRow1365 x =
    (1 : ℝ) * reducedSource1365 x := by
  norm_num [numericRow1365, reducedSource1365, Integer.Sparse.eval, Sparse.eval, nodeValue1713, nodeValue2457, nodeValue3278, nodeValue3281, nodeValue3293, nodeValue4069]

theorem reindexCheck1366 : Integer.Sparse.reindex keyMap MixedData.row1366 = numericRow1366 := by decide +kernel

theorem numericCheck1366 (x : Master → ℝ) : Integer.Sparse.eval numericRow1366 x =
    (1 : ℝ) * reducedSource1366 x := by
  norm_num [numericRow1366, reducedSource1366, Integer.Sparse.eval, Sparse.eval, nodeValue822, nodeValue1654, nodeValue1713, nodeValue1737, nodeValue4069]

theorem reindexCheck1367 : Integer.Sparse.reindex keyMap MixedData.row1367 = numericRow1367 := by decide +kernel

theorem numericCheck1367 (x : Master → ℝ) : Integer.Sparse.eval numericRow1367 x =
    (1 : ℝ) * reducedSource1367 x := by
  norm_num [numericRow1367, reducedSource1367, Integer.Sparse.eval, Sparse.eval, nodeValue1125, nodeValue1128, nodeValue1133, nodeValue1234, nodeValue2509, nodeValue4084]

theorem reindexCheck1368 : Integer.Sparse.reindex keyMap MixedData.row1368 = numericRow1368 := by decide +kernel

theorem numericCheck1368 (x : Master → ℝ) : Integer.Sparse.eval numericRow1368 x =
    (1 : ℝ) * reducedSource1368 x := by
  norm_num [numericRow1368, reducedSource1368, Integer.Sparse.eval, Sparse.eval, nodeValue651, nodeValue1169, nodeValue1270, nodeValue1293, nodeValue4091]

theorem reindexCheck1369 : Integer.Sparse.reindex keyMap MixedData.row1369 = numericRow1369 := by decide +kernel

theorem numericCheck1369 (x : Master → ℝ) : Integer.Sparse.eval numericRow1369 x =
    (1 : ℝ) * reducedSource1369 x := by
  norm_num [numericRow1369, reducedSource1369, Integer.Sparse.eval, Sparse.eval, nodeValue1654, nodeValue1656, nodeValue1658, nodeValue1737, nodeValue2702, nodeValue4069]

theorem reindexCheck1370 : Integer.Sparse.reindex keyMap MixedData.row1370 = numericRow1370 := by decide +kernel

theorem numericCheck1370 (x : Master → ℝ) : Integer.Sparse.eval numericRow1370 x =
    (1 : ℝ) * reducedSource1370 x := by
  norm_num [numericRow1370, reducedSource1370, Integer.Sparse.eval, Sparse.eval, nodeValue1710, nodeValue2702, nodeValue2737, nodeValue3308, nodeValue4069]

theorem reindexCheck1371 : Integer.Sparse.reindex keyMap MixedData.row1371 = numericRow1371 := by decide +kernel

theorem numericCheck1371 (x : Master → ℝ) : Integer.Sparse.eval numericRow1371 x =
    (1 : ℝ) * reducedSource1371 x := by
  norm_num [numericRow1371, reducedSource1371, Integer.Sparse.eval, Sparse.eval, nodeValue1602, nodeValue2457, nodeValue2466, nodeValue2502, nodeValue2702, nodeValue3293, nodeValue4069]

theorem reindexCheck1372 : Integer.Sparse.reindex keyMap MixedData.row1372 = numericRow1372 := by decide +kernel

theorem numericCheck1372 (x : Master → ℝ) : Integer.Sparse.eval numericRow1372 x =
    (1 : ℝ) * reducedSource1372 x := by
  norm_num [numericRow1372, reducedSource1372, Integer.Sparse.eval, Sparse.eval, nodeValue1737, nodeValue2702, nodeValue3288, nodeValue3293, nodeValue3308, nodeValue4069]

theorem reindexCheck1373 : Integer.Sparse.reindex keyMap MixedData.row1373 = numericRow1373 := by decide +kernel

theorem numericCheck1373 (x : Master → ℝ) : Integer.Sparse.eval numericRow1373 x =
    (1 : ℝ) * reducedSource1373 x := by
  norm_num [numericRow1373, reducedSource1373, Integer.Sparse.eval, Sparse.eval, nodeValue1127, nodeValue1132, nodeValue1134, nodeValue1141, nodeValue1237, nodeValue2512, nodeValue4092]

theorem reindexCheck1374 : Integer.Sparse.reindex keyMap MixedData.row1374 = numericRow1374 := by decide +kernel

theorem numericCheck1374 (x : Master → ℝ) : Integer.Sparse.eval numericRow1374 x =
    (1 : ℝ) * reducedSource1374 x := by
  norm_num [numericRow1374, reducedSource1374, Integer.Sparse.eval, Sparse.eval, nodeValue640, nodeValue1158, nodeValue1240, nodeValue1262, nodeValue1293, nodeValue4091]

theorem reindexCheck1375 : Integer.Sparse.reindex keyMap MixedData.row1375 = numericRow1375 := by decide +kernel

theorem numericCheck1375 (x : Master → ℝ) : Integer.Sparse.eval numericRow1375 x =
    (1 : ℝ) * reducedSource1375 x := by
  norm_num [numericRow1375, reducedSource1375, Integer.Sparse.eval, Sparse.eval, nodeValue1642, nodeValue1645, nodeValue1646, nodeValue1649, nodeValue1724, nodeValue3294, nodeValue4069]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSources_Rows85
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reducedZero1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1360 (mixedVector B) = 0 := by
  have h782 : mixedVector B (Sum.inr 782) = Sparse.eval nodeValue782 (mixedVector B) := by
    change mixedMoment B node782 node782Labels = _
    exact sound782 B hB hF
  have h784 : mixedVector B (Sum.inr 784) = Sparse.eval nodeValue784 (mixedVector B) := by
    change mixedMoment B node784 node784Labels = _
    exact sound784 B hB hF
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1596, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h782, h784, h803, h1705, h4069, reducedSource1360] using sourceEq1596 B hB

theorem rowSound1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1360 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1360, numericCheck1360, reducedZero1360 B hB hF, mul_zero]

theorem reducedZero1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1361 (mixedVector B) = 0 := by
  have h803 : mixedVector B (Sum.inr 803) = Sparse.eval nodeValue803 (mixedVector B) := by
    change mixedMoment B node803 node803Labels = _
    exact sound803 B hB hF
  have h1642 : mixedVector B (Sum.inr 1642) = Sparse.eval nodeValue1642 (mixedVector B) := by
    change mixedMoment B node1642 node1642Labels = _
    exact sound1642 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1597, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h803, h1642, h1705, h1713, h1724, h4069, reducedSource1361] using sourceEq1597 B hB

theorem rowSound1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1361 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1361, numericCheck1361, reducedZero1361 B hB hF, mul_zero]

theorem reducedZero1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1362 (mixedVector B) = 0 := by
  have h782 : mixedVector B (Sum.inr 782) = Sparse.eval nodeValue782 (mixedVector B) := by
    change mixedMoment B node782 node782Labels = _
    exact sound782 B hB hF
  have h1635 : mixedVector B (Sum.inr 1635) = Sparse.eval nodeValue1635 (mixedVector B) := by
    change mixedMoment B node1635 node1635Labels = _
    exact sound1635 B hB hF
  have h1705 : mixedVector B (Sum.inr 1705) = Sparse.eval nodeValue1705 (mixedVector B) := by
    change mixedMoment B node1705 node1705Labels = _
    exact sound1705 B hB hF
  have h1707 : mixedVector B (Sum.inr 1707) = Sparse.eval nodeValue1707 (mixedVector B) := by
    change mixedMoment B node1707 node1707Labels = _
    exact sound1707 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1598, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h782, h1635, h1705, h1707, h4069, reducedSource1362] using sourceEq1598 B hB

theorem rowSound1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1362 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1362, numericCheck1362, reducedZero1362 B hB hF, mul_zero]

theorem reducedZero1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1363 (mixedVector B) = 0 := by
  have h580 : mixedVector B (Sum.inr 580) = Sparse.eval nodeValue580 (mixedVector B) := by
    change mixedMoment B node580 node580Labels = _
    exact sound580 B hB hF
  have h944 : mixedVector B (Sum.inr 944) = Sparse.eval nodeValue944 (mixedVector B) := by
    change mixedMoment B node944 node944Labels = _
    exact sound944 B hB hF
  have h1021 : mixedVector B (Sum.inr 1021) = Sparse.eval nodeValue1021 (mixedVector B) := by
    change mixedMoment B node1021 node1021Labels = _
    exact sound1021 B hB hF
  have h1039 : mixedVector B (Sum.inr 1039) = Sparse.eval nodeValue1039 (mixedVector B) := by
    change mixedMoment B node1039 node1039Labels = _
    exact sound1039 B hB hF
  have h1044 : mixedVector B (Sum.inr 1044) = Sparse.eval nodeValue1044 (mixedVector B) := by
    change mixedMoment B node1044 node1044Labels = _
    exact sound1044 B hB hF
  have h4083 : mixedVector B (Sum.inr 4083) = Sparse.eval nodeValue4083 (mixedVector B) := by
    change mixedMoment B node4083 node4083Labels = _
    exact sound4083 B hB hF
  simpa only [sourceForm1600, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h580, h944, h1021, h1039, h1044, h4083, reducedSource1363] using sourceEq1600 B hB

theorem rowSound1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1363 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1363, numericCheck1363, reducedZero1363 B hB hF, mul_zero]

theorem reducedZero1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1364 (mixedVector B) = 0 := by
  have h1327 : mixedVector B (Sum.inr 1327) = Sparse.eval nodeValue1327 (mixedVector B) := by
    change mixedMoment B node1327 node1327Labels = _
    exact sound1327 B hB hF
  have h1328 : mixedVector B (Sum.inr 1328) = Sparse.eval nodeValue1328 (mixedVector B) := by
    change mixedMoment B node1328 node1328Labels = _
    exact sound1328 B hB hF
  have h1330 : mixedVector B (Sum.inr 1330) = Sparse.eval nodeValue1330 (mixedVector B) := by
    change mixedMoment B node1330 node1330Labels = _
    exact sound1330 B hB hF
  have h1335 : mixedVector B (Sum.inr 1335) = Sparse.eval nodeValue1335 (mixedVector B) := by
    change mixedMoment B node1335 node1335Labels = _
    exact sound1335 B hB hF
  have h1383 : mixedVector B (Sum.inr 1383) = Sparse.eval nodeValue1383 (mixedVector B) := by
    change mixedMoment B node1383 node1383Labels = _
    exact sound1383 B hB hF
  have h2924 : mixedVector B (Sum.inr 2924) = Sparse.eval nodeValue2924 (mixedVector B) := by
    change mixedMoment B node2924 node2924Labels = _
    exact sound2924 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1601, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1327, h1328, h1330, h1335, h1383, h2924, h4091, reducedSource1364] using sourceEq1601 B hB

theorem rowSound1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1364 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1364, numericCheck1364, reducedZero1364 B hB hF, mul_zero]

theorem reducedZero1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1365 (mixedVector B) = 0 := by
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h2457 : mixedVector B (Sum.inr 2457) = Sparse.eval nodeValue2457 (mixedVector B) := by
    change mixedMoment B node2457 node2457Labels = _
    exact sound2457 B hB hF
  have h3278 : mixedVector B (Sum.inr 3278) = Sparse.eval nodeValue3278 (mixedVector B) := by
    change mixedMoment B node3278 node3278Labels = _
    exact sound3278 B hB hF
  have h3281 : mixedVector B (Sum.inr 3281) = Sparse.eval nodeValue3281 (mixedVector B) := by
    change mixedMoment B node3281 node3281Labels = _
    exact sound3281 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1602, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1713, h2457, h3278, h3281, h3293, h4069, reducedSource1365] using sourceEq1602 B hB

theorem rowSound1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1365 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1365, numericCheck1365, reducedZero1365 B hB hF, mul_zero]

theorem reducedZero1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1366 (mixedVector B) = 0 := by
  have h822 : mixedVector B (Sum.inr 822) = Sparse.eval nodeValue822 (mixedVector B) := by
    change mixedMoment B node822 node822Labels = _
    exact sound822 B hB hF
  have h1654 : mixedVector B (Sum.inr 1654) = Sparse.eval nodeValue1654 (mixedVector B) := by
    change mixedMoment B node1654 node1654Labels = _
    exact sound1654 B hB hF
  have h1713 : mixedVector B (Sum.inr 1713) = Sparse.eval nodeValue1713 (mixedVector B) := by
    change mixedMoment B node1713 node1713Labels = _
    exact sound1713 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1604, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h822, h1654, h1713, h1737, h4069, reducedSource1366] using sourceEq1604 B hB

theorem rowSound1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1366 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1366, numericCheck1366, reducedZero1366 B hB hF, mul_zero]

theorem reducedZero1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1367 (mixedVector B) = 0 := by
  have h1125 : mixedVector B (Sum.inr 1125) = Sparse.eval nodeValue1125 (mixedVector B) := by
    change mixedMoment B node1125 node1125Labels = _
    exact sound1125 B hB hF
  have h1128 : mixedVector B (Sum.inr 1128) = Sparse.eval nodeValue1128 (mixedVector B) := by
    change mixedMoment B node1128 node1128Labels = _
    exact sound1128 B hB hF
  have h1133 : mixedVector B (Sum.inr 1133) = Sparse.eval nodeValue1133 (mixedVector B) := by
    change mixedMoment B node1133 node1133Labels = _
    exact sound1133 B hB hF
  have h1234 : mixedVector B (Sum.inr 1234) = Sparse.eval nodeValue1234 (mixedVector B) := by
    change mixedMoment B node1234 node1234Labels = _
    exact sound1234 B hB hF
  have h2509 : mixedVector B (Sum.inr 2509) = Sparse.eval nodeValue2509 (mixedVector B) := by
    change mixedMoment B node2509 node2509Labels = _
    exact sound2509 B hB hF
  have h4084 : mixedVector B (Sum.inr 4084) = Sparse.eval nodeValue4084 (mixedVector B) := by
    change mixedMoment B node4084 node4084Labels = _
    exact sound4084 B hB hF
  simpa only [sourceForm1606, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1125, h1128, h1133, h1234, h2509, h4084, reducedSource1367] using sourceEq1606 B hB

theorem rowSound1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1367 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1367, numericCheck1367, reducedZero1367 B hB hF, mul_zero]

theorem reducedZero1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1368 (mixedVector B) = 0 := by
  have h651 : mixedVector B (Sum.inr 651) = Sparse.eval nodeValue651 (mixedVector B) := by
    change mixedMoment B node651 node651Labels = _
    exact sound651 B hB hF
  have h1169 : mixedVector B (Sum.inr 1169) = Sparse.eval nodeValue1169 (mixedVector B) := by
    change mixedMoment B node1169 node1169Labels = _
    exact sound1169 B hB hF
  have h1270 : mixedVector B (Sum.inr 1270) = Sparse.eval nodeValue1270 (mixedVector B) := by
    change mixedMoment B node1270 node1270Labels = _
    exact sound1270 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1607, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h651, h1169, h1270, h1293, h4091, reducedSource1368] using sourceEq1607 B hB

theorem rowSound1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1368 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1368, numericCheck1368, reducedZero1368 B hB hF, mul_zero]

theorem reducedZero1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1369 (mixedVector B) = 0 := by
  have h1654 : mixedVector B (Sum.inr 1654) = Sparse.eval nodeValue1654 (mixedVector B) := by
    change mixedMoment B node1654 node1654Labels = _
    exact sound1654 B hB hF
  have h1656 : mixedVector B (Sum.inr 1656) = Sparse.eval nodeValue1656 (mixedVector B) := by
    change mixedMoment B node1656 node1656Labels = _
    exact sound1656 B hB hF
  have h1658 : mixedVector B (Sum.inr 1658) = Sparse.eval nodeValue1658 (mixedVector B) := by
    change mixedMoment B node1658 node1658Labels = _
    exact sound1658 B hB hF
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1608, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1654, h1656, h1658, h1737, h2702, h4069, reducedSource1369] using sourceEq1608 B hB

theorem rowSound1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1369 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1369, numericCheck1369, reducedZero1369 B hB hF, mul_zero]

theorem reducedZero1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1370 (mixedVector B) = 0 := by
  have h1710 : mixedVector B (Sum.inr 1710) = Sparse.eval nodeValue1710 (mixedVector B) := by
    change mixedMoment B node1710 node1710Labels = _
    exact sound1710 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h2737 : mixedVector B (Sum.inr 2737) = Sparse.eval nodeValue2737 (mixedVector B) := by
    change mixedMoment B node2737 node2737Labels = _
    exact sound2737 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1609, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1710, h2702, h2737, h3308, h4069, reducedSource1370] using sourceEq1609 B hB

theorem rowSound1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1370 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1370, numericCheck1370, reducedZero1370 B hB hF, mul_zero]

theorem reducedZero1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1371 (mixedVector B) = 0 := by
  have h1602 : mixedVector B (Sum.inr 1602) = Sparse.eval nodeValue1602 (mixedVector B) := by
    change mixedMoment B node1602 node1602Labels = _
    exact sound1602 B hB hF
  have h2457 : mixedVector B (Sum.inr 2457) = Sparse.eval nodeValue2457 (mixedVector B) := by
    change mixedMoment B node2457 node2457Labels = _
    exact sound2457 B hB hF
  have h2466 : mixedVector B (Sum.inr 2466) = Sparse.eval nodeValue2466 (mixedVector B) := by
    change mixedMoment B node2466 node2466Labels = _
    exact sound2466 B hB hF
  have h2502 : mixedVector B (Sum.inr 2502) = Sparse.eval nodeValue2502 (mixedVector B) := by
    change mixedMoment B node2502 node2502Labels = _
    exact sound2502 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1610, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1602, h2457, h2466, h2502, h2702, h3293, h4069, reducedSource1371] using sourceEq1610 B hB

theorem rowSound1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1371 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1371, numericCheck1371, reducedZero1371 B hB hF, mul_zero]

theorem reducedZero1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1372 (mixedVector B) = 0 := by
  have h1737 : mixedVector B (Sum.inr 1737) = Sparse.eval nodeValue1737 (mixedVector B) := by
    change mixedMoment B node1737 node1737Labels = _
    exact sound1737 B hB hF
  have h2702 : mixedVector B (Sum.inr 2702) = Sparse.eval nodeValue2702 (mixedVector B) := by
    change mixedMoment B node2702 node2702Labels = _
    exact sound2702 B hB hF
  have h3288 : mixedVector B (Sum.inr 3288) = Sparse.eval nodeValue3288 (mixedVector B) := by
    change mixedMoment B node3288 node3288Labels = _
    exact sound3288 B hB hF
  have h3293 : mixedVector B (Sum.inr 3293) = Sparse.eval nodeValue3293 (mixedVector B) := by
    change mixedMoment B node3293 node3293Labels = _
    exact sound3293 B hB hF
  have h3308 : mixedVector B (Sum.inr 3308) = Sparse.eval nodeValue3308 (mixedVector B) := by
    change mixedMoment B node3308 node3308Labels = _
    exact sound3308 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1611, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1737, h2702, h3288, h3293, h3308, h4069, reducedSource1372] using sourceEq1611 B hB

theorem rowSound1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1372 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1372, numericCheck1372, reducedZero1372 B hB hF, mul_zero]

theorem reducedZero1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1373 (mixedVector B) = 0 := by
  have h1127 : mixedVector B (Sum.inr 1127) = Sparse.eval nodeValue1127 (mixedVector B) := by
    change mixedMoment B node1127 node1127Labels = _
    exact sound1127 B hB hF
  have h1132 : mixedVector B (Sum.inr 1132) = Sparse.eval nodeValue1132 (mixedVector B) := by
    change mixedMoment B node1132 node1132Labels = _
    exact sound1132 B hB hF
  have h1134 : mixedVector B (Sum.inr 1134) = Sparse.eval nodeValue1134 (mixedVector B) := by
    change mixedMoment B node1134 node1134Labels = _
    exact sound1134 B hB hF
  have h1141 : mixedVector B (Sum.inr 1141) = Sparse.eval nodeValue1141 (mixedVector B) := by
    change mixedMoment B node1141 node1141Labels = _
    exact sound1141 B hB hF
  have h1237 : mixedVector B (Sum.inr 1237) = Sparse.eval nodeValue1237 (mixedVector B) := by
    change mixedMoment B node1237 node1237Labels = _
    exact sound1237 B hB hF
  have h2512 : mixedVector B (Sum.inr 2512) = Sparse.eval nodeValue2512 (mixedVector B) := by
    change mixedMoment B node2512 node2512Labels = _
    exact sound2512 B hB hF
  have h4092 : mixedVector B (Sum.inr 4092) = Sparse.eval nodeValue4092 (mixedVector B) := by
    change mixedMoment B node4092 node4092Labels = _
    exact sound4092 B hB hF
  simpa only [sourceForm1612, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1127, h1132, h1134, h1141, h1237, h2512, h4092, reducedSource1373] using sourceEq1612 B hB

theorem rowSound1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1373 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1373, numericCheck1373, reducedZero1373 B hB hF, mul_zero]

theorem reducedZero1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1374 (mixedVector B) = 0 := by
  have h640 : mixedVector B (Sum.inr 640) = Sparse.eval nodeValue640 (mixedVector B) := by
    change mixedMoment B node640 node640Labels = _
    exact sound640 B hB hF
  have h1158 : mixedVector B (Sum.inr 1158) = Sparse.eval nodeValue1158 (mixedVector B) := by
    change mixedMoment B node1158 node1158Labels = _
    exact sound1158 B hB hF
  have h1240 : mixedVector B (Sum.inr 1240) = Sparse.eval nodeValue1240 (mixedVector B) := by
    change mixedMoment B node1240 node1240Labels = _
    exact sound1240 B hB hF
  have h1262 : mixedVector B (Sum.inr 1262) = Sparse.eval nodeValue1262 (mixedVector B) := by
    change mixedMoment B node1262 node1262Labels = _
    exact sound1262 B hB hF
  have h1293 : mixedVector B (Sum.inr 1293) = Sparse.eval nodeValue1293 (mixedVector B) := by
    change mixedMoment B node1293 node1293Labels = _
    exact sound1293 B hB hF
  have h4091 : mixedVector B (Sum.inr 4091) = Sparse.eval nodeValue4091 (mixedVector B) := by
    change mixedMoment B node4091 node4091Labels = _
    exact sound4091 B hB hF
  simpa only [sourceForm1613, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h640, h1158, h1240, h1262, h1293, h4091, reducedSource1374] using sourceEq1613 B hB

theorem rowSound1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1374 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1374, numericCheck1374, reducedZero1374 B hB hF, mul_zero]

theorem reducedZero1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource1375 (mixedVector B) = 0 := by
  have h1642 : mixedVector B (Sum.inr 1642) = Sparse.eval nodeValue1642 (mixedVector B) := by
    change mixedMoment B node1642 node1642Labels = _
    exact sound1642 B hB hF
  have h1645 : mixedVector B (Sum.inr 1645) = Sparse.eval nodeValue1645 (mixedVector B) := by
    change mixedMoment B node1645 node1645Labels = _
    exact sound1645 B hB hF
  have h1646 : mixedVector B (Sum.inr 1646) = Sparse.eval nodeValue1646 (mixedVector B) := by
    change mixedMoment B node1646 node1646Labels = _
    exact sound1646 B hB hF
  have h1649 : mixedVector B (Sum.inr 1649) = Sparse.eval nodeValue1649 (mixedVector B) := by
    change mixedMoment B node1649 node1649Labels = _
    exact sound1649 B hB hF
  have h1724 : mixedVector B (Sum.inr 1724) = Sparse.eval nodeValue1724 (mixedVector B) := by
    change mixedMoment B node1724 node1724Labels = _
    exact sound1724 B hB hF
  have h3294 : mixedVector B (Sum.inr 3294) = Sparse.eval nodeValue3294 (mixedVector B) := by
    change mixedMoment B node3294 node3294Labels = _
    exact sound3294 B hB hF
  have h4069 : mixedVector B (Sum.inr 4069) = Sparse.eval nodeValue4069 (mixedVector B) := by
    change mixedMoment B node4069 node4069Labels = _
    exact sound4069 B hB hF
  simpa only [sourceForm1614, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h1642, h1645, h1646, h1649, h1724, h3294, h4069, reducedSource1375] using sourceEq1614 B hB

theorem rowSound1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row1375 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck1375, numericCheck1375, reducedZero1375 B hB hF, mul_zero]

theorem sourceRowsAt1360 : MixedData.sourceRows (1360 : Fin 2425) =
    MixedData.row1360 := by decide +kernel

theorem sourceRowsAt1361 : MixedData.sourceRows (1361 : Fin 2425) =
    MixedData.row1361 := by decide +kernel

theorem sourceRowsAt1362 : MixedData.sourceRows (1362 : Fin 2425) =
    MixedData.row1362 := by decide +kernel

theorem sourceRowsAt1363 : MixedData.sourceRows (1363 : Fin 2425) =
    MixedData.row1363 := by decide +kernel

theorem sourceRowsAt1364 : MixedData.sourceRows (1364 : Fin 2425) =
    MixedData.row1364 := by decide +kernel

theorem sourceRowsAt1365 : MixedData.sourceRows (1365 : Fin 2425) =
    MixedData.row1365 := by decide +kernel

theorem sourceRowsAt1366 : MixedData.sourceRows (1366 : Fin 2425) =
    MixedData.row1366 := by decide +kernel

theorem sourceRowsAt1367 : MixedData.sourceRows (1367 : Fin 2425) =
    MixedData.row1367 := by decide +kernel

theorem sourceRowsAt1368 : MixedData.sourceRows (1368 : Fin 2425) =
    MixedData.row1368 := by decide +kernel

theorem sourceRowsAt1369 : MixedData.sourceRows (1369 : Fin 2425) =
    MixedData.row1369 := by decide +kernel

theorem sourceRowsAt1370 : MixedData.sourceRows (1370 : Fin 2425) =
    MixedData.row1370 := by decide +kernel

theorem sourceRowsAt1371 : MixedData.sourceRows (1371 : Fin 2425) =
    MixedData.row1371 := by decide +kernel

theorem sourceRowsAt1372 : MixedData.sourceRows (1372 : Fin 2425) =
    MixedData.row1372 := by decide +kernel

theorem sourceRowsAt1373 : MixedData.sourceRows (1373 : Fin 2425) =
    MixedData.row1373 := by decide +kernel

theorem sourceRowsAt1374 : MixedData.sourceRows (1374 : Fin 2425) =
    MixedData.row1374 := by decide +kernel

theorem sourceRowsAt1375 : MixedData.sourceRows (1375 : Fin 2425) =
    MixedData.row1375 := by decide +kernel

theorem chunkSound85_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) (k : Fin 2425)
    (hk : k.val / 16 = 85) :
    Integer.Sparse.eval (MixedData.sourceRows k) (numericVector B) = 0 := by
  have heq : k.val = 1360 ∨ k.val = 1361 ∨ k.val = 1362 ∨ k.val = 1363 ∨ k.val = 1364 ∨ k.val = 1365 ∨ k.val = 1366 ∨ k.val = 1367 ∨ k.val = 1368 ∨ k.val = 1369 ∨ k.val = 1370 ∨ k.val = 1371 ∨ k.val = 1372 ∨ k.val = 1373 ∨ k.val = 1374 ∨ k.val = 1375 := by omega
  rcases heq with h1360 | h1361 | h1362 | h1363 | h1364 | h1365 | h1366 | h1367 | h1368 | h1369 | h1370 | h1371 | h1372 | h1373 | h1374 | h1375
  · have he : k = (1360 : Fin 2425) := Fin.ext h1360
    subst k
    rw [sourceRowsAt1360]
    exact rowSound1360 B hB hF
  · have he : k = (1361 : Fin 2425) := Fin.ext h1361
    subst k
    rw [sourceRowsAt1361]
    exact rowSound1361 B hB hF
  · have he : k = (1362 : Fin 2425) := Fin.ext h1362
    subst k
    rw [sourceRowsAt1362]
    exact rowSound1362 B hB hF
  · have he : k = (1363 : Fin 2425) := Fin.ext h1363
    subst k
    rw [sourceRowsAt1363]
    exact rowSound1363 B hB hF
  · have he : k = (1364 : Fin 2425) := Fin.ext h1364
    subst k
    rw [sourceRowsAt1364]
    exact rowSound1364 B hB hF
  · have he : k = (1365 : Fin 2425) := Fin.ext h1365
    subst k
    rw [sourceRowsAt1365]
    exact rowSound1365 B hB hF
  · have he : k = (1366 : Fin 2425) := Fin.ext h1366
    subst k
    rw [sourceRowsAt1366]
    exact rowSound1366 B hB hF
  · have he : k = (1367 : Fin 2425) := Fin.ext h1367
    subst k
    rw [sourceRowsAt1367]
    exact rowSound1367 B hB hF
  · have he : k = (1368 : Fin 2425) := Fin.ext h1368
    subst k
    rw [sourceRowsAt1368]
    exact rowSound1368 B hB hF
  · have he : k = (1369 : Fin 2425) := Fin.ext h1369
    subst k
    rw [sourceRowsAt1369]
    exact rowSound1369 B hB hF
  · have he : k = (1370 : Fin 2425) := Fin.ext h1370
    subst k
    rw [sourceRowsAt1370]
    exact rowSound1370 B hB hF
  · have he : k = (1371 : Fin 2425) := Fin.ext h1371
    subst k
    rw [sourceRowsAt1371]
    exact rowSound1371 B hB hF
  · have he : k = (1372 : Fin 2425) := Fin.ext h1372
    subst k
    rw [sourceRowsAt1372]
    exact rowSound1372 B hB hF
  · have he : k = (1373 : Fin 2425) := Fin.ext h1373
    subst k
    rw [sourceRowsAt1373]
    exact rowSound1373 B hB hF
  · have he : k = (1374 : Fin 2425) := Fin.ext h1374
    subst k
    rw [sourceRowsAt1374]
    exact rowSound1374 B hB hF
  · have he : k = (1375 : Fin 2425) := Fin.ext h1375
    subst k
    rw [sourceRowsAt1375]
    exact rowSound1375 B hB hF

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.chunkSound85_e_oai
