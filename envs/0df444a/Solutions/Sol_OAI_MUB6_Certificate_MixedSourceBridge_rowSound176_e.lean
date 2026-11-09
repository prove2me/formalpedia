-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T21:41:21.711444+00:00
-- url     : https://prove2.me/submissions/c422be29-7a06-4c92-a885-97b0703df8fa

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E070
import Definitions.Def_OAIQ106E086
import Definitions.Def_OAIQ106E115
import Definitions.Def_OAIQ106E120
import Definitions.Def_OAIQ106E125
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E170
import Theorems.Thm_OAI_MUB6_Certificate_MixedSemantics_sound3847_e

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

theorem transition_cross_normSq {m : ℕ} (B : Fin m → Basis) (hB : IsMUBFamily B)
    (ref : Basis) (s t : Fin m) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, conj (transition ref (B s) i k) * transition ref (B t) i l) = 6 := by
  rw [transition_column_inner, map_mul, hB s t hst k l]
  norm_num [Complex.normSq_ofNat]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Matrix_OffDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem offDiagSum_add_diag {V : Type*} [AddCommMonoid V] (f : Coord → Coord → V) :
    offDiagSum f + (∑ i, f i i) = ∑ i, ∑ j, f i j := by
  rw [offDiagSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem offDiagSum_sum {V ι : Type*} [AddCommMonoid V] [Fintype ι]
    (f : Coord → Coord → ι → V) :
    offDiagSum (fun i j => ∑ k, f i j k) =
      ∑ k, offDiagSum (fun i j => f i j k) := by
  unfold offDiagSum
  calc
    _ = ∑ i, ∑ k, ∑ j ∈ Finset.univ.erase i, f i j k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem offDiagSum_mul (c : ℂ) (f : Coord → Coord → ℂ) :
    offDiagSum (fun i j => c * f i j) = c * offDiagSum f := by
  simp only [offDiagSum, Finset.mul_sum]

theorem sum_mul_conj (z : Coord → ℂ) :
    (∑ i, ∑ j, z i * conj (z j)) = (Complex.normSq (∑ i, z i) : ℂ) := by
  rw [← Complex.mul_conj, map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_DifferentMatrices
attribute [-simp] _root_.OAI.MUB6.TaoArithmetic.decode_encode _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero _root_.OAI.MUB6.rowFourier_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem difference_reverse (i j : Coord) : difference j i = -difference i j := by
  simp [difference, neg_sub]

theorem cross_character_gram (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1) :
    (∑ i, ∑ j, character x (difference i j) * character y (-difference i j)) =
      (Complex.normSq (∑ i, x i * conj (y i)) : ℂ) := by
  rw [← sum_mul_conj]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [character_neg y hy, character_difference x hx, character_difference y hy]
  simp only [map_mul, starRingEnd_apply, star_star]
  ring

theorem cross_character_offdiag (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1)
    (hc : Complex.normSq (∑ i, x i * conj (y i)) = 6) :
    offDiagSum (fun i j => character x (difference i j) * character y (-difference i j)) = 0 := by
  have h := offDiagSum_add_diag
    (fun i j => character x (difference i j) * character y (-difference i j))
  rw [cross_character_gram x y hx hy, hc] at h
  have hd : (∑ i, character x (difference i i) * character y (-difference i i)) = (6 : ℂ) := by
    simp [difference]
  rw [hd] at h
  exact add_right_cancel (show _ + (6 : ℂ) = 0 + 6 by simpa using h)

theorem weighted_cross_character (x y : Coord → ℂ)
    (hx : ∀ i, Complex.normSq (x i) = 1) (hy : ∀ i, Complex.normSq (y i) = 1)
    (hc : Complex.normSq (∑ i, x i * conj (y i)) = 6) (a b : Charge) :
    offDiagSum (fun i j =>
      character x (a + difference i j) * character y (b + difference j i)) = 0 := by
  have he (i j : Coord) :
      character x (a + difference i j) * character y (b + difference j i) =
        (character x a * character y b) *
          (character x (difference i j) * character y (-difference i j)) := by
    rw [character_add x (fun i => unit_ne_zero (hx i)),
      character_add y (fun i => unit_ne_zero (hy i)), difference_reverse j i]
    ring_nf
  simp_rw [he]
  rw [offDiagSum_mul, cross_character_offdiag x y hx hy hc, mul_zero]

theorem g_product_expand (H K : CMatrix) (a b : Charge) :
    g H a * g K b = (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
      ∑ k, ∑ l, character (fun i => H i k) a * character (fun i => K i l) b := by
  unfold g
  calc
    _ = (6 : ℂ)⁻¹ * (6 : ℂ)⁻¹ *
      ((∑ k, character (fun i => H i k) a) * ∑ l, character (fun i => K i l) b) := by ring
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

/-- The different-matrix Fourier identity from unbiasedness of every pair of
columns. The off-diagonal indexing lists each difference `e_i-e_j` once. -/
theorem different_matrices_identity {H K : CMatrix} (hH : IsHadamard H) (hK : IsHadamard K)
    (hc : ∀ k l, Complex.normSq (∑ i, H i k * conj (K i l)) = 6) (a b : Charge) :
    offDiagSum (fun i j => g H (a + difference i j) * g K (b + difference j i)) = 0 := by
  simp_rw [g_product_expand]
  rw [offDiagSum_mul, offDiagSum_sum]
  simp_rw [offDiagSum_sum]
  have hz : (∑ k, ∑ l, offDiagSum (fun i j =>
      character (fun r => H r k) (a + difference i j) *
        character (fun r => K r l) (b + difference j i))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    exact weighted_cross_character _ _ (fun i => hH.1 i k) (fun i => hK.1 i l) (hc k l) a b
  rw [hz, mul_zero]

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

theorem relativeMatrix_cross (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s t : Coord) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, relativeMatrix B r s i k * conj (relativeMatrix B r t i l)) = 6 := by
  have ht : r.succAbove t ≠ r.succAbove s := by
    intro h
    exact hst (Fin.succAbove_right_injective h.symm)
  simpa only [relativeMatrix, mul_comm] using
    transition_cross_normSq B hB (B r) (r.succAbove t) (r.succAbove s) ht l k

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

theorem average_add (f g : ι → ℝ) :
    average (fun i => f i + g i) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

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

theorem sampledMatrix_cross (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (ρ : Coord ↪ Coord) (s t : Coord) (hst : s ≠ t) (k l : Coord) :
    Complex.normSq (∑ i, sampledMatrix B r ρ s i k * conj (sampledMatrix B r ρ t i l)) = 6 := by
  let e : Equiv.Perm Coord := Equiv.ofBijective ρ
    ⟨ρ.injective, Finite.surjective_of_injective ρ.injective⟩
  change Complex.normSq (∑ i, relativeMatrix B r s (e i) k * conj (relativeMatrix B r t (e i) l)) = 6
  rw [Equiv.sum_comp e (fun i => relativeMatrix B r s i k * conj (relativeMatrix B r t i l))]
  exact relativeMatrix_cross B hB r s t hst k l

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

theorem average_finset_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : ι → κ → ℝ) :
    average (fun i => ∑ k ∈ s, f i k) = ∑ k ∈ s, average (fun i => f i k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => simp only [Finset.sum_insert hk, average_add, ih]

theorem average_offDiagSum {ι : Type*} [Fintype ι] (f : ι → Coord → Coord → ℝ) :
    average (fun k => offDiagSum (f k)) = offDiagSum (fun i j => average (fun k => f k i j)) := by
  simp only [offDiagSum, average_sum, average_finset_sum]

theorem mixedMoment_different {l : ℕ} (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a b c : Charge) (s t u : Fin l) (hst : s ≠ t) :
    offDiagSum (fun i j =>
      mixedMoment B (tripleCharges (a + difference i j) (b + difference j i) c) ![s, t, u]) = 0 := by
  simp only [mixedMoment, ← average_offDiagSum]
  have hz (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
      offDiagSum (fun i j =>
        (mixedIntegrand B (tripleCharges (a + difference i j) (b + difference j i) c)
          ![s, t, u] r ρ τ).re) = 0 := by
    simp only [mixedIntegrand_three, offDiagSum, ← Complex.re_sum, ← Finset.sum_mul]
    change (offDiagSum (fun i j =>
      g (sampledMatrix B r ρ (τ s)) (a + difference i j) *
        g (sampledMatrix B r ρ (τ t)) (b + difference j i)) *
          g (sampledMatrix B r ρ (τ u)) c).re = 0
    rw [different_matrices_identity (sampledMatrix_isHadamard B hB r ρ _)
      (sampledMatrix_isHadamard B hB r ρ _)
      (sampledMatrix_cross B hB r ρ _ _ (fun h => hst (τ.injective h))) a b]
    simp
  simp only [hz, average_zero]

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

theorem canonical5570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5570 raw5570Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw5570 raw5570Labels = mixedMoment B raw5570step0 raw5570step0Labels := by
      have ha : raw5570step0 = (fun i j => raw5570 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5570step0 raw5570; decide +kernel
      have hl : raw5570step0Labels = raw5570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5570 raw5570Labels permutation152 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical5571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5571 raw5571Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw5571 raw5571Labels = mixedMoment B raw5571step0 raw5571step0Labels := by
      have ha : raw5571step0 = (fun i j => raw5571 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5571step0 raw5571; decide +kernel
      have hl : raw5571step0Labels = raw5571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5571 raw5571Labels permutation176 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical5572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5572 raw5572Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw5572 raw5572Labels = mixedMoment B raw5572step0 raw5572step0Labels := by
      have ha : raw5572step0 = (fun i j => raw5572 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5572step0 raw5572; decide +kernel
      have hl : raw5572step0Labels = raw5572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5572 raw5572Labels permutation200 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical5573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5573 raw5573Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw5573 raw5573Labels = mixedMoment B raw5573step0 raw5573step0Labels := by
      have ha : raw5573step0 = (fun i j => raw5573 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5573step0 raw5573; decide +kernel
      have hl : raw5573step0Labels = raw5573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5573 raw5573Labels permutation224 permutation3
    _ = mixedMoment B node3899 node3899Labels := by rfl

theorem canonical5574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5574 raw5574Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw5574 raw5574Labels = mixedMoment B raw5574step0 raw5574step0Labels := by
      have ha : raw5574step0 = (fun i j => raw5574 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5574step0 raw5574; decide +kernel
      have hl : raw5574step0Labels = raw5574Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5574 raw5574Labels permutation153 permutation3
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical5575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5575 raw5575Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw5575 raw5575Labels = mixedMoment B raw5575step0 raw5575step0Labels := by
      have ha : raw5575step0 = (fun i j => raw5575 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5575step0 raw5575; decide +kernel
      have hl : raw5575step0Labels = raw5575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5575 raw5575Labels permutation184 permutation3
    _ = mixedMoment B node784 node784Labels := by rfl

theorem canonical5576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5576 raw5576Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5576 raw5576Labels = mixedMoment B raw5576step0 raw5576step0Labels := by
      have ha : raw5576step0 = (fun i j => raw5576 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5576step0 raw5576; decide +kernel
      have hl : raw5576step0Labels = raw5576Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5576 raw5576Labels permutation184 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5577 raw5577Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5577 raw5577Labels = mixedMoment B raw5577step0 raw5577step0Labels := by
      have ha : raw5577step0 = (fun i j => raw5577 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5577step0 raw5577; decide +kernel
      have hl : raw5577step0Labels = raw5577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5577 raw5577Labels permutation208 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5578 raw5578Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw5578 raw5578Labels = mixedMoment B raw5578step0 raw5578step0Labels := by
      have ha : raw5578step0 = (fun i j => raw5578 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5578step0 raw5578; decide +kernel
      have hl : raw5578step0Labels = raw5578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5578 raw5578Labels permutation232 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical5579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5579 raw5579Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw5579 raw5579Labels = mixedMoment B raw5579step0 raw5579step0Labels := by
      have ha : raw5579step0 = (fun i j => raw5579 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5579step0 raw5579; decide +kernel
      have hl : raw5579step0Labels = raw5579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5579 raw5579Labels permutation187 permutation3
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical5580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5580 raw5580Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw5580 raw5580Labels = mixedMoment B raw5580step0 raw5580step0Labels := by
      have ha : raw5580step0 = (fun i j => raw5580 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5580step0 raw5580; decide +kernel
      have hl : raw5580step0Labels = raw5580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5580 raw5580Labels permutation160 permutation3
    _ = mixedMoment B node784 node784Labels := by rfl

theorem canonical5581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5581 raw5581Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5581 raw5581Labels = mixedMoment B raw5581step0 raw5581step0Labels := by
      have ha : raw5581step0 = (fun i j => raw5581 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5581step0 raw5581; decide +kernel
      have hl : raw5581step0Labels = raw5581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5581 raw5581Labels permutation160 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5582 raw5582Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5582 raw5582Labels = mixedMoment B raw5582step0 raw5582step0Labels := by
      have ha : raw5582step0 = (fun i j => raw5582 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5582step0 raw5582; decide +kernel
      have hl : raw5582step0Labels = raw5582Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5582 raw5582Labels permutation202 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5583 raw5583Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw5583 raw5583Labels = mixedMoment B raw5583step0 raw5583step0Labels := by
      have ha : raw5583step0 = (fun i j => raw5583 (permutation226 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5583step0 raw5583; decide +kernel
      have hl : raw5583step0Labels = raw5583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5583 raw5583Labels permutation226 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical5584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5584 raw5584Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw5584 raw5584Labels = mixedMoment B raw5584step0 raw5584step0Labels := by
      have ha : raw5584step0 = (fun i j => raw5584 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5584step0 raw5584; decide +kernel
      have hl : raw5584step0Labels = raw5584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5584 raw5584Labels permutation163 permutation3
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical5585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5585 raw5585Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw5585 raw5585Labels = mixedMoment B raw5585step0 raw5585step0Labels := by
      have ha : raw5585step0 = (fun i j => raw5585 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5585step0 raw5585; decide +kernel
      have hl : raw5585step0Labels = raw5585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5585 raw5585Labels permutation154 permutation3
    _ = mixedMoment B node784 node784Labels := by rfl

theorem canonical5586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5586 raw5586Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5586 raw5586Labels = mixedMoment B raw5586step0 raw5586step0Labels := by
      have ha : raw5586step0 = (fun i j => raw5586 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5586step0 raw5586; decide +kernel
      have hl : raw5586step0Labels = raw5586Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5586 raw5586Labels permutation154 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5587 raw5587Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5587 raw5587Labels = mixedMoment B raw5587step0 raw5587step0Labels := by
      have ha : raw5587step0 = (fun i j => raw5587 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5587step0 raw5587; decide +kernel
      have hl : raw5587step0Labels = raw5587Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5587 raw5587Labels permutation178 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

theorem canonical5588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5588 raw5588Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw5588 raw5588Labels = mixedMoment B raw5588step0 raw5588step0Labels := by
      have ha : raw5588step0 = (fun i j => raw5588 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5588step0 raw5588; decide +kernel
      have hl : raw5588step0Labels = raw5588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5588 raw5588Labels permutation224 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical5589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5589 raw5589Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw5589 raw5589Labels = mixedMoment B raw5589step0 raw5589step0Labels := by
      have ha : raw5589step0 = (fun i j => raw5589 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5589step0 raw5589; decide +kernel
      have hl : raw5589step0Labels = raw5589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5589 raw5589Labels permutation157 permutation3
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical5590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5590 raw5590Labels = mixedMoment B node778 node778Labels := by
  calc
    mixedMoment B raw5590 raw5590Labels = mixedMoment B raw5590step0 raw5590step0Labels := by
      have ha : raw5590step0 = (fun i j => raw5590 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5590step0 raw5590; decide +kernel
      have hl : raw5590step0Labels = raw5590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5590 raw5590Labels permutation153 permutation3
    _ = mixedMoment B node778 node778Labels := by rfl

theorem canonical5591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5591 raw5591Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw5591 raw5591Labels = mixedMoment B raw5591step0 raw5591step0Labels := by
      have ha : raw5591step0 = (fun i j => raw5591 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5591step0 raw5591; decide +kernel
      have hl : raw5591step0Labels = raw5591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5591 raw5591Labels permutation153 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

theorem canonical5592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5592 raw5592Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw5592 raw5592Labels = mixedMoment B raw5592step0 raw5592step0Labels := by
      have ha : raw5592step0 = (fun i j => raw5592 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5592step0 raw5592; decide +kernel
      have hl : raw5592step0Labels = raw5592Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5592 raw5592Labels permutation177 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

theorem canonical5593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5593 raw5593Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw5593 raw5593Labels = mixedMoment B raw5593step0 raw5593step0Labels := by
      have ha : raw5593step0 = (fun i j => raw5593 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5593step0 raw5593; decide +kernel
      have hl : raw5593step0Labels = raw5593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5593 raw5593Labels permutation201 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

theorem canonical5594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5594 raw5594Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw5594 raw5594Labels = mixedMoment B raw5594step0 raw5594step0Labels := by
      have ha : raw5594step0 = (fun i j => raw5594 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5594step0 raw5594; decide +kernel
      have hl : raw5594step0Labels = raw5594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5594 raw5594Labels permutation153 permutation3
    _ = mixedMoment B node2232 node2232Labels := by rfl

theorem canonical5595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5595 raw5595Labels = mixedMoment B node776 node776Labels := by
  calc
    mixedMoment B raw5595 raw5595Labels = mixedMoment B raw5595step0 raw5595step0Labels := by
      have ha : raw5595step0 = (fun i j => raw5595 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5595step0 raw5595; decide +kernel
      have hl : raw5595step0Labels = raw5595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5595 raw5595Labels permutation152 permutation3
    _ = mixedMoment B node776 node776Labels := by rfl

theorem canonical5596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5596 raw5596Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw5596 raw5596Labels = mixedMoment B raw5596step0 raw5596step0Labels := by
      have ha : raw5596step0 = (fun i j => raw5596 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5596step0 raw5596; decide +kernel
      have hl : raw5596step0Labels = raw5596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5596 raw5596Labels permutation152 permutation3
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical5597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5597 raw5597Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw5597 raw5597Labels = mixedMoment B raw5597step0 raw5597step0Labels := by
      have ha : raw5597step0 = (fun i j => raw5597 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5597step0 raw5597; decide +kernel
      have hl : raw5597step0Labels = raw5597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5597 raw5597Labels permutation176 permutation3
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical5598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5598 raw5598Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw5598 raw5598Labels = mixedMoment B raw5598step0 raw5598step0Labels := by
      have ha : raw5598step0 = (fun i j => raw5598 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5598step0 raw5598; decide +kernel
      have hl : raw5598step0Labels = raw5598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5598 raw5598Labels permutation200 permutation3
    _ = mixedMoment B node2009 node2009Labels := by rfl

theorem canonical5599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5599 raw5599Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw5599 raw5599Labels = mixedMoment B raw5599step0 raw5599step0Labels := by
      have ha : raw5599step0 = (fun i j => raw5599 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5599step0 raw5599; decide +kernel
      have hl : raw5599step0Labels = raw5599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5599 raw5599Labels permutation224 permutation3
    _ = mixedMoment B node2187 node2187Labels := by rfl

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

theorem sound776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node776 node776Labels = Sparse.eval nodeValue776 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 776) = mixedMoment B node776 node776Labels := rfl
  simpa [nodeValue776, Sparse.eval] using hc.symm

theorem sound778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node778 node778Labels = Sparse.eval nodeValue778 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 778) = mixedMoment B node778 node778Labels := rfl
  simpa [nodeValue778, Sparse.eval] using hc.symm

theorem sound784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node784 node784Labels = Sparse.eval nodeValue784 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 784) = mixedMoment B node784 node784Labels := rfl
  simpa [nodeValue784, Sparse.eval] using hc.symm

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

theorem sound2009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2009 node2009Labels = Sparse.eval nodeValue2009 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2009) = mixedMoment B node2009 node2009Labels := rfl
  simpa [nodeValue2009, Sparse.eval] using hc.symm

theorem sound2012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2012 node2012Labels = Sparse.eval nodeValue2012 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2012) = mixedMoment B node2012 node2012Labels := rfl
  simpa [nodeValue2012, Sparse.eval] using hc.symm

theorem sound2021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2021 node2021Labels = Sparse.eval nodeValue2021 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2021) = mixedMoment B node2021 node2021Labels := rfl
  simpa [nodeValue2021, Sparse.eval] using hc.symm

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

theorem sound2187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2187 node2187Labels = Sparse.eval nodeValue2187 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2187) = mixedMoment B node2187 node2187Labels := rfl
  simpa [nodeValue2187, Sparse.eval] using hc.symm

theorem sound2192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2192 node2192Labels = Sparse.eval nodeValue2192 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2192) = mixedMoment B node2192 node2192Labels := rfl
  simpa [nodeValue2192, Sparse.eval] using hc.symm

theorem sound2232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2232 node2232Labels = Sparse.eval nodeValue2232 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2232) = mixedMoment B node2232 node2232Labels := rfl
  simpa [nodeValue2232, Sparse.eval] using hc.symm

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

theorem sound2240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node2240 node2240Labels = Sparse.eval nodeValue2240 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 2240) = mixedMoment B node2240 node2240Labels := rfl
  simpa [nodeValue2240, Sparse.eval] using hc.symm

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Sound61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound3909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node3909 node3909Labels = Sparse.eval nodeValue3909 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 3909) = mixedMoment B node3909 node3909Labels := rfl
  simpa [nodeValue3909, Sparse.eval] using hc.symm

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_SourceRules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.MixedSemantics

theorem offDiagSum_explicit (f : Coord → Coord → ℝ) :
    offDiagSum f =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 +
      f 1 0 + f 1 2 + f 1 3 + f 1 4 + f 1 5 +
      f 2 0 + f 2 1 + f 2 3 + f 2 4 + f 2 5 +
      f 3 0 + f 3 1 + f 3 2 + f 3 4 + f 3 5 +
      f 4 0 + f 4 1 + f 4 2 + f 4 3 + f 4 5 +
      f 5 0 + f 5 1 + f 5 2 + f 5 3 + f 5 4 := by
  unfold offDiagSum
  simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  simp only [Fin.succ, Nat.reduceAdd]
  ring_nf
  rfl

end MUB6.Certificate.MixedSemantics

end

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

theorem sourceEq203 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm203 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA203 + difference 0 1) (sourceB203 + difference 1 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA203 + difference 0 1) (sourceB203 + difference 1 0) sourceC203) = raw5570 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5570; decide +kernel
    rw [ha]
    exact (canonical5570 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA203 + difference 0 2) (sourceB203 + difference 2 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA203 + difference 0 2) (sourceB203 + difference 2 0) sourceC203) = raw5571 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5571; decide +kernel
    rw [ha]
    exact (canonical5571 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA203 + difference 0 3) (sourceB203 + difference 3 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3847) := by
    have ha : (tripleCharges (sourceA203 + difference 0 3) (sourceB203 + difference 3 0) sourceC203) = raw5572 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5572; decide +kernel
    rw [ha]
    exact (canonical5572 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA203 + difference 0 4) (sourceB203 + difference 4 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3899) := by
    have ha : (tripleCharges (sourceA203 + difference 0 4) (sourceB203 + difference 4 0) sourceC203) = raw5573 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5573; decide +kernel
    rw [ha]
    exact (canonical5573 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA203 + difference 0 5) (sourceB203 + difference 5 0) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 3909) := by
    have ha : (tripleCharges (sourceA203 + difference 0 5) (sourceB203 + difference 5 0) sourceC203) = raw5574 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5574; decide +kernel
    rw [ha]
    exact (canonical5574 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA203 + difference 1 0) (sourceB203 + difference 0 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA203 + difference 1 0) (sourceB203 + difference 0 1) sourceC203) = raw5575 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5575; decide +kernel
    rw [ha]
    exact (canonical5575 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA203 + difference 1 2) (sourceB203 + difference 2 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 1 2) (sourceB203 + difference 2 1) sourceC203) = raw5576 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5576; decide +kernel
    rw [ha]
    exact (canonical5576 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA203 + difference 1 3) (sourceB203 + difference 3 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 1 3) (sourceB203 + difference 3 1) sourceC203) = raw5577 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5577; decide +kernel
    rw [ha]
    exact (canonical5577 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA203 + difference 1 4) (sourceB203 + difference 4 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA203 + difference 1 4) (sourceB203 + difference 4 1) sourceC203) = raw5578 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5578; decide +kernel
    rw [ha]
    exact (canonical5578 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA203 + difference 1 5) (sourceB203 + difference 5 1) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA203 + difference 1 5) (sourceB203 + difference 5 1) sourceC203) = raw5579 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5579; decide +kernel
    rw [ha]
    exact (canonical5579 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA203 + difference 2 0) (sourceB203 + difference 0 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA203 + difference 2 0) (sourceB203 + difference 0 2) sourceC203) = raw5580 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5580; decide +kernel
    rw [ha]
    exact (canonical5580 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA203 + difference 2 1) (sourceB203 + difference 1 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 2 1) (sourceB203 + difference 1 2) sourceC203) = raw5581 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5581; decide +kernel
    rw [ha]
    exact (canonical5581 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA203 + difference 2 3) (sourceB203 + difference 3 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 2 3) (sourceB203 + difference 3 2) sourceC203) = raw5582 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5582; decide +kernel
    rw [ha]
    exact (canonical5582 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA203 + difference 2 4) (sourceB203 + difference 4 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA203 + difference 2 4) (sourceB203 + difference 4 2) sourceC203) = raw5583 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5583; decide +kernel
    rw [ha]
    exact (canonical5583 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA203 + difference 2 5) (sourceB203 + difference 5 2) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA203 + difference 2 5) (sourceB203 + difference 5 2) sourceC203) = raw5584 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5584; decide +kernel
    rw [ha]
    exact (canonical5584 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA203 + difference 3 0) (sourceB203 + difference 0 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 784) := by
    have ha : (tripleCharges (sourceA203 + difference 3 0) (sourceB203 + difference 0 3) sourceC203) = raw5585 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5585; decide +kernel
    rw [ha]
    exact (canonical5585 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA203 + difference 3 1) (sourceB203 + difference 1 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 3 1) (sourceB203 + difference 1 3) sourceC203) = raw5586 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5586; decide +kernel
    rw [ha]
    exact (canonical5586 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA203 + difference 3 2) (sourceB203 + difference 2 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2021) := by
    have ha : (tripleCharges (sourceA203 + difference 3 2) (sourceB203 + difference 2 3) sourceC203) = raw5587 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5587; decide +kernel
    rw [ha]
    exact (canonical5587 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA203 + difference 3 4) (sourceB203 + difference 4 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2192) := by
    have ha : (tripleCharges (sourceA203 + difference 3 4) (sourceB203 + difference 4 3) sourceC203) = raw5588 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5588; decide +kernel
    rw [ha]
    exact (canonical5588 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA203 + difference 3 5) (sourceB203 + difference 5 3) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2240) := by
    have ha : (tripleCharges (sourceA203 + difference 3 5) (sourceB203 + difference 5 3) sourceC203) = raw5589 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5589; decide +kernel
    rw [ha]
    exact (canonical5589 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA203 + difference 4 0) (sourceB203 + difference 0 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 778) := by
    have ha : (tripleCharges (sourceA203 + difference 4 0) (sourceB203 + difference 0 4) sourceC203) = raw5590 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5590; decide +kernel
    rw [ha]
    exact (canonical5590 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA203 + difference 4 1) (sourceB203 + difference 1 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA203 + difference 4 1) (sourceB203 + difference 1 4) sourceC203) = raw5591 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5591; decide +kernel
    rw [ha]
    exact (canonical5591 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA203 + difference 4 2) (sourceB203 + difference 2 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA203 + difference 4 2) (sourceB203 + difference 2 4) sourceC203) = raw5592 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5592; decide +kernel
    rw [ha]
    exact (canonical5592 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA203 + difference 4 3) (sourceB203 + difference 3 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2012) := by
    have ha : (tripleCharges (sourceA203 + difference 4 3) (sourceB203 + difference 3 4) sourceC203) = raw5593 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5593; decide +kernel
    rw [ha]
    exact (canonical5593 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA203 + difference 4 5) (sourceB203 + difference 5 4) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2232) := by
    have ha : (tripleCharges (sourceA203 + difference 4 5) (sourceB203 + difference 5 4) sourceC203) = raw5594 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5594; decide +kernel
    rw [ha]
    exact (canonical5594 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA203 + difference 5 0) (sourceB203 + difference 0 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 776) := by
    have ha : (tripleCharges (sourceA203 + difference 5 0) (sourceB203 + difference 0 5) sourceC203) = raw5595 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5595; decide +kernel
    rw [ha]
    exact (canonical5595 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA203 + difference 5 1) (sourceB203 + difference 1 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA203 + difference 5 1) (sourceB203 + difference 1 5) sourceC203) = raw5596 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5596; decide +kernel
    rw [ha]
    exact (canonical5596 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA203 + difference 5 2) (sourceB203 + difference 2 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA203 + difference 5 2) (sourceB203 + difference 2 5) sourceC203) = raw5597 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5597; decide +kernel
    rw [ha]
    exact (canonical5597 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA203 + difference 5 3) (sourceB203 + difference 3 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2009) := by
    have ha : (tripleCharges (sourceA203 + difference 5 3) (sourceB203 + difference 3 5) sourceC203) = raw5598 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5598; decide +kernel
    rw [ha]
    exact (canonical5598 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA203 + difference 5 4) (sourceB203 + difference 4 5) sourceC203) (![0, 1, 0] : Fin 3 → Fin 2) =
      mixedVector B (Sum.inr 2187) := by
    have ha : (tripleCharges (sourceA203 + difference 5 4) (sourceB203 + difference 4 5) sourceC203) = raw5599 := by
      apply Matrix.ext; unfold tripleCharges sourceA203 sourceB203 sourceC203 difference raw5599; decide +kernel
    rw [ha]
    exact (canonical5599 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA203 sourceB203 sourceC203
    (0 : Fin 2) 1 0 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm203, Integer.Sparse.eval]
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

theorem reindexCheck176 : Integer.Sparse.reindex keyMap MixedData.row176 = numericRow176 := by decide +kernel

theorem numericCheck176 (x : Master → ℝ) : Integer.Sparse.eval numericRow176 x =
    (1440 : ℝ) * reducedSource176 x := by
  norm_num [numericRow176, reducedSource176, Integer.Sparse.eval, Sparse.eval, nodeValue776, nodeValue778, nodeValue784, nodeValue2009, nodeValue2012, nodeValue2021, nodeValue2187, nodeValue2192, nodeValue2232, nodeValue2240, nodeValue3847, nodeValue3899, nodeValue3909]
  ring

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

theorem reducedZero176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    reducedSource176 (mixedVector B) = 0 := by
  have h776 : mixedVector B (Sum.inr 776) = Sparse.eval nodeValue776 (mixedVector B) := by
    change mixedMoment B node776 node776Labels = _
    exact sound776 B hB hF
  have h778 : mixedVector B (Sum.inr 778) = Sparse.eval nodeValue778 (mixedVector B) := by
    change mixedMoment B node778 node778Labels = _
    exact sound778 B hB hF
  have h784 : mixedVector B (Sum.inr 784) = Sparse.eval nodeValue784 (mixedVector B) := by
    change mixedMoment B node784 node784Labels = _
    exact sound784 B hB hF
  have h2009 : mixedVector B (Sum.inr 2009) = Sparse.eval nodeValue2009 (mixedVector B) := by
    change mixedMoment B node2009 node2009Labels = _
    exact sound2009 B hB hF
  have h2012 : mixedVector B (Sum.inr 2012) = Sparse.eval nodeValue2012 (mixedVector B) := by
    change mixedMoment B node2012 node2012Labels = _
    exact sound2012 B hB hF
  have h2021 : mixedVector B (Sum.inr 2021) = Sparse.eval nodeValue2021 (mixedVector B) := by
    change mixedMoment B node2021 node2021Labels = _
    exact sound2021 B hB hF
  have h2187 : mixedVector B (Sum.inr 2187) = Sparse.eval nodeValue2187 (mixedVector B) := by
    change mixedMoment B node2187 node2187Labels = _
    exact sound2187 B hB hF
  have h2192 : mixedVector B (Sum.inr 2192) = Sparse.eval nodeValue2192 (mixedVector B) := by
    change mixedMoment B node2192 node2192Labels = _
    exact sound2192 B hB hF
  have h2232 : mixedVector B (Sum.inr 2232) = Sparse.eval nodeValue2232 (mixedVector B) := by
    change mixedMoment B node2232 node2232Labels = _
    exact sound2232 B hB hF
  have h2240 : mixedVector B (Sum.inr 2240) = Sparse.eval nodeValue2240 (mixedVector B) := by
    change mixedMoment B node2240 node2240Labels = _
    exact sound2240 B hB hF
  have h3847 : mixedVector B (Sum.inr 3847) = Sparse.eval nodeValue3847 (mixedVector B) := by
    change mixedMoment B node3847 node3847Labels = _
    exact sound3847_e B hB hF
  have h3899 : mixedVector B (Sum.inr 3899) = Sparse.eval nodeValue3899 (mixedVector B) := by
    change mixedMoment B node3899 node3899Labels = _
    exact sound3899 B hB hF
  have h3909 : mixedVector B (Sum.inr 3909) = Sparse.eval nodeValue3909 (mixedVector B) := by
    change mixedMoment B node3909 node3909Labels = _
    exact sound3909 B hB hF
  simpa only [sourceForm203, Integer.Sparse.eval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Prod.fst, Prod.snd, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero, h776, h778, h784, h2009, h2012, h2021, h2187, h2192, h2232, h2240, h3847, h3899, h3909, reducedSource176] using sourceEq203 B hB

theorem rowSound176_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval MixedData.row176 (numericVector B) = 0 := by
  rw [integer_eval_numericVector, reindexCheck176, numericCheck176, reducedZero176 B hB hF, mul_zero]

end MUB6.Certificate.MixedSourceBridge

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e_oai := @OAI.MUB6.Certificate.MixedSourceBridge.rowSound176_e_oai
