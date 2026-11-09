-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:53:22.370286+00:00
-- url     : https://prove2.me/submissions/1bae59a8-64fa-4443-b1db-58f623da5845
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E031
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E045
import Definitions.Def_OAIQ106E046
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow26_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEvalRow9_e

section
-- module Solutions.OAIQ106_MUB.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

theorem average_mul (c : ℝ) (f : ι → ℝ) :
    average (fun i => c * f i) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_sum (f : ι → κ → ℝ) :
    average (fun i => ∑ k, f i k) = ∑ k, average (fun i => f i k) := by
  simp only [average, ← Finset.mul_sum]
  rw [Finset.sum_comm]

theorem average_prod (f : ι × κ → ℝ) :
    average f = average (fun i => average (fun k => f (i, k))) := by
  simp only [average, Fintype.card_prod, Nat.cast_mul, mul_inv_rev,
    Fintype.sum_prod_type, ← Finset.mul_sum]
  ring

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
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
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

theorem mixedMoment_label_permutation {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) (σ : Equiv.Perm (Fin l)) :
    mixedMoment B A (σ ∘ label) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  have h (τ : Fin l ↪ Coord) : mixedIntegrand B A (σ ∘ label) r ρ τ =
      mixedIntegrand B A label r ρ (Equiv.embeddingCongr σ.symm (Equiv.refl Coord) τ) := by
    rfl
  simp_rw [h]
  exact average_equiv (Equiv.embeddingCongr σ.symm (Equiv.refl Coord))
    (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)

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

theorem mixedMoment_unused_first_label {p n l : ℕ} (hl : l < 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin l) :
    mixedMoment B A (Fin.succ ∘ label) = mixedMoment B A label := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  change average (fun τ : Fin (l + 1) ↪ Coord =>
    (mixedIntegrand B A label r ρ (Sampling.dropFirst τ)).re) = _
  exact Sampling.average_dropFirst hl
    (fun τ : Fin l ↪ Coord => (mixedIntegrand B A label r ρ τ).re)

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedLabelEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

/-- Injective renaming, including adding unused labels, preserves the moment. -/
theorem mixedMoment_label_embedding {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (e : Fin l ↪ Fin k) (label : Fin n → Fin l) :
    mixedMoment B A (e ∘ label) = mixedMoment B A label := by
  have hcard : l ≤ k := by
    simpa using Fintype.card_le_of_injective e e.injective
  induction k generalizing l with
  | zero =>
      have hl : l = 0 := Nat.eq_zero_of_le_zero hcard
      subst l
      have he : e ∘ label = label := funext fun j => Fin.elim0 (label j)
      rw [he]
  | succ k ih =>
      by_cases hl : l = k + 1
      · subst l
        let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective e
          ⟨e.injective, Finite.surjective_of_injective e.injective⟩
        exact mixedMoment_label_permutation B A label σ
      · have hlk : l ≤ k := by omega
        let f : Fin l ↪ Fin k := Fin.castLEEmb hlk
        obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
          (fun i => (f i).succ) e (fun _ _ h => f.injective (Fin.succ_inj.mp h)) e.injective
        have he : e ∘ label = σ ∘ (Fin.succ ∘ (f ∘ label)) := by
          funext j
          exact (hσ (label j)).symm
        rw [he, mixedMoment_label_permutation,
          mixedMoment_unused_first_label (show k < 6 by omega)]
        exact ih (by omega) f label hlk

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedMoments_MixedShifts
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem mixedIntegrand_three {l : ℕ} (B : Fin 7 → Basis) (a b c : Charge)
    (s t u : Fin l) (r : Fin 7) (ρ : Coord ↪ Coord) (τ : Fin l ↪ Coord) :
    mixedIntegrand B (tripleCharges a b c) ![s, t, u] r ρ τ =
      g (sampledMatrix B r ρ (τ s)) a * g (sampledMatrix B r ρ (τ t)) b *
        g (sampledMatrix B r ρ (τ u)) c := by
  simp [mixedIntegrand, tripleCharges, Fin.prod_univ_succ, rowFourier, g, character,
    sampledMatrix, mul_assoc]

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_AuxiliaryGram
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Auxiliary-column Gram matrices

The functions in manuscript §4 are interpreted, with the same sampled
column in all factors. Real Gram forms are nonnegative for any real positive
semidefinite coefficient matrix. No numerical certificate is assumed here.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix

namespace MUB6

section RealGram
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

lemma realGram_sum_left (F : ι → Ω → ℂ) (G : Ω → ℂ) :
    realGram (fun ω => ∑ i, F i ω) G = ∑ i, realGram (F i) G := by
  simp only [realGram, Finset.sum_mul, Complex.re_sum, average_sum]

lemma realGram_sum_right (F : Ω → ℂ) (G : ι → Ω → ℂ) :
    realGram F (fun ω => ∑ i, G i ω) = ∑ i, realGram F (G i) := by
  simp only [realGram, map_sum, Finset.mul_sum, Complex.re_sum, average_sum]

lemma realGram_smul_left (c : ℝ) (F G : Ω → ℂ) :
    realGram (fun ω => (c : ℂ) * F ω) G = c * realGram F G := by
  simp only [realGram, mul_assoc, Complex.re_ofReal_mul, average_mul]

lemma realGram_smul_right (c : ℝ) (F G : Ω → ℂ) :
    realGram F (fun ω => (c : ℂ) * G ω) = c * realGram F G := by
  simp only [realGram, map_mul, Complex.conj_ofReal]
  simp_rw [mul_left_comm (F _) (c : ℂ), Complex.re_ofReal_mul]
  exact average_mul c _

lemma realGram_weighted_sum {κ : Type*} [Fintype κ]
    (c : ι → ℝ) (d : κ → ℝ) (F : ι → Ω → ℂ) (G : κ → Ω → ℂ) :
    realGram (fun ω => ∑ i, (c i : ℂ) * F i ω)
      (fun ω => ∑ j, (d j : ℂ) * G j ω) =
        ∑ i, ∑ j, c i * d j * realGram (F i) (G j) := by
  simp only [realGram_sum_left, realGram_sum_right, realGram_smul_left,
    realGram_smul_right, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  funext i
  congr 1
  funext j
  ring

lemma realGram_symm (F G : Ω → ℂ) : realGram F G = realGram G F := by
  apply average_congr
  intro ω
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end RealGram

lemma average_column_re (f : Coord → ℂ) :
    average (fun k => (f k).re) = ((6 : ℂ)⁻¹ * ∑ k, f k).re := by
  norm_num [average, Complex.mul_re, Complex.re_sum]

lemma auxiliaryCharacter_product (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (a v : Charge) (ω : AuxiliarySample) :
    auxiliaryCharacter B (-a) ω * conj (auxiliaryCharacter B (-v) ω) =
      auxiliaryCharacter B (v - a) ω := by
  let x : Coord → ℂ := fun i => relativeMatrix B ω.1 (ω.2.2.1 0) (ω.2.1 i) ω.2.2.2
  have hx (i : Coord) : Complex.normSq (x i) = 1 :=
    (relativeMatrix_isHadamard B hB ω.1 _).1 _ _
  change character x (-a) * conj (character x (-v)) = character x (v - a)
  rw [character_neg x hx v, Complex.conj_conj, sub_eq_add_neg,
    character_add x (fun i => unit_ne_zero (hx i))]
  ring

lemma elementaryAuxiliary_product (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Coord) (a v : Charge) (ω : AuxiliarySample) :
    elementaryAuxiliary B s a ω * conj (elementaryAuxiliary B t v ω) =
      rowFourier (relativeMatrix B ω.1 (ω.2.2.1 s)) ω.2.1 a *
      rowFourier (relativeMatrix B ω.1 (ω.2.2.1 t)) ω.2.1 (-v) *
      auxiliaryCharacter B (v - a) ω := by
  simp only [elementaryAuxiliary, map_mul]
  rw [← rowFourier_neg (relativeMatrix_isHadamard B hB ω.1 _) ω.2.1 v]
  have h := auxiliaryCharacter_product B hB a v ω
  calc
    _ = (rowFourier (relativeMatrix B ω.1 (ω.2.2.1 s)) ω.2.1 a *
        rowFourier (relativeMatrix B ω.1 (ω.2.2.1 t)) ω.2.1 (-v)) *
        (auxiliaryCharacter B (-a) ω * conj (auxiliaryCharacter B (-v) ω)) := by ring
    _ = _ := by rw [h]

lemma elementaryAuxiliary_column_average (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Coord) (a v : Charge) (r : Fin 7) (ρ τ : Coord ↪ Coord) :
    average (fun k => (elementaryAuxiliary B s a (r, ρ, τ, k) *
      conj (elementaryAuxiliary B t v (r, ρ, τ, k))).re) =
      (rowFourier (relativeMatrix B r (τ s)) ρ a *
        rowFourier (relativeMatrix B r (τ t)) ρ (-v) *
        rowFourier (relativeMatrix B r (τ 0)) ρ (v - a)).re := by
  simp_rw [elementaryAuxiliary_product B hB]
  rw [average_column_re]
  simp only [auxiliaryCharacter, rowFourier, character]
  rw [← Finset.mul_sum]
  congr 1
  ring

/-- Integrating out the common column gives a three-factor mixed moment. -/
theorem elementaryAuxiliary_gram (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Coord) (a v : Charge) :
    realGram (elementaryAuxiliary B s a) (elementaryAuxiliary B t v) =
      mixedMoment B (gramCharges a v) (gramLabels s t) := by
  simp only [realGram, average_prod]
  unfold mixedMoment
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  rw [elementaryAuxiliary_column_average B hB]
  change _ = (mixedIntegrand B (tripleCharges a (-v) (v - a)) ![s, t, 0] r ρ τ).re
  rw [mixedIntegrand_three]
  rfl

private lemma pair_labels_relabel (B : Fin 7 → Basis) (a v : Charge)
    (q : Fin 3 → Fin 2) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (pairLabelEmbedding s ∘ q) =
      mixedMoment B (gramCharges a v) (pairLabelEmbedding 0 ∘ q) :=
  (mixedMoment_label_embedding (by decide) B _ (pairLabelEmbedding s) q).trans
    (mixedMoment_label_embedding (by decide) B _ (pairLabelEmbedding 0) q).symm

lemma gramMoment_zero_succ (B : Fin 7 → Basis) (a v : Charge) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (gramLabels 0 s.succ) =
      mixedMoment B (gramCharges a v) (gramLabels 0 1) := by
  have h := pair_labels_relabel B a v ![1, 0, 1] s
  have hs : pairLabelEmbedding s ∘ ![1, 0, 1] = gramLabels 0 s.succ := by
    funext j
    fin_cases j <;> rfl
  have h0 : pairLabelEmbedding 0 ∘ ![1, 0, 1] = gramLabels 0 1 := by
    funext j
    fin_cases j <;> rfl
  rwa [hs, h0] at h

lemma gramMoment_succ_zero (B : Fin 7 → Basis) (a v : Charge) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (gramLabels s.succ 0) =
      mixedMoment B (gramCharges a v) (gramLabels 1 0) := by
  have h := pair_labels_relabel B a v ![0, 1, 1] s
  have hs : pairLabelEmbedding s ∘ ![0, 1, 1] = gramLabels s.succ 0 := by
    funext j
    fin_cases j <;> rfl
  have h0 : pairLabelEmbedding 0 ∘ ![0, 1, 1] = gramLabels 1 0 := by
    funext j
    fin_cases j <;> rfl
  rwa [hs, h0] at h

lemma gramMoment_succ_self (B : Fin 7 → Basis) (a v : Charge) (s : Fin 5) :
    mixedMoment B (gramCharges a v) (gramLabels s.succ s.succ) =
      mixedMoment B (gramCharges a v) (gramLabels 1 1) := by
  have h := pair_labels_relabel B a v ![0, 0, 1] s
  have hs : pairLabelEmbedding s ∘ ![0, 0, 1] = gramLabels s.succ s.succ := by
    funext j
    fin_cases j <;> rfl
  have h0 : pairLabelEmbedding 0 ∘ ![0, 0, 1] = gramLabels 1 1 := by
    funext j
    fin_cases j <;> rfl
  rwa [hs, h0] at h

lemma gramMoment_succ_distinct (B : Fin 7 → Basis) (a v : Charge) (s t : Fin 5)
    (hst : s ≠ t) :
    mixedMoment B (gramCharges a v) (gramLabels s.succ t.succ) =
      mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
  have h := mixedMoment_label_embedding (by decide) B (gramCharges a v)
    (tripleLabelEmbedding s t hst) id
  have h0 := mixedMoment_label_embedding (by decide) B (gramCharges a v)
    (tripleLabelEmbedding 0 1 (by decide)) id
  exact h.trans h0.symm

lemma auxiliaryF_zero (B : Fin 7 → Basis) (a : Charge) :
    auxiliaryF B 0 a = elementaryAuxiliary B 0 a := by simp [auxiliaryF]

lemma auxiliaryF_one (B : Fin 7 → Basis) (a : Charge) :
    auxiliaryF B 1 a = fun ω => (((5 : ℝ)⁻¹ : ℝ) : ℂ) *
      ∑ s : Fin 5, elementaryAuxiliary B s.succ a ω := by
  simp [auxiliaryF]

/-- The `(0,0)` case of the manuscript Gram formula. -/
theorem auxiliaryGram_zero_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 0 a) (auxiliaryF B 0 v) =
      mixedMoment B (gramCharges a v) (gramLabels 0 0) := by
  rw [auxiliaryF_zero, auxiliaryF_zero, elementaryAuxiliary_gram B hB]

/-- The `(0,1)` case of the manuscript Gram formula. -/
theorem auxiliaryGram_zero_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 0 a) (auxiliaryF B 1 v) =
      mixedMoment B (gramCharges a v) (gramLabels 0 1) := by
  rw [auxiliaryF_zero, auxiliaryF_one, realGram_smul_right, realGram_sum_right]
  simp_rw [elementaryAuxiliary_gram B hB, gramMoment_zero_succ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The `(1,0)` case of the manuscript Gram formula. -/
theorem auxiliaryGram_one_zero (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 1 a) (auxiliaryF B 0 v) =
      mixedMoment B (gramCharges a v) (gramLabels 1 0) := by
  rw [auxiliaryF_one, auxiliaryF_zero, realGram_smul_left, realGram_sum_left]
  simp_rw [elementaryAuxiliary_gram B hB, gramMoment_succ_zero]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma five_by_five_same_different (A C : ℝ) :
    (∑ s : Fin 5, ∑ t : Fin 5, if s = t then A else C) = 5 * A + 20 * C := by
  have h (s t : Fin 5) : (if s = t then A else C) = (if s = t then A - C else 0) + C := by
    split_ifs <;> ring
  simp_rw [h, Finset.sum_add_distrib]
  simp
  ring

/-- Five diagonal and twenty off-diagonal choices produce the exact `1/5`
and `4/5` coefficients in the `(1,1)` Gram entry. -/
theorem auxiliaryGram_one_one (B : Fin 7 → Basis) (hB : IsMUBFamily B) (a v : Charge) :
    realGram (auxiliaryF B 1 a) (auxiliaryF B 1 v) =
      (1 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 1) +
      (4 / 5 : ℝ) * mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
  rw [auxiliaryF_one, auxiliaryF_one, realGram_smul_left, realGram_smul_right,
    realGram_sum_left]
  simp_rw [realGram_sum_right, elementaryAuxiliary_gram B hB]
  have h (s t : Fin 5) : mixedMoment B (gramCharges a v) (gramLabels s.succ t.succ) =
      if s = t then mixedMoment B (gramCharges a v) (gramLabels 1 1)
      else mixedMoment B (gramCharges a v) (gramLabels 1 2) := by
    by_cases hst : s = t
    · subst t
      rw [ite_eq_left rfl]
      exact gramMoment_succ_self B a v s
    · rw [ite_eq_right hst]
      exact gramMoment_succ_distinct B a v s t hst
  simp_rw [h]
  rw [five_by_five_same_different]
  ring

/-- A uniform statement of all three entries other than `(1,1)`. -/
theorem auxiliaryGram_other (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (hst : ¬ (s = 1 ∧ t = 1)) (a v : Charge) :
    realGram (auxiliaryF B s a) (auxiliaryF B t v) =
      mixedMoment B (gramCharges a v)
        (gramLabels (Fin.castLE (by decide : 2 ≤ 6) s) (Fin.castLE (by decide : 2 ≤ 6) t)) := by
  fin_cases s <;> fin_cases t
  · exact auxiliaryGram_zero_zero B hB a v
  · exact auxiliaryGram_zero_one B hB a v
  · exact auxiliaryGram_one_zero B hB a v
  · exact (hst ⟨rfl, rfl⟩).elim

theorem auxiliaryGram_eq (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    realGram (auxiliaryF B s a) (auxiliaryF B t v) =
      auxiliaryMixedEntry B s t a v := by
  unfold auxiliaryMixedEntry
  split_ifs with hst
  · rcases hst with ⟨rfl, rfl⟩
    exact auxiliaryGram_one_one B hB a v
  · exact auxiliaryGram_other B hB s t hst a v

end MUB6

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_AuxiliaryInterpretation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Interpreting the certificate's expanded auxiliary functions

The integer tagged terms are ordinary finite linear combinations of the
manuscript's two auxiliary functions. Their real Gram products expand into
the exact mixed-moment expressions used by the certificate. Positive
semidefiniteness of a coefficient matrix proves nonnegativity independently
of how its entries or its finite lists of terms were obtained.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramFunctions

theorem LinearForm.auxiliaryEval_gram (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) :
    realGram (P.auxiliaryEval B) (Q.auxiliaryEval B) = P.mixedGram Q B := by
  unfold LinearForm.auxiliaryEval LinearForm.eval LinearForm.mixedGram
  have hcast (z : ℤ) : (z : ℂ) = ((z : ℝ) : ℂ) := by norm_cast
  simp_rw [hcast]
  rw [realGram_weighted_sum]
  simp_rw [auxiliaryGram_eq B hB]

end MUB6.Certificate.GramFunctions

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_CompareMerge
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse collection needs only a computable comparison, not order axioms.
The comparison changes the representation but never its real evaluation. -/
namespace MUB6.Certificate.Integer.Sparse

variable {ι : Type*} [DecidableEq ι]

theorem eval_mergeByFuel (less : ι → ι → Bool) (fuel : ℕ)
    (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeByFuel less fuel a b) x = eval a x + eval b x := by
  induction fuel generalizing a b with
  | zero => simp [mergeByFuel]
  | succ fuel ih =>
    cases a with
    | nil => simp [mergeByFuel]
    | cons a as =>
      cases b with
      | nil => simp [mergeByFuel]
      | cons b bs =>
        simp only [mergeByFuel]
        split_ifs with hlt heq hz
        · simp only [eval_cons, ih]
          ring
        · simp only [ih, eval_cons]
          have hc : (a.2 : ℝ) + (b.2 : ℝ) = 0 := by exact_mod_cast hz
          have hcx := congrArg (fun z : ℝ => z * x b.1) hc
          simp only [add_mul, zero_mul] at hcx
          rw [heq]
          linarith
        · simp only [eval_cons, ih, Int.cast_add]
          rw [heq]
          ring
        · simp only [eval_cons, ih]
          ring

@[simp] theorem eval_mergeBy (less : ι → ι → Bool) (a b : Sparse ι) (x : ι → ℝ) :
    eval (mergeBy less a b) x = eval a x + eval b x := eval_mergeByFuel _ _ _ _ _

omit [DecidableEq ι] in
theorem eval_flatten (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval vs.flatten x = (vs.map (fun v => eval v x)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem eval_mergePairs (less : ι → ι → Bool) (vs : List (Sparse ι)) (x : ι → ℝ) :
    ((mergePairs less vs).map (fun v => eval v x)).sum =
      (vs.map (fun v => eval v x)).sum := by
  induction vs using mergePairs.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a b rest ih => simp [mergePairs, ih, add_assoc]

theorem eval_collectLevels (less : ι → ι → Bool) (fuel : ℕ)
    (vs : List (Sparse ι)) (x : ι → ℝ) :
    eval (collectLevels less fuel vs) x = (vs.map (fun v => eval v x)).sum := by
  induction fuel generalizing vs with
  | zero => exact eval_flatten vs x
  | succ fuel ih =>
    cases vs with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => simp [collectLevels]
      | cons b rest =>
        rw [collectLevels, ih, eval_mergePairs]

@[simp] theorem eval_collectBalanced (less : ι → ι → Bool) (v : Sparse ι) (x : ι → ℝ) :
    eval (collectBalanced less v) x = eval v x := by
  rw [collectBalanced, eval_collectLevels]
  simp [eval, Function.comp_def]

end MUB6.Certificate.Integer.Sparse

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Moments_GramNormalization
attribute [-simp] _root_.OAI.MUB6.fixZeroPermutation_succ _root_.OAI.MUB6.fixZeroPermutation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row permutation and symmetry normalization of auxiliary Gram terms.
The normalizer is executable, but its interpretation theorem is an ordinary
proof valid for arbitrary complex mutually unbiased bases. -/

open scoped BigOperators

namespace MUB6.GramNormalization

theorem orderedKey_leftCharge (s t : Fin 2) (a v : Charge) :
    (orderedKey s t a v).leftCharge = a ∘ rowPermutation a v := by
  funext i
  have hi : i.val < (rowOrder a v).length := by rw [rowOrder_length]; exact i.isLt
  simp [Key.leftCharge, orderedKey, List.getD_eq_getElem?_getD, hi,
    rowPermutation, Equiv.ofBijective, rowAt]

theorem orderedKey_rightCharge (s t : Fin 2) (a v : Charge) :
    (orderedKey s t a v).rightCharge = v ∘ rowPermutation a v := by
  funext i
  have hi : i.val < (rowOrder a v).length := by rw [rowOrder_length]; exact i.isLt
  simp [Key.rightCharge, orderedKey, List.getD_eq_getElem?_getD, hi,
    rowPermutation, Equiv.ofBijective, rowAt]

theorem auxiliaryMixedEntry_row_permutation (B : Fin 7 → Basis)
    (s t : Fin 2) (a v : Charge) (π : Equiv.Perm Coord) :
    auxiliaryMixedEntry B s t (a ∘ π) (v ∘ π) = auxiliaryMixedEntry B s t a v := by
  have h : gramCharges (a ∘ π) (v ∘ π) = fun i j => gramCharges a v (π i) j := rfl
  simp only [auxiliaryMixedEntry, h, mixedMoment_row_permutation]

theorem auxiliaryMixedEntry_symm (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    auxiliaryMixedEntry B s t a v = auxiliaryMixedEntry B t s v a := by
  rw [← auxiliaryGram_eq B hB, ← auxiliaryGram_eq B hB, realGram_symm]

theorem eval_orderedKey (B : Fin 7 → Basis) (s t : Fin 2) (a v : Charge) :
    eval B (orderedKey s t a v) = auxiliaryMixedEntry B s t a v := by
  unfold eval
  rw [orderedKey_leftCharge, orderedKey_rightCharge]
  exact auxiliaryMixedEntry_row_permutation B s t a v (rowPermutation a v)

theorem eval_normalize (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (s t : Fin 2) (a v : Charge) :
    eval B (normalize s t a v) = auxiliaryMixedEntry B s t a v := by
  unfold normalize
  split <;> rw [eval_orderedKey]
  exact auxiliaryMixedEntry_symm B hB t s v a

end MUB6.GramNormalization

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_Certificate_GramPolynomial
attribute [-simp] _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_reindex _root_.OAI.MUB6.Certificate.Integer.Sparse.eval_toRational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite auxiliary Gram products interpreted as sparse normalized keys. -/
namespace MUB6.Certificate.GramPolynomial

open GramFunctions GramNormalization
open scoped BigOperators

theorem normalizedRow_eval (s : Fin 2) (a : Charge) (Q : LinearForm)
    (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (normalizedRow s a Q) (GramNormalization.eval B) =
      ∑ j, ((Q.terms j).coefficient : ℝ) *
        auxiliaryMixedEntry B s (Q.terms j).tag a (Q.terms j).charge := by
  simp [normalizedRow, Integer.Sparse.eval, List.map_ofFn, List.sum_ofFn,
    GramNormalization.eval_normalize B hB]

theorem mixedGram_eq_rows (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) :
    P.mixedGram Q B = ∑ i, ((P.terms i).coefficient : ℝ) *
      Integer.Sparse.eval (normalizedRow (P.terms i).tag (P.terms i).charge Q)
        (GramNormalization.eval B) := by
  simp_rw [normalizedRow_eval _ _ _ B hB, Finset.mul_sum]
  unfold LinearForm.mixedGram
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mixedGram_symm (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) : P.mixedGram Q B = Q.mixedGram P B := by
  rw [← LinearForm.auxiliaryEval_gram P Q B hB,
    ← LinearForm.auxiliaryEval_gram Q P B hB, realGram_symm]

theorem collectWeightedRows_eval {n : ℕ} (rows : Fin n → Integer.Sparse Key)
    (weights : Fin n → ℤ) (x : Key → ℝ) :
    Integer.Sparse.eval
      (Integer.Sparse.collectLevels keyLess n
        (List.ofFn fun i => Integer.Sparse.scale (weights i) (rows i))) x =
      ∑ i, (weights i : ℝ) * Integer.Sparse.eval (rows i) x := by
  rw [Integer.Sparse.eval_collectLevels]
  simp [List.map_ofFn, List.sum_ofFn]

end MUB6.Certificate.GramPolynomial

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block119
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12206 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form0 = rawRow12206 := by decide +kernel

theorem rowCheck12206 : row12206 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12206 := by decide +kernel

theorem rowEval12206 (x : Key → ℝ) : Integer.Sparse.eval row12206 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12206, Integer.Sparse.eval_collectBalanced, rawRowCheck12206]

theorem rawRowCheck12207 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form0 = rawRow12207 := by decide +kernel

theorem rowCheck12207 : row12207 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12207 := by decide +kernel

theorem rowEval12207 (x : Key → ℝ) : Integer.Sparse.eval row12207 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12207, Integer.Sparse.eval_collectBalanced, rawRowCheck12207]

theorem rawRowCheck12208 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form0 = rawRow12208 := by decide +kernel

theorem rowCheck12208 : row12208 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12208 := by decide +kernel

theorem rowEval12208 (x : Key → ℝ) : Integer.Sparse.eval row12208 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12208, Integer.Sparse.eval_collectBalanced, rawRowCheck12208]

theorem rawRowCheck12209 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form0 = rawRow12209 := by decide +kernel

theorem rowCheck12209 : row12209 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12209 := by decide +kernel

theorem rowEval12209 (x : Key → ℝ) : Integer.Sparse.eval row12209 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form0) x := by
  rw [rowCheck12209, Integer.Sparse.eval_collectBalanced, rawRowCheck12209]

theorem rawRowCheck12210 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form0 = rawRow12210 := by decide +kernel

theorem rowCheck12210 : row12210 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12210 := by decide +kernel

theorem rowEval12210 (x : Key → ℝ) : Integer.Sparse.eval row12210 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form0) x := by
  rw [rowCheck12210, Integer.Sparse.eval_collectBalanced, rawRowCheck12210]

theorem rawRowCheck12211 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form1 = rawRow12211 := by decide +kernel

theorem rowCheck12211 : row12211 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12211 := by decide +kernel

theorem rowEval12211 (x : Key → ℝ) : Integer.Sparse.eval row12211 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12211, Integer.Sparse.eval_collectBalanced, rawRowCheck12211]

theorem rawRowCheck12212 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form1 = rawRow12212 := by decide +kernel

theorem rowCheck12212 : row12212 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12212 := by decide +kernel

theorem rowEval12212 (x : Key → ℝ) : Integer.Sparse.eval row12212 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12212, Integer.Sparse.eval_collectBalanced, rawRowCheck12212]

theorem rawRowCheck12213 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form1 = rawRow12213 := by decide +kernel

theorem rowCheck12213 : row12213 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12213 := by decide +kernel

theorem rowEval12213 (x : Key → ℝ) : Integer.Sparse.eval row12213 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12213, Integer.Sparse.eval_collectBalanced, rawRowCheck12213]

theorem rawRowCheck12214 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form1 = rawRow12214 := by decide +kernel

theorem rowCheck12214 : row12214 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12214 := by decide +kernel

theorem rowEval12214 (x : Key → ℝ) : Integer.Sparse.eval row12214 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form1) x := by
  rw [rowCheck12214, Integer.Sparse.eval_collectBalanced, rawRowCheck12214]

theorem rawRowCheck12215 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form1 = rawRow12215 := by decide +kernel

theorem rowCheck12215 : row12215 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12215 := by decide +kernel

theorem rowEval12215 (x : Key → ℝ) : Integer.Sparse.eval row12215 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form1) x := by
  rw [rowCheck12215, Integer.Sparse.eval_collectBalanced, rawRowCheck12215]

theorem rawRowCheck12216 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form2 = rawRow12216 := by decide +kernel

theorem rowCheck12216 : row12216 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12216 := by decide +kernel

theorem rowEval12216 (x : Key → ℝ) : Integer.Sparse.eval row12216 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12216, Integer.Sparse.eval_collectBalanced, rawRowCheck12216]

theorem rawRowCheck12217 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form2 = rawRow12217 := by decide +kernel

theorem rowCheck12217 : row12217 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12217 := by decide +kernel

theorem rowEval12217 (x : Key → ℝ) : Integer.Sparse.eval row12217 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12217, Integer.Sparse.eval_collectBalanced, rawRowCheck12217]

theorem rawRowCheck12218 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form2 = rawRow12218 := by decide +kernel

theorem rowCheck12218 : row12218 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12218 := by decide +kernel

theorem rowEval12218 (x : Key → ℝ) : Integer.Sparse.eval row12218 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12218, Integer.Sparse.eval_collectBalanced, rawRowCheck12218]

theorem rawRowCheck12219 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form2 = rawRow12219 := by decide +kernel

theorem rowCheck12219 : row12219 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12219 := by decide +kernel

theorem rowEval12219 (x : Key → ℝ) : Integer.Sparse.eval row12219 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form2) x := by
  rw [rowCheck12219, Integer.Sparse.eval_collectBalanced, rawRowCheck12219]

theorem rawRowCheck12220 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form2 = rawRow12220 := by decide +kernel

theorem rowCheck12220 : row12220 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12220 := by decide +kernel

theorem rowEval12220 (x : Key → ℝ) : Integer.Sparse.eval row12220 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form2) x := by
  rw [rowCheck12220, Integer.Sparse.eval_collectBalanced, rawRowCheck12220]

theorem rawRowCheck12221 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form3 = rawRow12221 := by decide +kernel

theorem rowCheck12221 : row12221 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12221 := by decide +kernel

theorem rowEval12221 (x : Key → ℝ) : Integer.Sparse.eval row12221 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12221, Integer.Sparse.eval_collectBalanced, rawRowCheck12221]

theorem rawRowCheck12222 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form3 = rawRow12222 := by decide +kernel

theorem rowCheck12222 : row12222 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12222 := by decide +kernel

theorem rowEval12222 (x : Key → ℝ) : Integer.Sparse.eval row12222 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12222, Integer.Sparse.eval_collectBalanced, rawRowCheck12222]

theorem rawRowCheck12223 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form3 = rawRow12223 := by decide +kernel

theorem rowCheck12223 : row12223 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12223 := by decide +kernel

theorem rowEval12223 (x : Key → ℝ) : Integer.Sparse.eval row12223 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12223, Integer.Sparse.eval_collectBalanced, rawRowCheck12223]

theorem rawRowCheck12224 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form3 = rawRow12224 := by decide +kernel

theorem rowCheck12224 : row12224 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12224 := by decide +kernel

theorem rowEval12224 (x : Key → ℝ) : Integer.Sparse.eval row12224 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form3) x := by
  rw [rowCheck12224, Integer.Sparse.eval_collectBalanced, rawRowCheck12224]

theorem rawRowCheck12225 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form3 = rawRow12225 := by decide +kernel

theorem rowCheck12225 : row12225 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12225 := by decide +kernel

theorem rowEval12225 (x : Key → ℝ) : Integer.Sparse.eval row12225 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form3) x := by
  rw [rowCheck12225, Integer.Sparse.eval_collectBalanced, rawRowCheck12225]

theorem rawRowCheck12226 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form4 = rawRow12226 := by decide +kernel

theorem rowCheck12226 : row12226 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12226 := by decide +kernel

theorem rowEval12226 (x : Key → ℝ) : Integer.Sparse.eval row12226 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12226, Integer.Sparse.eval_collectBalanced, rawRowCheck12226]

theorem rawRowCheck12227 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form4 = rawRow12227 := by decide +kernel

theorem rowCheck12227 : row12227 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12227 := by decide +kernel

theorem rowEval12227 (x : Key → ℝ) : Integer.Sparse.eval row12227 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12227, Integer.Sparse.eval_collectBalanced, rawRowCheck12227]

theorem rawRowCheck12228 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form4 = rawRow12228 := by decide +kernel

theorem rowCheck12228 : row12228 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12228 := by decide +kernel

theorem rowEval12228 (x : Key → ℝ) : Integer.Sparse.eval row12228 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12228, Integer.Sparse.eval_collectBalanced, rawRowCheck12228]

theorem rawRowCheck12229 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form4 = rawRow12229 := by decide +kernel

theorem rowCheck12229 : row12229 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12229 := by decide +kernel

theorem rowEval12229 (x : Key → ℝ) : Integer.Sparse.eval row12229 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form4) x := by
  rw [rowCheck12229, Integer.Sparse.eval_collectBalanced, rawRowCheck12229]

theorem rawRowCheck12230 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form4 = rawRow12230 := by decide +kernel

theorem rowCheck12230 : row12230 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12230 := by decide +kernel

theorem rowEval12230 (x : Key → ℝ) : Integer.Sparse.eval row12230 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form4) x := by
  rw [rowCheck12230, Integer.Sparse.eval_collectBalanced, rawRowCheck12230]

theorem rawRowCheck12231 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form5 = rawRow12231 := by decide +kernel

theorem rowCheck12231 : row12231 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12231 := by decide +kernel

theorem rowEval12231 (x : Key → ℝ) : Integer.Sparse.eval row12231 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12231, Integer.Sparse.eval_collectBalanced, rawRowCheck12231]

theorem rawRowCheck12232 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form5 = rawRow12232 := by decide +kernel

theorem rowCheck12232 : row12232 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12232 := by decide +kernel

theorem rowEval12232 (x : Key → ℝ) : Integer.Sparse.eval row12232 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12232, Integer.Sparse.eval_collectBalanced, rawRowCheck12232]

theorem rawRowCheck12233 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form5 = rawRow12233 := by decide +kernel

theorem rowCheck12233 : row12233 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12233 := by decide +kernel

theorem rowEval12233 (x : Key → ℝ) : Integer.Sparse.eval row12233 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12233, Integer.Sparse.eval_collectBalanced, rawRowCheck12233]

theorem rawRowCheck12234 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form5 = rawRow12234 := by decide +kernel

theorem rowCheck12234 : row12234 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12234 := by decide +kernel

theorem rowEval12234 (x : Key → ℝ) : Integer.Sparse.eval row12234 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form5) x := by
  rw [rowCheck12234, Integer.Sparse.eval_collectBalanced, rawRowCheck12234]

theorem rawRowCheck12235 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form5 = rawRow12235 := by decide +kernel

theorem rowCheck12235 : row12235 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12235 := by decide +kernel

theorem rowEval12235 (x : Key → ℝ) : Integer.Sparse.eval row12235 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form5) x := by
  rw [rowCheck12235, Integer.Sparse.eval_collectBalanced, rawRowCheck12235]

theorem rawRowCheck12236 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form6 = rawRow12236 := by decide +kernel

theorem rowCheck12236 : row12236 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12236 := by decide +kernel

theorem rowEval12236 (x : Key → ℝ) : Integer.Sparse.eval row12236 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12236, Integer.Sparse.eval_collectBalanced, rawRowCheck12236]

theorem rawRowCheck12237 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form6 = rawRow12237 := by decide +kernel

theorem rowCheck12237 : row12237 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12237 := by decide +kernel

theorem rowEval12237 (x : Key → ℝ) : Integer.Sparse.eval row12237 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12237, Integer.Sparse.eval_collectBalanced, rawRowCheck12237]

theorem rawRowCheck12238 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form6 = rawRow12238 := by decide +kernel

theorem rowCheck12238 : row12238 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12238 := by decide +kernel

theorem rowEval12238 (x : Key → ℝ) : Integer.Sparse.eval row12238 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12238, Integer.Sparse.eval_collectBalanced, rawRowCheck12238]

theorem rawRowCheck12239 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form6 = rawRow12239 := by decide +kernel

theorem rowCheck12239 : row12239 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12239 := by decide +kernel

theorem rowEval12239 (x : Key → ℝ) : Integer.Sparse.eval row12239 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form6) x := by
  rw [rowCheck12239, Integer.Sparse.eval_collectBalanced, rawRowCheck12239]

theorem rawRowCheck12240 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form6 = rawRow12240 := by decide +kernel

theorem rowCheck12240 : row12240 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12240 := by decide +kernel

theorem rowEval12240 (x : Key → ℝ) : Integer.Sparse.eval row12240 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form6) x := by
  rw [rowCheck12240, Integer.Sparse.eval_collectBalanced, rawRowCheck12240]

theorem rawRowCheck12241 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form7 = rawRow12241 := by decide +kernel

theorem rowCheck12241 : row12241 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12241 := by decide +kernel

theorem rowEval12241 (x : Key → ℝ) : Integer.Sparse.eval row12241 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12241, Integer.Sparse.eval_collectBalanced, rawRowCheck12241]

theorem rawRowCheck12242 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form7 = rawRow12242 := by decide +kernel

theorem rowCheck12242 : row12242 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12242 := by decide +kernel

theorem rowEval12242 (x : Key → ℝ) : Integer.Sparse.eval row12242 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12242, Integer.Sparse.eval_collectBalanced, rawRowCheck12242]

theorem rawRowCheck12243 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form7 = rawRow12243 := by decide +kernel

theorem rowCheck12243 : row12243 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12243 := by decide +kernel

theorem rowEval12243 (x : Key → ℝ) : Integer.Sparse.eval row12243 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12243, Integer.Sparse.eval_collectBalanced, rawRowCheck12243]

theorem rawRowCheck12244 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form7 = rawRow12244 := by decide +kernel

theorem rowCheck12244 : row12244 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12244 := by decide +kernel

theorem rowEval12244 (x : Key → ℝ) : Integer.Sparse.eval row12244 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form7) x := by
  rw [rowCheck12244, Integer.Sparse.eval_collectBalanced, rawRowCheck12244]

theorem rawRowCheck12245 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form7 = rawRow12245 := by decide +kernel

theorem rowCheck12245 : row12245 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12245 := by decide +kernel

theorem rowEval12245 (x : Key → ℝ) : Integer.Sparse.eval row12245 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form7) x := by
  rw [rowCheck12245, Integer.Sparse.eval_collectBalanced, rawRowCheck12245]

theorem rawRowCheck12246 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form8 = rawRow12246 := by decide +kernel

theorem rowCheck12246 : row12246 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12246 := by decide +kernel

theorem rowEval12246 (x : Key → ℝ) : Integer.Sparse.eval row12246 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12246, Integer.Sparse.eval_collectBalanced, rawRowCheck12246]

theorem rawRowCheck12247 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form8 = rawRow12247 := by decide +kernel

theorem rowCheck12247 : row12247 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12247 := by decide +kernel

theorem rowEval12247 (x : Key → ℝ) : Integer.Sparse.eval row12247 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12247, Integer.Sparse.eval_collectBalanced, rawRowCheck12247]

theorem rawRowCheck12248 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form8 = rawRow12248 := by decide +kernel

theorem rowCheck12248 : row12248 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12248 := by decide +kernel

theorem rowEval12248 (x : Key → ℝ) : Integer.Sparse.eval row12248 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12248, Integer.Sparse.eval_collectBalanced, rawRowCheck12248]

theorem rawRowCheck12249 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form8 = rawRow12249 := by decide +kernel

theorem rowCheck12249 : row12249 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12249 := by decide +kernel

theorem rowEval12249 (x : Key → ℝ) : Integer.Sparse.eval row12249 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck12249, Integer.Sparse.eval_collectBalanced, rawRowCheck12249]

theorem rawRowCheck12250 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form8 = rawRow12250 := by decide +kernel

theorem rowCheck12250 : row12250 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12250 := by decide +kernel

theorem rowEval12250 (x : Key → ℝ) : Integer.Sparse.eval row12250 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck12250, Integer.Sparse.eval_collectBalanced, rawRowCheck12250]

theorem rawRowCheck12251 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form9 = rawRow12251 := by decide +kernel

theorem rowCheck12251 : row12251 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12251 := by decide +kernel

theorem rowEval12251 (x : Key → ℝ) : Integer.Sparse.eval row12251 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12251, Integer.Sparse.eval_collectBalanced, rawRowCheck12251]

theorem rawRowCheck12252 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form9 = rawRow12252 := by decide +kernel

theorem rowCheck12252 : row12252 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12252 := by decide +kernel

theorem rowEval12252 (x : Key → ℝ) : Integer.Sparse.eval row12252 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12252, Integer.Sparse.eval_collectBalanced, rawRowCheck12252]

theorem rawRowCheck12253 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form9 = rawRow12253 := by decide +kernel

theorem rowCheck12253 : row12253 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12253 := by decide +kernel

theorem rowEval12253 (x : Key → ℝ) : Integer.Sparse.eval row12253 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12253, Integer.Sparse.eval_collectBalanced, rawRowCheck12253]

theorem rawRowCheck12254 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form9 = rawRow12254 := by decide +kernel

theorem rowCheck12254 : row12254 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12254 := by decide +kernel

theorem rowEval12254 (x : Key → ℝ) : Integer.Sparse.eval row12254 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck12254, Integer.Sparse.eval_collectBalanced, rawRowCheck12254]

theorem rawRowCheck12255 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form9 = rawRow12255 := by decide +kernel

theorem rowCheck12255 : row12255 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12255 := by decide +kernel

theorem rowEval12255 (x : Key → ℝ) : Integer.Sparse.eval row12255 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck12255, Integer.Sparse.eval_collectBalanced, rawRowCheck12255]

theorem rawRowCheck12256 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form10 = rawRow12256 := by decide +kernel

theorem rowCheck12256 : row12256 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12256 := by decide +kernel

theorem rowEval12256 (x : Key → ℝ) : Integer.Sparse.eval row12256 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12256, Integer.Sparse.eval_collectBalanced, rawRowCheck12256]

theorem rawRowCheck12257 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form10 = rawRow12257 := by decide +kernel

theorem rowCheck12257 : row12257 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12257 := by decide +kernel

theorem rowEval12257 (x : Key → ℝ) : Integer.Sparse.eval row12257 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12257, Integer.Sparse.eval_collectBalanced, rawRowCheck12257]

theorem rawRowCheck12258 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form10 = rawRow12258 := by decide +kernel

theorem rowCheck12258 : row12258 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12258 := by decide +kernel

theorem rowEval12258 (x : Key → ℝ) : Integer.Sparse.eval row12258 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12258, Integer.Sparse.eval_collectBalanced, rawRowCheck12258]

theorem rawRowCheck12259 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form10 = rawRow12259 := by decide +kernel

theorem rowCheck12259 : row12259 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12259 := by decide +kernel

theorem rowEval12259 (x : Key → ℝ) : Integer.Sparse.eval row12259 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck12259, Integer.Sparse.eval_collectBalanced, rawRowCheck12259]

theorem rawRowCheck12260 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form10 = rawRow12260 := by decide +kernel

theorem rowCheck12260 : row12260 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12260 := by decide +kernel

theorem rowEval12260 (x : Key → ℝ) : Integer.Sparse.eval row12260 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck12260, Integer.Sparse.eval_collectBalanced, rawRowCheck12260]

theorem rawRowCheck12261 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form11 = rawRow12261 := by decide +kernel

theorem rowCheck12261 : row12261 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12261 := by decide +kernel

theorem rowEval12261 (x : Key → ℝ) : Integer.Sparse.eval row12261 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12261, Integer.Sparse.eval_collectBalanced, rawRowCheck12261]

theorem rawRowCheck12262 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form11 = rawRow12262 := by decide +kernel

theorem rowCheck12262 : row12262 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12262 := by decide +kernel

theorem rowEval12262 (x : Key → ℝ) : Integer.Sparse.eval row12262 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12262, Integer.Sparse.eval_collectBalanced, rawRowCheck12262]

theorem rawRowCheck12263 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form11 = rawRow12263 := by decide +kernel

theorem rowCheck12263 : row12263 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12263 := by decide +kernel

theorem rowEval12263 (x : Key → ℝ) : Integer.Sparse.eval row12263 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12263, Integer.Sparse.eval_collectBalanced, rawRowCheck12263]

theorem rawRowCheck12264 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form11 = rawRow12264 := by decide +kernel

theorem rowCheck12264 : row12264 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12264 := by decide +kernel

theorem rowEval12264 (x : Key → ℝ) : Integer.Sparse.eval row12264 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck12264, Integer.Sparse.eval_collectBalanced, rawRowCheck12264]

theorem rawRowCheck12265 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form11 = rawRow12265 := by decide +kernel

theorem rowCheck12265 : row12265 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12265 := by decide +kernel

theorem rowEval12265 (x : Key → ℝ) : Integer.Sparse.eval row12265 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck12265, Integer.Sparse.eval_collectBalanced, rawRowCheck12265]

theorem rawRowCheck12266 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form12 = rawRow12266 := by decide +kernel

theorem rowCheck12266 : row12266 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12266 := by decide +kernel

theorem rowEval12266 (x : Key → ℝ) : Integer.Sparse.eval row12266 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12266, Integer.Sparse.eval_collectBalanced, rawRowCheck12266]

theorem rawRowCheck12267 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form12 = rawRow12267 := by decide +kernel

theorem rowCheck12267 : row12267 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12267 := by decide +kernel

theorem rowEval12267 (x : Key → ℝ) : Integer.Sparse.eval row12267 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12267, Integer.Sparse.eval_collectBalanced, rawRowCheck12267]

theorem rawRowCheck12268 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form12 = rawRow12268 := by decide +kernel

theorem rowCheck12268 : row12268 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12268 := by decide +kernel

theorem rowEval12268 (x : Key → ℝ) : Integer.Sparse.eval row12268 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12268, Integer.Sparse.eval_collectBalanced, rawRowCheck12268]

theorem rawRowCheck12269 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form12 = rawRow12269 := by decide +kernel

theorem rowCheck12269 : row12269 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12269 := by decide +kernel

theorem rowEval12269 (x : Key → ℝ) : Integer.Sparse.eval row12269 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck12269, Integer.Sparse.eval_collectBalanced, rawRowCheck12269]

theorem rawRowCheck12270 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form12 = rawRow12270 := by decide +kernel

theorem rowCheck12270 : row12270 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12270 := by decide +kernel

theorem rowEval12270 (x : Key → ℝ) : Integer.Sparse.eval row12270 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck12270, Integer.Sparse.eval_collectBalanced, rawRowCheck12270]

theorem rawRowCheck12271 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form13 = rawRow12271 := by decide +kernel

theorem rowCheck12271 : row12271 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12271 := by decide +kernel

theorem rowEval12271 (x : Key → ℝ) : Integer.Sparse.eval row12271 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12271, Integer.Sparse.eval_collectBalanced, rawRowCheck12271]

theorem rawRowCheck12272 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form13 = rawRow12272 := by decide +kernel

theorem rowCheck12272 : row12272 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12272 := by decide +kernel

theorem rowEval12272 (x : Key → ℝ) : Integer.Sparse.eval row12272 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12272, Integer.Sparse.eval_collectBalanced, rawRowCheck12272]

theorem rawRowCheck12273 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form13 = rawRow12273 := by decide +kernel

theorem rowCheck12273 : row12273 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12273 := by decide +kernel

theorem rowEval12273 (x : Key → ℝ) : Integer.Sparse.eval row12273 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12273, Integer.Sparse.eval_collectBalanced, rawRowCheck12273]

theorem rawRowCheck12274 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form13 = rawRow12274 := by decide +kernel

theorem rowCheck12274 : row12274 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12274 := by decide +kernel

theorem rowEval12274 (x : Key → ℝ) : Integer.Sparse.eval row12274 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form13) x := by
  rw [rowCheck12274, Integer.Sparse.eval_collectBalanced, rawRowCheck12274]

theorem rawRowCheck12275 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form13 = rawRow12275 := by decide +kernel

theorem rowCheck12275 : row12275 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12275 := by decide +kernel

theorem rowEval12275 (x : Key → ℝ) : Integer.Sparse.eval row12275 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form13) x := by
  rw [rowCheck12275, Integer.Sparse.eval_collectBalanced, rawRowCheck12275]

theorem rawRowCheck12276 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form14 = rawRow12276 := by decide +kernel

theorem rowCheck12276 : row12276 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12276 := by decide +kernel

theorem rowEval12276 (x : Key → ℝ) : Integer.Sparse.eval row12276 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12276, Integer.Sparse.eval_collectBalanced, rawRowCheck12276]

theorem rawRowCheck12277 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form14 = rawRow12277 := by decide +kernel

theorem rowCheck12277 : row12277 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12277 := by decide +kernel

theorem rowEval12277 (x : Key → ℝ) : Integer.Sparse.eval row12277 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12277, Integer.Sparse.eval_collectBalanced, rawRowCheck12277]

theorem rawRowCheck12278 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form14 = rawRow12278 := by decide +kernel

theorem rowCheck12278 : row12278 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12278 := by decide +kernel

theorem rowEval12278 (x : Key → ℝ) : Integer.Sparse.eval row12278 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12278, Integer.Sparse.eval_collectBalanced, rawRowCheck12278]

theorem rawRowCheck12279 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form14 = rawRow12279 := by decide +kernel

theorem rowCheck12279 : row12279 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12279 := by decide +kernel

theorem rowEval12279 (x : Key → ℝ) : Integer.Sparse.eval row12279 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form14) x := by
  rw [rowCheck12279, Integer.Sparse.eval_collectBalanced, rawRowCheck12279]

theorem rawRowCheck12280 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form14 = rawRow12280 := by decide +kernel

theorem rowCheck12280 : row12280 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12280 := by decide +kernel

theorem rowEval12280 (x : Key → ℝ) : Integer.Sparse.eval row12280 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form14) x := by
  rw [rowCheck12280, Integer.Sparse.eval_collectBalanced, rawRowCheck12280]

theorem rawRowCheck12281 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form15 = rawRow12281 := by decide +kernel

theorem rowCheck12281 : row12281 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12281 := by decide +kernel

theorem rowEval12281 (x : Key → ℝ) : Integer.Sparse.eval row12281 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12281, Integer.Sparse.eval_collectBalanced, rawRowCheck12281]

theorem rawRowCheck12282 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form15 = rawRow12282 := by decide +kernel

theorem rowCheck12282 : row12282 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12282 := by decide +kernel

theorem rowEval12282 (x : Key → ℝ) : Integer.Sparse.eval row12282 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12282, Integer.Sparse.eval_collectBalanced, rawRowCheck12282]

theorem rawRowCheck12283 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form15 = rawRow12283 := by decide +kernel

theorem rowCheck12283 : row12283 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12283 := by decide +kernel

theorem rowEval12283 (x : Key → ℝ) : Integer.Sparse.eval row12283 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12283, Integer.Sparse.eval_collectBalanced, rawRowCheck12283]

theorem rawRowCheck12284 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form15 = rawRow12284 := by decide +kernel

theorem rowCheck12284 : row12284 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12284 := by decide +kernel

theorem rowEval12284 (x : Key → ℝ) : Integer.Sparse.eval row12284 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form15) x := by
  rw [rowCheck12284, Integer.Sparse.eval_collectBalanced, rawRowCheck12284]

theorem rawRowCheck12285 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form15 = rawRow12285 := by decide +kernel

theorem rowCheck12285 : row12285 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12285 := by decide +kernel

theorem rowEval12285 (x : Key → ℝ) : Integer.Sparse.eval row12285 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form15) x := by
  rw [rowCheck12285, Integer.Sparse.eval_collectBalanced, rawRowCheck12285]

theorem rawRowCheck12286 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form16 = rawRow12286 := by decide +kernel

theorem rowCheck12286 : row12286 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12286 := by decide +kernel

theorem rowEval12286 (x : Key → ℝ) : Integer.Sparse.eval row12286 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12286, Integer.Sparse.eval_collectBalanced, rawRowCheck12286]

theorem rawRowCheck12287 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form16 = rawRow12287 := by decide +kernel

theorem rowCheck12287 : row12287 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12287 := by decide +kernel

theorem rowEval12287 (x : Key → ℝ) : Integer.Sparse.eval row12287 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12287, Integer.Sparse.eval_collectBalanced, rawRowCheck12287]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block120
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12288 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form16 = rawRow12288 := by decide +kernel

theorem rowCheck12288 : row12288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12288 := by decide +kernel

theorem rowEval12288 (x : Key → ℝ) : Integer.Sparse.eval row12288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12288, Integer.Sparse.eval_collectBalanced, rawRowCheck12288]

theorem rawRowCheck12289 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form16 = rawRow12289 := by decide +kernel

theorem rowCheck12289 : row12289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12289 := by decide +kernel

theorem rowEval12289 (x : Key → ℝ) : Integer.Sparse.eval row12289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form16) x := by
  rw [rowCheck12289, Integer.Sparse.eval_collectBalanced, rawRowCheck12289]

theorem rawRowCheck12290 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form16 = rawRow12290 := by decide +kernel

theorem rowCheck12290 : row12290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12290 := by decide +kernel

theorem rowEval12290 (x : Key → ℝ) : Integer.Sparse.eval row12290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form16) x := by
  rw [rowCheck12290, Integer.Sparse.eval_collectBalanced, rawRowCheck12290]

theorem rawRowCheck12291 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form17 = rawRow12291 := by decide +kernel

theorem rowCheck12291 : row12291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12291 := by decide +kernel

theorem rowEval12291 (x : Key → ℝ) : Integer.Sparse.eval row12291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12291, Integer.Sparse.eval_collectBalanced, rawRowCheck12291]

theorem rawRowCheck12292 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form17 = rawRow12292 := by decide +kernel

theorem rowCheck12292 : row12292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12292 := by decide +kernel

theorem rowEval12292 (x : Key → ℝ) : Integer.Sparse.eval row12292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12292, Integer.Sparse.eval_collectBalanced, rawRowCheck12292]

theorem rawRowCheck12293 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form17 = rawRow12293 := by decide +kernel

theorem rowCheck12293 : row12293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12293 := by decide +kernel

theorem rowEval12293 (x : Key → ℝ) : Integer.Sparse.eval row12293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12293, Integer.Sparse.eval_collectBalanced, rawRowCheck12293]

theorem rawRowCheck12294 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form17 = rawRow12294 := by decide +kernel

theorem rowCheck12294 : row12294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12294 := by decide +kernel

theorem rowEval12294 (x : Key → ℝ) : Integer.Sparse.eval row12294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form17) x := by
  rw [rowCheck12294, Integer.Sparse.eval_collectBalanced, rawRowCheck12294]

theorem rawRowCheck12295 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form17 = rawRow12295 := by decide +kernel

theorem rowCheck12295 : row12295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12295 := by decide +kernel

theorem rowEval12295 (x : Key → ℝ) : Integer.Sparse.eval row12295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form17) x := by
  rw [rowCheck12295, Integer.Sparse.eval_collectBalanced, rawRowCheck12295]

theorem rawRowCheck12296 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form18 = rawRow12296 := by decide +kernel

theorem rowCheck12296 : row12296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12296 := by decide +kernel

theorem rowEval12296 (x : Key → ℝ) : Integer.Sparse.eval row12296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12296, Integer.Sparse.eval_collectBalanced, rawRowCheck12296]

theorem rawRowCheck12297 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form18 = rawRow12297 := by decide +kernel

theorem rowCheck12297 : row12297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12297 := by decide +kernel

theorem rowEval12297 (x : Key → ℝ) : Integer.Sparse.eval row12297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12297, Integer.Sparse.eval_collectBalanced, rawRowCheck12297]

theorem rawRowCheck12298 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form18 = rawRow12298 := by decide +kernel

theorem rowCheck12298 : row12298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12298 := by decide +kernel

theorem rowEval12298 (x : Key → ℝ) : Integer.Sparse.eval row12298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12298, Integer.Sparse.eval_collectBalanced, rawRowCheck12298]

theorem rawRowCheck12299 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form18 = rawRow12299 := by decide +kernel

theorem rowCheck12299 : row12299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12299 := by decide +kernel

theorem rowEval12299 (x : Key → ℝ) : Integer.Sparse.eval row12299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form18) x := by
  rw [rowCheck12299, Integer.Sparse.eval_collectBalanced, rawRowCheck12299]

theorem rawRowCheck12300 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form18 = rawRow12300 := by decide +kernel

theorem rowCheck12300 : row12300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12300 := by decide +kernel

theorem rowEval12300 (x : Key → ℝ) : Integer.Sparse.eval row12300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form18) x := by
  rw [rowCheck12300, Integer.Sparse.eval_collectBalanced, rawRowCheck12300]

theorem rawRowCheck12301 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form19 = rawRow12301 := by decide +kernel

theorem rowCheck12301 : row12301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12301 := by decide +kernel

theorem rowEval12301 (x : Key → ℝ) : Integer.Sparse.eval row12301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12301, Integer.Sparse.eval_collectBalanced, rawRowCheck12301]

theorem rawRowCheck12302 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form19 = rawRow12302 := by decide +kernel

theorem rowCheck12302 : row12302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12302 := by decide +kernel

theorem rowEval12302 (x : Key → ℝ) : Integer.Sparse.eval row12302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12302, Integer.Sparse.eval_collectBalanced, rawRowCheck12302]

theorem rawRowCheck12303 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form19 = rawRow12303 := by decide +kernel

theorem rowCheck12303 : row12303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12303 := by decide +kernel

theorem rowEval12303 (x : Key → ℝ) : Integer.Sparse.eval row12303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12303, Integer.Sparse.eval_collectBalanced, rawRowCheck12303]

theorem rawRowCheck12304 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form19 = rawRow12304 := by decide +kernel

theorem rowCheck12304 : row12304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12304 := by decide +kernel

theorem rowEval12304 (x : Key → ℝ) : Integer.Sparse.eval row12304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form19) x := by
  rw [rowCheck12304, Integer.Sparse.eval_collectBalanced, rawRowCheck12304]

theorem rawRowCheck12305 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form19 = rawRow12305 := by decide +kernel

theorem rowCheck12305 : row12305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12305 := by decide +kernel

theorem rowEval12305 (x : Key → ℝ) : Integer.Sparse.eval row12305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form19) x := by
  rw [rowCheck12305, Integer.Sparse.eval_collectBalanced, rawRowCheck12305]

theorem rawRowCheck12306 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form20 = rawRow12306 := by decide +kernel

theorem rowCheck12306 : row12306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12306 := by decide +kernel

theorem rowEval12306 (x : Key → ℝ) : Integer.Sparse.eval row12306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12306, Integer.Sparse.eval_collectBalanced, rawRowCheck12306]

theorem rawRowCheck12307 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form20 = rawRow12307 := by decide +kernel

theorem rowCheck12307 : row12307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12307 := by decide +kernel

theorem rowEval12307 (x : Key → ℝ) : Integer.Sparse.eval row12307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12307, Integer.Sparse.eval_collectBalanced, rawRowCheck12307]

theorem rawRowCheck12308 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form20 = rawRow12308 := by decide +kernel

theorem rowCheck12308 : row12308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12308 := by decide +kernel

theorem rowEval12308 (x : Key → ℝ) : Integer.Sparse.eval row12308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12308, Integer.Sparse.eval_collectBalanced, rawRowCheck12308]

theorem rawRowCheck12309 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form20 = rawRow12309 := by decide +kernel

theorem rowCheck12309 : row12309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12309 := by decide +kernel

theorem rowEval12309 (x : Key → ℝ) : Integer.Sparse.eval row12309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form20) x := by
  rw [rowCheck12309, Integer.Sparse.eval_collectBalanced, rawRowCheck12309]

theorem rawRowCheck12310 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form20 = rawRow12310 := by decide +kernel

theorem rowCheck12310 : row12310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12310 := by decide +kernel

theorem rowEval12310 (x : Key → ℝ) : Integer.Sparse.eval row12310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form20) x := by
  rw [rowCheck12310, Integer.Sparse.eval_collectBalanced, rawRowCheck12310]

theorem rawRowCheck12311 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form21 = rawRow12311 := by decide +kernel

theorem rowCheck12311 : row12311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12311 := by decide +kernel

theorem rowEval12311 (x : Key → ℝ) : Integer.Sparse.eval row12311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12311, Integer.Sparse.eval_collectBalanced, rawRowCheck12311]

theorem rawRowCheck12312 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form21 = rawRow12312 := by decide +kernel

theorem rowCheck12312 : row12312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12312 := by decide +kernel

theorem rowEval12312 (x : Key → ℝ) : Integer.Sparse.eval row12312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12312, Integer.Sparse.eval_collectBalanced, rawRowCheck12312]

theorem rawRowCheck12313 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form21 = rawRow12313 := by decide +kernel

theorem rowCheck12313 : row12313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12313 := by decide +kernel

theorem rowEval12313 (x : Key → ℝ) : Integer.Sparse.eval row12313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12313, Integer.Sparse.eval_collectBalanced, rawRowCheck12313]

theorem rawRowCheck12314 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form21 = rawRow12314 := by decide +kernel

theorem rowCheck12314 : row12314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12314 := by decide +kernel

theorem rowEval12314 (x : Key → ℝ) : Integer.Sparse.eval row12314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form21) x := by
  rw [rowCheck12314, Integer.Sparse.eval_collectBalanced, rawRowCheck12314]

theorem rawRowCheck12315 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form21 = rawRow12315 := by decide +kernel

theorem rowCheck12315 : row12315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12315 := by decide +kernel

theorem rowEval12315 (x : Key → ℝ) : Integer.Sparse.eval row12315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form21) x := by
  rw [rowCheck12315, Integer.Sparse.eval_collectBalanced, rawRowCheck12315]

theorem rawRowCheck12316 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form22 = rawRow12316 := by decide +kernel

theorem rowCheck12316 : row12316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12316 := by decide +kernel

theorem rowEval12316 (x : Key → ℝ) : Integer.Sparse.eval row12316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12316, Integer.Sparse.eval_collectBalanced, rawRowCheck12316]

theorem rawRowCheck12317 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form22 = rawRow12317 := by decide +kernel

theorem rowCheck12317 : row12317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12317 := by decide +kernel

theorem rowEval12317 (x : Key → ℝ) : Integer.Sparse.eval row12317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12317, Integer.Sparse.eval_collectBalanced, rawRowCheck12317]

theorem rawRowCheck12318 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form22 = rawRow12318 := by decide +kernel

theorem rowCheck12318 : row12318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12318 := by decide +kernel

theorem rowEval12318 (x : Key → ℝ) : Integer.Sparse.eval row12318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12318, Integer.Sparse.eval_collectBalanced, rawRowCheck12318]

theorem rawRowCheck12319 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form22 = rawRow12319 := by decide +kernel

theorem rowCheck12319 : row12319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12319 := by decide +kernel

theorem rowEval12319 (x : Key → ℝ) : Integer.Sparse.eval row12319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form22) x := by
  rw [rowCheck12319, Integer.Sparse.eval_collectBalanced, rawRowCheck12319]

theorem rawRowCheck12320 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form22 = rawRow12320 := by decide +kernel

theorem rowCheck12320 : row12320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12320 := by decide +kernel

theorem rowEval12320 (x : Key → ℝ) : Integer.Sparse.eval row12320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form22) x := by
  rw [rowCheck12320, Integer.Sparse.eval_collectBalanced, rawRowCheck12320]

theorem rawRowCheck12321 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form23 = rawRow12321 := by decide +kernel

theorem rowCheck12321 : row12321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12321 := by decide +kernel

theorem rowEval12321 (x : Key → ℝ) : Integer.Sparse.eval row12321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12321, Integer.Sparse.eval_collectBalanced, rawRowCheck12321]

theorem rawRowCheck12322 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form23 = rawRow12322 := by decide +kernel

theorem rowCheck12322 : row12322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12322 := by decide +kernel

theorem rowEval12322 (x : Key → ℝ) : Integer.Sparse.eval row12322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12322, Integer.Sparse.eval_collectBalanced, rawRowCheck12322]

theorem rawRowCheck12323 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form23 = rawRow12323 := by decide +kernel

theorem rowCheck12323 : row12323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12323 := by decide +kernel

theorem rowEval12323 (x : Key → ℝ) : Integer.Sparse.eval row12323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12323, Integer.Sparse.eval_collectBalanced, rawRowCheck12323]

theorem rawRowCheck12324 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form23 = rawRow12324 := by decide +kernel

theorem rowCheck12324 : row12324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12324 := by decide +kernel

theorem rowEval12324 (x : Key → ℝ) : Integer.Sparse.eval row12324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form23) x := by
  rw [rowCheck12324, Integer.Sparse.eval_collectBalanced, rawRowCheck12324]

theorem rawRowCheck12325 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form23 = rawRow12325 := by decide +kernel

theorem rowCheck12325 : row12325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12325 := by decide +kernel

theorem rowEval12325 (x : Key → ℝ) : Integer.Sparse.eval row12325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form23) x := by
  rw [rowCheck12325, Integer.Sparse.eval_collectBalanced, rawRowCheck12325]

theorem rawRowCheck12326 : GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form24 = rawRow12326 := by decide +kernel

theorem rowCheck12326 : row12326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12326 := by decide +kernel

theorem rowEval12326 (x : Key → ℝ) : Integer.Sparse.eval row12326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, -2, 0, 0, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12326, Integer.Sparse.eval_collectBalanced, rawRowCheck12326]

theorem rawRowCheck12327 : GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form24 = rawRow12327 := by decide +kernel

theorem rowCheck12327 : row12327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12327 := by decide +kernel

theorem rowEval12327 (x : Key → ℝ) : Integer.Sparse.eval row12327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, -2, 0, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12327, Integer.Sparse.eval_collectBalanced, rawRowCheck12327]

theorem rawRowCheck12328 : GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form24 = rawRow12328 := by decide +kernel

theorem rowCheck12328 : row12328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12328 := by decide +kernel

theorem rowEval12328 (x : Key → ℝ) : Integer.Sparse.eval row12328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, -2, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12328, Integer.Sparse.eval_collectBalanced, rawRowCheck12328]

theorem rawRowCheck12329 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form24 = rawRow12329 := by decide +kernel

theorem rowCheck12329 : row12329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12329 := by decide +kernel

theorem rowEval12329 (x : Key → ℝ) : Integer.Sparse.eval row12329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12329, Integer.Sparse.eval_collectBalanced, rawRowCheck12329]

theorem rawRowCheck12330 : GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form24 = rawRow12330 := by decide +kernel

theorem rowCheck12330 : row12330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12330 := by decide +kernel

theorem rowEval12330 (x : Key → ℝ) : Integer.Sparse.eval row12330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![2, 0, 0, 0, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck12330, Integer.Sparse.eval_collectBalanced, rawRowCheck12330]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck24_0 : entry24_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_0 k)) := by decide +kernel

theorem rowsSound24_0 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form0) x := by
  fin_cases k
  · exact rowEval12206 x
  · exact rowEval12207 x
  · exact rowEval12208 x
  · exact rowEval12209 x
  · exact rowEval12210 x

theorem entryEval24_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_0 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form0 B := by
  rw [entryCheck24_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_0]

theorem entryCheck24_1 : entry24_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_1 k)) := by decide +kernel

theorem rowsSound24_1 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form1) x := by
  fin_cases k
  · exact rowEval12211 x
  · exact rowEval12212 x
  · exact rowEval12213 x
  · exact rowEval12214 x
  · exact rowEval12215 x

theorem entryEval24_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_1 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form1 B := by
  rw [entryCheck24_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_1]

theorem entryCheck24_2 : entry24_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_2 k)) := by decide +kernel

theorem rowsSound24_2 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form2) x := by
  fin_cases k
  · exact rowEval12216 x
  · exact rowEval12217 x
  · exact rowEval12218 x
  · exact rowEval12219 x
  · exact rowEval12220 x

theorem entryEval24_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_2 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form2 B := by
  rw [entryCheck24_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_2]

theorem entryCheck24_3 : entry24_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_3 k)) := by decide +kernel

theorem rowsSound24_3 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form3) x := by
  fin_cases k
  · exact rowEval12221 x
  · exact rowEval12222 x
  · exact rowEval12223 x
  · exact rowEval12224 x
  · exact rowEval12225 x

theorem entryEval24_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_3 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form3 B := by
  rw [entryCheck24_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_3]

theorem entryCheck24_4 : entry24_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_4 k)) := by decide +kernel

theorem rowsSound24_4 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form4) x := by
  fin_cases k
  · exact rowEval12226 x
  · exact rowEval12227 x
  · exact rowEval12228 x
  · exact rowEval12229 x
  · exact rowEval12230 x

theorem entryEval24_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_4 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form4 B := by
  rw [entryCheck24_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_4]

theorem entryCheck24_5 : entry24_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_5 k)) := by decide +kernel

theorem rowsSound24_5 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form5) x := by
  fin_cases k
  · exact rowEval12231 x
  · exact rowEval12232 x
  · exact rowEval12233 x
  · exact rowEval12234 x
  · exact rowEval12235 x

theorem entryEval24_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_5 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form5 B := by
  rw [entryCheck24_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_5]

theorem entryCheck24_6 : entry24_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_6 k)) := by decide +kernel

theorem rowsSound24_6 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form6) x := by
  fin_cases k
  · exact rowEval12236 x
  · exact rowEval12237 x
  · exact rowEval12238 x
  · exact rowEval12239 x
  · exact rowEval12240 x

theorem entryEval24_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_6 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form6 B := by
  rw [entryCheck24_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_6]

theorem entryCheck24_7 : entry24_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_7 k)) := by decide +kernel

theorem rowsSound24_7 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form7) x := by
  fin_cases k
  · exact rowEval12241 x
  · exact rowEval12242 x
  · exact rowEval12243 x
  · exact rowEval12244 x
  · exact rowEval12245 x

theorem entryEval24_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_7 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form7 B := by
  rw [entryCheck24_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_7]

theorem entryCheck24_8 : entry24_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_8 k)) := by decide +kernel

theorem rowsSound24_8 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form8) x := by
  fin_cases k
  · exact rowEval12246 x
  · exact rowEval12247 x
  · exact rowEval12248 x
  · exact rowEval12249 x
  · exact rowEval12250 x

theorem entryEval24_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_8 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form8 B := by
  rw [entryCheck24_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_8]

theorem entryCheck24_9 : entry24_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_9 k)) := by decide +kernel

theorem rowsSound24_9 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form9) x := by
  fin_cases k
  · exact rowEval12251 x
  · exact rowEval12252 x
  · exact rowEval12253 x
  · exact rowEval12254 x
  · exact rowEval12255 x

theorem entryEval24_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_9 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form9 B := by
  rw [entryCheck24_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_9]

theorem entryCheck24_10 : entry24_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_10 k)) := by decide +kernel

theorem rowsSound24_10 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form10) x := by
  fin_cases k
  · exact rowEval12256 x
  · exact rowEval12257 x
  · exact rowEval12258 x
  · exact rowEval12259 x
  · exact rowEval12260 x

theorem entryEval24_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_10 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form10 B := by
  rw [entryCheck24_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_10]

theorem entryCheck24_11 : entry24_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_11 k)) := by decide +kernel

theorem rowsSound24_11 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form11) x := by
  fin_cases k
  · exact rowEval12261 x
  · exact rowEval12262 x
  · exact rowEval12263 x
  · exact rowEval12264 x
  · exact rowEval12265 x

theorem entryEval24_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_11 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form11 B := by
  rw [entryCheck24_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_11]

theorem entryCheck24_12 : entry24_12 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_12 k)) := by decide +kernel

theorem rowsSound24_12 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_12 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form12) x := by
  fin_cases k
  · exact rowEval12266 x
  · exact rowEval12267 x
  · exact rowEval12268 x
  · exact rowEval12269 x
  · exact rowEval12270 x

theorem entryEval24_12 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_12 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form12 B := by
  rw [entryCheck24_12, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form12 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_12]

theorem entryCheck24_13 : entry24_13 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_13 k)) := by decide +kernel

theorem rowsSound24_13 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_13 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form13) x := by
  fin_cases k
  · exact rowEval12271 x
  · exact rowEval12272 x
  · exact rowEval12273 x
  · exact rowEval12274 x
  · exact rowEval12275 x

theorem entryEval24_13 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_13 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form13 B := by
  rw [entryCheck24_13, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form13 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_13]

theorem entryCheck24_14 : entry24_14 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_14 k)) := by decide +kernel

theorem rowsSound24_14 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_14 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form14) x := by
  fin_cases k
  · exact rowEval12276 x
  · exact rowEval12277 x
  · exact rowEval12278 x
  · exact rowEval12279 x
  · exact rowEval12280 x

theorem entryEval24_14 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_14 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form14 B := by
  rw [entryCheck24_14, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form14 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_14]

theorem entryCheck24_15 : entry24_15 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_15 k)) := by decide +kernel

theorem rowsSound24_15 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_15 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form15) x := by
  fin_cases k
  · exact rowEval12281 x
  · exact rowEval12282 x
  · exact rowEval12283 x
  · exact rowEval12284 x
  · exact rowEval12285 x

theorem entryEval24_15 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_15 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form15 B := by
  rw [entryCheck24_15, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form15 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_15]

theorem entryCheck24_16 : entry24_16 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_16 k)) := by decide +kernel

theorem rowsSound24_16 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_16 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form16) x := by
  fin_cases k
  · exact rowEval12286 x
  · exact rowEval12287 x
  · exact rowEval12288 x
  · exact rowEval12289 x
  · exact rowEval12290 x

theorem entryEval24_16 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_16 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form16 B := by
  rw [entryCheck24_16, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form16 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_16]

theorem entryCheck24_17 : entry24_17 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_17 k)) := by decide +kernel

theorem rowsSound24_17 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_17 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form17) x := by
  fin_cases k
  · exact rowEval12291 x
  · exact rowEval12292 x
  · exact rowEval12293 x
  · exact rowEval12294 x
  · exact rowEval12295 x

theorem entryEval24_17 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_17 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form17 B := by
  rw [entryCheck24_17, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form17 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_17]

theorem entryCheck24_18 : entry24_18 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_18 k)) := by decide +kernel

theorem rowsSound24_18 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_18 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form18) x := by
  fin_cases k
  · exact rowEval12296 x
  · exact rowEval12297 x
  · exact rowEval12298 x
  · exact rowEval12299 x
  · exact rowEval12300 x

theorem entryEval24_18 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_18 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form18 B := by
  rw [entryCheck24_18, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form18 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_18]

theorem entryCheck24_19 : entry24_19 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_19 k)) := by decide +kernel

theorem rowsSound24_19 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_19 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form19) x := by
  fin_cases k
  · exact rowEval12301 x
  · exact rowEval12302 x
  · exact rowEval12303 x
  · exact rowEval12304 x
  · exact rowEval12305 x

theorem entryEval24_19 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_19 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form19 B := by
  rw [entryCheck24_19, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form19 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_19]

theorem entryCheck24_20 : entry24_20 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_20 k)) := by decide +kernel

theorem rowsSound24_20 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_20 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form20) x := by
  fin_cases k
  · exact rowEval12306 x
  · exact rowEval12307 x
  · exact rowEval12308 x
  · exact rowEval12309 x
  · exact rowEval12310 x

theorem entryEval24_20 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_20 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form20 B := by
  rw [entryCheck24_20, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form20 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_20]

theorem entryCheck24_21 : entry24_21 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_21 k)) := by decide +kernel

theorem rowsSound24_21 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_21 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form21) x := by
  fin_cases k
  · exact rowEval12311 x
  · exact rowEval12312 x
  · exact rowEval12313 x
  · exact rowEval12314 x
  · exact rowEval12315 x

theorem entryEval24_21 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_21 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form21 B := by
  rw [entryCheck24_21, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form21 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_21]

theorem entryCheck24_22 : entry24_22 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_22 k)) := by decide +kernel

theorem rowsSound24_22 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_22 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form22) x := by
  fin_cases k
  · exact rowEval12316 x
  · exact rowEval12317 x
  · exact rowEval12318 x
  · exact rowEval12319 x
  · exact rowEval12320 x

theorem entryEval24_22 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_22 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form22 B := by
  rw [entryCheck24_22, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form22 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_22]

theorem entryCheck24_23 : entry24_23 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_23 k)) := by decide +kernel

theorem rowsSound24_23 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_23 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form23) x := by
  fin_cases k
  · exact rowEval12321 x
  · exact rowEval12322 x
  · exact rowEval12323 x
  · exact rowEval12324 x
  · exact rowEval12325 x

theorem entryEval24_23 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_23 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form23 B := by
  rw [entryCheck24_23, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form23 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_23]

theorem entryCheck24_24 : entry24_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form24.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form24.terms k).coefficient) (rows24_24 k)) := by decide +kernel

theorem rowsSound24_24 (k : Fin GramFunctions.Block3.form24.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows24_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form24.terms k).tag (GramFunctions.Block3.form24.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval12326 x
  · exact rowEval12327 x
  · exact rowEval12328 x
  · exact rowEval12329 x
  · exact rowEval12330 x

theorem entryEval24_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry24_24 (GramNormalization.eval B) = GramFunctions.Block3.form24.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck24_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form24 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound24_24]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck12523 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form24 = rawRow12523 := by decide +kernel

theorem rowCheck12523 : row12523 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12523 := by decide +kernel

theorem rowEval12523 (x : Key → ℝ) : Integer.Sparse.eval row12523 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, -1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12523, Integer.Sparse.eval_collectBalanced, rawRowCheck12523]

theorem rawRowCheck12524 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form24 = rawRow12524 := by decide +kernel

theorem rowCheck12524 : row12524 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12524 := by decide +kernel

theorem rowEval12524 (x : Key → ℝ) : Integer.Sparse.eval row12524 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -1, 1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12524, Integer.Sparse.eval_collectBalanced, rawRowCheck12524]

theorem rawRowCheck12525 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form24 = rawRow12525 := by decide +kernel

theorem rowCheck12525 : row12525 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12525 := by decide +kernel

theorem rowEval12525 (x : Key → ℝ) : Integer.Sparse.eval row12525 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12525, Integer.Sparse.eval_collectBalanced, rawRowCheck12525]

theorem rawRowCheck12526 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form24 = rawRow12526 := by decide +kernel

theorem rowCheck12526 : row12526 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12526 := by decide +kernel

theorem rowEval12526 (x : Key → ℝ) : Integer.Sparse.eval row12526 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12526, Integer.Sparse.eval_collectBalanced, rawRowCheck12526]

theorem rawRowCheck12527 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form24 = rawRow12527 := by decide +kernel

theorem rowCheck12527 : row12527 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12527 := by decide +kernel

theorem rowEval12527 (x : Key → ℝ) : Integer.Sparse.eval row12527 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, -1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck12527, Integer.Sparse.eval_collectBalanced, rawRowCheck12527]

theorem rawRowCheck12528 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form24 = rawRow12528 := by decide +kernel

theorem rowCheck12528 : row12528 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12528 := by decide +kernel

theorem rowEval12528 (x : Key → ℝ) : Integer.Sparse.eval row12528 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -1, 0, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12528, Integer.Sparse.eval_collectBalanced, rawRowCheck12528]

theorem rawRowCheck12529 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form24 = rawRow12529 := by decide +kernel

theorem rowCheck12529 : row12529 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12529 := by decide +kernel

theorem rowEval12529 (x : Key → ℝ) : Integer.Sparse.eval row12529 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12529, Integer.Sparse.eval_collectBalanced, rawRowCheck12529]

theorem rawRowCheck12530 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form24 = rawRow12530 := by decide +kernel

theorem rowCheck12530 : row12530 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow12530 := by decide +kernel

theorem rowEval12530 (x : Key → ℝ) : Integer.Sparse.eval row12530 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -1, -1] GramFunctions.Block3.form24) x := by
  rw [rowCheck12530, Integer.Sparse.eval_collectBalanced, rawRowCheck12530]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck25_24 : entry25_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form25.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form25.terms k).coefficient) (rows25_24 k)) := by decide +kernel

theorem rowsSound25_24 (k : Fin GramFunctions.Block3.form25.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows25_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form25.terms k).tag (GramFunctions.Block3.form25.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval12523 x
  · exact rowEval12524 x
  · exact rowEval12525 x
  · exact rowEval12526 x
  · exact rowEval12527 x
  · exact rowEval12528 x
  · exact rowEval12529 x
  · exact rowEval12530 x

theorem entryEval25_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry25_24 (GramNormalization.eval B) = GramFunctions.Block3.form25.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck25_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form25 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound25_24]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block126
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck13115 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form24 = rawRow13115 := by decide +kernel

theorem rowCheck13115 : row13115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13115 := by decide +kernel

theorem rowEval13115 (x : Key → ℝ) : Integer.Sparse.eval row13115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 0, 1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13115, Integer.Sparse.eval_collectBalanced, rawRowCheck13115]

theorem rawRowCheck13116 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form24 = rawRow13116 := by decide +kernel

theorem rowCheck13116 : row13116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13116 := by decide +kernel

theorem rowEval13116 (x : Key → ℝ) : Integer.Sparse.eval row13116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13116, Integer.Sparse.eval_collectBalanced, rawRowCheck13116]

theorem rawRowCheck13117 : GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form24 = rawRow13117 := by decide +kernel

theorem rowCheck13117 : row13117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13117 := by decide +kernel

theorem rowEval13117 (x : Key → ℝ) : Integer.Sparse.eval row13117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, -2, 1, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13117, Integer.Sparse.eval_collectBalanced, rawRowCheck13117]

theorem rawRowCheck13118 : GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form24 = rawRow13118 := by decide +kernel

theorem rowCheck13118 : row13118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13118 := by decide +kernel

theorem rowEval13118 (x : Key → ℝ) : Integer.Sparse.eval row13118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, -2, 1, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13118, Integer.Sparse.eval_collectBalanced, rawRowCheck13118]

theorem rawRowCheck13119 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form24 = rawRow13119 := by decide +kernel

theorem rowCheck13119 : row13119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13119 := by decide +kernel

theorem rowEval13119 (x : Key → ℝ) : Integer.Sparse.eval row13119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13119, Integer.Sparse.eval_collectBalanced, rawRowCheck13119]

theorem rawRowCheck13120 : GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form24 = rawRow13120 := by decide +kernel

theorem rowCheck13120 : row13120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13120 := by decide +kernel

theorem rowEval13120 (x : Key → ℝ) : Integer.Sparse.eval row13120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 0, 1, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13120, Integer.Sparse.eval_collectBalanced, rawRowCheck13120]

theorem rawRowCheck13121 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form24 = rawRow13121 := by decide +kernel

theorem rowCheck13121 : row13121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13121 := by decide +kernel

theorem rowEval13121 (x : Key → ℝ) : Integer.Sparse.eval row13121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13121, Integer.Sparse.eval_collectBalanced, rawRowCheck13121]

theorem rawRowCheck13122 : GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form24 = rawRow13122 := by decide +kernel

theorem rowCheck13122 : row13122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13122 := by decide +kernel

theorem rowEval13122 (x : Key → ℝ) : Integer.Sparse.eval row13122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, -2, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13122, Integer.Sparse.eval_collectBalanced, rawRowCheck13122]

theorem rawRowCheck13123 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form24 = rawRow13123 := by decide +kernel

theorem rowCheck13123 : row13123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13123 := by decide +kernel

theorem rowEval13123 (x : Key → ℝ) : Integer.Sparse.eval row13123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13123, Integer.Sparse.eval_collectBalanced, rawRowCheck13123]

theorem rawRowCheck13124 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form24 = rawRow13124 := by decide +kernel

theorem rowCheck13124 : row13124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13124 := by decide +kernel

theorem rowEval13124 (x : Key → ℝ) : Integer.Sparse.eval row13124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 0, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13124, Integer.Sparse.eval_collectBalanced, rawRowCheck13124]

theorem rawRowCheck13125 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form24 = rawRow13125 := by decide +kernel

theorem rowCheck13125 : row13125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13125 := by decide +kernel

theorem rowEval13125 (x : Key → ℝ) : Integer.Sparse.eval row13125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13125, Integer.Sparse.eval_collectBalanced, rawRowCheck13125]

theorem rawRowCheck13126 : GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form24 = rawRow13126 := by decide +kernel

theorem rowCheck13126 : row13126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13126 := by decide +kernel

theorem rowEval13126 (x : Key → ℝ) : Integer.Sparse.eval row13126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 0, 1, 1, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13126, Integer.Sparse.eval_collectBalanced, rawRowCheck13126]

theorem rawRowCheck13127 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form24 = rawRow13127 := by decide +kernel

theorem rowCheck13127 : row13127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13127 := by decide +kernel

theorem rowEval13127 (x : Key → ℝ) : Integer.Sparse.eval row13127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13127, Integer.Sparse.eval_collectBalanced, rawRowCheck13127]

theorem rawRowCheck13128 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form24 = rawRow13128 := by decide +kernel

theorem rowCheck13128 : row13128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13128 := by decide +kernel

theorem rowEval13128 (x : Key → ℝ) : Integer.Sparse.eval row13128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 0, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13128, Integer.Sparse.eval_collectBalanced, rawRowCheck13128]

theorem rawRowCheck13129 : GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form24 = rawRow13129 := by decide +kernel

theorem rowCheck13129 : row13129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13129 := by decide +kernel

theorem rowEval13129 (x : Key → ℝ) : Integer.Sparse.eval row13129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, -2, 1, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13129, Integer.Sparse.eval_collectBalanced, rawRowCheck13129]

theorem rawRowCheck13130 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form24 = rawRow13130 := by decide +kernel

theorem rowCheck13130 : row13130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13130 := by decide +kernel

theorem rowEval13130 (x : Key → ℝ) : Integer.Sparse.eval row13130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 0, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13130, Integer.Sparse.eval_collectBalanced, rawRowCheck13130]

theorem rawRowCheck13131 : GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form24 = rawRow13131 := by decide +kernel

theorem rowCheck13131 : row13131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13131 := by decide +kernel

theorem rowEval13131 (x : Key → ℝ) : Integer.Sparse.eval row13131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, -2, 1, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13131, Integer.Sparse.eval_collectBalanced, rawRowCheck13131]

theorem rawRowCheck13132 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form24 = rawRow13132 := by decide +kernel

theorem rowCheck13132 : row13132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13132 := by decide +kernel

theorem rowEval13132 (x : Key → ℝ) : Integer.Sparse.eval row13132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, -2, 1] GramFunctions.Block3.form24) x := by
  rw [rowCheck13132, Integer.Sparse.eval_collectBalanced, rawRowCheck13132]

theorem rawRowCheck13133 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form24 = rawRow13133 := by decide +kernel

theorem rowCheck13133 : row13133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13133 := by decide +kernel

theorem rowEval13133 (x : Key → ℝ) : Integer.Sparse.eval row13133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 0, 1, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13133, Integer.Sparse.eval_collectBalanced, rawRowCheck13133]

theorem rawRowCheck13134 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form24 = rawRow13134 := by decide +kernel

theorem rowCheck13134 : row13134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13134 := by decide +kernel

theorem rowEval13134 (x : Key → ℝ) : Integer.Sparse.eval row13134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13134, Integer.Sparse.eval_collectBalanced, rawRowCheck13134]

theorem rawRowCheck13135 : GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form24 = rawRow13135 := by decide +kernel

theorem rowCheck13135 : row13135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13135 := by decide +kernel

theorem rowEval13135 (x : Key → ℝ) : Integer.Sparse.eval row13135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 0, 1, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13135, Integer.Sparse.eval_collectBalanced, rawRowCheck13135]

theorem rawRowCheck13136 : GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form24 = rawRow13136 := by decide +kernel

theorem rowCheck13136 : row13136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13136 := by decide +kernel

theorem rowEval13136 (x : Key → ℝ) : Integer.Sparse.eval row13136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, -2, 0, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13136, Integer.Sparse.eval_collectBalanced, rawRowCheck13136]

theorem rawRowCheck13137 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form24 = rawRow13137 := by decide +kernel

theorem rowCheck13137 : row13137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13137 := by decide +kernel

theorem rowEval13137 (x : Key → ℝ) : Integer.Sparse.eval row13137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, -2, 0] GramFunctions.Block3.form24) x := by
  rw [rowCheck13137, Integer.Sparse.eval_collectBalanced, rawRowCheck13137]

theorem rawRowCheck13138 : GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form24 = rawRow13138 := by decide +kernel

theorem rowCheck13138 : row13138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow13138 := by decide +kernel

theorem rowEval13138 (x : Key → ℝ) : Integer.Sparse.eval row13138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![0, 1, 1, 0, 0, -2] GramFunctions.Block3.form24) x := by
  rw [rowCheck13138, Integer.Sparse.eval_collectBalanced, rawRowCheck13138]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck26_24 : entry26_24 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form26.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form26.terms k).coefficient) (rows26_24 k)) := by decide +kernel

theorem rowsSound26_24 (k : Fin GramFunctions.Block3.form26.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows26_24 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block3.form26.terms k).tag (GramFunctions.Block3.form26.terms k).charge GramFunctions.Block3.form24) x := by
  fin_cases k
  · exact rowEval13115 x
  · exact rowEval13116 x
  · exact rowEval13117 x
  · exact rowEval13118 x
  · exact rowEval13119 x
  · exact rowEval13120 x
  · exact rowEval13121 x
  · exact rowEval13122 x
  · exact rowEval13123 x
  · exact rowEval13124 x
  · exact rowEval13125 x
  · exact rowEval13126 x
  · exact rowEval13127 x
  · exact rowEval13128 x
  · exact rowEval13129 x
  · exact rowEval13130 x
  · exact rowEval13131 x
  · exact rowEval13132 x
  · exact rowEval13133 x
  · exact rowEval13134 x
  · exact rowEval13135 x
  · exact rowEval13136 x
  · exact rowEval13137 x
  · exact rowEval13138 x

theorem entryEval26_24 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry26_24 (GramNormalization.eval B) = GramFunctions.Block3.form26.mixedGram GramFunctions.Block3.form24 B := by
  rw [entryCheck26_24, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block3.form26 GramFunctions.Block3.form24 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound26_24]

end MUB6.Certificate.GramEntries.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

theorem entryEvalRow24 (j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 24 j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms 24).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases j
  · exact entryEval24_0 B hB
  · exact entryEval24_1 B hB
  · exact entryEval24_2 B hB
  · exact entryEval24_3 B hB
  · exact entryEval24_4 B hB
  · exact entryEval24_5 B hB
  · exact entryEval24_6 B hB
  · exact entryEval24_7 B hB
  · exact entryEval24_8 B hB
  · exact entryEval24_9 B hB
  · exact entryEval24_10 B hB
  · exact entryEval24_11 B hB
  · exact entryEval24_12 B hB
  · exact entryEval24_13 B hB
  · exact entryEval24_14 B hB
  · exact entryEval24_15 B hB
  · exact entryEval24_16 B hB
  · exact entryEval24_17 B hB
  · exact entryEval24_18 B hB
  · exact entryEval24_19 B hB
  · exact entryEval24_20 B hB
  · exact entryEval24_21 B hB
  · exact entryEval24_22 B hB
  · exact entryEval24_23 B hB
  · exact entryEval24_24 B hB
  · exact (entryEval25_24 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)
  · exact (entryEval26_24 B hB).trans
      (GramPolynomial.mixedGram_symm _ _ B hB)

theorem entryEval_e_oai (i j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (GramNormalization.eval B) =
      (GramFunctions.Block3.forms i).mixedGram (GramFunctions.Block3.forms j) B := by
  fin_cases i
  · exact entryEvalRow0_e j B hB
  · exact entryEvalRow1_e j B hB
  · exact entryEvalRow2_e j B hB
  · exact entryEvalRow3_e j B hB
  · exact entryEvalRow4_e j B hB
  · exact entryEvalRow5_e j B hB
  · exact entryEvalRow6_e j B hB
  · exact entryEvalRow7_e j B hB
  · exact entryEvalRow8_e j B hB
  · exact entryEvalRow9_e j B hB
  · exact entryEvalRow10_e j B hB
  · exact entryEvalRow11_e j B hB
  · exact entryEvalRow12_e j B hB
  · exact entryEvalRow13_e j B hB
  · exact entryEvalRow14_e j B hB
  · exact entryEvalRow15_e j B hB
  · exact entryEvalRow16_e j B hB
  · exact entryEvalRow17_e j B hB
  · exact entryEvalRow18_e j B hB
  · exact entryEvalRow19_e j B hB
  · exact entryEvalRow20_e j B hB
  · exact entryEvalRow21_e j B hB
  · exact entryEvalRow22_e j B hB
  · exact entryEvalRow23_e j B hB
  · exact entryEvalRow24 j B hB
  · exact entryEvalRow25_e j B hB
  · exact entryEvalRow26_e j B hB

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryEval_e_oai
