-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:50:33.817866+00:00
-- url     : https://prove2.me/submissions/c2cff605-6e28-464d-978c-305d8eaf5455

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E037
import Definitions.Def_OAIQ106E038
import Definitions.Def_OAIQ106E040
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block5_entryEval11_6_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block177
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19604 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19604 := by decide +kernel

theorem rowCheck19604 : row19604 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19604 := by decide +kernel

theorem rowEval19604 (x : Key → ℝ) : Integer.Sparse.eval row19604 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19604, Integer.Sparse.eval_collectBalanced, rawRowCheck19604]

theorem rawRowCheck19605 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19605 := by decide +kernel

theorem rowCheck19605 : row19605 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19605 := by decide +kernel

theorem rowEval19605 (x : Key → ℝ) : Integer.Sparse.eval row19605 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19605, Integer.Sparse.eval_collectBalanced, rawRowCheck19605]

theorem rawRowCheck19606 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19606 := by decide +kernel

theorem rowCheck19606 : row19606 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19606 := by decide +kernel

theorem rowEval19606 (x : Key → ℝ) : Integer.Sparse.eval row19606 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19606, Integer.Sparse.eval_collectBalanced, rawRowCheck19606]

theorem rawRowCheck19607 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0 = rawRow19607 := by decide +kernel

theorem rowCheck19607 : row19607 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19607 := by decide +kernel

theorem rowEval19607 (x : Key → ℝ) : Integer.Sparse.eval row19607 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19607, Integer.Sparse.eval_collectBalanced, rawRowCheck19607]

theorem rawRowCheck19608 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0 = rawRow19608 := by decide +kernel

theorem rowCheck19608 : row19608 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19608 := by decide +kernel

theorem rowEval19608 (x : Key → ℝ) : Integer.Sparse.eval row19608 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19608, Integer.Sparse.eval_collectBalanced, rawRowCheck19608]

theorem rawRowCheck19609 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0 = rawRow19609 := by decide +kernel

theorem rowCheck19609 : row19609 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19609 := by decide +kernel

theorem rowEval19609 (x : Key → ℝ) : Integer.Sparse.eval row19609 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19609, Integer.Sparse.eval_collectBalanced, rawRowCheck19609]

theorem rawRowCheck19610 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0 = rawRow19610 := by decide +kernel

theorem rowCheck19610 : row19610 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19610 := by decide +kernel

theorem rowEval19610 (x : Key → ℝ) : Integer.Sparse.eval row19610 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19610, Integer.Sparse.eval_collectBalanced, rawRowCheck19610]

theorem rawRowCheck19611 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0 = rawRow19611 := by decide +kernel

theorem rowCheck19611 : row19611 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19611 := by decide +kernel

theorem rowEval19611 (x : Key → ℝ) : Integer.Sparse.eval row19611 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19611, Integer.Sparse.eval_collectBalanced, rawRowCheck19611]

theorem rawRowCheck19612 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0 = rawRow19612 := by decide +kernel

theorem rowCheck19612 : row19612 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19612 := by decide +kernel

theorem rowEval19612 (x : Key → ℝ) : Integer.Sparse.eval row19612 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19612, Integer.Sparse.eval_collectBalanced, rawRowCheck19612]

theorem rawRowCheck19613 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19613 := by decide +kernel

theorem rowCheck19613 : row19613 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19613 := by decide +kernel

theorem rowEval19613 (x : Key → ℝ) : Integer.Sparse.eval row19613 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19613, Integer.Sparse.eval_collectBalanced, rawRowCheck19613]

theorem rawRowCheck19614 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19614 := by decide +kernel

theorem rowCheck19614 : row19614 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19614 := by decide +kernel

theorem rowEval19614 (x : Key → ℝ) : Integer.Sparse.eval row19614 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19614, Integer.Sparse.eval_collectBalanced, rawRowCheck19614]

theorem rawRowCheck19615 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19615 := by decide +kernel

theorem rowCheck19615 : row19615 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19615 := by decide +kernel

theorem rowEval19615 (x : Key → ℝ) : Integer.Sparse.eval row19615 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19615, Integer.Sparse.eval_collectBalanced, rawRowCheck19615]

theorem rawRowCheck19616 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0 = rawRow19616 := by decide +kernel

theorem rowCheck19616 : row19616 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19616 := by decide +kernel

theorem rowEval19616 (x : Key → ℝ) : Integer.Sparse.eval row19616 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19616, Integer.Sparse.eval_collectBalanced, rawRowCheck19616]

theorem rawRowCheck19617 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0 = rawRow19617 := by decide +kernel

theorem rowCheck19617 : row19617 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19617 := by decide +kernel

theorem rowEval19617 (x : Key → ℝ) : Integer.Sparse.eval row19617 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19617, Integer.Sparse.eval_collectBalanced, rawRowCheck19617]

theorem rawRowCheck19618 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0 = rawRow19618 := by decide +kernel

theorem rowCheck19618 : row19618 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19618 := by decide +kernel

theorem rowEval19618 (x : Key → ℝ) : Integer.Sparse.eval row19618 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19618, Integer.Sparse.eval_collectBalanced, rawRowCheck19618]

theorem rawRowCheck19619 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19619 := by decide +kernel

theorem rowCheck19619 : row19619 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19619 := by decide +kernel

theorem rowEval19619 (x : Key → ℝ) : Integer.Sparse.eval row19619 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19619, Integer.Sparse.eval_collectBalanced, rawRowCheck19619]

theorem rawRowCheck19620 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19620 := by decide +kernel

theorem rowCheck19620 : row19620 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19620 := by decide +kernel

theorem rowEval19620 (x : Key → ℝ) : Integer.Sparse.eval row19620 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19620, Integer.Sparse.eval_collectBalanced, rawRowCheck19620]

theorem rawRowCheck19621 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19621 := by decide +kernel

theorem rowCheck19621 : row19621 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19621 := by decide +kernel

theorem rowEval19621 (x : Key → ℝ) : Integer.Sparse.eval row19621 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19621, Integer.Sparse.eval_collectBalanced, rawRowCheck19621]

theorem rawRowCheck19622 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19622 := by decide +kernel

theorem rowCheck19622 : row19622 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19622 := by decide +kernel

theorem rowEval19622 (x : Key → ℝ) : Integer.Sparse.eval row19622 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19622, Integer.Sparse.eval_collectBalanced, rawRowCheck19622]

theorem rawRowCheck19623 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19623 := by decide +kernel

theorem rowCheck19623 : row19623 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19623 := by decide +kernel

theorem rowEval19623 (x : Key → ℝ) : Integer.Sparse.eval row19623 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19623, Integer.Sparse.eval_collectBalanced, rawRowCheck19623]

theorem rawRowCheck19624 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19624 := by decide +kernel

theorem rowCheck19624 : row19624 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19624 := by decide +kernel

theorem rowEval19624 (x : Key → ℝ) : Integer.Sparse.eval row19624 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19624, Integer.Sparse.eval_collectBalanced, rawRowCheck19624]

theorem rawRowCheck19625 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19625 := by decide +kernel

theorem rowCheck19625 : row19625 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19625 := by decide +kernel

theorem rowEval19625 (x : Key → ℝ) : Integer.Sparse.eval row19625 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19625, Integer.Sparse.eval_collectBalanced, rawRowCheck19625]

theorem rawRowCheck19626 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19626 := by decide +kernel

theorem rowCheck19626 : row19626 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19626 := by decide +kernel

theorem rowEval19626 (x : Key → ℝ) : Integer.Sparse.eval row19626 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19626, Integer.Sparse.eval_collectBalanced, rawRowCheck19626]

theorem rawRowCheck19627 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19627 := by decide +kernel

theorem rowCheck19627 : row19627 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19627 := by decide +kernel

theorem rowEval19627 (x : Key → ℝ) : Integer.Sparse.eval row19627 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19627, Integer.Sparse.eval_collectBalanced, rawRowCheck19627]

theorem rawRowCheck19628 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0 = rawRow19628 := by decide +kernel

theorem rowCheck19628 : row19628 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19628 := by decide +kernel

theorem rowEval19628 (x : Key → ℝ) : Integer.Sparse.eval row19628 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19628, Integer.Sparse.eval_collectBalanced, rawRowCheck19628]

theorem rawRowCheck19629 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0 = rawRow19629 := by decide +kernel

theorem rowCheck19629 : row19629 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19629 := by decide +kernel

theorem rowEval19629 (x : Key → ℝ) : Integer.Sparse.eval row19629 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19629, Integer.Sparse.eval_collectBalanced, rawRowCheck19629]

theorem rawRowCheck19630 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0 = rawRow19630 := by decide +kernel

theorem rowCheck19630 : row19630 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19630 := by decide +kernel

theorem rowEval19630 (x : Key → ℝ) : Integer.Sparse.eval row19630 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19630, Integer.Sparse.eval_collectBalanced, rawRowCheck19630]

theorem rawRowCheck19631 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0 = rawRow19631 := by decide +kernel

theorem rowCheck19631 : row19631 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19631 := by decide +kernel

theorem rowEval19631 (x : Key → ℝ) : Integer.Sparse.eval row19631 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19631, Integer.Sparse.eval_collectBalanced, rawRowCheck19631]

theorem rawRowCheck19632 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0 = rawRow19632 := by decide +kernel

theorem rowCheck19632 : row19632 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19632 := by decide +kernel

theorem rowEval19632 (x : Key → ℝ) : Integer.Sparse.eval row19632 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19632, Integer.Sparse.eval_collectBalanced, rawRowCheck19632]

theorem rawRowCheck19633 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0 = rawRow19633 := by decide +kernel

theorem rowCheck19633 : row19633 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19633 := by decide +kernel

theorem rowEval19633 (x : Key → ℝ) : Integer.Sparse.eval row19633 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19633, Integer.Sparse.eval_collectBalanced, rawRowCheck19633]

theorem rawRowCheck19634 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0 = rawRow19634 := by decide +kernel

theorem rowCheck19634 : row19634 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19634 := by decide +kernel

theorem rowEval19634 (x : Key → ℝ) : Integer.Sparse.eval row19634 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19634, Integer.Sparse.eval_collectBalanced, rawRowCheck19634]

theorem rawRowCheck19635 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0 = rawRow19635 := by decide +kernel

theorem rowCheck19635 : row19635 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19635 := by decide +kernel

theorem rowEval19635 (x : Key → ℝ) : Integer.Sparse.eval row19635 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19635, Integer.Sparse.eval_collectBalanced, rawRowCheck19635]

theorem rawRowCheck19636 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0 = rawRow19636 := by decide +kernel

theorem rowCheck19636 : row19636 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19636 := by decide +kernel

theorem rowEval19636 (x : Key → ℝ) : Integer.Sparse.eval row19636 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19636, Integer.Sparse.eval_collectBalanced, rawRowCheck19636]

theorem rawRowCheck19637 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0 = rawRow19637 := by decide +kernel

theorem rowCheck19637 : row19637 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19637 := by decide +kernel

theorem rowEval19637 (x : Key → ℝ) : Integer.Sparse.eval row19637 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19637, Integer.Sparse.eval_collectBalanced, rawRowCheck19637]

theorem rawRowCheck19638 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0 = rawRow19638 := by decide +kernel

theorem rowCheck19638 : row19638 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19638 := by decide +kernel

theorem rowEval19638 (x : Key → ℝ) : Integer.Sparse.eval row19638 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19638, Integer.Sparse.eval_collectBalanced, rawRowCheck19638]

theorem rawRowCheck19639 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0 = rawRow19639 := by decide +kernel

theorem rowCheck19639 : row19639 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19639 := by decide +kernel

theorem rowEval19639 (x : Key → ℝ) : Integer.Sparse.eval row19639 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19639, Integer.Sparse.eval_collectBalanced, rawRowCheck19639]

theorem rawRowCheck19640 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0 = rawRow19640 := by decide +kernel

theorem rowCheck19640 : row19640 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19640 := by decide +kernel

theorem rowEval19640 (x : Key → ℝ) : Integer.Sparse.eval row19640 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19640, Integer.Sparse.eval_collectBalanced, rawRowCheck19640]

theorem rawRowCheck19641 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0 = rawRow19641 := by decide +kernel

theorem rowCheck19641 : row19641 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19641 := by decide +kernel

theorem rowEval19641 (x : Key → ℝ) : Integer.Sparse.eval row19641 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19641, Integer.Sparse.eval_collectBalanced, rawRowCheck19641]

theorem rawRowCheck19642 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0 = rawRow19642 := by decide +kernel

theorem rowCheck19642 : row19642 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19642 := by decide +kernel

theorem rowEval19642 (x : Key → ℝ) : Integer.Sparse.eval row19642 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19642, Integer.Sparse.eval_collectBalanced, rawRowCheck19642]

theorem rawRowCheck19643 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0 = rawRow19643 := by decide +kernel

theorem rowCheck19643 : row19643 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19643 := by decide +kernel

theorem rowEval19643 (x : Key → ℝ) : Integer.Sparse.eval row19643 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19643, Integer.Sparse.eval_collectBalanced, rawRowCheck19643]

theorem rawRowCheck19644 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0 = rawRow19644 := by decide +kernel

theorem rowCheck19644 : row19644 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19644 := by decide +kernel

theorem rowEval19644 (x : Key → ℝ) : Integer.Sparse.eval row19644 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19644, Integer.Sparse.eval_collectBalanced, rawRowCheck19644]

theorem rawRowCheck19645 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0 = rawRow19645 := by decide +kernel

theorem rowCheck19645 : row19645 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19645 := by decide +kernel

theorem rowEval19645 (x : Key → ℝ) : Integer.Sparse.eval row19645 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19645, Integer.Sparse.eval_collectBalanced, rawRowCheck19645]

theorem rawRowCheck19646 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19646 := by decide +kernel

theorem rowCheck19646 : row19646 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19646 := by decide +kernel

theorem rowEval19646 (x : Key → ℝ) : Integer.Sparse.eval row19646 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19646, Integer.Sparse.eval_collectBalanced, rawRowCheck19646]

theorem rawRowCheck19647 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19647 := by decide +kernel

theorem rowCheck19647 : row19647 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19647 := by decide +kernel

theorem rowEval19647 (x : Key → ℝ) : Integer.Sparse.eval row19647 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19647, Integer.Sparse.eval_collectBalanced, rawRowCheck19647]

theorem rawRowCheck19648 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19648 := by decide +kernel

theorem rowCheck19648 : row19648 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19648 := by decide +kernel

theorem rowEval19648 (x : Key → ℝ) : Integer.Sparse.eval row19648 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19648, Integer.Sparse.eval_collectBalanced, rawRowCheck19648]

theorem rawRowCheck19649 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19649 := by decide +kernel

theorem rowCheck19649 : row19649 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19649 := by decide +kernel

theorem rowEval19649 (x : Key → ℝ) : Integer.Sparse.eval row19649 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19649, Integer.Sparse.eval_collectBalanced, rawRowCheck19649]

theorem rawRowCheck19650 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19650 := by decide +kernel

theorem rowCheck19650 : row19650 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19650 := by decide +kernel

theorem rowEval19650 (x : Key → ℝ) : Integer.Sparse.eval row19650 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19650, Integer.Sparse.eval_collectBalanced, rawRowCheck19650]

theorem rawRowCheck19651 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19651 := by decide +kernel

theorem rowCheck19651 : row19651 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19651 := by decide +kernel

theorem rowEval19651 (x : Key → ℝ) : Integer.Sparse.eval row19651 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19651, Integer.Sparse.eval_collectBalanced, rawRowCheck19651]

theorem rawRowCheck19652 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0 = rawRow19652 := by decide +kernel

theorem rowCheck19652 : row19652 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19652 := by decide +kernel

theorem rowEval19652 (x : Key → ℝ) : Integer.Sparse.eval row19652 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19652, Integer.Sparse.eval_collectBalanced, rawRowCheck19652]

theorem rawRowCheck19653 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0 = rawRow19653 := by decide +kernel

theorem rowCheck19653 : row19653 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19653 := by decide +kernel

theorem rowEval19653 (x : Key → ℝ) : Integer.Sparse.eval row19653 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19653, Integer.Sparse.eval_collectBalanced, rawRowCheck19653]

theorem rawRowCheck19654 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0 = rawRow19654 := by decide +kernel

theorem rowCheck19654 : row19654 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19654 := by decide +kernel

theorem rowEval19654 (x : Key → ℝ) : Integer.Sparse.eval row19654 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19654, Integer.Sparse.eval_collectBalanced, rawRowCheck19654]

theorem rawRowCheck19655 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0 = rawRow19655 := by decide +kernel

theorem rowCheck19655 : row19655 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19655 := by decide +kernel

theorem rowEval19655 (x : Key → ℝ) : Integer.Sparse.eval row19655 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19655, Integer.Sparse.eval_collectBalanced, rawRowCheck19655]

theorem rawRowCheck19656 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0 = rawRow19656 := by decide +kernel

theorem rowCheck19656 : row19656 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19656 := by decide +kernel

theorem rowEval19656 (x : Key → ℝ) : Integer.Sparse.eval row19656 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19656, Integer.Sparse.eval_collectBalanced, rawRowCheck19656]

theorem rawRowCheck19657 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0 = rawRow19657 := by decide +kernel

theorem rowCheck19657 : row19657 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19657 := by decide +kernel

theorem rowEval19657 (x : Key → ℝ) : Integer.Sparse.eval row19657 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19657, Integer.Sparse.eval_collectBalanced, rawRowCheck19657]

theorem rawRowCheck19658 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0 = rawRow19658 := by decide +kernel

theorem rowCheck19658 : row19658 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19658 := by decide +kernel

theorem rowEval19658 (x : Key → ℝ) : Integer.Sparse.eval row19658 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19658, Integer.Sparse.eval_collectBalanced, rawRowCheck19658]

theorem rawRowCheck19659 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0 = rawRow19659 := by decide +kernel

theorem rowCheck19659 : row19659 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19659 := by decide +kernel

theorem rowEval19659 (x : Key → ℝ) : Integer.Sparse.eval row19659 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19659, Integer.Sparse.eval_collectBalanced, rawRowCheck19659]

theorem rawRowCheck19660 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0 = rawRow19660 := by decide +kernel

theorem rowCheck19660 : row19660 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19660 := by decide +kernel

theorem rowEval19660 (x : Key → ℝ) : Integer.Sparse.eval row19660 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form0) x := by
  rw [rowCheck19660, Integer.Sparse.eval_collectBalanced, rawRowCheck19660]

theorem rawRowCheck19661 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0 = rawRow19661 := by decide +kernel

theorem rowCheck19661 : row19661 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19661 := by decide +kernel

theorem rowEval19661 (x : Key → ℝ) : Integer.Sparse.eval row19661 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19661, Integer.Sparse.eval_collectBalanced, rawRowCheck19661]

theorem rawRowCheck19662 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0 = rawRow19662 := by decide +kernel

theorem rowCheck19662 : row19662 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19662 := by decide +kernel

theorem rowEval19662 (x : Key → ℝ) : Integer.Sparse.eval row19662 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form0) x := by
  rw [rowCheck19662, Integer.Sparse.eval_collectBalanced, rawRowCheck19662]

theorem rawRowCheck19663 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0 = rawRow19663 := by decide +kernel

theorem rowCheck19663 : row19663 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19663 := by decide +kernel

theorem rowEval19663 (x : Key → ℝ) : Integer.Sparse.eval row19663 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form0) x := by
  rw [rowCheck19663, Integer.Sparse.eval_collectBalanced, rawRowCheck19663]

theorem rawRowCheck19664 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19664 := by decide +kernel

theorem rowCheck19664 : row19664 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19664 := by decide +kernel

theorem rowEval19664 (x : Key → ℝ) : Integer.Sparse.eval row19664 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19664, Integer.Sparse.eval_collectBalanced, rawRowCheck19664]

theorem rawRowCheck19665 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19665 := by decide +kernel

theorem rowCheck19665 : row19665 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19665 := by decide +kernel

theorem rowEval19665 (x : Key → ℝ) : Integer.Sparse.eval row19665 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19665, Integer.Sparse.eval_collectBalanced, rawRowCheck19665]

theorem rawRowCheck19666 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19666 := by decide +kernel

theorem rowCheck19666 : row19666 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19666 := by decide +kernel

theorem rowEval19666 (x : Key → ℝ) : Integer.Sparse.eval row19666 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19666, Integer.Sparse.eval_collectBalanced, rawRowCheck19666]

theorem rawRowCheck19667 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1 = rawRow19667 := by decide +kernel

theorem rowCheck19667 : row19667 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19667 := by decide +kernel

theorem rowEval19667 (x : Key → ℝ) : Integer.Sparse.eval row19667 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19667, Integer.Sparse.eval_collectBalanced, rawRowCheck19667]

theorem rawRowCheck19668 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1 = rawRow19668 := by decide +kernel

theorem rowCheck19668 : row19668 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19668 := by decide +kernel

theorem rowEval19668 (x : Key → ℝ) : Integer.Sparse.eval row19668 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19668, Integer.Sparse.eval_collectBalanced, rawRowCheck19668]

theorem rawRowCheck19669 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1 = rawRow19669 := by decide +kernel

theorem rowCheck19669 : row19669 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19669 := by decide +kernel

theorem rowEval19669 (x : Key → ℝ) : Integer.Sparse.eval row19669 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19669, Integer.Sparse.eval_collectBalanced, rawRowCheck19669]

theorem rawRowCheck19670 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1 = rawRow19670 := by decide +kernel

theorem rowCheck19670 : row19670 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19670 := by decide +kernel

theorem rowEval19670 (x : Key → ℝ) : Integer.Sparse.eval row19670 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19670, Integer.Sparse.eval_collectBalanced, rawRowCheck19670]

theorem rawRowCheck19671 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1 = rawRow19671 := by decide +kernel

theorem rowCheck19671 : row19671 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19671 := by decide +kernel

theorem rowEval19671 (x : Key → ℝ) : Integer.Sparse.eval row19671 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19671, Integer.Sparse.eval_collectBalanced, rawRowCheck19671]

theorem rawRowCheck19672 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1 = rawRow19672 := by decide +kernel

theorem rowCheck19672 : row19672 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19672 := by decide +kernel

theorem rowEval19672 (x : Key → ℝ) : Integer.Sparse.eval row19672 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19672, Integer.Sparse.eval_collectBalanced, rawRowCheck19672]

theorem rawRowCheck19673 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19673 := by decide +kernel

theorem rowCheck19673 : row19673 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19673 := by decide +kernel

theorem rowEval19673 (x : Key → ℝ) : Integer.Sparse.eval row19673 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19673, Integer.Sparse.eval_collectBalanced, rawRowCheck19673]

theorem rawRowCheck19674 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19674 := by decide +kernel

theorem rowCheck19674 : row19674 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19674 := by decide +kernel

theorem rowEval19674 (x : Key → ℝ) : Integer.Sparse.eval row19674 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19674, Integer.Sparse.eval_collectBalanced, rawRowCheck19674]

theorem rawRowCheck19675 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19675 := by decide +kernel

theorem rowCheck19675 : row19675 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19675 := by decide +kernel

theorem rowEval19675 (x : Key → ℝ) : Integer.Sparse.eval row19675 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19675, Integer.Sparse.eval_collectBalanced, rawRowCheck19675]

theorem rawRowCheck19676 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1 = rawRow19676 := by decide +kernel

theorem rowCheck19676 : row19676 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19676 := by decide +kernel

theorem rowEval19676 (x : Key → ℝ) : Integer.Sparse.eval row19676 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19676, Integer.Sparse.eval_collectBalanced, rawRowCheck19676]

theorem rawRowCheck19677 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1 = rawRow19677 := by decide +kernel

theorem rowCheck19677 : row19677 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19677 := by decide +kernel

theorem rowEval19677 (x : Key → ℝ) : Integer.Sparse.eval row19677 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19677, Integer.Sparse.eval_collectBalanced, rawRowCheck19677]

theorem rawRowCheck19678 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1 = rawRow19678 := by decide +kernel

theorem rowCheck19678 : row19678 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19678 := by decide +kernel

theorem rowEval19678 (x : Key → ℝ) : Integer.Sparse.eval row19678 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19678, Integer.Sparse.eval_collectBalanced, rawRowCheck19678]

theorem rawRowCheck19679 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19679 := by decide +kernel

theorem rowCheck19679 : row19679 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19679 := by decide +kernel

theorem rowEval19679 (x : Key → ℝ) : Integer.Sparse.eval row19679 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19679, Integer.Sparse.eval_collectBalanced, rawRowCheck19679]

theorem rawRowCheck19680 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19680 := by decide +kernel

theorem rowCheck19680 : row19680 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19680 := by decide +kernel

theorem rowEval19680 (x : Key → ℝ) : Integer.Sparse.eval row19680 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19680, Integer.Sparse.eval_collectBalanced, rawRowCheck19680]

theorem rawRowCheck19681 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19681 := by decide +kernel

theorem rowCheck19681 : row19681 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19681 := by decide +kernel

theorem rowEval19681 (x : Key → ℝ) : Integer.Sparse.eval row19681 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19681, Integer.Sparse.eval_collectBalanced, rawRowCheck19681]

theorem rawRowCheck19682 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19682 := by decide +kernel

theorem rowCheck19682 : row19682 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19682 := by decide +kernel

theorem rowEval19682 (x : Key → ℝ) : Integer.Sparse.eval row19682 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19682, Integer.Sparse.eval_collectBalanced, rawRowCheck19682]

theorem rawRowCheck19683 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19683 := by decide +kernel

theorem rowCheck19683 : row19683 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19683 := by decide +kernel

theorem rowEval19683 (x : Key → ℝ) : Integer.Sparse.eval row19683 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19683, Integer.Sparse.eval_collectBalanced, rawRowCheck19683]

theorem rawRowCheck19684 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19684 := by decide +kernel

theorem rowCheck19684 : row19684 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19684 := by decide +kernel

theorem rowEval19684 (x : Key → ℝ) : Integer.Sparse.eval row19684 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19684, Integer.Sparse.eval_collectBalanced, rawRowCheck19684]

theorem rawRowCheck19685 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19685 := by decide +kernel

theorem rowCheck19685 : row19685 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19685 := by decide +kernel

theorem rowEval19685 (x : Key → ℝ) : Integer.Sparse.eval row19685 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19685, Integer.Sparse.eval_collectBalanced, rawRowCheck19685]

theorem rawRowCheck19686 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19686 := by decide +kernel

theorem rowCheck19686 : row19686 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19686 := by decide +kernel

theorem rowEval19686 (x : Key → ℝ) : Integer.Sparse.eval row19686 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19686, Integer.Sparse.eval_collectBalanced, rawRowCheck19686]

theorem rawRowCheck19687 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19687 := by decide +kernel

theorem rowCheck19687 : row19687 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19687 := by decide +kernel

theorem rowEval19687 (x : Key → ℝ) : Integer.Sparse.eval row19687 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19687, Integer.Sparse.eval_collectBalanced, rawRowCheck19687]

theorem rawRowCheck19688 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1 = rawRow19688 := by decide +kernel

theorem rowCheck19688 : row19688 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19688 := by decide +kernel

theorem rowEval19688 (x : Key → ℝ) : Integer.Sparse.eval row19688 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19688, Integer.Sparse.eval_collectBalanced, rawRowCheck19688]

theorem rawRowCheck19689 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1 = rawRow19689 := by decide +kernel

theorem rowCheck19689 : row19689 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19689 := by decide +kernel

theorem rowEval19689 (x : Key → ℝ) : Integer.Sparse.eval row19689 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19689, Integer.Sparse.eval_collectBalanced, rawRowCheck19689]

theorem rawRowCheck19690 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1 = rawRow19690 := by decide +kernel

theorem rowCheck19690 : row19690 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19690 := by decide +kernel

theorem rowEval19690 (x : Key → ℝ) : Integer.Sparse.eval row19690 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19690, Integer.Sparse.eval_collectBalanced, rawRowCheck19690]

theorem rawRowCheck19691 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1 = rawRow19691 := by decide +kernel

theorem rowCheck19691 : row19691 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19691 := by decide +kernel

theorem rowEval19691 (x : Key → ℝ) : Integer.Sparse.eval row19691 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19691, Integer.Sparse.eval_collectBalanced, rawRowCheck19691]

theorem rawRowCheck19692 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1 = rawRow19692 := by decide +kernel

theorem rowCheck19692 : row19692 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19692 := by decide +kernel

theorem rowEval19692 (x : Key → ℝ) : Integer.Sparse.eval row19692 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19692, Integer.Sparse.eval_collectBalanced, rawRowCheck19692]

theorem rawRowCheck19693 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1 = rawRow19693 := by decide +kernel

theorem rowCheck19693 : row19693 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19693 := by decide +kernel

theorem rowEval19693 (x : Key → ℝ) : Integer.Sparse.eval row19693 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19693, Integer.Sparse.eval_collectBalanced, rawRowCheck19693]

theorem rawRowCheck19694 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1 = rawRow19694 := by decide +kernel

theorem rowCheck19694 : row19694 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19694 := by decide +kernel

theorem rowEval19694 (x : Key → ℝ) : Integer.Sparse.eval row19694 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19694, Integer.Sparse.eval_collectBalanced, rawRowCheck19694]

theorem rawRowCheck19695 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1 = rawRow19695 := by decide +kernel

theorem rowCheck19695 : row19695 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19695 := by decide +kernel

theorem rowEval19695 (x : Key → ℝ) : Integer.Sparse.eval row19695 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19695, Integer.Sparse.eval_collectBalanced, rawRowCheck19695]

theorem rawRowCheck19696 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1 = rawRow19696 := by decide +kernel

theorem rowCheck19696 : row19696 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19696 := by decide +kernel

theorem rowEval19696 (x : Key → ℝ) : Integer.Sparse.eval row19696 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19696, Integer.Sparse.eval_collectBalanced, rawRowCheck19696]

theorem rawRowCheck19697 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1 = rawRow19697 := by decide +kernel

theorem rowCheck19697 : row19697 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19697 := by decide +kernel

theorem rowEval19697 (x : Key → ℝ) : Integer.Sparse.eval row19697 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19697, Integer.Sparse.eval_collectBalanced, rawRowCheck19697]

theorem rawRowCheck19698 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1 = rawRow19698 := by decide +kernel

theorem rowCheck19698 : row19698 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19698 := by decide +kernel

theorem rowEval19698 (x : Key → ℝ) : Integer.Sparse.eval row19698 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19698, Integer.Sparse.eval_collectBalanced, rawRowCheck19698]

theorem rawRowCheck19699 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1 = rawRow19699 := by decide +kernel

theorem rowCheck19699 : row19699 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19699 := by decide +kernel

theorem rowEval19699 (x : Key → ℝ) : Integer.Sparse.eval row19699 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19699, Integer.Sparse.eval_collectBalanced, rawRowCheck19699]

theorem rawRowCheck19700 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1 = rawRow19700 := by decide +kernel

theorem rowCheck19700 : row19700 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19700 := by decide +kernel

theorem rowEval19700 (x : Key → ℝ) : Integer.Sparse.eval row19700 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19700, Integer.Sparse.eval_collectBalanced, rawRowCheck19700]

theorem rawRowCheck19701 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1 = rawRow19701 := by decide +kernel

theorem rowCheck19701 : row19701 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19701 := by decide +kernel

theorem rowEval19701 (x : Key → ℝ) : Integer.Sparse.eval row19701 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19701, Integer.Sparse.eval_collectBalanced, rawRowCheck19701]

theorem rawRowCheck19702 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1 = rawRow19702 := by decide +kernel

theorem rowCheck19702 : row19702 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19702 := by decide +kernel

theorem rowEval19702 (x : Key → ℝ) : Integer.Sparse.eval row19702 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19702, Integer.Sparse.eval_collectBalanced, rawRowCheck19702]

theorem rawRowCheck19703 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1 = rawRow19703 := by decide +kernel

theorem rowCheck19703 : row19703 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19703 := by decide +kernel

theorem rowEval19703 (x : Key → ℝ) : Integer.Sparse.eval row19703 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19703, Integer.Sparse.eval_collectBalanced, rawRowCheck19703]

theorem rawRowCheck19704 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1 = rawRow19704 := by decide +kernel

theorem rowCheck19704 : row19704 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19704 := by decide +kernel

theorem rowEval19704 (x : Key → ℝ) : Integer.Sparse.eval row19704 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19704, Integer.Sparse.eval_collectBalanced, rawRowCheck19704]

theorem rawRowCheck19705 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1 = rawRow19705 := by decide +kernel

theorem rowCheck19705 : row19705 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19705 := by decide +kernel

theorem rowEval19705 (x : Key → ℝ) : Integer.Sparse.eval row19705 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19705, Integer.Sparse.eval_collectBalanced, rawRowCheck19705]

theorem rawRowCheck19706 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19706 := by decide +kernel

theorem rowCheck19706 : row19706 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19706 := by decide +kernel

theorem rowEval19706 (x : Key → ℝ) : Integer.Sparse.eval row19706 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19706, Integer.Sparse.eval_collectBalanced, rawRowCheck19706]

theorem rawRowCheck19707 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19707 := by decide +kernel

theorem rowCheck19707 : row19707 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19707 := by decide +kernel

theorem rowEval19707 (x : Key → ℝ) : Integer.Sparse.eval row19707 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19707, Integer.Sparse.eval_collectBalanced, rawRowCheck19707]

theorem rawRowCheck19708 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19708 := by decide +kernel

theorem rowCheck19708 : row19708 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19708 := by decide +kernel

theorem rowEval19708 (x : Key → ℝ) : Integer.Sparse.eval row19708 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19708, Integer.Sparse.eval_collectBalanced, rawRowCheck19708]

theorem rawRowCheck19709 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19709 := by decide +kernel

theorem rowCheck19709 : row19709 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19709 := by decide +kernel

theorem rowEval19709 (x : Key → ℝ) : Integer.Sparse.eval row19709 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19709, Integer.Sparse.eval_collectBalanced, rawRowCheck19709]

theorem rawRowCheck19710 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19710 := by decide +kernel

theorem rowCheck19710 : row19710 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19710 := by decide +kernel

theorem rowEval19710 (x : Key → ℝ) : Integer.Sparse.eval row19710 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19710, Integer.Sparse.eval_collectBalanced, rawRowCheck19710]

theorem rawRowCheck19711 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19711 := by decide +kernel

theorem rowCheck19711 : row19711 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19711 := by decide +kernel

theorem rowEval19711 (x : Key → ℝ) : Integer.Sparse.eval row19711 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19711, Integer.Sparse.eval_collectBalanced, rawRowCheck19711]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block178
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19712 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1 = rawRow19712 := by decide +kernel

theorem rowCheck19712 : row19712 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19712 := by decide +kernel

theorem rowEval19712 (x : Key → ℝ) : Integer.Sparse.eval row19712 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19712, Integer.Sparse.eval_collectBalanced, rawRowCheck19712]

theorem rawRowCheck19713 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1 = rawRow19713 := by decide +kernel

theorem rowCheck19713 : row19713 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19713 := by decide +kernel

theorem rowEval19713 (x : Key → ℝ) : Integer.Sparse.eval row19713 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19713, Integer.Sparse.eval_collectBalanced, rawRowCheck19713]

theorem rawRowCheck19714 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1 = rawRow19714 := by decide +kernel

theorem rowCheck19714 : row19714 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19714 := by decide +kernel

theorem rowEval19714 (x : Key → ℝ) : Integer.Sparse.eval row19714 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19714, Integer.Sparse.eval_collectBalanced, rawRowCheck19714]

theorem rawRowCheck19715 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1 = rawRow19715 := by decide +kernel

theorem rowCheck19715 : row19715 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19715 := by decide +kernel

theorem rowEval19715 (x : Key → ℝ) : Integer.Sparse.eval row19715 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19715, Integer.Sparse.eval_collectBalanced, rawRowCheck19715]

theorem rawRowCheck19716 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1 = rawRow19716 := by decide +kernel

theorem rowCheck19716 : row19716 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19716 := by decide +kernel

theorem rowEval19716 (x : Key → ℝ) : Integer.Sparse.eval row19716 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19716, Integer.Sparse.eval_collectBalanced, rawRowCheck19716]

theorem rawRowCheck19717 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1 = rawRow19717 := by decide +kernel

theorem rowCheck19717 : row19717 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19717 := by decide +kernel

theorem rowEval19717 (x : Key → ℝ) : Integer.Sparse.eval row19717 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19717, Integer.Sparse.eval_collectBalanced, rawRowCheck19717]

theorem rawRowCheck19718 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1 = rawRow19718 := by decide +kernel

theorem rowCheck19718 : row19718 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19718 := by decide +kernel

theorem rowEval19718 (x : Key → ℝ) : Integer.Sparse.eval row19718 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19718, Integer.Sparse.eval_collectBalanced, rawRowCheck19718]

theorem rawRowCheck19719 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1 = rawRow19719 := by decide +kernel

theorem rowCheck19719 : row19719 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19719 := by decide +kernel

theorem rowEval19719 (x : Key → ℝ) : Integer.Sparse.eval row19719 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19719, Integer.Sparse.eval_collectBalanced, rawRowCheck19719]

theorem rawRowCheck19720 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1 = rawRow19720 := by decide +kernel

theorem rowCheck19720 : row19720 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19720 := by decide +kernel

theorem rowEval19720 (x : Key → ℝ) : Integer.Sparse.eval row19720 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form1) x := by
  rw [rowCheck19720, Integer.Sparse.eval_collectBalanced, rawRowCheck19720]

theorem rawRowCheck19721 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1 = rawRow19721 := by decide +kernel

theorem rowCheck19721 : row19721 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19721 := by decide +kernel

theorem rowEval19721 (x : Key → ℝ) : Integer.Sparse.eval row19721 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19721, Integer.Sparse.eval_collectBalanced, rawRowCheck19721]

theorem rawRowCheck19722 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1 = rawRow19722 := by decide +kernel

theorem rowCheck19722 : row19722 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19722 := by decide +kernel

theorem rowEval19722 (x : Key → ℝ) : Integer.Sparse.eval row19722 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form1) x := by
  rw [rowCheck19722, Integer.Sparse.eval_collectBalanced, rawRowCheck19722]

theorem rawRowCheck19723 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1 = rawRow19723 := by decide +kernel

theorem rowCheck19723 : row19723 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19723 := by decide +kernel

theorem rowEval19723 (x : Key → ℝ) : Integer.Sparse.eval row19723 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form1) x := by
  rw [rowCheck19723, Integer.Sparse.eval_collectBalanced, rawRowCheck19723]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block180
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20024 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form7 = rawRow20024 := by decide +kernel

theorem rowCheck20024 : row20024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20024 := by decide +kernel

theorem rowEval20024 (x : Key → ℝ) : Integer.Sparse.eval row20024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20024, Integer.Sparse.eval_collectBalanced, rawRowCheck20024]

theorem rawRowCheck20025 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form7 = rawRow20025 := by decide +kernel

theorem rowCheck20025 : row20025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20025 := by decide +kernel

theorem rowEval20025 (x : Key → ℝ) : Integer.Sparse.eval row20025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20025, Integer.Sparse.eval_collectBalanced, rawRowCheck20025]

theorem rawRowCheck20026 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form7 = rawRow20026 := by decide +kernel

theorem rowCheck20026 : row20026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20026 := by decide +kernel

theorem rowEval20026 (x : Key → ℝ) : Integer.Sparse.eval row20026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20026, Integer.Sparse.eval_collectBalanced, rawRowCheck20026]

theorem rawRowCheck20027 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form7 = rawRow20027 := by decide +kernel

theorem rowCheck20027 : row20027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20027 := by decide +kernel

theorem rowEval20027 (x : Key → ℝ) : Integer.Sparse.eval row20027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20027, Integer.Sparse.eval_collectBalanced, rawRowCheck20027]

theorem rawRowCheck20028 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form7 = rawRow20028 := by decide +kernel

theorem rowCheck20028 : row20028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20028 := by decide +kernel

theorem rowEval20028 (x : Key → ℝ) : Integer.Sparse.eval row20028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20028, Integer.Sparse.eval_collectBalanced, rawRowCheck20028]

theorem rawRowCheck20029 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form7 = rawRow20029 := by decide +kernel

theorem rowCheck20029 : row20029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20029 := by decide +kernel

theorem rowEval20029 (x : Key → ℝ) : Integer.Sparse.eval row20029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20029, Integer.Sparse.eval_collectBalanced, rawRowCheck20029]

theorem rawRowCheck20030 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form7 = rawRow20030 := by decide +kernel

theorem rowCheck20030 : row20030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20030 := by decide +kernel

theorem rowEval20030 (x : Key → ℝ) : Integer.Sparse.eval row20030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20030, Integer.Sparse.eval_collectBalanced, rawRowCheck20030]

theorem rawRowCheck20031 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form7 = rawRow20031 := by decide +kernel

theorem rowCheck20031 : row20031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20031 := by decide +kernel

theorem rowEval20031 (x : Key → ℝ) : Integer.Sparse.eval row20031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20031, Integer.Sparse.eval_collectBalanced, rawRowCheck20031]

theorem rawRowCheck20032 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form7 = rawRow20032 := by decide +kernel

theorem rowCheck20032 : row20032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20032 := by decide +kernel

theorem rowEval20032 (x : Key → ℝ) : Integer.Sparse.eval row20032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20032, Integer.Sparse.eval_collectBalanced, rawRowCheck20032]

theorem rawRowCheck20033 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow20033 := by decide +kernel

theorem rowCheck20033 : row20033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20033 := by decide +kernel

theorem rowEval20033 (x : Key → ℝ) : Integer.Sparse.eval row20033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20033, Integer.Sparse.eval_collectBalanced, rawRowCheck20033]

theorem rawRowCheck20034 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow20034 := by decide +kernel

theorem rowCheck20034 : row20034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20034 := by decide +kernel

theorem rowEval20034 (x : Key → ℝ) : Integer.Sparse.eval row20034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20034, Integer.Sparse.eval_collectBalanced, rawRowCheck20034]

theorem rawRowCheck20035 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow20035 := by decide +kernel

theorem rowCheck20035 : row20035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20035 := by decide +kernel

theorem rowEval20035 (x : Key → ℝ) : Integer.Sparse.eval row20035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20035, Integer.Sparse.eval_collectBalanced, rawRowCheck20035]

theorem rawRowCheck20036 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form7 = rawRow20036 := by decide +kernel

theorem rowCheck20036 : row20036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20036 := by decide +kernel

theorem rowEval20036 (x : Key → ℝ) : Integer.Sparse.eval row20036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20036, Integer.Sparse.eval_collectBalanced, rawRowCheck20036]

theorem rawRowCheck20037 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form7 = rawRow20037 := by decide +kernel

theorem rowCheck20037 : row20037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20037 := by decide +kernel

theorem rowEval20037 (x : Key → ℝ) : Integer.Sparse.eval row20037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20037, Integer.Sparse.eval_collectBalanced, rawRowCheck20037]

theorem rawRowCheck20038 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form7 = rawRow20038 := by decide +kernel

theorem rowCheck20038 : row20038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20038 := by decide +kernel

theorem rowEval20038 (x : Key → ℝ) : Integer.Sparse.eval row20038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20038, Integer.Sparse.eval_collectBalanced, rawRowCheck20038]

theorem rawRowCheck20039 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form7 = rawRow20039 := by decide +kernel

theorem rowCheck20039 : row20039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20039 := by decide +kernel

theorem rowEval20039 (x : Key → ℝ) : Integer.Sparse.eval row20039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20039, Integer.Sparse.eval_collectBalanced, rawRowCheck20039]

theorem rawRowCheck20040 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form7 = rawRow20040 := by decide +kernel

theorem rowCheck20040 : row20040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20040 := by decide +kernel

theorem rowEval20040 (x : Key → ℝ) : Integer.Sparse.eval row20040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20040, Integer.Sparse.eval_collectBalanced, rawRowCheck20040]

theorem rawRowCheck20041 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form7 = rawRow20041 := by decide +kernel

theorem rowCheck20041 : row20041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20041 := by decide +kernel

theorem rowEval20041 (x : Key → ℝ) : Integer.Sparse.eval row20041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20041, Integer.Sparse.eval_collectBalanced, rawRowCheck20041]

theorem rawRowCheck20042 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form7 = rawRow20042 := by decide +kernel

theorem rowCheck20042 : row20042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20042 := by decide +kernel

theorem rowEval20042 (x : Key → ℝ) : Integer.Sparse.eval row20042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20042, Integer.Sparse.eval_collectBalanced, rawRowCheck20042]

theorem rawRowCheck20043 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form7 = rawRow20043 := by decide +kernel

theorem rowCheck20043 : row20043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20043 := by decide +kernel

theorem rowEval20043 (x : Key → ℝ) : Integer.Sparse.eval row20043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20043, Integer.Sparse.eval_collectBalanced, rawRowCheck20043]

theorem rawRowCheck20044 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form7 = rawRow20044 := by decide +kernel

theorem rowCheck20044 : row20044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20044 := by decide +kernel

theorem rowEval20044 (x : Key → ℝ) : Integer.Sparse.eval row20044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20044, Integer.Sparse.eval_collectBalanced, rawRowCheck20044]

theorem rawRowCheck20045 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form7 = rawRow20045 := by decide +kernel

theorem rowCheck20045 : row20045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20045 := by decide +kernel

theorem rowEval20045 (x : Key → ℝ) : Integer.Sparse.eval row20045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20045, Integer.Sparse.eval_collectBalanced, rawRowCheck20045]

theorem rawRowCheck20046 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form7 = rawRow20046 := by decide +kernel

theorem rowCheck20046 : row20046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20046 := by decide +kernel

theorem rowEval20046 (x : Key → ℝ) : Integer.Sparse.eval row20046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20046, Integer.Sparse.eval_collectBalanced, rawRowCheck20046]

theorem rawRowCheck20047 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form7 = rawRow20047 := by decide +kernel

theorem rowCheck20047 : row20047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20047 := by decide +kernel

theorem rowEval20047 (x : Key → ℝ) : Integer.Sparse.eval row20047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20047, Integer.Sparse.eval_collectBalanced, rawRowCheck20047]

theorem rawRowCheck20048 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form7 = rawRow20048 := by decide +kernel

theorem rowCheck20048 : row20048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20048 := by decide +kernel

theorem rowEval20048 (x : Key → ℝ) : Integer.Sparse.eval row20048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20048, Integer.Sparse.eval_collectBalanced, rawRowCheck20048]

theorem rawRowCheck20049 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form7 = rawRow20049 := by decide +kernel

theorem rowCheck20049 : row20049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20049 := by decide +kernel

theorem rowEval20049 (x : Key → ℝ) : Integer.Sparse.eval row20049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20049, Integer.Sparse.eval_collectBalanced, rawRowCheck20049]

theorem rawRowCheck20050 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form7 = rawRow20050 := by decide +kernel

theorem rowCheck20050 : row20050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20050 := by decide +kernel

theorem rowEval20050 (x : Key → ℝ) : Integer.Sparse.eval row20050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20050, Integer.Sparse.eval_collectBalanced, rawRowCheck20050]

theorem rawRowCheck20051 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form7 = rawRow20051 := by decide +kernel

theorem rowCheck20051 : row20051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20051 := by decide +kernel

theorem rowEval20051 (x : Key → ℝ) : Integer.Sparse.eval row20051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20051, Integer.Sparse.eval_collectBalanced, rawRowCheck20051]

theorem rawRowCheck20052 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form7 = rawRow20052 := by decide +kernel

theorem rowCheck20052 : row20052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20052 := by decide +kernel

theorem rowEval20052 (x : Key → ℝ) : Integer.Sparse.eval row20052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20052, Integer.Sparse.eval_collectBalanced, rawRowCheck20052]

theorem rawRowCheck20053 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form7 = rawRow20053 := by decide +kernel

theorem rowCheck20053 : row20053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20053 := by decide +kernel

theorem rowEval20053 (x : Key → ℝ) : Integer.Sparse.eval row20053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20053, Integer.Sparse.eval_collectBalanced, rawRowCheck20053]

theorem rawRowCheck20054 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form7 = rawRow20054 := by decide +kernel

theorem rowCheck20054 : row20054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20054 := by decide +kernel

theorem rowEval20054 (x : Key → ℝ) : Integer.Sparse.eval row20054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20054, Integer.Sparse.eval_collectBalanced, rawRowCheck20054]

theorem rawRowCheck20055 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form7 = rawRow20055 := by decide +kernel

theorem rowCheck20055 : row20055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20055 := by decide +kernel

theorem rowEval20055 (x : Key → ℝ) : Integer.Sparse.eval row20055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20055, Integer.Sparse.eval_collectBalanced, rawRowCheck20055]

theorem rawRowCheck20056 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form7 = rawRow20056 := by decide +kernel

theorem rowCheck20056 : row20056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20056 := by decide +kernel

theorem rowEval20056 (x : Key → ℝ) : Integer.Sparse.eval row20056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20056, Integer.Sparse.eval_collectBalanced, rawRowCheck20056]

theorem rawRowCheck20057 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form7 = rawRow20057 := by decide +kernel

theorem rowCheck20057 : row20057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20057 := by decide +kernel

theorem rowEval20057 (x : Key → ℝ) : Integer.Sparse.eval row20057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20057, Integer.Sparse.eval_collectBalanced, rawRowCheck20057]

theorem rawRowCheck20058 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form7 = rawRow20058 := by decide +kernel

theorem rowCheck20058 : row20058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20058 := by decide +kernel

theorem rowEval20058 (x : Key → ℝ) : Integer.Sparse.eval row20058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20058, Integer.Sparse.eval_collectBalanced, rawRowCheck20058]

theorem rawRowCheck20059 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form7 = rawRow20059 := by decide +kernel

theorem rowCheck20059 : row20059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20059 := by decide +kernel

theorem rowEval20059 (x : Key → ℝ) : Integer.Sparse.eval row20059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20059, Integer.Sparse.eval_collectBalanced, rawRowCheck20059]

theorem rawRowCheck20060 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form7 = rawRow20060 := by decide +kernel

theorem rowCheck20060 : row20060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20060 := by decide +kernel

theorem rowEval20060 (x : Key → ℝ) : Integer.Sparse.eval row20060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20060, Integer.Sparse.eval_collectBalanced, rawRowCheck20060]

theorem rawRowCheck20061 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form7 = rawRow20061 := by decide +kernel

theorem rowCheck20061 : row20061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20061 := by decide +kernel

theorem rowEval20061 (x : Key → ℝ) : Integer.Sparse.eval row20061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20061, Integer.Sparse.eval_collectBalanced, rawRowCheck20061]

theorem rawRowCheck20062 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form7 = rawRow20062 := by decide +kernel

theorem rowCheck20062 : row20062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20062 := by decide +kernel

theorem rowEval20062 (x : Key → ℝ) : Integer.Sparse.eval row20062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20062, Integer.Sparse.eval_collectBalanced, rawRowCheck20062]

theorem rawRowCheck20063 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form7 = rawRow20063 := by decide +kernel

theorem rowCheck20063 : row20063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20063 := by decide +kernel

theorem rowEval20063 (x : Key → ℝ) : Integer.Sparse.eval row20063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20063, Integer.Sparse.eval_collectBalanced, rawRowCheck20063]

theorem rawRowCheck20064 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form7 = rawRow20064 := by decide +kernel

theorem rowCheck20064 : row20064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20064 := by decide +kernel

theorem rowEval20064 (x : Key → ℝ) : Integer.Sparse.eval row20064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20064, Integer.Sparse.eval_collectBalanced, rawRowCheck20064]

theorem rawRowCheck20065 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form7 = rawRow20065 := by decide +kernel

theorem rowCheck20065 : row20065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20065 := by decide +kernel

theorem rowEval20065 (x : Key → ℝ) : Integer.Sparse.eval row20065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20065, Integer.Sparse.eval_collectBalanced, rawRowCheck20065]

theorem rawRowCheck20066 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form7 = rawRow20066 := by decide +kernel

theorem rowCheck20066 : row20066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20066 := by decide +kernel

theorem rowEval20066 (x : Key → ℝ) : Integer.Sparse.eval row20066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20066, Integer.Sparse.eval_collectBalanced, rawRowCheck20066]

theorem rawRowCheck20067 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form7 = rawRow20067 := by decide +kernel

theorem rowCheck20067 : row20067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20067 := by decide +kernel

theorem rowEval20067 (x : Key → ℝ) : Integer.Sparse.eval row20067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20067, Integer.Sparse.eval_collectBalanced, rawRowCheck20067]

theorem rawRowCheck20068 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form7 = rawRow20068 := by decide +kernel

theorem rowCheck20068 : row20068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20068 := by decide +kernel

theorem rowEval20068 (x : Key → ℝ) : Integer.Sparse.eval row20068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20068, Integer.Sparse.eval_collectBalanced, rawRowCheck20068]

theorem rawRowCheck20069 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form7 = rawRow20069 := by decide +kernel

theorem rowCheck20069 : row20069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20069 := by decide +kernel

theorem rowEval20069 (x : Key → ℝ) : Integer.Sparse.eval row20069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20069, Integer.Sparse.eval_collectBalanced, rawRowCheck20069]

theorem rawRowCheck20070 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form7 = rawRow20070 := by decide +kernel

theorem rowCheck20070 : row20070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20070 := by decide +kernel

theorem rowEval20070 (x : Key → ℝ) : Integer.Sparse.eval row20070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20070, Integer.Sparse.eval_collectBalanced, rawRowCheck20070]

theorem rawRowCheck20071 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form7 = rawRow20071 := by decide +kernel

theorem rowCheck20071 : row20071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20071 := by decide +kernel

theorem rowEval20071 (x : Key → ℝ) : Integer.Sparse.eval row20071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20071, Integer.Sparse.eval_collectBalanced, rawRowCheck20071]

theorem rawRowCheck20072 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form7 = rawRow20072 := by decide +kernel

theorem rowCheck20072 : row20072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20072 := by decide +kernel

theorem rowEval20072 (x : Key → ℝ) : Integer.Sparse.eval row20072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20072, Integer.Sparse.eval_collectBalanced, rawRowCheck20072]

theorem rawRowCheck20073 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form7 = rawRow20073 := by decide +kernel

theorem rowCheck20073 : row20073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20073 := by decide +kernel

theorem rowEval20073 (x : Key → ℝ) : Integer.Sparse.eval row20073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20073, Integer.Sparse.eval_collectBalanced, rawRowCheck20073]

theorem rawRowCheck20074 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form7 = rawRow20074 := by decide +kernel

theorem rowCheck20074 : row20074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20074 := by decide +kernel

theorem rowEval20074 (x : Key → ℝ) : Integer.Sparse.eval row20074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20074, Integer.Sparse.eval_collectBalanced, rawRowCheck20074]

theorem rawRowCheck20075 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form7 = rawRow20075 := by decide +kernel

theorem rowCheck20075 : row20075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20075 := by decide +kernel

theorem rowEval20075 (x : Key → ℝ) : Integer.Sparse.eval row20075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20075, Integer.Sparse.eval_collectBalanced, rawRowCheck20075]

theorem rawRowCheck20076 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form7 = rawRow20076 := by decide +kernel

theorem rowCheck20076 : row20076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20076 := by decide +kernel

theorem rowEval20076 (x : Key → ℝ) : Integer.Sparse.eval row20076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20076, Integer.Sparse.eval_collectBalanced, rawRowCheck20076]

theorem rawRowCheck20077 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form7 = rawRow20077 := by decide +kernel

theorem rowCheck20077 : row20077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20077 := by decide +kernel

theorem rowEval20077 (x : Key → ℝ) : Integer.Sparse.eval row20077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20077, Integer.Sparse.eval_collectBalanced, rawRowCheck20077]

theorem rawRowCheck20078 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form7 = rawRow20078 := by decide +kernel

theorem rowCheck20078 : row20078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20078 := by decide +kernel

theorem rowEval20078 (x : Key → ℝ) : Integer.Sparse.eval row20078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20078, Integer.Sparse.eval_collectBalanced, rawRowCheck20078]

theorem rawRowCheck20079 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form7 = rawRow20079 := by decide +kernel

theorem rowCheck20079 : row20079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20079 := by decide +kernel

theorem rowEval20079 (x : Key → ℝ) : Integer.Sparse.eval row20079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20079, Integer.Sparse.eval_collectBalanced, rawRowCheck20079]

theorem rawRowCheck20080 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form7 = rawRow20080 := by decide +kernel

theorem rowCheck20080 : row20080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20080 := by decide +kernel

theorem rowEval20080 (x : Key → ℝ) : Integer.Sparse.eval row20080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form7) x := by
  rw [rowCheck20080, Integer.Sparse.eval_collectBalanced, rawRowCheck20080]

theorem rawRowCheck20081 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form7 = rawRow20081 := by decide +kernel

theorem rowCheck20081 : row20081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20081 := by decide +kernel

theorem rowEval20081 (x : Key → ℝ) : Integer.Sparse.eval row20081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20081, Integer.Sparse.eval_collectBalanced, rawRowCheck20081]

theorem rawRowCheck20082 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form7 = rawRow20082 := by decide +kernel

theorem rowCheck20082 : row20082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20082 := by decide +kernel

theorem rowEval20082 (x : Key → ℝ) : Integer.Sparse.eval row20082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form7) x := by
  rw [rowCheck20082, Integer.Sparse.eval_collectBalanced, rawRowCheck20082]

theorem rawRowCheck20083 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form7 = rawRow20083 := by decide +kernel

theorem rowCheck20083 : row20083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20083 := by decide +kernel

theorem rowEval20083 (x : Key → ℝ) : Integer.Sparse.eval row20083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form7) x := by
  rw [rowCheck20083, Integer.Sparse.eval_collectBalanced, rawRowCheck20083]

theorem rawRowCheck20084 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form8 = rawRow20084 := by decide +kernel

theorem rowCheck20084 : row20084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20084 := by decide +kernel

theorem rowEval20084 (x : Key → ℝ) : Integer.Sparse.eval row20084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20084, Integer.Sparse.eval_collectBalanced, rawRowCheck20084]

theorem rawRowCheck20085 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form8 = rawRow20085 := by decide +kernel

theorem rowCheck20085 : row20085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20085 := by decide +kernel

theorem rowEval20085 (x : Key → ℝ) : Integer.Sparse.eval row20085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20085, Integer.Sparse.eval_collectBalanced, rawRowCheck20085]

theorem rawRowCheck20086 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form8 = rawRow20086 := by decide +kernel

theorem rowCheck20086 : row20086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20086 := by decide +kernel

theorem rowEval20086 (x : Key → ℝ) : Integer.Sparse.eval row20086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20086, Integer.Sparse.eval_collectBalanced, rawRowCheck20086]

theorem rawRowCheck20087 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form8 = rawRow20087 := by decide +kernel

theorem rowCheck20087 : row20087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20087 := by decide +kernel

theorem rowEval20087 (x : Key → ℝ) : Integer.Sparse.eval row20087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20087, Integer.Sparse.eval_collectBalanced, rawRowCheck20087]

theorem rawRowCheck20088 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form8 = rawRow20088 := by decide +kernel

theorem rowCheck20088 : row20088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20088 := by decide +kernel

theorem rowEval20088 (x : Key → ℝ) : Integer.Sparse.eval row20088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20088, Integer.Sparse.eval_collectBalanced, rawRowCheck20088]

theorem rawRowCheck20089 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form8 = rawRow20089 := by decide +kernel

theorem rowCheck20089 : row20089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20089 := by decide +kernel

theorem rowEval20089 (x : Key → ℝ) : Integer.Sparse.eval row20089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20089, Integer.Sparse.eval_collectBalanced, rawRowCheck20089]

theorem rawRowCheck20090 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form8 = rawRow20090 := by decide +kernel

theorem rowCheck20090 : row20090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20090 := by decide +kernel

theorem rowEval20090 (x : Key → ℝ) : Integer.Sparse.eval row20090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20090, Integer.Sparse.eval_collectBalanced, rawRowCheck20090]

theorem rawRowCheck20091 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form8 = rawRow20091 := by decide +kernel

theorem rowCheck20091 : row20091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20091 := by decide +kernel

theorem rowEval20091 (x : Key → ℝ) : Integer.Sparse.eval row20091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20091, Integer.Sparse.eval_collectBalanced, rawRowCheck20091]

theorem rawRowCheck20092 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form8 = rawRow20092 := by decide +kernel

theorem rowCheck20092 : row20092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20092 := by decide +kernel

theorem rowEval20092 (x : Key → ℝ) : Integer.Sparse.eval row20092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20092, Integer.Sparse.eval_collectBalanced, rawRowCheck20092]

theorem rawRowCheck20093 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form8 = rawRow20093 := by decide +kernel

theorem rowCheck20093 : row20093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20093 := by decide +kernel

theorem rowEval20093 (x : Key → ℝ) : Integer.Sparse.eval row20093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20093, Integer.Sparse.eval_collectBalanced, rawRowCheck20093]

theorem rawRowCheck20094 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form8 = rawRow20094 := by decide +kernel

theorem rowCheck20094 : row20094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20094 := by decide +kernel

theorem rowEval20094 (x : Key → ℝ) : Integer.Sparse.eval row20094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20094, Integer.Sparse.eval_collectBalanced, rawRowCheck20094]

theorem rawRowCheck20095 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form8 = rawRow20095 := by decide +kernel

theorem rowCheck20095 : row20095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20095 := by decide +kernel

theorem rowEval20095 (x : Key → ℝ) : Integer.Sparse.eval row20095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20095, Integer.Sparse.eval_collectBalanced, rawRowCheck20095]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block181
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck20096 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form8 = rawRow20096 := by decide +kernel

theorem rowCheck20096 : row20096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20096 := by decide +kernel

theorem rowEval20096 (x : Key → ℝ) : Integer.Sparse.eval row20096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20096, Integer.Sparse.eval_collectBalanced, rawRowCheck20096]

theorem rawRowCheck20097 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form8 = rawRow20097 := by decide +kernel

theorem rowCheck20097 : row20097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20097 := by decide +kernel

theorem rowEval20097 (x : Key → ℝ) : Integer.Sparse.eval row20097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20097, Integer.Sparse.eval_collectBalanced, rawRowCheck20097]

theorem rawRowCheck20098 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form8 = rawRow20098 := by decide +kernel

theorem rowCheck20098 : row20098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20098 := by decide +kernel

theorem rowEval20098 (x : Key → ℝ) : Integer.Sparse.eval row20098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20098, Integer.Sparse.eval_collectBalanced, rawRowCheck20098]

theorem rawRowCheck20099 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form8 = rawRow20099 := by decide +kernel

theorem rowCheck20099 : row20099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20099 := by decide +kernel

theorem rowEval20099 (x : Key → ℝ) : Integer.Sparse.eval row20099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20099, Integer.Sparse.eval_collectBalanced, rawRowCheck20099]

theorem rawRowCheck20100 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form8 = rawRow20100 := by decide +kernel

theorem rowCheck20100 : row20100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20100 := by decide +kernel

theorem rowEval20100 (x : Key → ℝ) : Integer.Sparse.eval row20100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20100, Integer.Sparse.eval_collectBalanced, rawRowCheck20100]

theorem rawRowCheck20101 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form8 = rawRow20101 := by decide +kernel

theorem rowCheck20101 : row20101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20101 := by decide +kernel

theorem rowEval20101 (x : Key → ℝ) : Integer.Sparse.eval row20101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20101, Integer.Sparse.eval_collectBalanced, rawRowCheck20101]

theorem rawRowCheck20102 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form8 = rawRow20102 := by decide +kernel

theorem rowCheck20102 : row20102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20102 := by decide +kernel

theorem rowEval20102 (x : Key → ℝ) : Integer.Sparse.eval row20102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20102, Integer.Sparse.eval_collectBalanced, rawRowCheck20102]

theorem rawRowCheck20103 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form8 = rawRow20103 := by decide +kernel

theorem rowCheck20103 : row20103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20103 := by decide +kernel

theorem rowEval20103 (x : Key → ℝ) : Integer.Sparse.eval row20103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20103, Integer.Sparse.eval_collectBalanced, rawRowCheck20103]

theorem rawRowCheck20104 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form8 = rawRow20104 := by decide +kernel

theorem rowCheck20104 : row20104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20104 := by decide +kernel

theorem rowEval20104 (x : Key → ℝ) : Integer.Sparse.eval row20104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20104, Integer.Sparse.eval_collectBalanced, rawRowCheck20104]

theorem rawRowCheck20105 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form8 = rawRow20105 := by decide +kernel

theorem rowCheck20105 : row20105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20105 := by decide +kernel

theorem rowEval20105 (x : Key → ℝ) : Integer.Sparse.eval row20105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20105, Integer.Sparse.eval_collectBalanced, rawRowCheck20105]

theorem rawRowCheck20106 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form8 = rawRow20106 := by decide +kernel

theorem rowCheck20106 : row20106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20106 := by decide +kernel

theorem rowEval20106 (x : Key → ℝ) : Integer.Sparse.eval row20106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20106, Integer.Sparse.eval_collectBalanced, rawRowCheck20106]

theorem rawRowCheck20107 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form8 = rawRow20107 := by decide +kernel

theorem rowCheck20107 : row20107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20107 := by decide +kernel

theorem rowEval20107 (x : Key → ℝ) : Integer.Sparse.eval row20107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20107, Integer.Sparse.eval_collectBalanced, rawRowCheck20107]

theorem rawRowCheck20108 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form8 = rawRow20108 := by decide +kernel

theorem rowCheck20108 : row20108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20108 := by decide +kernel

theorem rowEval20108 (x : Key → ℝ) : Integer.Sparse.eval row20108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20108, Integer.Sparse.eval_collectBalanced, rawRowCheck20108]

theorem rawRowCheck20109 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form8 = rawRow20109 := by decide +kernel

theorem rowCheck20109 : row20109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20109 := by decide +kernel

theorem rowEval20109 (x : Key → ℝ) : Integer.Sparse.eval row20109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20109, Integer.Sparse.eval_collectBalanced, rawRowCheck20109]

theorem rawRowCheck20110 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form8 = rawRow20110 := by decide +kernel

theorem rowCheck20110 : row20110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20110 := by decide +kernel

theorem rowEval20110 (x : Key → ℝ) : Integer.Sparse.eval row20110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20110, Integer.Sparse.eval_collectBalanced, rawRowCheck20110]

theorem rawRowCheck20111 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form8 = rawRow20111 := by decide +kernel

theorem rowCheck20111 : row20111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20111 := by decide +kernel

theorem rowEval20111 (x : Key → ℝ) : Integer.Sparse.eval row20111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20111, Integer.Sparse.eval_collectBalanced, rawRowCheck20111]

theorem rawRowCheck20112 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form8 = rawRow20112 := by decide +kernel

theorem rowCheck20112 : row20112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20112 := by decide +kernel

theorem rowEval20112 (x : Key → ℝ) : Integer.Sparse.eval row20112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20112, Integer.Sparse.eval_collectBalanced, rawRowCheck20112]

theorem rawRowCheck20113 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form8 = rawRow20113 := by decide +kernel

theorem rowCheck20113 : row20113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20113 := by decide +kernel

theorem rowEval20113 (x : Key → ℝ) : Integer.Sparse.eval row20113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20113, Integer.Sparse.eval_collectBalanced, rawRowCheck20113]

theorem rawRowCheck20114 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form8 = rawRow20114 := by decide +kernel

theorem rowCheck20114 : row20114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20114 := by decide +kernel

theorem rowEval20114 (x : Key → ℝ) : Integer.Sparse.eval row20114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20114, Integer.Sparse.eval_collectBalanced, rawRowCheck20114]

theorem rawRowCheck20115 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form8 = rawRow20115 := by decide +kernel

theorem rowCheck20115 : row20115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20115 := by decide +kernel

theorem rowEval20115 (x : Key → ℝ) : Integer.Sparse.eval row20115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20115, Integer.Sparse.eval_collectBalanced, rawRowCheck20115]

theorem rawRowCheck20116 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form8 = rawRow20116 := by decide +kernel

theorem rowCheck20116 : row20116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20116 := by decide +kernel

theorem rowEval20116 (x : Key → ℝ) : Integer.Sparse.eval row20116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20116, Integer.Sparse.eval_collectBalanced, rawRowCheck20116]

theorem rawRowCheck20117 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form8 = rawRow20117 := by decide +kernel

theorem rowCheck20117 : row20117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20117 := by decide +kernel

theorem rowEval20117 (x : Key → ℝ) : Integer.Sparse.eval row20117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20117, Integer.Sparse.eval_collectBalanced, rawRowCheck20117]

theorem rawRowCheck20118 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form8 = rawRow20118 := by decide +kernel

theorem rowCheck20118 : row20118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20118 := by decide +kernel

theorem rowEval20118 (x : Key → ℝ) : Integer.Sparse.eval row20118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20118, Integer.Sparse.eval_collectBalanced, rawRowCheck20118]

theorem rawRowCheck20119 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form8 = rawRow20119 := by decide +kernel

theorem rowCheck20119 : row20119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20119 := by decide +kernel

theorem rowEval20119 (x : Key → ℝ) : Integer.Sparse.eval row20119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20119, Integer.Sparse.eval_collectBalanced, rawRowCheck20119]

theorem rawRowCheck20120 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form8 = rawRow20120 := by decide +kernel

theorem rowCheck20120 : row20120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20120 := by decide +kernel

theorem rowEval20120 (x : Key → ℝ) : Integer.Sparse.eval row20120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20120, Integer.Sparse.eval_collectBalanced, rawRowCheck20120]

theorem rawRowCheck20121 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form8 = rawRow20121 := by decide +kernel

theorem rowCheck20121 : row20121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20121 := by decide +kernel

theorem rowEval20121 (x : Key → ℝ) : Integer.Sparse.eval row20121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20121, Integer.Sparse.eval_collectBalanced, rawRowCheck20121]

theorem rawRowCheck20122 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form8 = rawRow20122 := by decide +kernel

theorem rowCheck20122 : row20122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20122 := by decide +kernel

theorem rowEval20122 (x : Key → ℝ) : Integer.Sparse.eval row20122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20122, Integer.Sparse.eval_collectBalanced, rawRowCheck20122]

theorem rawRowCheck20123 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form8 = rawRow20123 := by decide +kernel

theorem rowCheck20123 : row20123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20123 := by decide +kernel

theorem rowEval20123 (x : Key → ℝ) : Integer.Sparse.eval row20123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20123, Integer.Sparse.eval_collectBalanced, rawRowCheck20123]

theorem rawRowCheck20124 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form8 = rawRow20124 := by decide +kernel

theorem rowCheck20124 : row20124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20124 := by decide +kernel

theorem rowEval20124 (x : Key → ℝ) : Integer.Sparse.eval row20124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20124, Integer.Sparse.eval_collectBalanced, rawRowCheck20124]

theorem rawRowCheck20125 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form8 = rawRow20125 := by decide +kernel

theorem rowCheck20125 : row20125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20125 := by decide +kernel

theorem rowEval20125 (x : Key → ℝ) : Integer.Sparse.eval row20125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20125, Integer.Sparse.eval_collectBalanced, rawRowCheck20125]

theorem rawRowCheck20126 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form8 = rawRow20126 := by decide +kernel

theorem rowCheck20126 : row20126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20126 := by decide +kernel

theorem rowEval20126 (x : Key → ℝ) : Integer.Sparse.eval row20126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20126, Integer.Sparse.eval_collectBalanced, rawRowCheck20126]

theorem rawRowCheck20127 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form8 = rawRow20127 := by decide +kernel

theorem rowCheck20127 : row20127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20127 := by decide +kernel

theorem rowEval20127 (x : Key → ℝ) : Integer.Sparse.eval row20127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20127, Integer.Sparse.eval_collectBalanced, rawRowCheck20127]

theorem rawRowCheck20128 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form8 = rawRow20128 := by decide +kernel

theorem rowCheck20128 : row20128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20128 := by decide +kernel

theorem rowEval20128 (x : Key → ℝ) : Integer.Sparse.eval row20128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20128, Integer.Sparse.eval_collectBalanced, rawRowCheck20128]

theorem rawRowCheck20129 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form8 = rawRow20129 := by decide +kernel

theorem rowCheck20129 : row20129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20129 := by decide +kernel

theorem rowEval20129 (x : Key → ℝ) : Integer.Sparse.eval row20129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20129, Integer.Sparse.eval_collectBalanced, rawRowCheck20129]

theorem rawRowCheck20130 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form8 = rawRow20130 := by decide +kernel

theorem rowCheck20130 : row20130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20130 := by decide +kernel

theorem rowEval20130 (x : Key → ℝ) : Integer.Sparse.eval row20130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20130, Integer.Sparse.eval_collectBalanced, rawRowCheck20130]

theorem rawRowCheck20131 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form8 = rawRow20131 := by decide +kernel

theorem rowCheck20131 : row20131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20131 := by decide +kernel

theorem rowEval20131 (x : Key → ℝ) : Integer.Sparse.eval row20131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20131, Integer.Sparse.eval_collectBalanced, rawRowCheck20131]

theorem rawRowCheck20132 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form8 = rawRow20132 := by decide +kernel

theorem rowCheck20132 : row20132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20132 := by decide +kernel

theorem rowEval20132 (x : Key → ℝ) : Integer.Sparse.eval row20132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20132, Integer.Sparse.eval_collectBalanced, rawRowCheck20132]

theorem rawRowCheck20133 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form8 = rawRow20133 := by decide +kernel

theorem rowCheck20133 : row20133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20133 := by decide +kernel

theorem rowEval20133 (x : Key → ℝ) : Integer.Sparse.eval row20133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20133, Integer.Sparse.eval_collectBalanced, rawRowCheck20133]

theorem rawRowCheck20134 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form8 = rawRow20134 := by decide +kernel

theorem rowCheck20134 : row20134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20134 := by decide +kernel

theorem rowEval20134 (x : Key → ℝ) : Integer.Sparse.eval row20134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20134, Integer.Sparse.eval_collectBalanced, rawRowCheck20134]

theorem rawRowCheck20135 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form8 = rawRow20135 := by decide +kernel

theorem rowCheck20135 : row20135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20135 := by decide +kernel

theorem rowEval20135 (x : Key → ℝ) : Integer.Sparse.eval row20135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20135, Integer.Sparse.eval_collectBalanced, rawRowCheck20135]

theorem rawRowCheck20136 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form8 = rawRow20136 := by decide +kernel

theorem rowCheck20136 : row20136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20136 := by decide +kernel

theorem rowEval20136 (x : Key → ℝ) : Integer.Sparse.eval row20136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20136, Integer.Sparse.eval_collectBalanced, rawRowCheck20136]

theorem rawRowCheck20137 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form8 = rawRow20137 := by decide +kernel

theorem rowCheck20137 : row20137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20137 := by decide +kernel

theorem rowEval20137 (x : Key → ℝ) : Integer.Sparse.eval row20137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20137, Integer.Sparse.eval_collectBalanced, rawRowCheck20137]

theorem rawRowCheck20138 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form8 = rawRow20138 := by decide +kernel

theorem rowCheck20138 : row20138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20138 := by decide +kernel

theorem rowEval20138 (x : Key → ℝ) : Integer.Sparse.eval row20138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20138, Integer.Sparse.eval_collectBalanced, rawRowCheck20138]

theorem rawRowCheck20139 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form8 = rawRow20139 := by decide +kernel

theorem rowCheck20139 : row20139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20139 := by decide +kernel

theorem rowEval20139 (x : Key → ℝ) : Integer.Sparse.eval row20139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20139, Integer.Sparse.eval_collectBalanced, rawRowCheck20139]

theorem rawRowCheck20140 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form8 = rawRow20140 := by decide +kernel

theorem rowCheck20140 : row20140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20140 := by decide +kernel

theorem rowEval20140 (x : Key → ℝ) : Integer.Sparse.eval row20140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form8) x := by
  rw [rowCheck20140, Integer.Sparse.eval_collectBalanced, rawRowCheck20140]

theorem rawRowCheck20141 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form8 = rawRow20141 := by decide +kernel

theorem rowCheck20141 : row20141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20141 := by decide +kernel

theorem rowEval20141 (x : Key → ℝ) : Integer.Sparse.eval row20141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20141, Integer.Sparse.eval_collectBalanced, rawRowCheck20141]

theorem rawRowCheck20142 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form8 = rawRow20142 := by decide +kernel

theorem rowCheck20142 : row20142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20142 := by decide +kernel

theorem rowEval20142 (x : Key → ℝ) : Integer.Sparse.eval row20142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form8) x := by
  rw [rowCheck20142, Integer.Sparse.eval_collectBalanced, rawRowCheck20142]

theorem rawRowCheck20143 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form8 = rawRow20143 := by decide +kernel

theorem rowCheck20143 : row20143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20143 := by decide +kernel

theorem rowEval20143 (x : Key → ℝ) : Integer.Sparse.eval row20143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form8) x := by
  rw [rowCheck20143, Integer.Sparse.eval_collectBalanced, rawRowCheck20143]

theorem rawRowCheck20144 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form9 = rawRow20144 := by decide +kernel

theorem rowCheck20144 : row20144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20144 := by decide +kernel

theorem rowEval20144 (x : Key → ℝ) : Integer.Sparse.eval row20144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20144, Integer.Sparse.eval_collectBalanced, rawRowCheck20144]

theorem rawRowCheck20145 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form9 = rawRow20145 := by decide +kernel

theorem rowCheck20145 : row20145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20145 := by decide +kernel

theorem rowEval20145 (x : Key → ℝ) : Integer.Sparse.eval row20145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20145, Integer.Sparse.eval_collectBalanced, rawRowCheck20145]

theorem rawRowCheck20146 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form9 = rawRow20146 := by decide +kernel

theorem rowCheck20146 : row20146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20146 := by decide +kernel

theorem rowEval20146 (x : Key → ℝ) : Integer.Sparse.eval row20146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20146, Integer.Sparse.eval_collectBalanced, rawRowCheck20146]

theorem rawRowCheck20147 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form9 = rawRow20147 := by decide +kernel

theorem rowCheck20147 : row20147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20147 := by decide +kernel

theorem rowEval20147 (x : Key → ℝ) : Integer.Sparse.eval row20147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20147, Integer.Sparse.eval_collectBalanced, rawRowCheck20147]

theorem rawRowCheck20148 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form9 = rawRow20148 := by decide +kernel

theorem rowCheck20148 : row20148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20148 := by decide +kernel

theorem rowEval20148 (x : Key → ℝ) : Integer.Sparse.eval row20148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20148, Integer.Sparse.eval_collectBalanced, rawRowCheck20148]

theorem rawRowCheck20149 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form9 = rawRow20149 := by decide +kernel

theorem rowCheck20149 : row20149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20149 := by decide +kernel

theorem rowEval20149 (x : Key → ℝ) : Integer.Sparse.eval row20149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20149, Integer.Sparse.eval_collectBalanced, rawRowCheck20149]

theorem rawRowCheck20150 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form9 = rawRow20150 := by decide +kernel

theorem rowCheck20150 : row20150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20150 := by decide +kernel

theorem rowEval20150 (x : Key → ℝ) : Integer.Sparse.eval row20150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20150, Integer.Sparse.eval_collectBalanced, rawRowCheck20150]

theorem rawRowCheck20151 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form9 = rawRow20151 := by decide +kernel

theorem rowCheck20151 : row20151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20151 := by decide +kernel

theorem rowEval20151 (x : Key → ℝ) : Integer.Sparse.eval row20151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20151, Integer.Sparse.eval_collectBalanced, rawRowCheck20151]

theorem rawRowCheck20152 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form9 = rawRow20152 := by decide +kernel

theorem rowCheck20152 : row20152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20152 := by decide +kernel

theorem rowEval20152 (x : Key → ℝ) : Integer.Sparse.eval row20152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20152, Integer.Sparse.eval_collectBalanced, rawRowCheck20152]

theorem rawRowCheck20153 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form9 = rawRow20153 := by decide +kernel

theorem rowCheck20153 : row20153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20153 := by decide +kernel

theorem rowEval20153 (x : Key → ℝ) : Integer.Sparse.eval row20153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20153, Integer.Sparse.eval_collectBalanced, rawRowCheck20153]

theorem rawRowCheck20154 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form9 = rawRow20154 := by decide +kernel

theorem rowCheck20154 : row20154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20154 := by decide +kernel

theorem rowEval20154 (x : Key → ℝ) : Integer.Sparse.eval row20154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20154, Integer.Sparse.eval_collectBalanced, rawRowCheck20154]

theorem rawRowCheck20155 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form9 = rawRow20155 := by decide +kernel

theorem rowCheck20155 : row20155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20155 := by decide +kernel

theorem rowEval20155 (x : Key → ℝ) : Integer.Sparse.eval row20155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20155, Integer.Sparse.eval_collectBalanced, rawRowCheck20155]

theorem rawRowCheck20156 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form9 = rawRow20156 := by decide +kernel

theorem rowCheck20156 : row20156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20156 := by decide +kernel

theorem rowEval20156 (x : Key → ℝ) : Integer.Sparse.eval row20156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20156, Integer.Sparse.eval_collectBalanced, rawRowCheck20156]

theorem rawRowCheck20157 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form9 = rawRow20157 := by decide +kernel

theorem rowCheck20157 : row20157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20157 := by decide +kernel

theorem rowEval20157 (x : Key → ℝ) : Integer.Sparse.eval row20157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20157, Integer.Sparse.eval_collectBalanced, rawRowCheck20157]

theorem rawRowCheck20158 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form9 = rawRow20158 := by decide +kernel

theorem rowCheck20158 : row20158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20158 := by decide +kernel

theorem rowEval20158 (x : Key → ℝ) : Integer.Sparse.eval row20158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20158, Integer.Sparse.eval_collectBalanced, rawRowCheck20158]

theorem rawRowCheck20159 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form9 = rawRow20159 := by decide +kernel

theorem rowCheck20159 : row20159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20159 := by decide +kernel

theorem rowEval20159 (x : Key → ℝ) : Integer.Sparse.eval row20159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20159, Integer.Sparse.eval_collectBalanced, rawRowCheck20159]

theorem rawRowCheck20160 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form9 = rawRow20160 := by decide +kernel

theorem rowCheck20160 : row20160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20160 := by decide +kernel

theorem rowEval20160 (x : Key → ℝ) : Integer.Sparse.eval row20160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20160, Integer.Sparse.eval_collectBalanced, rawRowCheck20160]

theorem rawRowCheck20161 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form9 = rawRow20161 := by decide +kernel

theorem rowCheck20161 : row20161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20161 := by decide +kernel

theorem rowEval20161 (x : Key → ℝ) : Integer.Sparse.eval row20161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20161, Integer.Sparse.eval_collectBalanced, rawRowCheck20161]

theorem rawRowCheck20162 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form9 = rawRow20162 := by decide +kernel

theorem rowCheck20162 : row20162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20162 := by decide +kernel

theorem rowEval20162 (x : Key → ℝ) : Integer.Sparse.eval row20162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20162, Integer.Sparse.eval_collectBalanced, rawRowCheck20162]

theorem rawRowCheck20163 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form9 = rawRow20163 := by decide +kernel

theorem rowCheck20163 : row20163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20163 := by decide +kernel

theorem rowEval20163 (x : Key → ℝ) : Integer.Sparse.eval row20163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20163, Integer.Sparse.eval_collectBalanced, rawRowCheck20163]

theorem rawRowCheck20164 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form9 = rawRow20164 := by decide +kernel

theorem rowCheck20164 : row20164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20164 := by decide +kernel

theorem rowEval20164 (x : Key → ℝ) : Integer.Sparse.eval row20164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20164, Integer.Sparse.eval_collectBalanced, rawRowCheck20164]

theorem rawRowCheck20165 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form9 = rawRow20165 := by decide +kernel

theorem rowCheck20165 : row20165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20165 := by decide +kernel

theorem rowEval20165 (x : Key → ℝ) : Integer.Sparse.eval row20165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20165, Integer.Sparse.eval_collectBalanced, rawRowCheck20165]

theorem rawRowCheck20166 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form9 = rawRow20166 := by decide +kernel

theorem rowCheck20166 : row20166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20166 := by decide +kernel

theorem rowEval20166 (x : Key → ℝ) : Integer.Sparse.eval row20166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20166, Integer.Sparse.eval_collectBalanced, rawRowCheck20166]

theorem rawRowCheck20167 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form9 = rawRow20167 := by decide +kernel

theorem rowCheck20167 : row20167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20167 := by decide +kernel

theorem rowEval20167 (x : Key → ℝ) : Integer.Sparse.eval row20167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20167, Integer.Sparse.eval_collectBalanced, rawRowCheck20167]

theorem rawRowCheck20168 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form9 = rawRow20168 := by decide +kernel

theorem rowCheck20168 : row20168 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20168 := by decide +kernel

theorem rowEval20168 (x : Key → ℝ) : Integer.Sparse.eval row20168 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20168, Integer.Sparse.eval_collectBalanced, rawRowCheck20168]

theorem rawRowCheck20169 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form9 = rawRow20169 := by decide +kernel

theorem rowCheck20169 : row20169 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20169 := by decide +kernel

theorem rowEval20169 (x : Key → ℝ) : Integer.Sparse.eval row20169 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20169, Integer.Sparse.eval_collectBalanced, rawRowCheck20169]

theorem rawRowCheck20170 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form9 = rawRow20170 := by decide +kernel

theorem rowCheck20170 : row20170 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20170 := by decide +kernel

theorem rowEval20170 (x : Key → ℝ) : Integer.Sparse.eval row20170 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20170, Integer.Sparse.eval_collectBalanced, rawRowCheck20170]

theorem rawRowCheck20171 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form9 = rawRow20171 := by decide +kernel

theorem rowCheck20171 : row20171 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20171 := by decide +kernel

theorem rowEval20171 (x : Key → ℝ) : Integer.Sparse.eval row20171 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20171, Integer.Sparse.eval_collectBalanced, rawRowCheck20171]

theorem rawRowCheck20172 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form9 = rawRow20172 := by decide +kernel

theorem rowCheck20172 : row20172 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20172 := by decide +kernel

theorem rowEval20172 (x : Key → ℝ) : Integer.Sparse.eval row20172 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20172, Integer.Sparse.eval_collectBalanced, rawRowCheck20172]

theorem rawRowCheck20173 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form9 = rawRow20173 := by decide +kernel

theorem rowCheck20173 : row20173 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20173 := by decide +kernel

theorem rowEval20173 (x : Key → ℝ) : Integer.Sparse.eval row20173 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20173, Integer.Sparse.eval_collectBalanced, rawRowCheck20173]

theorem rawRowCheck20174 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form9 = rawRow20174 := by decide +kernel

theorem rowCheck20174 : row20174 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20174 := by decide +kernel

theorem rowEval20174 (x : Key → ℝ) : Integer.Sparse.eval row20174 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20174, Integer.Sparse.eval_collectBalanced, rawRowCheck20174]

theorem rawRowCheck20175 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form9 = rawRow20175 := by decide +kernel

theorem rowCheck20175 : row20175 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20175 := by decide +kernel

theorem rowEval20175 (x : Key → ℝ) : Integer.Sparse.eval row20175 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20175, Integer.Sparse.eval_collectBalanced, rawRowCheck20175]

theorem rawRowCheck20176 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form9 = rawRow20176 := by decide +kernel

theorem rowCheck20176 : row20176 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20176 := by decide +kernel

theorem rowEval20176 (x : Key → ℝ) : Integer.Sparse.eval row20176 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20176, Integer.Sparse.eval_collectBalanced, rawRowCheck20176]

theorem rawRowCheck20177 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form9 = rawRow20177 := by decide +kernel

theorem rowCheck20177 : row20177 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20177 := by decide +kernel

theorem rowEval20177 (x : Key → ℝ) : Integer.Sparse.eval row20177 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20177, Integer.Sparse.eval_collectBalanced, rawRowCheck20177]

theorem rawRowCheck20178 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form9 = rawRow20178 := by decide +kernel

theorem rowCheck20178 : row20178 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20178 := by decide +kernel

theorem rowEval20178 (x : Key → ℝ) : Integer.Sparse.eval row20178 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20178, Integer.Sparse.eval_collectBalanced, rawRowCheck20178]

theorem rawRowCheck20179 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form9 = rawRow20179 := by decide +kernel

theorem rowCheck20179 : row20179 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20179 := by decide +kernel

theorem rowEval20179 (x : Key → ℝ) : Integer.Sparse.eval row20179 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20179, Integer.Sparse.eval_collectBalanced, rawRowCheck20179]

theorem rawRowCheck20180 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form9 = rawRow20180 := by decide +kernel

theorem rowCheck20180 : row20180 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20180 := by decide +kernel

theorem rowEval20180 (x : Key → ℝ) : Integer.Sparse.eval row20180 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20180, Integer.Sparse.eval_collectBalanced, rawRowCheck20180]

theorem rawRowCheck20181 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form9 = rawRow20181 := by decide +kernel

theorem rowCheck20181 : row20181 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20181 := by decide +kernel

theorem rowEval20181 (x : Key → ℝ) : Integer.Sparse.eval row20181 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20181, Integer.Sparse.eval_collectBalanced, rawRowCheck20181]

theorem rawRowCheck20182 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form9 = rawRow20182 := by decide +kernel

theorem rowCheck20182 : row20182 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20182 := by decide +kernel

theorem rowEval20182 (x : Key → ℝ) : Integer.Sparse.eval row20182 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20182, Integer.Sparse.eval_collectBalanced, rawRowCheck20182]

theorem rawRowCheck20183 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form9 = rawRow20183 := by decide +kernel

theorem rowCheck20183 : row20183 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20183 := by decide +kernel

theorem rowEval20183 (x : Key → ℝ) : Integer.Sparse.eval row20183 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20183, Integer.Sparse.eval_collectBalanced, rawRowCheck20183]

theorem rawRowCheck20184 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form9 = rawRow20184 := by decide +kernel

theorem rowCheck20184 : row20184 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20184 := by decide +kernel

theorem rowEval20184 (x : Key → ℝ) : Integer.Sparse.eval row20184 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20184, Integer.Sparse.eval_collectBalanced, rawRowCheck20184]

theorem rawRowCheck20185 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form9 = rawRow20185 := by decide +kernel

theorem rowCheck20185 : row20185 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20185 := by decide +kernel

theorem rowEval20185 (x : Key → ℝ) : Integer.Sparse.eval row20185 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20185, Integer.Sparse.eval_collectBalanced, rawRowCheck20185]

theorem rawRowCheck20186 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form9 = rawRow20186 := by decide +kernel

theorem rowCheck20186 : row20186 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20186 := by decide +kernel

theorem rowEval20186 (x : Key → ℝ) : Integer.Sparse.eval row20186 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20186, Integer.Sparse.eval_collectBalanced, rawRowCheck20186]

theorem rawRowCheck20187 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form9 = rawRow20187 := by decide +kernel

theorem rowCheck20187 : row20187 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20187 := by decide +kernel

theorem rowEval20187 (x : Key → ℝ) : Integer.Sparse.eval row20187 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20187, Integer.Sparse.eval_collectBalanced, rawRowCheck20187]

theorem rawRowCheck20188 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form9 = rawRow20188 := by decide +kernel

theorem rowCheck20188 : row20188 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20188 := by decide +kernel

theorem rowEval20188 (x : Key → ℝ) : Integer.Sparse.eval row20188 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20188, Integer.Sparse.eval_collectBalanced, rawRowCheck20188]

theorem rawRowCheck20189 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form9 = rawRow20189 := by decide +kernel

theorem rowCheck20189 : row20189 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20189 := by decide +kernel

theorem rowEval20189 (x : Key → ℝ) : Integer.Sparse.eval row20189 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20189, Integer.Sparse.eval_collectBalanced, rawRowCheck20189]

theorem rawRowCheck20190 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form9 = rawRow20190 := by decide +kernel

theorem rowCheck20190 : row20190 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20190 := by decide +kernel

theorem rowEval20190 (x : Key → ℝ) : Integer.Sparse.eval row20190 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20190, Integer.Sparse.eval_collectBalanced, rawRowCheck20190]

theorem rawRowCheck20191 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form9 = rawRow20191 := by decide +kernel

theorem rowCheck20191 : row20191 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20191 := by decide +kernel

theorem rowEval20191 (x : Key → ℝ) : Integer.Sparse.eval row20191 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20191, Integer.Sparse.eval_collectBalanced, rawRowCheck20191]

theorem rawRowCheck20192 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form9 = rawRow20192 := by decide +kernel

theorem rowCheck20192 : row20192 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20192 := by decide +kernel

theorem rowEval20192 (x : Key → ℝ) : Integer.Sparse.eval row20192 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20192, Integer.Sparse.eval_collectBalanced, rawRowCheck20192]

theorem rawRowCheck20193 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form9 = rawRow20193 := by decide +kernel

theorem rowCheck20193 : row20193 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20193 := by decide +kernel

theorem rowEval20193 (x : Key → ℝ) : Integer.Sparse.eval row20193 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20193, Integer.Sparse.eval_collectBalanced, rawRowCheck20193]

theorem rawRowCheck20194 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form9 = rawRow20194 := by decide +kernel

theorem rowCheck20194 : row20194 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20194 := by decide +kernel

theorem rowEval20194 (x : Key → ℝ) : Integer.Sparse.eval row20194 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20194, Integer.Sparse.eval_collectBalanced, rawRowCheck20194]

theorem rawRowCheck20195 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form9 = rawRow20195 := by decide +kernel

theorem rowCheck20195 : row20195 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20195 := by decide +kernel

theorem rowEval20195 (x : Key → ℝ) : Integer.Sparse.eval row20195 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20195, Integer.Sparse.eval_collectBalanced, rawRowCheck20195]

theorem rawRowCheck20196 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form9 = rawRow20196 := by decide +kernel

theorem rowCheck20196 : row20196 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20196 := by decide +kernel

theorem rowEval20196 (x : Key → ℝ) : Integer.Sparse.eval row20196 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20196, Integer.Sparse.eval_collectBalanced, rawRowCheck20196]

theorem rawRowCheck20197 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form9 = rawRow20197 := by decide +kernel

theorem rowCheck20197 : row20197 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20197 := by decide +kernel

theorem rowEval20197 (x : Key → ℝ) : Integer.Sparse.eval row20197 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20197, Integer.Sparse.eval_collectBalanced, rawRowCheck20197]

theorem rawRowCheck20198 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form9 = rawRow20198 := by decide +kernel

theorem rowCheck20198 : row20198 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20198 := by decide +kernel

theorem rowEval20198 (x : Key → ℝ) : Integer.Sparse.eval row20198 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20198, Integer.Sparse.eval_collectBalanced, rawRowCheck20198]

theorem rawRowCheck20199 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form9 = rawRow20199 := by decide +kernel

theorem rowCheck20199 : row20199 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20199 := by decide +kernel

theorem rowEval20199 (x : Key → ℝ) : Integer.Sparse.eval row20199 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20199, Integer.Sparse.eval_collectBalanced, rawRowCheck20199]

theorem rawRowCheck20200 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form9 = rawRow20200 := by decide +kernel

theorem rowCheck20200 : row20200 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20200 := by decide +kernel

theorem rowEval20200 (x : Key → ℝ) : Integer.Sparse.eval row20200 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form9) x := by
  rw [rowCheck20200, Integer.Sparse.eval_collectBalanced, rawRowCheck20200]

theorem rawRowCheck20201 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form9 = rawRow20201 := by decide +kernel

theorem rowCheck20201 : row20201 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20201 := by decide +kernel

theorem rowEval20201 (x : Key → ℝ) : Integer.Sparse.eval row20201 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20201, Integer.Sparse.eval_collectBalanced, rawRowCheck20201]

theorem rawRowCheck20202 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form9 = rawRow20202 := by decide +kernel

theorem rowCheck20202 : row20202 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20202 := by decide +kernel

theorem rowEval20202 (x : Key → ℝ) : Integer.Sparse.eval row20202 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form9) x := by
  rw [rowCheck20202, Integer.Sparse.eval_collectBalanced, rawRowCheck20202]

theorem rawRowCheck20203 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form9 = rawRow20203 := by decide +kernel

theorem rowCheck20203 : row20203 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20203 := by decide +kernel

theorem rowEval20203 (x : Key → ℝ) : Integer.Sparse.eval row20203 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form9) x := by
  rw [rowCheck20203, Integer.Sparse.eval_collectBalanced, rawRowCheck20203]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form0) x := by
  fin_cases k
  · exact rowEval19604 x
  · exact rowEval19605 x
  · exact rowEval19606 x
  · exact rowEval19607 x
  · exact rowEval19608 x
  · exact rowEval19609 x
  · exact rowEval19610 x
  · exact rowEval19611 x
  · exact rowEval19612 x
  · exact rowEval19613 x
  · exact rowEval19614 x
  · exact rowEval19615 x
  · exact rowEval19616 x
  · exact rowEval19617 x
  · exact rowEval19618 x
  · exact rowEval19619 x
  · exact rowEval19620 x
  · exact rowEval19621 x
  · exact rowEval19622 x
  · exact rowEval19623 x
  · exact rowEval19624 x
  · exact rowEval19625 x
  · exact rowEval19626 x
  · exact rowEval19627 x
  · exact rowEval19628 x
  · exact rowEval19629 x
  · exact rowEval19630 x
  · exact rowEval19631 x
  · exact rowEval19632 x
  · exact rowEval19633 x
  · exact rowEval19634 x
  · exact rowEval19635 x
  · exact rowEval19636 x
  · exact rowEval19637 x
  · exact rowEval19638 x
  · exact rowEval19639 x
  · exact rowEval19640 x
  · exact rowEval19641 x
  · exact rowEval19642 x
  · exact rowEval19643 x
  · exact rowEval19644 x
  · exact rowEval19645 x
  · exact rowEval19646 x
  · exact rowEval19647 x
  · exact rowEval19648 x
  · exact rowEval19649 x
  · exact rowEval19650 x
  · exact rowEval19651 x
  · exact rowEval19652 x
  · exact rowEval19653 x
  · exact rowEval19654 x
  · exact rowEval19655 x
  · exact rowEval19656 x
  · exact rowEval19657 x
  · exact rowEval19658 x
  · exact rowEval19659 x
  · exact rowEval19660 x
  · exact rowEval19661 x
  · exact rowEval19662 x
  · exact rowEval19663 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form1) x := by
  fin_cases k
  · exact rowEval19664 x
  · exact rowEval19665 x
  · exact rowEval19666 x
  · exact rowEval19667 x
  · exact rowEval19668 x
  · exact rowEval19669 x
  · exact rowEval19670 x
  · exact rowEval19671 x
  · exact rowEval19672 x
  · exact rowEval19673 x
  · exact rowEval19674 x
  · exact rowEval19675 x
  · exact rowEval19676 x
  · exact rowEval19677 x
  · exact rowEval19678 x
  · exact rowEval19679 x
  · exact rowEval19680 x
  · exact rowEval19681 x
  · exact rowEval19682 x
  · exact rowEval19683 x
  · exact rowEval19684 x
  · exact rowEval19685 x
  · exact rowEval19686 x
  · exact rowEval19687 x
  · exact rowEval19688 x
  · exact rowEval19689 x
  · exact rowEval19690 x
  · exact rowEval19691 x
  · exact rowEval19692 x
  · exact rowEval19693 x
  · exact rowEval19694 x
  · exact rowEval19695 x
  · exact rowEval19696 x
  · exact rowEval19697 x
  · exact rowEval19698 x
  · exact rowEval19699 x
  · exact rowEval19700 x
  · exact rowEval19701 x
  · exact rowEval19702 x
  · exact rowEval19703 x
  · exact rowEval19704 x
  · exact rowEval19705 x
  · exact rowEval19706 x
  · exact rowEval19707 x
  · exact rowEval19708 x
  · exact rowEval19709 x
  · exact rowEval19710 x
  · exact rowEval19711 x
  · exact rowEval19712 x
  · exact rowEval19713 x
  · exact rowEval19714 x
  · exact rowEval19715 x
  · exact rowEval19716 x
  · exact rowEval19717 x
  · exact rowEval19718 x
  · exact rowEval19719 x
  · exact rowEval19720 x
  · exact rowEval19721 x
  · exact rowEval19722 x
  · exact rowEval19723 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form7) x := by
  fin_cases k
  · exact rowEval20024 x
  · exact rowEval20025 x
  · exact rowEval20026 x
  · exact rowEval20027 x
  · exact rowEval20028 x
  · exact rowEval20029 x
  · exact rowEval20030 x
  · exact rowEval20031 x
  · exact rowEval20032 x
  · exact rowEval20033 x
  · exact rowEval20034 x
  · exact rowEval20035 x
  · exact rowEval20036 x
  · exact rowEval20037 x
  · exact rowEval20038 x
  · exact rowEval20039 x
  · exact rowEval20040 x
  · exact rowEval20041 x
  · exact rowEval20042 x
  · exact rowEval20043 x
  · exact rowEval20044 x
  · exact rowEval20045 x
  · exact rowEval20046 x
  · exact rowEval20047 x
  · exact rowEval20048 x
  · exact rowEval20049 x
  · exact rowEval20050 x
  · exact rowEval20051 x
  · exact rowEval20052 x
  · exact rowEval20053 x
  · exact rowEval20054 x
  · exact rowEval20055 x
  · exact rowEval20056 x
  · exact rowEval20057 x
  · exact rowEval20058 x
  · exact rowEval20059 x
  · exact rowEval20060 x
  · exact rowEval20061 x
  · exact rowEval20062 x
  · exact rowEval20063 x
  · exact rowEval20064 x
  · exact rowEval20065 x
  · exact rowEval20066 x
  · exact rowEval20067 x
  · exact rowEval20068 x
  · exact rowEval20069 x
  · exact rowEval20070 x
  · exact rowEval20071 x
  · exact rowEval20072 x
  · exact rowEval20073 x
  · exact rowEval20074 x
  · exact rowEval20075 x
  · exact rowEval20076 x
  · exact rowEval20077 x
  · exact rowEval20078 x
  · exact rowEval20079 x
  · exact rowEval20080 x
  · exact rowEval20081 x
  · exact rowEval20082 x
  · exact rowEval20083 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form8) x := by
  fin_cases k
  · exact rowEval20084 x
  · exact rowEval20085 x
  · exact rowEval20086 x
  · exact rowEval20087 x
  · exact rowEval20088 x
  · exact rowEval20089 x
  · exact rowEval20090 x
  · exact rowEval20091 x
  · exact rowEval20092 x
  · exact rowEval20093 x
  · exact rowEval20094 x
  · exact rowEval20095 x
  · exact rowEval20096 x
  · exact rowEval20097 x
  · exact rowEval20098 x
  · exact rowEval20099 x
  · exact rowEval20100 x
  · exact rowEval20101 x
  · exact rowEval20102 x
  · exact rowEval20103 x
  · exact rowEval20104 x
  · exact rowEval20105 x
  · exact rowEval20106 x
  · exact rowEval20107 x
  · exact rowEval20108 x
  · exact rowEval20109 x
  · exact rowEval20110 x
  · exact rowEval20111 x
  · exact rowEval20112 x
  · exact rowEval20113 x
  · exact rowEval20114 x
  · exact rowEval20115 x
  · exact rowEval20116 x
  · exact rowEval20117 x
  · exact rowEval20118 x
  · exact rowEval20119 x
  · exact rowEval20120 x
  · exact rowEval20121 x
  · exact rowEval20122 x
  · exact rowEval20123 x
  · exact rowEval20124 x
  · exact rowEval20125 x
  · exact rowEval20126 x
  · exact rowEval20127 x
  · exact rowEval20128 x
  · exact rowEval20129 x
  · exact rowEval20130 x
  · exact rowEval20131 x
  · exact rowEval20132 x
  · exact rowEval20133 x
  · exact rowEval20134 x
  · exact rowEval20135 x
  · exact rowEval20136 x
  · exact rowEval20137 x
  · exact rowEval20138 x
  · exact rowEval20139 x
  · exact rowEval20140 x
  · exact rowEval20141 x
  · exact rowEval20142 x
  · exact rowEval20143 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form9) x := by
  fin_cases k
  · exact rowEval20144 x
  · exact rowEval20145 x
  · exact rowEval20146 x
  · exact rowEval20147 x
  · exact rowEval20148 x
  · exact rowEval20149 x
  · exact rowEval20150 x
  · exact rowEval20151 x
  · exact rowEval20152 x
  · exact rowEval20153 x
  · exact rowEval20154 x
  · exact rowEval20155 x
  · exact rowEval20156 x
  · exact rowEval20157 x
  · exact rowEval20158 x
  · exact rowEval20159 x
  · exact rowEval20160 x
  · exact rowEval20161 x
  · exact rowEval20162 x
  · exact rowEval20163 x
  · exact rowEval20164 x
  · exact rowEval20165 x
  · exact rowEval20166 x
  · exact rowEval20167 x
  · exact rowEval20168 x
  · exact rowEval20169 x
  · exact rowEval20170 x
  · exact rowEval20171 x
  · exact rowEval20172 x
  · exact rowEval20173 x
  · exact rowEval20174 x
  · exact rowEval20175 x
  · exact rowEval20176 x
  · exact rowEval20177 x
  · exact rowEval20178 x
  · exact rowEval20179 x
  · exact rowEval20180 x
  · exact rowEval20181 x
  · exact rowEval20182 x
  · exact rowEval20183 x
  · exact rowEval20184 x
  · exact rowEval20185 x
  · exact rowEval20186 x
  · exact rowEval20187 x
  · exact rowEval20188 x
  · exact rowEval20189 x
  · exact rowEval20190 x
  · exact rowEval20191 x
  · exact rowEval20192 x
  · exact rowEval20193 x
  · exact rowEval20194 x
  · exact rowEval20195 x
  · exact rowEval20196 x
  · exact rowEval20197 x
  · exact rowEval20198 x
  · exact rowEval20199 x
  · exact rowEval20200 x
  · exact rowEval20201 x
  · exact rowEval20202 x
  · exact rowEval20203 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

theorem entryEvalRow11_e_oai (j : Fin 12) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 11 j) (GramNormalization.eval B) =
      (GramFunctions.Block5.forms 11).mixedGram (GramFunctions.Block5.forms j) B := by
  fin_cases j
  · exact entryEval11_0 B hB
  · exact entryEval11_1 B hB
  · exact entryEval11_2_e B hB
  · exact entryEval11_3_e B hB
  · exact entryEval11_4_e B hB
  · exact entryEval11_5_e B hB
  · exact entryEval11_6_e B hB
  · exact entryEval11_7 B hB
  · exact entryEval11_8 B hB
  · exact entryEval11_9 B hB
  · exact entryEval11_10_e B hB
  · exact entryEval11_11_e B hB

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEvalRow11_e_oai
