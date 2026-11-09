-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T16:56:50.130028+00:00
-- url     : https://prove2.me/submissions/29ddde84-5e90-43b2-8b4e-709fb3cb4061

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E023
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E055
import Definitions.Def_OAIQ106E056
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block2_entryEval10_8_e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block79
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7048 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form1 = rawRow7048 := by decide +kernel

theorem rowCheck7048 : row7048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7048 := by decide +kernel

theorem rowEval7048 (x : Key → ℝ) : Integer.Sparse.eval row7048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7048, Integer.Sparse.eval_collectBalanced, rawRowCheck7048]

theorem rawRowCheck7049 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form1 = rawRow7049 := by decide +kernel

theorem rowCheck7049 : row7049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7049 := by decide +kernel

theorem rowEval7049 (x : Key → ℝ) : Integer.Sparse.eval row7049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7049, Integer.Sparse.eval_collectBalanced, rawRowCheck7049]

theorem rawRowCheck7050 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form1 = rawRow7050 := by decide +kernel

theorem rowCheck7050 : row7050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7050 := by decide +kernel

theorem rowEval7050 (x : Key → ℝ) : Integer.Sparse.eval row7050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7050, Integer.Sparse.eval_collectBalanced, rawRowCheck7050]

theorem rawRowCheck7051 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow7051 := by decide +kernel

theorem rowCheck7051 : row7051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7051 := by decide +kernel

theorem rowEval7051 (x : Key → ℝ) : Integer.Sparse.eval row7051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7051, Integer.Sparse.eval_collectBalanced, rawRowCheck7051]

theorem rawRowCheck7052 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow7052 := by decide +kernel

theorem rowCheck7052 : row7052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7052 := by decide +kernel

theorem rowEval7052 (x : Key → ℝ) : Integer.Sparse.eval row7052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7052, Integer.Sparse.eval_collectBalanced, rawRowCheck7052]

theorem rawRowCheck7053 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow7053 := by decide +kernel

theorem rowCheck7053 : row7053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7053 := by decide +kernel

theorem rowEval7053 (x : Key → ℝ) : Integer.Sparse.eval row7053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7053, Integer.Sparse.eval_collectBalanced, rawRowCheck7053]

theorem rawRowCheck7054 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form1 = rawRow7054 := by decide +kernel

theorem rowCheck7054 : row7054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7054 := by decide +kernel

theorem rowEval7054 (x : Key → ℝ) : Integer.Sparse.eval row7054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7054, Integer.Sparse.eval_collectBalanced, rawRowCheck7054]

theorem rawRowCheck7055 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form1 = rawRow7055 := by decide +kernel

theorem rowCheck7055 : row7055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7055 := by decide +kernel

theorem rowEval7055 (x : Key → ℝ) : Integer.Sparse.eval row7055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7055, Integer.Sparse.eval_collectBalanced, rawRowCheck7055]

theorem rawRowCheck7056 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form1 = rawRow7056 := by decide +kernel

theorem rowCheck7056 : row7056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7056 := by decide +kernel

theorem rowEval7056 (x : Key → ℝ) : Integer.Sparse.eval row7056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7056, Integer.Sparse.eval_collectBalanced, rawRowCheck7056]

theorem rawRowCheck7057 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form1 = rawRow7057 := by decide +kernel

theorem rowCheck7057 : row7057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7057 := by decide +kernel

theorem rowEval7057 (x : Key → ℝ) : Integer.Sparse.eval row7057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7057, Integer.Sparse.eval_collectBalanced, rawRowCheck7057]

theorem rawRowCheck7058 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form1 = rawRow7058 := by decide +kernel

theorem rowCheck7058 : row7058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7058 := by decide +kernel

theorem rowEval7058 (x : Key → ℝ) : Integer.Sparse.eval row7058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7058, Integer.Sparse.eval_collectBalanced, rawRowCheck7058]

theorem rawRowCheck7059 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form1 = rawRow7059 := by decide +kernel

theorem rowCheck7059 : row7059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7059 := by decide +kernel

theorem rowEval7059 (x : Key → ℝ) : Integer.Sparse.eval row7059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7059, Integer.Sparse.eval_collectBalanced, rawRowCheck7059]

theorem rawRowCheck7060 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form1 = rawRow7060 := by decide +kernel

theorem rowCheck7060 : row7060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7060 := by decide +kernel

theorem rowEval7060 (x : Key → ℝ) : Integer.Sparse.eval row7060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7060, Integer.Sparse.eval_collectBalanced, rawRowCheck7060]

theorem rawRowCheck7061 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form1 = rawRow7061 := by decide +kernel

theorem rowCheck7061 : row7061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7061 := by decide +kernel

theorem rowEval7061 (x : Key → ℝ) : Integer.Sparse.eval row7061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7061, Integer.Sparse.eval_collectBalanced, rawRowCheck7061]

theorem rawRowCheck7062 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form1 = rawRow7062 := by decide +kernel

theorem rowCheck7062 : row7062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7062 := by decide +kernel

theorem rowEval7062 (x : Key → ℝ) : Integer.Sparse.eval row7062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7062, Integer.Sparse.eval_collectBalanced, rawRowCheck7062]

theorem rawRowCheck7063 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form1 = rawRow7063 := by decide +kernel

theorem rowCheck7063 : row7063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7063 := by decide +kernel

theorem rowEval7063 (x : Key → ℝ) : Integer.Sparse.eval row7063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7063, Integer.Sparse.eval_collectBalanced, rawRowCheck7063]

theorem rawRowCheck7064 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form1 = rawRow7064 := by decide +kernel

theorem rowCheck7064 : row7064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7064 := by decide +kernel

theorem rowEval7064 (x : Key → ℝ) : Integer.Sparse.eval row7064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7064, Integer.Sparse.eval_collectBalanced, rawRowCheck7064]

theorem rawRowCheck7065 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form1 = rawRow7065 := by decide +kernel

theorem rowCheck7065 : row7065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7065 := by decide +kernel

theorem rowEval7065 (x : Key → ℝ) : Integer.Sparse.eval row7065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7065, Integer.Sparse.eval_collectBalanced, rawRowCheck7065]

theorem rawRowCheck7066 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form1 = rawRow7066 := by decide +kernel

theorem rowCheck7066 : row7066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7066 := by decide +kernel

theorem rowEval7066 (x : Key → ℝ) : Integer.Sparse.eval row7066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7066, Integer.Sparse.eval_collectBalanced, rawRowCheck7066]

theorem rawRowCheck7067 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form1 = rawRow7067 := by decide +kernel

theorem rowCheck7067 : row7067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7067 := by decide +kernel

theorem rowEval7067 (x : Key → ℝ) : Integer.Sparse.eval row7067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7067, Integer.Sparse.eval_collectBalanced, rawRowCheck7067]

theorem rawRowCheck7068 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form1 = rawRow7068 := by decide +kernel

theorem rowCheck7068 : row7068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7068 := by decide +kernel

theorem rowEval7068 (x : Key → ℝ) : Integer.Sparse.eval row7068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7068, Integer.Sparse.eval_collectBalanced, rawRowCheck7068]

theorem rawRowCheck7069 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form1 = rawRow7069 := by decide +kernel

theorem rowCheck7069 : row7069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7069 := by decide +kernel

theorem rowEval7069 (x : Key → ℝ) : Integer.Sparse.eval row7069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7069, Integer.Sparse.eval_collectBalanced, rawRowCheck7069]

theorem rawRowCheck7070 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form1 = rawRow7070 := by decide +kernel

theorem rowCheck7070 : row7070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7070 := by decide +kernel

theorem rowEval7070 (x : Key → ℝ) : Integer.Sparse.eval row7070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7070, Integer.Sparse.eval_collectBalanced, rawRowCheck7070]

theorem rawRowCheck7071 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form1 = rawRow7071 := by decide +kernel

theorem rowCheck7071 : row7071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7071 := by decide +kernel

theorem rowEval7071 (x : Key → ℝ) : Integer.Sparse.eval row7071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7071, Integer.Sparse.eval_collectBalanced, rawRowCheck7071]

theorem rawRowCheck7072 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form1 = rawRow7072 := by decide +kernel

theorem rowCheck7072 : row7072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7072 := by decide +kernel

theorem rowEval7072 (x : Key → ℝ) : Integer.Sparse.eval row7072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7072, Integer.Sparse.eval_collectBalanced, rawRowCheck7072]

theorem rawRowCheck7073 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form1 = rawRow7073 := by decide +kernel

theorem rowCheck7073 : row7073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7073 := by decide +kernel

theorem rowEval7073 (x : Key → ℝ) : Integer.Sparse.eval row7073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7073, Integer.Sparse.eval_collectBalanced, rawRowCheck7073]

theorem rawRowCheck7074 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form1 = rawRow7074 := by decide +kernel

theorem rowCheck7074 : row7074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7074 := by decide +kernel

theorem rowEval7074 (x : Key → ℝ) : Integer.Sparse.eval row7074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7074, Integer.Sparse.eval_collectBalanced, rawRowCheck7074]

theorem rawRowCheck7075 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form1 = rawRow7075 := by decide +kernel

theorem rowCheck7075 : row7075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7075 := by decide +kernel

theorem rowEval7075 (x : Key → ℝ) : Integer.Sparse.eval row7075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7075, Integer.Sparse.eval_collectBalanced, rawRowCheck7075]

theorem rawRowCheck7076 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form1 = rawRow7076 := by decide +kernel

theorem rowCheck7076 : row7076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7076 := by decide +kernel

theorem rowEval7076 (x : Key → ℝ) : Integer.Sparse.eval row7076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form1) x := by
  rw [rowCheck7076, Integer.Sparse.eval_collectBalanced, rawRowCheck7076]

theorem rawRowCheck7077 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form1 = rawRow7077 := by decide +kernel

theorem rowCheck7077 : row7077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7077 := by decide +kernel

theorem rowEval7077 (x : Key → ℝ) : Integer.Sparse.eval row7077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form1) x := by
  rw [rowCheck7077, Integer.Sparse.eval_collectBalanced, rawRowCheck7077]

theorem rawRowCheck7078 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form2 = rawRow7078 := by decide +kernel

theorem rowCheck7078 : row7078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7078 := by decide +kernel

theorem rowEval7078 (x : Key → ℝ) : Integer.Sparse.eval row7078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7078, Integer.Sparse.eval_collectBalanced, rawRowCheck7078]

theorem rawRowCheck7079 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form2 = rawRow7079 := by decide +kernel

theorem rowCheck7079 : row7079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7079 := by decide +kernel

theorem rowEval7079 (x : Key → ℝ) : Integer.Sparse.eval row7079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7079, Integer.Sparse.eval_collectBalanced, rawRowCheck7079]

theorem rawRowCheck7080 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form2 = rawRow7080 := by decide +kernel

theorem rowCheck7080 : row7080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7080 := by decide +kernel

theorem rowEval7080 (x : Key → ℝ) : Integer.Sparse.eval row7080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7080, Integer.Sparse.eval_collectBalanced, rawRowCheck7080]

theorem rawRowCheck7081 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow7081 := by decide +kernel

theorem rowCheck7081 : row7081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7081 := by decide +kernel

theorem rowEval7081 (x : Key → ℝ) : Integer.Sparse.eval row7081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7081, Integer.Sparse.eval_collectBalanced, rawRowCheck7081]

theorem rawRowCheck7082 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow7082 := by decide +kernel

theorem rowCheck7082 : row7082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7082 := by decide +kernel

theorem rowEval7082 (x : Key → ℝ) : Integer.Sparse.eval row7082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7082, Integer.Sparse.eval_collectBalanced, rawRowCheck7082]

theorem rawRowCheck7083 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow7083 := by decide +kernel

theorem rowCheck7083 : row7083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7083 := by decide +kernel

theorem rowEval7083 (x : Key → ℝ) : Integer.Sparse.eval row7083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7083, Integer.Sparse.eval_collectBalanced, rawRowCheck7083]

theorem rawRowCheck7084 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form2 = rawRow7084 := by decide +kernel

theorem rowCheck7084 : row7084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7084 := by decide +kernel

theorem rowEval7084 (x : Key → ℝ) : Integer.Sparse.eval row7084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7084, Integer.Sparse.eval_collectBalanced, rawRowCheck7084]

theorem rawRowCheck7085 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form2 = rawRow7085 := by decide +kernel

theorem rowCheck7085 : row7085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7085 := by decide +kernel

theorem rowEval7085 (x : Key → ℝ) : Integer.Sparse.eval row7085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7085, Integer.Sparse.eval_collectBalanced, rawRowCheck7085]

theorem rawRowCheck7086 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form2 = rawRow7086 := by decide +kernel

theorem rowCheck7086 : row7086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7086 := by decide +kernel

theorem rowEval7086 (x : Key → ℝ) : Integer.Sparse.eval row7086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7086, Integer.Sparse.eval_collectBalanced, rawRowCheck7086]

theorem rawRowCheck7087 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form2 = rawRow7087 := by decide +kernel

theorem rowCheck7087 : row7087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7087 := by decide +kernel

theorem rowEval7087 (x : Key → ℝ) : Integer.Sparse.eval row7087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7087, Integer.Sparse.eval_collectBalanced, rawRowCheck7087]

theorem rawRowCheck7088 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form2 = rawRow7088 := by decide +kernel

theorem rowCheck7088 : row7088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7088 := by decide +kernel

theorem rowEval7088 (x : Key → ℝ) : Integer.Sparse.eval row7088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7088, Integer.Sparse.eval_collectBalanced, rawRowCheck7088]

theorem rawRowCheck7089 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form2 = rawRow7089 := by decide +kernel

theorem rowCheck7089 : row7089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7089 := by decide +kernel

theorem rowEval7089 (x : Key → ℝ) : Integer.Sparse.eval row7089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7089, Integer.Sparse.eval_collectBalanced, rawRowCheck7089]

theorem rawRowCheck7090 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form2 = rawRow7090 := by decide +kernel

theorem rowCheck7090 : row7090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7090 := by decide +kernel

theorem rowEval7090 (x : Key → ℝ) : Integer.Sparse.eval row7090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7090, Integer.Sparse.eval_collectBalanced, rawRowCheck7090]

theorem rawRowCheck7091 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form2 = rawRow7091 := by decide +kernel

theorem rowCheck7091 : row7091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7091 := by decide +kernel

theorem rowEval7091 (x : Key → ℝ) : Integer.Sparse.eval row7091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7091, Integer.Sparse.eval_collectBalanced, rawRowCheck7091]

theorem rawRowCheck7092 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form2 = rawRow7092 := by decide +kernel

theorem rowCheck7092 : row7092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7092 := by decide +kernel

theorem rowEval7092 (x : Key → ℝ) : Integer.Sparse.eval row7092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7092, Integer.Sparse.eval_collectBalanced, rawRowCheck7092]

theorem rawRowCheck7093 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form2 = rawRow7093 := by decide +kernel

theorem rowCheck7093 : row7093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7093 := by decide +kernel

theorem rowEval7093 (x : Key → ℝ) : Integer.Sparse.eval row7093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7093, Integer.Sparse.eval_collectBalanced, rawRowCheck7093]

theorem rawRowCheck7094 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form2 = rawRow7094 := by decide +kernel

theorem rowCheck7094 : row7094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7094 := by decide +kernel

theorem rowEval7094 (x : Key → ℝ) : Integer.Sparse.eval row7094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7094, Integer.Sparse.eval_collectBalanced, rawRowCheck7094]

theorem rawRowCheck7095 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form2 = rawRow7095 := by decide +kernel

theorem rowCheck7095 : row7095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7095 := by decide +kernel

theorem rowEval7095 (x : Key → ℝ) : Integer.Sparse.eval row7095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7095, Integer.Sparse.eval_collectBalanced, rawRowCheck7095]

theorem rawRowCheck7096 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form2 = rawRow7096 := by decide +kernel

theorem rowCheck7096 : row7096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7096 := by decide +kernel

theorem rowEval7096 (x : Key → ℝ) : Integer.Sparse.eval row7096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7096, Integer.Sparse.eval_collectBalanced, rawRowCheck7096]

theorem rawRowCheck7097 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form2 = rawRow7097 := by decide +kernel

theorem rowCheck7097 : row7097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7097 := by decide +kernel

theorem rowEval7097 (x : Key → ℝ) : Integer.Sparse.eval row7097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7097, Integer.Sparse.eval_collectBalanced, rawRowCheck7097]

theorem rawRowCheck7098 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form2 = rawRow7098 := by decide +kernel

theorem rowCheck7098 : row7098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7098 := by decide +kernel

theorem rowEval7098 (x : Key → ℝ) : Integer.Sparse.eval row7098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7098, Integer.Sparse.eval_collectBalanced, rawRowCheck7098]

theorem rawRowCheck7099 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form2 = rawRow7099 := by decide +kernel

theorem rowCheck7099 : row7099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7099 := by decide +kernel

theorem rowEval7099 (x : Key → ℝ) : Integer.Sparse.eval row7099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7099, Integer.Sparse.eval_collectBalanced, rawRowCheck7099]

theorem rawRowCheck7100 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form2 = rawRow7100 := by decide +kernel

theorem rowCheck7100 : row7100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7100 := by decide +kernel

theorem rowEval7100 (x : Key → ℝ) : Integer.Sparse.eval row7100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7100, Integer.Sparse.eval_collectBalanced, rawRowCheck7100]

theorem rawRowCheck7101 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form2 = rawRow7101 := by decide +kernel

theorem rowCheck7101 : row7101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7101 := by decide +kernel

theorem rowEval7101 (x : Key → ℝ) : Integer.Sparse.eval row7101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7101, Integer.Sparse.eval_collectBalanced, rawRowCheck7101]

theorem rawRowCheck7102 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form2 = rawRow7102 := by decide +kernel

theorem rowCheck7102 : row7102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7102 := by decide +kernel

theorem rowEval7102 (x : Key → ℝ) : Integer.Sparse.eval row7102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7102, Integer.Sparse.eval_collectBalanced, rawRowCheck7102]

theorem rawRowCheck7103 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form2 = rawRow7103 := by decide +kernel

theorem rowCheck7103 : row7103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7103 := by decide +kernel

theorem rowEval7103 (x : Key → ℝ) : Integer.Sparse.eval row7103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7103, Integer.Sparse.eval_collectBalanced, rawRowCheck7103]

theorem rawRowCheck7104 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form2 = rawRow7104 := by decide +kernel

theorem rowCheck7104 : row7104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7104 := by decide +kernel

theorem rowEval7104 (x : Key → ℝ) : Integer.Sparse.eval row7104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7104, Integer.Sparse.eval_collectBalanced, rawRowCheck7104]

theorem rawRowCheck7105 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form2 = rawRow7105 := by decide +kernel

theorem rowCheck7105 : row7105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7105 := by decide +kernel

theorem rowEval7105 (x : Key → ℝ) : Integer.Sparse.eval row7105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7105, Integer.Sparse.eval_collectBalanced, rawRowCheck7105]

theorem rawRowCheck7106 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form2 = rawRow7106 := by decide +kernel

theorem rowCheck7106 : row7106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7106 := by decide +kernel

theorem rowEval7106 (x : Key → ℝ) : Integer.Sparse.eval row7106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form2) x := by
  rw [rowCheck7106, Integer.Sparse.eval_collectBalanced, rawRowCheck7106]

theorem rawRowCheck7107 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form2 = rawRow7107 := by decide +kernel

theorem rowCheck7107 : row7107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7107 := by decide +kernel

theorem rowEval7107 (x : Key → ℝ) : Integer.Sparse.eval row7107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form2) x := by
  rw [rowCheck7107, Integer.Sparse.eval_collectBalanced, rawRowCheck7107]

theorem rawRowCheck7108 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form3 = rawRow7108 := by decide +kernel

theorem rowCheck7108 : row7108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7108 := by decide +kernel

theorem rowEval7108 (x : Key → ℝ) : Integer.Sparse.eval row7108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7108, Integer.Sparse.eval_collectBalanced, rawRowCheck7108]

theorem rawRowCheck7109 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form3 = rawRow7109 := by decide +kernel

theorem rowCheck7109 : row7109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7109 := by decide +kernel

theorem rowEval7109 (x : Key → ℝ) : Integer.Sparse.eval row7109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7109, Integer.Sparse.eval_collectBalanced, rawRowCheck7109]

theorem rawRowCheck7110 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form3 = rawRow7110 := by decide +kernel

theorem rowCheck7110 : row7110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7110 := by decide +kernel

theorem rowEval7110 (x : Key → ℝ) : Integer.Sparse.eval row7110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7110, Integer.Sparse.eval_collectBalanced, rawRowCheck7110]

theorem rawRowCheck7111 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow7111 := by decide +kernel

theorem rowCheck7111 : row7111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7111 := by decide +kernel

theorem rowEval7111 (x : Key → ℝ) : Integer.Sparse.eval row7111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7111, Integer.Sparse.eval_collectBalanced, rawRowCheck7111]

theorem rawRowCheck7112 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow7112 := by decide +kernel

theorem rowCheck7112 : row7112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7112 := by decide +kernel

theorem rowEval7112 (x : Key → ℝ) : Integer.Sparse.eval row7112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7112, Integer.Sparse.eval_collectBalanced, rawRowCheck7112]

theorem rawRowCheck7113 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow7113 := by decide +kernel

theorem rowCheck7113 : row7113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7113 := by decide +kernel

theorem rowEval7113 (x : Key → ℝ) : Integer.Sparse.eval row7113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7113, Integer.Sparse.eval_collectBalanced, rawRowCheck7113]

theorem rawRowCheck7114 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form3 = rawRow7114 := by decide +kernel

theorem rowCheck7114 : row7114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7114 := by decide +kernel

theorem rowEval7114 (x : Key → ℝ) : Integer.Sparse.eval row7114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7114, Integer.Sparse.eval_collectBalanced, rawRowCheck7114]

theorem rawRowCheck7115 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form3 = rawRow7115 := by decide +kernel

theorem rowCheck7115 : row7115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7115 := by decide +kernel

theorem rowEval7115 (x : Key → ℝ) : Integer.Sparse.eval row7115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7115, Integer.Sparse.eval_collectBalanced, rawRowCheck7115]

theorem rawRowCheck7116 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form3 = rawRow7116 := by decide +kernel

theorem rowCheck7116 : row7116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7116 := by decide +kernel

theorem rowEval7116 (x : Key → ℝ) : Integer.Sparse.eval row7116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7116, Integer.Sparse.eval_collectBalanced, rawRowCheck7116]

theorem rawRowCheck7117 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form3 = rawRow7117 := by decide +kernel

theorem rowCheck7117 : row7117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7117 := by decide +kernel

theorem rowEval7117 (x : Key → ℝ) : Integer.Sparse.eval row7117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7117, Integer.Sparse.eval_collectBalanced, rawRowCheck7117]

theorem rawRowCheck7118 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form3 = rawRow7118 := by decide +kernel

theorem rowCheck7118 : row7118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7118 := by decide +kernel

theorem rowEval7118 (x : Key → ℝ) : Integer.Sparse.eval row7118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7118, Integer.Sparse.eval_collectBalanced, rawRowCheck7118]

theorem rawRowCheck7119 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form3 = rawRow7119 := by decide +kernel

theorem rowCheck7119 : row7119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7119 := by decide +kernel

theorem rowEval7119 (x : Key → ℝ) : Integer.Sparse.eval row7119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7119, Integer.Sparse.eval_collectBalanced, rawRowCheck7119]

theorem rawRowCheck7120 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form3 = rawRow7120 := by decide +kernel

theorem rowCheck7120 : row7120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7120 := by decide +kernel

theorem rowEval7120 (x : Key → ℝ) : Integer.Sparse.eval row7120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7120, Integer.Sparse.eval_collectBalanced, rawRowCheck7120]

theorem rawRowCheck7121 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form3 = rawRow7121 := by decide +kernel

theorem rowCheck7121 : row7121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7121 := by decide +kernel

theorem rowEval7121 (x : Key → ℝ) : Integer.Sparse.eval row7121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7121, Integer.Sparse.eval_collectBalanced, rawRowCheck7121]

theorem rawRowCheck7122 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form3 = rawRow7122 := by decide +kernel

theorem rowCheck7122 : row7122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7122 := by decide +kernel

theorem rowEval7122 (x : Key → ℝ) : Integer.Sparse.eval row7122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7122, Integer.Sparse.eval_collectBalanced, rawRowCheck7122]

theorem rawRowCheck7123 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form3 = rawRow7123 := by decide +kernel

theorem rowCheck7123 : row7123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7123 := by decide +kernel

theorem rowEval7123 (x : Key → ℝ) : Integer.Sparse.eval row7123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7123, Integer.Sparse.eval_collectBalanced, rawRowCheck7123]

theorem rawRowCheck7124 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form3 = rawRow7124 := by decide +kernel

theorem rowCheck7124 : row7124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7124 := by decide +kernel

theorem rowEval7124 (x : Key → ℝ) : Integer.Sparse.eval row7124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7124, Integer.Sparse.eval_collectBalanced, rawRowCheck7124]

theorem rawRowCheck7125 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form3 = rawRow7125 := by decide +kernel

theorem rowCheck7125 : row7125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7125 := by decide +kernel

theorem rowEval7125 (x : Key → ℝ) : Integer.Sparse.eval row7125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7125, Integer.Sparse.eval_collectBalanced, rawRowCheck7125]

theorem rawRowCheck7126 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form3 = rawRow7126 := by decide +kernel

theorem rowCheck7126 : row7126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7126 := by decide +kernel

theorem rowEval7126 (x : Key → ℝ) : Integer.Sparse.eval row7126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7126, Integer.Sparse.eval_collectBalanced, rawRowCheck7126]

theorem rawRowCheck7127 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form3 = rawRow7127 := by decide +kernel

theorem rowCheck7127 : row7127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7127 := by decide +kernel

theorem rowEval7127 (x : Key → ℝ) : Integer.Sparse.eval row7127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7127, Integer.Sparse.eval_collectBalanced, rawRowCheck7127]

theorem rawRowCheck7128 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form3 = rawRow7128 := by decide +kernel

theorem rowCheck7128 : row7128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7128 := by decide +kernel

theorem rowEval7128 (x : Key → ℝ) : Integer.Sparse.eval row7128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7128, Integer.Sparse.eval_collectBalanced, rawRowCheck7128]

theorem rawRowCheck7129 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form3 = rawRow7129 := by decide +kernel

theorem rowCheck7129 : row7129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7129 := by decide +kernel

theorem rowEval7129 (x : Key → ℝ) : Integer.Sparse.eval row7129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7129, Integer.Sparse.eval_collectBalanced, rawRowCheck7129]

theorem rawRowCheck7130 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form3 = rawRow7130 := by decide +kernel

theorem rowCheck7130 : row7130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7130 := by decide +kernel

theorem rowEval7130 (x : Key → ℝ) : Integer.Sparse.eval row7130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7130, Integer.Sparse.eval_collectBalanced, rawRowCheck7130]

theorem rawRowCheck7131 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form3 = rawRow7131 := by decide +kernel

theorem rowCheck7131 : row7131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7131 := by decide +kernel

theorem rowEval7131 (x : Key → ℝ) : Integer.Sparse.eval row7131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7131, Integer.Sparse.eval_collectBalanced, rawRowCheck7131]

theorem rawRowCheck7132 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form3 = rawRow7132 := by decide +kernel

theorem rowCheck7132 : row7132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7132 := by decide +kernel

theorem rowEval7132 (x : Key → ℝ) : Integer.Sparse.eval row7132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7132, Integer.Sparse.eval_collectBalanced, rawRowCheck7132]

theorem rawRowCheck7133 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form3 = rawRow7133 := by decide +kernel

theorem rowCheck7133 : row7133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7133 := by decide +kernel

theorem rowEval7133 (x : Key → ℝ) : Integer.Sparse.eval row7133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7133, Integer.Sparse.eval_collectBalanced, rawRowCheck7133]

theorem rawRowCheck7134 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form3 = rawRow7134 := by decide +kernel

theorem rowCheck7134 : row7134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7134 := by decide +kernel

theorem rowEval7134 (x : Key → ℝ) : Integer.Sparse.eval row7134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7134, Integer.Sparse.eval_collectBalanced, rawRowCheck7134]

theorem rawRowCheck7135 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form3 = rawRow7135 := by decide +kernel

theorem rowCheck7135 : row7135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7135 := by decide +kernel

theorem rowEval7135 (x : Key → ℝ) : Integer.Sparse.eval row7135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7135, Integer.Sparse.eval_collectBalanced, rawRowCheck7135]

theorem rawRowCheck7136 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form3 = rawRow7136 := by decide +kernel

theorem rowCheck7136 : row7136 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7136 := by decide +kernel

theorem rowEval7136 (x : Key → ℝ) : Integer.Sparse.eval row7136 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form3) x := by
  rw [rowCheck7136, Integer.Sparse.eval_collectBalanced, rawRowCheck7136]

theorem rawRowCheck7137 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form3 = rawRow7137 := by decide +kernel

theorem rowCheck7137 : row7137 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7137 := by decide +kernel

theorem rowEval7137 (x : Key → ℝ) : Integer.Sparse.eval row7137 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form3) x := by
  rw [rowCheck7137, Integer.Sparse.eval_collectBalanced, rawRowCheck7137]

theorem rawRowCheck7138 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form4 = rawRow7138 := by decide +kernel

theorem rowCheck7138 : row7138 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7138 := by decide +kernel

theorem rowEval7138 (x : Key → ℝ) : Integer.Sparse.eval row7138 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7138, Integer.Sparse.eval_collectBalanced, rawRowCheck7138]

theorem rawRowCheck7139 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form4 = rawRow7139 := by decide +kernel

theorem rowCheck7139 : row7139 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7139 := by decide +kernel

theorem rowEval7139 (x : Key → ℝ) : Integer.Sparse.eval row7139 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7139, Integer.Sparse.eval_collectBalanced, rawRowCheck7139]

theorem rawRowCheck7140 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form4 = rawRow7140 := by decide +kernel

theorem rowCheck7140 : row7140 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7140 := by decide +kernel

theorem rowEval7140 (x : Key → ℝ) : Integer.Sparse.eval row7140 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7140, Integer.Sparse.eval_collectBalanced, rawRowCheck7140]

theorem rawRowCheck7141 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow7141 := by decide +kernel

theorem rowCheck7141 : row7141 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7141 := by decide +kernel

theorem rowEval7141 (x : Key → ℝ) : Integer.Sparse.eval row7141 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7141, Integer.Sparse.eval_collectBalanced, rawRowCheck7141]

theorem rawRowCheck7142 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow7142 := by decide +kernel

theorem rowCheck7142 : row7142 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7142 := by decide +kernel

theorem rowEval7142 (x : Key → ℝ) : Integer.Sparse.eval row7142 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7142, Integer.Sparse.eval_collectBalanced, rawRowCheck7142]

theorem rawRowCheck7143 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow7143 := by decide +kernel

theorem rowCheck7143 : row7143 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7143 := by decide +kernel

theorem rowEval7143 (x : Key → ℝ) : Integer.Sparse.eval row7143 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7143, Integer.Sparse.eval_collectBalanced, rawRowCheck7143]

theorem rawRowCheck7144 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form4 = rawRow7144 := by decide +kernel

theorem rowCheck7144 : row7144 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7144 := by decide +kernel

theorem rowEval7144 (x : Key → ℝ) : Integer.Sparse.eval row7144 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7144, Integer.Sparse.eval_collectBalanced, rawRowCheck7144]

theorem rawRowCheck7145 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form4 = rawRow7145 := by decide +kernel

theorem rowCheck7145 : row7145 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7145 := by decide +kernel

theorem rowEval7145 (x : Key → ℝ) : Integer.Sparse.eval row7145 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7145, Integer.Sparse.eval_collectBalanced, rawRowCheck7145]

theorem rawRowCheck7146 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form4 = rawRow7146 := by decide +kernel

theorem rowCheck7146 : row7146 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7146 := by decide +kernel

theorem rowEval7146 (x : Key → ℝ) : Integer.Sparse.eval row7146 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7146, Integer.Sparse.eval_collectBalanced, rawRowCheck7146]

theorem rawRowCheck7147 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form4 = rawRow7147 := by decide +kernel

theorem rowCheck7147 : row7147 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7147 := by decide +kernel

theorem rowEval7147 (x : Key → ℝ) : Integer.Sparse.eval row7147 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7147, Integer.Sparse.eval_collectBalanced, rawRowCheck7147]

theorem rawRowCheck7148 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form4 = rawRow7148 := by decide +kernel

theorem rowCheck7148 : row7148 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7148 := by decide +kernel

theorem rowEval7148 (x : Key → ℝ) : Integer.Sparse.eval row7148 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7148, Integer.Sparse.eval_collectBalanced, rawRowCheck7148]

theorem rawRowCheck7149 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form4 = rawRow7149 := by decide +kernel

theorem rowCheck7149 : row7149 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7149 := by decide +kernel

theorem rowEval7149 (x : Key → ℝ) : Integer.Sparse.eval row7149 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7149, Integer.Sparse.eval_collectBalanced, rawRowCheck7149]

theorem rawRowCheck7150 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form4 = rawRow7150 := by decide +kernel

theorem rowCheck7150 : row7150 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7150 := by decide +kernel

theorem rowEval7150 (x : Key → ℝ) : Integer.Sparse.eval row7150 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7150, Integer.Sparse.eval_collectBalanced, rawRowCheck7150]

theorem rawRowCheck7151 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form4 = rawRow7151 := by decide +kernel

theorem rowCheck7151 : row7151 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7151 := by decide +kernel

theorem rowEval7151 (x : Key → ℝ) : Integer.Sparse.eval row7151 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7151, Integer.Sparse.eval_collectBalanced, rawRowCheck7151]

theorem rawRowCheck7152 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form4 = rawRow7152 := by decide +kernel

theorem rowCheck7152 : row7152 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7152 := by decide +kernel

theorem rowEval7152 (x : Key → ℝ) : Integer.Sparse.eval row7152 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7152, Integer.Sparse.eval_collectBalanced, rawRowCheck7152]

theorem rawRowCheck7153 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form4 = rawRow7153 := by decide +kernel

theorem rowCheck7153 : row7153 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7153 := by decide +kernel

theorem rowEval7153 (x : Key → ℝ) : Integer.Sparse.eval row7153 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7153, Integer.Sparse.eval_collectBalanced, rawRowCheck7153]

theorem rawRowCheck7154 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form4 = rawRow7154 := by decide +kernel

theorem rowCheck7154 : row7154 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7154 := by decide +kernel

theorem rowEval7154 (x : Key → ℝ) : Integer.Sparse.eval row7154 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7154, Integer.Sparse.eval_collectBalanced, rawRowCheck7154]

theorem rawRowCheck7155 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form4 = rawRow7155 := by decide +kernel

theorem rowCheck7155 : row7155 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7155 := by decide +kernel

theorem rowEval7155 (x : Key → ℝ) : Integer.Sparse.eval row7155 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7155, Integer.Sparse.eval_collectBalanced, rawRowCheck7155]

theorem rawRowCheck7156 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form4 = rawRow7156 := by decide +kernel

theorem rowCheck7156 : row7156 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7156 := by decide +kernel

theorem rowEval7156 (x : Key → ℝ) : Integer.Sparse.eval row7156 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7156, Integer.Sparse.eval_collectBalanced, rawRowCheck7156]

theorem rawRowCheck7157 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form4 = rawRow7157 := by decide +kernel

theorem rowCheck7157 : row7157 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7157 := by decide +kernel

theorem rowEval7157 (x : Key → ℝ) : Integer.Sparse.eval row7157 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7157, Integer.Sparse.eval_collectBalanced, rawRowCheck7157]

theorem rawRowCheck7158 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form4 = rawRow7158 := by decide +kernel

theorem rowCheck7158 : row7158 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7158 := by decide +kernel

theorem rowEval7158 (x : Key → ℝ) : Integer.Sparse.eval row7158 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7158, Integer.Sparse.eval_collectBalanced, rawRowCheck7158]

theorem rawRowCheck7159 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form4 = rawRow7159 := by decide +kernel

theorem rowCheck7159 : row7159 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7159 := by decide +kernel

theorem rowEval7159 (x : Key → ℝ) : Integer.Sparse.eval row7159 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7159, Integer.Sparse.eval_collectBalanced, rawRowCheck7159]

theorem rawRowCheck7160 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form4 = rawRow7160 := by decide +kernel

theorem rowCheck7160 : row7160 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7160 := by decide +kernel

theorem rowEval7160 (x : Key → ℝ) : Integer.Sparse.eval row7160 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7160, Integer.Sparse.eval_collectBalanced, rawRowCheck7160]

theorem rawRowCheck7161 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form4 = rawRow7161 := by decide +kernel

theorem rowCheck7161 : row7161 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7161 := by decide +kernel

theorem rowEval7161 (x : Key → ℝ) : Integer.Sparse.eval row7161 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7161, Integer.Sparse.eval_collectBalanced, rawRowCheck7161]

theorem rawRowCheck7162 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form4 = rawRow7162 := by decide +kernel

theorem rowCheck7162 : row7162 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7162 := by decide +kernel

theorem rowEval7162 (x : Key → ℝ) : Integer.Sparse.eval row7162 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7162, Integer.Sparse.eval_collectBalanced, rawRowCheck7162]

theorem rawRowCheck7163 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form4 = rawRow7163 := by decide +kernel

theorem rowCheck7163 : row7163 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7163 := by decide +kernel

theorem rowEval7163 (x : Key → ℝ) : Integer.Sparse.eval row7163 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7163, Integer.Sparse.eval_collectBalanced, rawRowCheck7163]

theorem rawRowCheck7164 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form4 = rawRow7164 := by decide +kernel

theorem rowCheck7164 : row7164 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7164 := by decide +kernel

theorem rowEval7164 (x : Key → ℝ) : Integer.Sparse.eval row7164 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7164, Integer.Sparse.eval_collectBalanced, rawRowCheck7164]

theorem rawRowCheck7165 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form4 = rawRow7165 := by decide +kernel

theorem rowCheck7165 : row7165 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7165 := by decide +kernel

theorem rowEval7165 (x : Key → ℝ) : Integer.Sparse.eval row7165 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7165, Integer.Sparse.eval_collectBalanced, rawRowCheck7165]

theorem rawRowCheck7166 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form4 = rawRow7166 := by decide +kernel

theorem rowCheck7166 : row7166 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7166 := by decide +kernel

theorem rowEval7166 (x : Key → ℝ) : Integer.Sparse.eval row7166 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form4) x := by
  rw [rowCheck7166, Integer.Sparse.eval_collectBalanced, rawRowCheck7166]

theorem rawRowCheck7167 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form4 = rawRow7167 := by decide +kernel

theorem rowCheck7167 : row7167 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7167 := by decide +kernel

theorem rowEval7167 (x : Key → ℝ) : Integer.Sparse.eval row7167 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form4) x := by
  rw [rowCheck7167, Integer.Sparse.eval_collectBalanced, rawRowCheck7167]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7288 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form9 = rawRow7288 := by decide +kernel

theorem rowCheck7288 : row7288 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7288 := by decide +kernel

theorem rowEval7288 (x : Key → ℝ) : Integer.Sparse.eval row7288 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7288, Integer.Sparse.eval_collectBalanced, rawRowCheck7288]

theorem rawRowCheck7289 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form9 = rawRow7289 := by decide +kernel

theorem rowCheck7289 : row7289 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7289 := by decide +kernel

theorem rowEval7289 (x : Key → ℝ) : Integer.Sparse.eval row7289 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7289, Integer.Sparse.eval_collectBalanced, rawRowCheck7289]

theorem rawRowCheck7290 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form9 = rawRow7290 := by decide +kernel

theorem rowCheck7290 : row7290 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7290 := by decide +kernel

theorem rowEval7290 (x : Key → ℝ) : Integer.Sparse.eval row7290 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7290, Integer.Sparse.eval_collectBalanced, rawRowCheck7290]

theorem rawRowCheck7291 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow7291 := by decide +kernel

theorem rowCheck7291 : row7291 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7291 := by decide +kernel

theorem rowEval7291 (x : Key → ℝ) : Integer.Sparse.eval row7291 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7291, Integer.Sparse.eval_collectBalanced, rawRowCheck7291]

theorem rawRowCheck7292 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow7292 := by decide +kernel

theorem rowCheck7292 : row7292 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7292 := by decide +kernel

theorem rowEval7292 (x : Key → ℝ) : Integer.Sparse.eval row7292 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7292, Integer.Sparse.eval_collectBalanced, rawRowCheck7292]

theorem rawRowCheck7293 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow7293 := by decide +kernel

theorem rowCheck7293 : row7293 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7293 := by decide +kernel

theorem rowEval7293 (x : Key → ℝ) : Integer.Sparse.eval row7293 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7293, Integer.Sparse.eval_collectBalanced, rawRowCheck7293]

theorem rawRowCheck7294 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form9 = rawRow7294 := by decide +kernel

theorem rowCheck7294 : row7294 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7294 := by decide +kernel

theorem rowEval7294 (x : Key → ℝ) : Integer.Sparse.eval row7294 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7294, Integer.Sparse.eval_collectBalanced, rawRowCheck7294]

theorem rawRowCheck7295 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form9 = rawRow7295 := by decide +kernel

theorem rowCheck7295 : row7295 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7295 := by decide +kernel

theorem rowEval7295 (x : Key → ℝ) : Integer.Sparse.eval row7295 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7295, Integer.Sparse.eval_collectBalanced, rawRowCheck7295]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck7296 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form9 = rawRow7296 := by decide +kernel

theorem rowCheck7296 : row7296 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7296 := by decide +kernel

theorem rowEval7296 (x : Key → ℝ) : Integer.Sparse.eval row7296 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7296, Integer.Sparse.eval_collectBalanced, rawRowCheck7296]

theorem rawRowCheck7297 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form9 = rawRow7297 := by decide +kernel

theorem rowCheck7297 : row7297 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7297 := by decide +kernel

theorem rowEval7297 (x : Key → ℝ) : Integer.Sparse.eval row7297 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7297, Integer.Sparse.eval_collectBalanced, rawRowCheck7297]

theorem rawRowCheck7298 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form9 = rawRow7298 := by decide +kernel

theorem rowCheck7298 : row7298 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7298 := by decide +kernel

theorem rowEval7298 (x : Key → ℝ) : Integer.Sparse.eval row7298 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7298, Integer.Sparse.eval_collectBalanced, rawRowCheck7298]

theorem rawRowCheck7299 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form9 = rawRow7299 := by decide +kernel

theorem rowCheck7299 : row7299 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7299 := by decide +kernel

theorem rowEval7299 (x : Key → ℝ) : Integer.Sparse.eval row7299 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7299, Integer.Sparse.eval_collectBalanced, rawRowCheck7299]

theorem rawRowCheck7300 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7300 := by decide +kernel

theorem rowCheck7300 : row7300 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7300 := by decide +kernel

theorem rowEval7300 (x : Key → ℝ) : Integer.Sparse.eval row7300 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7300, Integer.Sparse.eval_collectBalanced, rawRowCheck7300]

theorem rawRowCheck7301 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7301 := by decide +kernel

theorem rowCheck7301 : row7301 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7301 := by decide +kernel

theorem rowEval7301 (x : Key → ℝ) : Integer.Sparse.eval row7301 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7301, Integer.Sparse.eval_collectBalanced, rawRowCheck7301]

theorem rawRowCheck7302 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7302 := by decide +kernel

theorem rowCheck7302 : row7302 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7302 := by decide +kernel

theorem rowEval7302 (x : Key → ℝ) : Integer.Sparse.eval row7302 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7302, Integer.Sparse.eval_collectBalanced, rawRowCheck7302]

theorem rawRowCheck7303 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7303 := by decide +kernel

theorem rowCheck7303 : row7303 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7303 := by decide +kernel

theorem rowEval7303 (x : Key → ℝ) : Integer.Sparse.eval row7303 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7303, Integer.Sparse.eval_collectBalanced, rawRowCheck7303]

theorem rawRowCheck7304 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7304 := by decide +kernel

theorem rowCheck7304 : row7304 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7304 := by decide +kernel

theorem rowEval7304 (x : Key → ℝ) : Integer.Sparse.eval row7304 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7304, Integer.Sparse.eval_collectBalanced, rawRowCheck7304]

theorem rawRowCheck7305 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7305 := by decide +kernel

theorem rowCheck7305 : row7305 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7305 := by decide +kernel

theorem rowEval7305 (x : Key → ℝ) : Integer.Sparse.eval row7305 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7305, Integer.Sparse.eval_collectBalanced, rawRowCheck7305]

theorem rawRowCheck7306 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form9 = rawRow7306 := by decide +kernel

theorem rowCheck7306 : row7306 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7306 := by decide +kernel

theorem rowEval7306 (x : Key → ℝ) : Integer.Sparse.eval row7306 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7306, Integer.Sparse.eval_collectBalanced, rawRowCheck7306]

theorem rawRowCheck7307 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form9 = rawRow7307 := by decide +kernel

theorem rowCheck7307 : row7307 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7307 := by decide +kernel

theorem rowEval7307 (x : Key → ℝ) : Integer.Sparse.eval row7307 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7307, Integer.Sparse.eval_collectBalanced, rawRowCheck7307]

theorem rawRowCheck7308 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form9 = rawRow7308 := by decide +kernel

theorem rowCheck7308 : row7308 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7308 := by decide +kernel

theorem rowEval7308 (x : Key → ℝ) : Integer.Sparse.eval row7308 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7308, Integer.Sparse.eval_collectBalanced, rawRowCheck7308]

theorem rawRowCheck7309 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form9 = rawRow7309 := by decide +kernel

theorem rowCheck7309 : row7309 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7309 := by decide +kernel

theorem rowEval7309 (x : Key → ℝ) : Integer.Sparse.eval row7309 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7309, Integer.Sparse.eval_collectBalanced, rawRowCheck7309]

theorem rawRowCheck7310 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9 = rawRow7310 := by decide +kernel

theorem rowCheck7310 : row7310 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7310 := by decide +kernel

theorem rowEval7310 (x : Key → ℝ) : Integer.Sparse.eval row7310 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7310, Integer.Sparse.eval_collectBalanced, rawRowCheck7310]

theorem rawRowCheck7311 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form9 = rawRow7311 := by decide +kernel

theorem rowCheck7311 : row7311 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7311 := by decide +kernel

theorem rowEval7311 (x : Key → ℝ) : Integer.Sparse.eval row7311 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7311, Integer.Sparse.eval_collectBalanced, rawRowCheck7311]

theorem rawRowCheck7312 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form9 = rawRow7312 := by decide +kernel

theorem rowCheck7312 : row7312 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7312 := by decide +kernel

theorem rowEval7312 (x : Key → ℝ) : Integer.Sparse.eval row7312 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7312, Integer.Sparse.eval_collectBalanced, rawRowCheck7312]

theorem rawRowCheck7313 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form9 = rawRow7313 := by decide +kernel

theorem rowCheck7313 : row7313 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7313 := by decide +kernel

theorem rowEval7313 (x : Key → ℝ) : Integer.Sparse.eval row7313 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7313, Integer.Sparse.eval_collectBalanced, rawRowCheck7313]

theorem rawRowCheck7314 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form9 = rawRow7314 := by decide +kernel

theorem rowCheck7314 : row7314 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7314 := by decide +kernel

theorem rowEval7314 (x : Key → ℝ) : Integer.Sparse.eval row7314 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7314, Integer.Sparse.eval_collectBalanced, rawRowCheck7314]

theorem rawRowCheck7315 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form9 = rawRow7315 := by decide +kernel

theorem rowCheck7315 : row7315 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7315 := by decide +kernel

theorem rowEval7315 (x : Key → ℝ) : Integer.Sparse.eval row7315 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7315, Integer.Sparse.eval_collectBalanced, rawRowCheck7315]

theorem rawRowCheck7316 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form9 = rawRow7316 := by decide +kernel

theorem rowCheck7316 : row7316 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7316 := by decide +kernel

theorem rowEval7316 (x : Key → ℝ) : Integer.Sparse.eval row7316 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form9) x := by
  rw [rowCheck7316, Integer.Sparse.eval_collectBalanced, rawRowCheck7316]

theorem rawRowCheck7317 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form9 = rawRow7317 := by decide +kernel

theorem rowCheck7317 : row7317 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7317 := by decide +kernel

theorem rowEval7317 (x : Key → ℝ) : Integer.Sparse.eval row7317 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form9) x := by
  rw [rowCheck7317, Integer.Sparse.eval_collectBalanced, rawRowCheck7317]

theorem rawRowCheck7318 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form10 = rawRow7318 := by decide +kernel

theorem rowCheck7318 : row7318 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7318 := by decide +kernel

theorem rowEval7318 (x : Key → ℝ) : Integer.Sparse.eval row7318 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 0, 1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7318, Integer.Sparse.eval_collectBalanced, rawRowCheck7318]

theorem rawRowCheck7319 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form10 = rawRow7319 := by decide +kernel

theorem rowCheck7319 : row7319 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7319 := by decide +kernel

theorem rowEval7319 (x : Key → ℝ) : Integer.Sparse.eval row7319 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7319, Integer.Sparse.eval_collectBalanced, rawRowCheck7319]

theorem rawRowCheck7320 : GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form10 = rawRow7320 := by decide +kernel

theorem rowCheck7320 : row7320 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7320 := by decide +kernel

theorem rowEval7320 (x : Key → ℝ) : Integer.Sparse.eval row7320 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 0, 1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7320, Integer.Sparse.eval_collectBalanced, rawRowCheck7320]

theorem rawRowCheck7321 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form10 = rawRow7321 := by decide +kernel

theorem rowCheck7321 : row7321 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7321 := by decide +kernel

theorem rowEval7321 (x : Key → ℝ) : Integer.Sparse.eval row7321 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7321, Integer.Sparse.eval_collectBalanced, rawRowCheck7321]

theorem rawRowCheck7322 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form10 = rawRow7322 := by decide +kernel

theorem rowCheck7322 : row7322 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7322 := by decide +kernel

theorem rowEval7322 (x : Key → ℝ) : Integer.Sparse.eval row7322 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 0, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7322, Integer.Sparse.eval_collectBalanced, rawRowCheck7322]

theorem rawRowCheck7323 : GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form10 = rawRow7323 := by decide +kernel

theorem rowCheck7323 : row7323 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7323 := by decide +kernel

theorem rowEval7323 (x : Key → ℝ) : Integer.Sparse.eval row7323 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, -1, 1, 1, 0, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7323, Integer.Sparse.eval_collectBalanced, rawRowCheck7323]

theorem rawRowCheck7324 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form10 = rawRow7324 := by decide +kernel

theorem rowCheck7324 : row7324 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7324 := by decide +kernel

theorem rowEval7324 (x : Key → ℝ) : Integer.Sparse.eval row7324 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 0, 1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7324, Integer.Sparse.eval_collectBalanced, rawRowCheck7324]

theorem rawRowCheck7325 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form10 = rawRow7325 := by decide +kernel

theorem rowCheck7325 : row7325 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7325 := by decide +kernel

theorem rowEval7325 (x : Key → ℝ) : Integer.Sparse.eval row7325 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7325, Integer.Sparse.eval_collectBalanced, rawRowCheck7325]

theorem rawRowCheck7326 : GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form10 = rawRow7326 := by decide +kernel

theorem rowCheck7326 : row7326 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7326 := by decide +kernel

theorem rowEval7326 (x : Key → ℝ) : Integer.Sparse.eval row7326 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, -1, 1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7326, Integer.Sparse.eval_collectBalanced, rawRowCheck7326]

theorem rawRowCheck7327 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form10 = rawRow7327 := by decide +kernel

theorem rowCheck7327 : row7327 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7327 := by decide +kernel

theorem rowEval7327 (x : Key → ℝ) : Integer.Sparse.eval row7327 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, -1, 1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7327, Integer.Sparse.eval_collectBalanced, rawRowCheck7327]

theorem rawRowCheck7328 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form10 = rawRow7328 := by decide +kernel

theorem rowCheck7328 : row7328 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7328 := by decide +kernel

theorem rowEval7328 (x : Key → ℝ) : Integer.Sparse.eval row7328 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, -1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7328, Integer.Sparse.eval_collectBalanced, rawRowCheck7328]

theorem rawRowCheck7329 : GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form10 = rawRow7329 := by decide +kernel

theorem rowCheck7329 : row7329 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7329 := by decide +kernel

theorem rowEval7329 (x : Key → ℝ) : Integer.Sparse.eval row7329 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 0, 1, 1, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7329, Integer.Sparse.eval_collectBalanced, rawRowCheck7329]

theorem rawRowCheck7330 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form10 = rawRow7330 := by decide +kernel

theorem rowCheck7330 : row7330 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7330 := by decide +kernel

theorem rowEval7330 (x : Key → ℝ) : Integer.Sparse.eval row7330 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7330, Integer.Sparse.eval_collectBalanced, rawRowCheck7330]

theorem rawRowCheck7331 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form10 = rawRow7331 := by decide +kernel

theorem rowCheck7331 : row7331 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7331 := by decide +kernel

theorem rowEval7331 (x : Key → ℝ) : Integer.Sparse.eval row7331 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, -1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7331, Integer.Sparse.eval_collectBalanced, rawRowCheck7331]

theorem rawRowCheck7332 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form10 = rawRow7332 := by decide +kernel

theorem rowCheck7332 : row7332 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7332 := by decide +kernel

theorem rowEval7332 (x : Key → ℝ) : Integer.Sparse.eval row7332 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, -1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7332, Integer.Sparse.eval_collectBalanced, rawRowCheck7332]

theorem rawRowCheck7333 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form10 = rawRow7333 := by decide +kernel

theorem rowCheck7333 : row7333 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7333 := by decide +kernel

theorem rowEval7333 (x : Key → ℝ) : Integer.Sparse.eval row7333 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 0, 1, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7333, Integer.Sparse.eval_collectBalanced, rawRowCheck7333]

theorem rawRowCheck7334 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form10 = rawRow7334 := by decide +kernel

theorem rowCheck7334 : row7334 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7334 := by decide +kernel

theorem rowEval7334 (x : Key → ℝ) : Integer.Sparse.eval row7334 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, -1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7334, Integer.Sparse.eval_collectBalanced, rawRowCheck7334]

theorem rawRowCheck7335 : GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form10 = rawRow7335 := by decide +kernel

theorem rowCheck7335 : row7335 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7335 := by decide +kernel

theorem rowEval7335 (x : Key → ℝ) : Integer.Sparse.eval row7335 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 0, 1, 1, 0, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7335, Integer.Sparse.eval_collectBalanced, rawRowCheck7335]

theorem rawRowCheck7336 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form10 = rawRow7336 := by decide +kernel

theorem rowCheck7336 : row7336 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7336 := by decide +kernel

theorem rowEval7336 (x : Key → ℝ) : Integer.Sparse.eval row7336 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7336, Integer.Sparse.eval_collectBalanced, rawRowCheck7336]

theorem rawRowCheck7337 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form10 = rawRow7337 := by decide +kernel

theorem rowCheck7337 : row7337 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7337 := by decide +kernel

theorem rowEval7337 (x : Key → ℝ) : Integer.Sparse.eval row7337 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 0, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7337, Integer.Sparse.eval_collectBalanced, rawRowCheck7337]

theorem rawRowCheck7338 : GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form10 = rawRow7338 := by decide +kernel

theorem rowCheck7338 : row7338 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7338 := by decide +kernel

theorem rowEval7338 (x : Key → ℝ) : Integer.Sparse.eval row7338 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, -1, 1, 0, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7338, Integer.Sparse.eval_collectBalanced, rawRowCheck7338]

theorem rawRowCheck7339 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form10 = rawRow7339 := by decide +kernel

theorem rowCheck7339 : row7339 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7339 := by decide +kernel

theorem rowEval7339 (x : Key → ℝ) : Integer.Sparse.eval row7339 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 0, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7339, Integer.Sparse.eval_collectBalanced, rawRowCheck7339]

theorem rawRowCheck7340 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form10 = rawRow7340 := by decide +kernel

theorem rowCheck7340 : row7340 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7340 := by decide +kernel

theorem rowEval7340 (x : Key → ℝ) : Integer.Sparse.eval row7340 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, -1, 1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7340, Integer.Sparse.eval_collectBalanced, rawRowCheck7340]

theorem rawRowCheck7341 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form10 = rawRow7341 := by decide +kernel

theorem rowCheck7341 : row7341 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7341 := by decide +kernel

theorem rowEval7341 (x : Key → ℝ) : Integer.Sparse.eval row7341 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, -1, 1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7341, Integer.Sparse.eval_collectBalanced, rawRowCheck7341]

theorem rawRowCheck7342 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form10 = rawRow7342 := by decide +kernel

theorem rowCheck7342 : row7342 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7342 := by decide +kernel

theorem rowEval7342 (x : Key → ℝ) : Integer.Sparse.eval row7342 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 0, 1, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7342, Integer.Sparse.eval_collectBalanced, rawRowCheck7342]

theorem rawRowCheck7343 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form10 = rawRow7343 := by decide +kernel

theorem rowCheck7343 : row7343 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7343 := by decide +kernel

theorem rowEval7343 (x : Key → ℝ) : Integer.Sparse.eval row7343 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, -1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7343, Integer.Sparse.eval_collectBalanced, rawRowCheck7343]

theorem rawRowCheck7344 : GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form10 = rawRow7344 := by decide +kernel

theorem rowCheck7344 : row7344 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7344 := by decide +kernel

theorem rowEval7344 (x : Key → ℝ) : Integer.Sparse.eval row7344 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 0, 1, 0, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7344, Integer.Sparse.eval_collectBalanced, rawRowCheck7344]

theorem rawRowCheck7345 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form10 = rawRow7345 := by decide +kernel

theorem rowCheck7345 : row7345 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7345 := by decide +kernel

theorem rowEval7345 (x : Key → ℝ) : Integer.Sparse.eval row7345 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, -1, 0, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7345, Integer.Sparse.eval_collectBalanced, rawRowCheck7345]

theorem rawRowCheck7346 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form10 = rawRow7346 := by decide +kernel

theorem rowCheck7346 : row7346 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7346 := by decide +kernel

theorem rowEval7346 (x : Key → ℝ) : Integer.Sparse.eval row7346 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, -1, 0] GramFunctions.Block2.form10) x := by
  rw [rowCheck7346, Integer.Sparse.eval_collectBalanced, rawRowCheck7346]

theorem rawRowCheck7347 : GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form10 = rawRow7347 := by decide +kernel

theorem rowCheck7347 : row7347 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow7347 := by decide +kernel

theorem rowEval7347 (x : Key → ℝ) : Integer.Sparse.eval row7347 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![-1, 1, 1, 0, 0, -1] GramFunctions.Block2.form10) x := by
  rw [rowCheck7347, Integer.Sparse.eval_collectBalanced, rawRowCheck7347]

end MUB6.Certificate.GramRows

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2Row10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form1) x := by
  fin_cases k
  · exact rowEval7048 x
  · exact rowEval7049 x
  · exact rowEval7050 x
  · exact rowEval7051 x
  · exact rowEval7052 x
  · exact rowEval7053 x
  · exact rowEval7054 x
  · exact rowEval7055 x
  · exact rowEval7056 x
  · exact rowEval7057 x
  · exact rowEval7058 x
  · exact rowEval7059 x
  · exact rowEval7060 x
  · exact rowEval7061 x
  · exact rowEval7062 x
  · exact rowEval7063 x
  · exact rowEval7064 x
  · exact rowEval7065 x
  · exact rowEval7066 x
  · exact rowEval7067 x
  · exact rowEval7068 x
  · exact rowEval7069 x
  · exact rowEval7070 x
  · exact rowEval7071 x
  · exact rowEval7072 x
  · exact rowEval7073 x
  · exact rowEval7074 x
  · exact rowEval7075 x
  · exact rowEval7076 x
  · exact rowEval7077 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form2) x := by
  fin_cases k
  · exact rowEval7078 x
  · exact rowEval7079 x
  · exact rowEval7080 x
  · exact rowEval7081 x
  · exact rowEval7082 x
  · exact rowEval7083 x
  · exact rowEval7084 x
  · exact rowEval7085 x
  · exact rowEval7086 x
  · exact rowEval7087 x
  · exact rowEval7088 x
  · exact rowEval7089 x
  · exact rowEval7090 x
  · exact rowEval7091 x
  · exact rowEval7092 x
  · exact rowEval7093 x
  · exact rowEval7094 x
  · exact rowEval7095 x
  · exact rowEval7096 x
  · exact rowEval7097 x
  · exact rowEval7098 x
  · exact rowEval7099 x
  · exact rowEval7100 x
  · exact rowEval7101 x
  · exact rowEval7102 x
  · exact rowEval7103 x
  · exact rowEval7104 x
  · exact rowEval7105 x
  · exact rowEval7106 x
  · exact rowEval7107 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form3) x := by
  fin_cases k
  · exact rowEval7108 x
  · exact rowEval7109 x
  · exact rowEval7110 x
  · exact rowEval7111 x
  · exact rowEval7112 x
  · exact rowEval7113 x
  · exact rowEval7114 x
  · exact rowEval7115 x
  · exact rowEval7116 x
  · exact rowEval7117 x
  · exact rowEval7118 x
  · exact rowEval7119 x
  · exact rowEval7120 x
  · exact rowEval7121 x
  · exact rowEval7122 x
  · exact rowEval7123 x
  · exact rowEval7124 x
  · exact rowEval7125 x
  · exact rowEval7126 x
  · exact rowEval7127 x
  · exact rowEval7128 x
  · exact rowEval7129 x
  · exact rowEval7130 x
  · exact rowEval7131 x
  · exact rowEval7132 x
  · exact rowEval7133 x
  · exact rowEval7134 x
  · exact rowEval7135 x
  · exact rowEval7136 x
  · exact rowEval7137 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form4) x := by
  fin_cases k
  · exact rowEval7138 x
  · exact rowEval7139 x
  · exact rowEval7140 x
  · exact rowEval7141 x
  · exact rowEval7142 x
  · exact rowEval7143 x
  · exact rowEval7144 x
  · exact rowEval7145 x
  · exact rowEval7146 x
  · exact rowEval7147 x
  · exact rowEval7148 x
  · exact rowEval7149 x
  · exact rowEval7150 x
  · exact rowEval7151 x
  · exact rowEval7152 x
  · exact rowEval7153 x
  · exact rowEval7154 x
  · exact rowEval7155 x
  · exact rowEval7156 x
  · exact rowEval7157 x
  · exact rowEval7158 x
  · exact rowEval7159 x
  · exact rowEval7160 x
  · exact rowEval7161 x
  · exact rowEval7162 x
  · exact rowEval7163 x
  · exact rowEval7164 x
  · exact rowEval7165 x
  · exact rowEval7166 x
  · exact rowEval7167 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form9) x := by
  fin_cases k
  · exact rowEval7288 x
  · exact rowEval7289 x
  · exact rowEval7290 x
  · exact rowEval7291 x
  · exact rowEval7292 x
  · exact rowEval7293 x
  · exact rowEval7294 x
  · exact rowEval7295 x
  · exact rowEval7296 x
  · exact rowEval7297 x
  · exact rowEval7298 x
  · exact rowEval7299 x
  · exact rowEval7300 x
  · exact rowEval7301 x
  · exact rowEval7302 x
  · exact rowEval7303 x
  · exact rowEval7304 x
  · exact rowEval7305 x
  · exact rowEval7306 x
  · exact rowEval7307 x
  · exact rowEval7308 x
  · exact rowEval7309 x
  · exact rowEval7310 x
  · exact rowEval7311 x
  · exact rowEval7312 x
  · exact rowEval7313 x
  · exact rowEval7314 x
  · exact rowEval7315 x
  · exact rowEval7316 x
  · exact rowEval7317 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block2.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block2.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block2.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block2.form10.terms k).tag (GramFunctions.Block2.form10.terms k).charge GramFunctions.Block2.form10) x := by
  fin_cases k
  · exact rowEval7318 x
  · exact rowEval7319 x
  · exact rowEval7320 x
  · exact rowEval7321 x
  · exact rowEval7322 x
  · exact rowEval7323 x
  · exact rowEval7324 x
  · exact rowEval7325 x
  · exact rowEval7326 x
  · exact rowEval7327 x
  · exact rowEval7328 x
  · exact rowEval7329 x
  · exact rowEval7330 x
  · exact rowEval7331 x
  · exact rowEval7332 x
  · exact rowEval7333 x
  · exact rowEval7334 x
  · exact rowEval7335 x
  · exact rowEval7336 x
  · exact rowEval7337 x
  · exact rowEval7338 x
  · exact rowEval7339 x
  · exact rowEval7340 x
  · exact rowEval7341 x
  · exact rowEval7342 x
  · exact rowEval7343 x
  · exact rowEval7344 x
  · exact rowEval7345 x
  · exact rowEval7346 x
  · exact rowEval7347 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block2.form10.mixedGram GramFunctions.Block2.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block2.form10 GramFunctions.Block2.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block2

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block2

theorem entryEvalRow10_e_oai (j : Fin 11) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries 10 j) (GramNormalization.eval B) =
      (GramFunctions.Block2.forms 10).mixedGram (GramFunctions.Block2.forms j) B := by
  fin_cases j
  · exact entryEval10_0_e B hB
  · exact entryEval10_1 B hB
  · exact entryEval10_2 B hB
  · exact entryEval10_3 B hB
  · exact entryEval10_4 B hB
  · exact entryEval10_5_e B hB
  · exact entryEval10_6_e B hB
  · exact entryEval10_7_e B hB
  · exact entryEval10_8_e B hB
  · exact entryEval10_9 B hB
  · exact entryEval10_10 B hB

end MUB6.Certificate.GramEntries.Block2

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e_oai := @OAI.MUB6.Certificate.GramEntries.Block2.entryEvalRow10_e_oai
