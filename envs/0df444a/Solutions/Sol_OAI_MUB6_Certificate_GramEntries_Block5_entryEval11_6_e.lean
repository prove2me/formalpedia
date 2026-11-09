-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T17:49:06.549207+00:00
-- url     : https://prove2.me/submissions/09dae06f-87cf-4f94-ba85-68441fc1bf0e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E041
import Definitions.Def_OAIQ106E044
import Definitions.Def_OAIQ106E050
import Definitions.Def_OAIQ106E151
import Definitions.Def_OAIQ106E153
import Definitions.Def_OAIQ106E170
import Definitions.Def_OAIQ106E172

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramRows_Block179
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rawRowCheck19964 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19964 := by decide +kernel

theorem rowCheck19964 : row19964 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19964 := by decide +kernel

theorem rowEval19964 (x : Key → ℝ) : Integer.Sparse.eval row19964 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19964, Integer.Sparse.eval_collectBalanced, rawRowCheck19964]

theorem rawRowCheck19965 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19965 := by decide +kernel

theorem rowCheck19965 : row19965 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19965 := by decide +kernel

theorem rowEval19965 (x : Key → ℝ) : Integer.Sparse.eval row19965 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19965, Integer.Sparse.eval_collectBalanced, rawRowCheck19965]

theorem rawRowCheck19966 : GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19966 := by decide +kernel

theorem rowCheck19966 : row19966 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19966 := by decide +kernel

theorem rowEval19966 (x : Key → ℝ) : Integer.Sparse.eval row19966 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, -1, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19966, Integer.Sparse.eval_collectBalanced, rawRowCheck19966]

theorem rawRowCheck19967 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form6 = rawRow19967 := by decide +kernel

theorem rowCheck19967 : row19967 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19967 := by decide +kernel

theorem rowEval19967 (x : Key → ℝ) : Integer.Sparse.eval row19967 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19967, Integer.Sparse.eval_collectBalanced, rawRowCheck19967]

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

theorem rawRowCheck19968 : GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form6 = rawRow19968 := by decide +kernel

theorem rowCheck19968 : row19968 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19968 := by decide +kernel

theorem rowEval19968 (x : Key → ℝ) : Integer.Sparse.eval row19968 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, -1, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19968, Integer.Sparse.eval_collectBalanced, rawRowCheck19968]

theorem rawRowCheck19969 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form6 = rawRow19969 := by decide +kernel

theorem rowCheck19969 : row19969 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19969 := by decide +kernel

theorem rowEval19969 (x : Key → ℝ) : Integer.Sparse.eval row19969 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, -1, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19969, Integer.Sparse.eval_collectBalanced, rawRowCheck19969]

theorem rawRowCheck19970 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form6 = rawRow19970 := by decide +kernel

theorem rowCheck19970 : row19970 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19970 := by decide +kernel

theorem rowEval19970 (x : Key → ℝ) : Integer.Sparse.eval row19970 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 0, 2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19970, Integer.Sparse.eval_collectBalanced, rawRowCheck19970]

theorem rawRowCheck19971 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form6 = rawRow19971 := by decide +kernel

theorem rowCheck19971 : row19971 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19971 := by decide +kernel

theorem rowEval19971 (x : Key → ℝ) : Integer.Sparse.eval row19971 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19971, Integer.Sparse.eval_collectBalanced, rawRowCheck19971]

theorem rawRowCheck19972 : GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form6 = rawRow19972 := by decide +kernel

theorem rowCheck19972 : row19972 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19972 := by decide +kernel

theorem rowEval19972 (x : Key → ℝ) : Integer.Sparse.eval row19972 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 0, 2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19972, Integer.Sparse.eval_collectBalanced, rawRowCheck19972]

theorem rawRowCheck19973 : GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow19973 := by decide +kernel

theorem rowCheck19973 : row19973 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19973 := by decide +kernel

theorem rowEval19973 (x : Key → ℝ) : Integer.Sparse.eval row19973 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19973, Integer.Sparse.eval_collectBalanced, rawRowCheck19973]

theorem rawRowCheck19974 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow19974 := by decide +kernel

theorem rowCheck19974 : row19974 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19974 := by decide +kernel

theorem rowEval19974 (x : Key → ℝ) : Integer.Sparse.eval row19974 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19974, Integer.Sparse.eval_collectBalanced, rawRowCheck19974]

theorem rawRowCheck19975 : GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow19975 := by decide +kernel

theorem rowCheck19975 : row19975 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19975 := by decide +kernel

theorem rowEval19975 (x : Key → ℝ) : Integer.Sparse.eval row19975 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -2, 2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19975, Integer.Sparse.eval_collectBalanced, rawRowCheck19975]

theorem rawRowCheck19976 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form6 = rawRow19976 := by decide +kernel

theorem rowCheck19976 : row19976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19976 := by decide +kernel

theorem rowEval19976 (x : Key → ℝ) : Integer.Sparse.eval row19976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19976, Integer.Sparse.eval_collectBalanced, rawRowCheck19976]

theorem rawRowCheck19977 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form6 = rawRow19977 := by decide +kernel

theorem rowCheck19977 : row19977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19977 := by decide +kernel

theorem rowEval19977 (x : Key → ℝ) : Integer.Sparse.eval row19977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 0, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19977, Integer.Sparse.eval_collectBalanced, rawRowCheck19977]

theorem rawRowCheck19978 : GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form6 = rawRow19978 := by decide +kernel

theorem rowCheck19978 : row19978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19978 := by decide +kernel

theorem rowEval19978 (x : Key → ℝ) : Integer.Sparse.eval row19978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, -2, 2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19978, Integer.Sparse.eval_collectBalanced, rawRowCheck19978]

theorem rawRowCheck19979 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19979 := by decide +kernel

theorem rowCheck19979 : row19979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19979 := by decide +kernel

theorem rowEval19979 (x : Key → ℝ) : Integer.Sparse.eval row19979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19979, Integer.Sparse.eval_collectBalanced, rawRowCheck19979]

theorem rawRowCheck19980 : GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19980 := by decide +kernel

theorem rowCheck19980 : row19980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19980 := by decide +kernel

theorem rowEval19980 (x : Key → ℝ) : Integer.Sparse.eval row19980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19980, Integer.Sparse.eval_collectBalanced, rawRowCheck19980]

theorem rawRowCheck19981 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19981 := by decide +kernel

theorem rowCheck19981 : row19981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19981 := by decide +kernel

theorem rowEval19981 (x : Key → ℝ) : Integer.Sparse.eval row19981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19981, Integer.Sparse.eval_collectBalanced, rawRowCheck19981]

theorem rawRowCheck19982 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19982 := by decide +kernel

theorem rowCheck19982 : row19982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19982 := by decide +kernel

theorem rowEval19982 (x : Key → ℝ) : Integer.Sparse.eval row19982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19982, Integer.Sparse.eval_collectBalanced, rawRowCheck19982]

theorem rawRowCheck19983 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19983 := by decide +kernel

theorem rowCheck19983 : row19983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19983 := by decide +kernel

theorem rowEval19983 (x : Key → ℝ) : Integer.Sparse.eval row19983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19983, Integer.Sparse.eval_collectBalanced, rawRowCheck19983]

theorem rawRowCheck19984 : GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19984 := by decide +kernel

theorem rowCheck19984 : row19984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19984 := by decide +kernel

theorem rowEval19984 (x : Key → ℝ) : Integer.Sparse.eval row19984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 0, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19984, Integer.Sparse.eval_collectBalanced, rawRowCheck19984]

theorem rawRowCheck19985 : GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form6 = rawRow19985 := by decide +kernel

theorem rowCheck19985 : row19985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19985 := by decide +kernel

theorem rowEval19985 (x : Key → ℝ) : Integer.Sparse.eval row19985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19985, Integer.Sparse.eval_collectBalanced, rawRowCheck19985]

theorem rawRowCheck19986 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form6 = rawRow19986 := by decide +kernel

theorem rowCheck19986 : row19986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19986 := by decide +kernel

theorem rowEval19986 (x : Key → ℝ) : Integer.Sparse.eval row19986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19986, Integer.Sparse.eval_collectBalanced, rawRowCheck19986]

theorem rawRowCheck19987 : GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form6 = rawRow19987 := by decide +kernel

theorem rowCheck19987 : row19987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19987 := by decide +kernel

theorem rowEval19987 (x : Key → ℝ) : Integer.Sparse.eval row19987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, -1, 2, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19987, Integer.Sparse.eval_collectBalanced, rawRowCheck19987]

theorem rawRowCheck19988 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form6 = rawRow19988 := by decide +kernel

theorem rowCheck19988 : row19988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19988 := by decide +kernel

theorem rowEval19988 (x : Key → ℝ) : Integer.Sparse.eval row19988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19988, Integer.Sparse.eval_collectBalanced, rawRowCheck19988]

theorem rawRowCheck19989 : GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form6 = rawRow19989 := by decide +kernel

theorem rowCheck19989 : row19989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19989 := by decide +kernel

theorem rowEval19989 (x : Key → ℝ) : Integer.Sparse.eval row19989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, -1, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19989, Integer.Sparse.eval_collectBalanced, rawRowCheck19989]

theorem rawRowCheck19990 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form6 = rawRow19990 := by decide +kernel

theorem rowCheck19990 : row19990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19990 := by decide +kernel

theorem rowEval19990 (x : Key → ℝ) : Integer.Sparse.eval row19990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, -1, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19990, Integer.Sparse.eval_collectBalanced, rawRowCheck19990]

theorem rawRowCheck19991 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form6 = rawRow19991 := by decide +kernel

theorem rowCheck19991 : row19991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19991 := by decide +kernel

theorem rowEval19991 (x : Key → ℝ) : Integer.Sparse.eval row19991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 0, 2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19991, Integer.Sparse.eval_collectBalanced, rawRowCheck19991]

theorem rawRowCheck19992 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form6 = rawRow19992 := by decide +kernel

theorem rowCheck19992 : row19992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19992 := by decide +kernel

theorem rowEval19992 (x : Key → ℝ) : Integer.Sparse.eval row19992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19992, Integer.Sparse.eval_collectBalanced, rawRowCheck19992]

theorem rawRowCheck19993 : GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form6 = rawRow19993 := by decide +kernel

theorem rowCheck19993 : row19993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19993 := by decide +kernel

theorem rowEval19993 (x : Key → ℝ) : Integer.Sparse.eval row19993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -2, 2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck19993, Integer.Sparse.eval_collectBalanced, rawRowCheck19993]

theorem rawRowCheck19994 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form6 = rawRow19994 := by decide +kernel

theorem rowCheck19994 : row19994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19994 := by decide +kernel

theorem rowEval19994 (x : Key → ℝ) : Integer.Sparse.eval row19994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 0, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19994, Integer.Sparse.eval_collectBalanced, rawRowCheck19994]

theorem rawRowCheck19995 : GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form6 = rawRow19995 := by decide +kernel

theorem rowCheck19995 : row19995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19995 := by decide +kernel

theorem rowEval19995 (x : Key → ℝ) : Integer.Sparse.eval row19995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, -2, 2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19995, Integer.Sparse.eval_collectBalanced, rawRowCheck19995]

theorem rawRowCheck19996 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form6 = rawRow19996 := by decide +kernel

theorem rowCheck19996 : row19996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19996 := by decide +kernel

theorem rowEval19996 (x : Key → ℝ) : Integer.Sparse.eval row19996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19996, Integer.Sparse.eval_collectBalanced, rawRowCheck19996]

theorem rawRowCheck19997 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form6 = rawRow19997 := by decide +kernel

theorem rowCheck19997 : row19997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19997 := by decide +kernel

theorem rowEval19997 (x : Key → ℝ) : Integer.Sparse.eval row19997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 0, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19997, Integer.Sparse.eval_collectBalanced, rawRowCheck19997]

theorem rawRowCheck19998 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form6 = rawRow19998 := by decide +kernel

theorem rowCheck19998 : row19998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19998 := by decide +kernel

theorem rowEval19998 (x : Key → ℝ) : Integer.Sparse.eval row19998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck19998, Integer.Sparse.eval_collectBalanced, rawRowCheck19998]

theorem rawRowCheck19999 : GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form6 = rawRow19999 := by decide +kernel

theorem rowCheck19999 : row19999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow19999 := by decide +kernel

theorem rowEval19999 (x : Key → ℝ) : Integer.Sparse.eval row19999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, -1, 2, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck19999, Integer.Sparse.eval_collectBalanced, rawRowCheck19999]

theorem rawRowCheck20000 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form6 = rawRow20000 := by decide +kernel

theorem rowCheck20000 : row20000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20000 := by decide +kernel

theorem rowEval20000 (x : Key → ℝ) : Integer.Sparse.eval row20000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, -1, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20000, Integer.Sparse.eval_collectBalanced, rawRowCheck20000]

theorem rawRowCheck20001 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form6 = rawRow20001 := by decide +kernel

theorem rowCheck20001 : row20001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20001 := by decide +kernel

theorem rowEval20001 (x : Key → ℝ) : Integer.Sparse.eval row20001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -2, 2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20001, Integer.Sparse.eval_collectBalanced, rawRowCheck20001]

theorem rawRowCheck20002 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form6 = rawRow20002 := by decide +kernel

theorem rowCheck20002 : row20002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20002 := by decide +kernel

theorem rowEval20002 (x : Key → ℝ) : Integer.Sparse.eval row20002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, -2, 2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20002, Integer.Sparse.eval_collectBalanced, rawRowCheck20002]

theorem rawRowCheck20003 : GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form6 = rawRow20003 := by decide +kernel

theorem rowCheck20003 : row20003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20003 := by decide +kernel

theorem rowEval20003 (x : Key → ℝ) : Integer.Sparse.eval row20003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, -1, 2, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20003, Integer.Sparse.eval_collectBalanced, rawRowCheck20003]

theorem rawRowCheck20004 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form6 = rawRow20004 := by decide +kernel

theorem rowCheck20004 : row20004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20004 := by decide +kernel

theorem rowEval20004 (x : Key → ℝ) : Integer.Sparse.eval row20004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20004, Integer.Sparse.eval_collectBalanced, rawRowCheck20004]

theorem rawRowCheck20005 : GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form6 = rawRow20005 := by decide +kernel

theorem rowCheck20005 : row20005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20005 := by decide +kernel

theorem rowEval20005 (x : Key → ℝ) : Integer.Sparse.eval row20005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 0, 2, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20005, Integer.Sparse.eval_collectBalanced, rawRowCheck20005]

theorem rawRowCheck20006 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form6 = rawRow20006 := by decide +kernel

theorem rowCheck20006 : row20006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20006 := by decide +kernel

theorem rowEval20006 (x : Key → ℝ) : Integer.Sparse.eval row20006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20006, Integer.Sparse.eval_collectBalanced, rawRowCheck20006]

theorem rawRowCheck20007 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form6 = rawRow20007 := by decide +kernel

theorem rowCheck20007 : row20007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20007 := by decide +kernel

theorem rowEval20007 (x : Key → ℝ) : Integer.Sparse.eval row20007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20007, Integer.Sparse.eval_collectBalanced, rawRowCheck20007]

theorem rawRowCheck20008 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form6 = rawRow20008 := by decide +kernel

theorem rowCheck20008 : row20008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20008 := by decide +kernel

theorem rowEval20008 (x : Key → ℝ) : Integer.Sparse.eval row20008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20008, Integer.Sparse.eval_collectBalanced, rawRowCheck20008]

theorem rawRowCheck20009 : GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form6 = rawRow20009 := by decide +kernel

theorem rowCheck20009 : row20009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20009 := by decide +kernel

theorem rowEval20009 (x : Key → ℝ) : Integer.Sparse.eval row20009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20009, Integer.Sparse.eval_collectBalanced, rawRowCheck20009]

theorem rawRowCheck20010 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form6 = rawRow20010 := by decide +kernel

theorem rowCheck20010 : row20010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20010 := by decide +kernel

theorem rowEval20010 (x : Key → ℝ) : Integer.Sparse.eval row20010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20010, Integer.Sparse.eval_collectBalanced, rawRowCheck20010]

theorem rawRowCheck20011 : GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form6 = rawRow20011 := by decide +kernel

theorem rowCheck20011 : row20011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20011 := by decide +kernel

theorem rowEval20011 (x : Key → ℝ) : Integer.Sparse.eval row20011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 0, 2, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20011, Integer.Sparse.eval_collectBalanced, rawRowCheck20011]

theorem rawRowCheck20012 : GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form6 = rawRow20012 := by decide +kernel

theorem rowCheck20012 : row20012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20012 := by decide +kernel

theorem rowEval20012 (x : Key → ℝ) : Integer.Sparse.eval row20012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, -1, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20012, Integer.Sparse.eval_collectBalanced, rawRowCheck20012]

theorem rawRowCheck20013 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form6 = rawRow20013 := by decide +kernel

theorem rowCheck20013 : row20013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20013 := by decide +kernel

theorem rowEval20013 (x : Key → ℝ) : Integer.Sparse.eval row20013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20013, Integer.Sparse.eval_collectBalanced, rawRowCheck20013]

theorem rawRowCheck20014 : GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form6 = rawRow20014 := by decide +kernel

theorem rowCheck20014 : row20014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20014 := by decide +kernel

theorem rowEval20014 (x : Key → ℝ) : Integer.Sparse.eval row20014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -2, 0, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20014, Integer.Sparse.eval_collectBalanced, rawRowCheck20014]

theorem rawRowCheck20015 : GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form6 = rawRow20015 := by decide +kernel

theorem rowCheck20015 : row20015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20015 := by decide +kernel

theorem rowEval20015 (x : Key → ℝ) : Integer.Sparse.eval row20015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, -2, 0, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20015, Integer.Sparse.eval_collectBalanced, rawRowCheck20015]

theorem rawRowCheck20016 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form6 = rawRow20016 := by decide +kernel

theorem rowCheck20016 : row20016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20016 := by decide +kernel

theorem rowEval20016 (x : Key → ℝ) : Integer.Sparse.eval row20016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20016, Integer.Sparse.eval_collectBalanced, rawRowCheck20016]

theorem rawRowCheck20017 : GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form6 = rawRow20017 := by decide +kernel

theorem rowCheck20017 : row20017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20017 := by decide +kernel

theorem rowEval20017 (x : Key → ℝ) : Integer.Sparse.eval row20017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, -1, 0, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20017, Integer.Sparse.eval_collectBalanced, rawRowCheck20017]

theorem rawRowCheck20018 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form6 = rawRow20018 := by decide +kernel

theorem rowCheck20018 : row20018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20018 := by decide +kernel

theorem rowEval20018 (x : Key → ℝ) : Integer.Sparse.eval row20018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, -1, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20018, Integer.Sparse.eval_collectBalanced, rawRowCheck20018]

theorem rawRowCheck20019 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form6 = rawRow20019 := by decide +kernel

theorem rowCheck20019 : row20019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20019 := by decide +kernel

theorem rowEval20019 (x : Key → ℝ) : Integer.Sparse.eval row20019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -2, 0, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20019, Integer.Sparse.eval_collectBalanced, rawRowCheck20019]

theorem rawRowCheck20020 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form6 = rawRow20020 := by decide +kernel

theorem rowCheck20020 : row20020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20020 := by decide +kernel

theorem rowEval20020 (x : Key → ℝ) : Integer.Sparse.eval row20020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, -2, 0] GramFunctions.Block5.form6) x := by
  rw [rowCheck20020, Integer.Sparse.eval_collectBalanced, rawRowCheck20020]

theorem rawRowCheck20021 : GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form6 = rawRow20021 := by decide +kernel

theorem rowCheck20021 : row20021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20021 := by decide +kernel

theorem rowEval20021 (x : Key → ℝ) : Integer.Sparse.eval row20021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, -1, 0, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20021, Integer.Sparse.eval_collectBalanced, rawRowCheck20021]

theorem rawRowCheck20022 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form6 = rawRow20022 := by decide +kernel

theorem rowCheck20022 : row20022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20022 := by decide +kernel

theorem rowEval20022 (x : Key → ℝ) : Integer.Sparse.eval row20022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -2, -1] GramFunctions.Block5.form6) x := by
  rw [rowCheck20022, Integer.Sparse.eval_collectBalanced, rawRowCheck20022]

theorem rawRowCheck20023 : GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form6 = rawRow20023 := by decide +kernel

theorem rowCheck20023 : row20023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow20023 := by decide +kernel

theorem rowEval20023 (x : Key → ℝ) : Integer.Sparse.eval row20023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 0 ![1, 2, 0, 0, -1, -2] GramFunctions.Block5.form6) x := by
  rw [rowCheck20023, Integer.Sparse.eval_collectBalanced, rawRowCheck20023]

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

theorem entryCheck11_6 : entry11_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form11.terms k).coefficient) (rows11_6 k)) := by decide +kernel

theorem rowsSound11_6 (k : Fin GramFunctions.Block5.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block5.form11.terms k).tag (GramFunctions.Block5.form11.terms k).charge GramFunctions.Block5.form6) x := by
  fin_cases k
  · exact rowEval19964 x
  · exact rowEval19965 x
  · exact rowEval19966 x
  · exact rowEval19967 x
  · exact rowEval19968 x
  · exact rowEval19969 x
  · exact rowEval19970 x
  · exact rowEval19971 x
  · exact rowEval19972 x
  · exact rowEval19973 x
  · exact rowEval19974 x
  · exact rowEval19975 x
  · exact rowEval19976 x
  · exact rowEval19977 x
  · exact rowEval19978 x
  · exact rowEval19979 x
  · exact rowEval19980 x
  · exact rowEval19981 x
  · exact rowEval19982 x
  · exact rowEval19983 x
  · exact rowEval19984 x
  · exact rowEval19985 x
  · exact rowEval19986 x
  · exact rowEval19987 x
  · exact rowEval19988 x
  · exact rowEval19989 x
  · exact rowEval19990 x
  · exact rowEval19991 x
  · exact rowEval19992 x
  · exact rowEval19993 x
  · exact rowEval19994 x
  · exact rowEval19995 x
  · exact rowEval19996 x
  · exact rowEval19997 x
  · exact rowEval19998 x
  · exact rowEval19999 x
  · exact rowEval20000 x
  · exact rowEval20001 x
  · exact rowEval20002 x
  · exact rowEval20003 x
  · exact rowEval20004 x
  · exact rowEval20005 x
  · exact rowEval20006 x
  · exact rowEval20007 x
  · exact rowEval20008 x
  · exact rowEval20009 x
  · exact rowEval20010 x
  · exact rowEval20011 x
  · exact rowEval20012 x
  · exact rowEval20013 x
  · exact rowEval20014 x
  · exact rowEval20015 x
  · exact rowEval20016 x
  · exact rowEval20017 x
  · exact rowEval20018 x
  · exact rowEval20019 x
  · exact rowEval20020 x
  · exact rowEval20021 x
  · exact rowEval20022 x
  · exact rowEval20023 x

theorem entryEval11_6_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_6 (GramNormalization.eval B) = GramFunctions.Block5.form11.mixedGram GramFunctions.Block5.form6 B := by
  rw [entryCheck11_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block5.form11 GramFunctions.Block5.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_6]

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryEval11_6_e_oai
