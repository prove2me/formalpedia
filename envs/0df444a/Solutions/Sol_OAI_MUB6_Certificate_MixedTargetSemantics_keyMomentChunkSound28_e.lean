-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:05.646637+00:00
-- url     : https://prove2.me/submissions/8aaf05e6-b146-4225-87c5-e2f218fa5293

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E130
import Definitions.Def_OAIQ106E137
import Definitions.Def_OAIQ106E147
import Definitions.Def_OAIQ106E151

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
attribute [-simp] _root_.OAI.MUB6.embedCharge_apply _root_.OAI.MUB6.offDiagSum_zero _root_.OAI.MUB6.rowFourier_zero
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13433 raw13433Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw13433 raw13433Labels = mixedMoment B raw13433step0 raw13433step0Labels := by
      have hz : ∀ j, raw13433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13433step0 = (fun i j => raw13433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13433step0 raw13433; decide +kernel
      have hl : raw13433step0Labels = raw13433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13433 raw13433Labels permutation434 hz
    mixedMoment B raw13433step0 raw13433step0Labels = mixedMoment B raw13433step1 raw13433step1Labels := by
      have ha : raw13433step1 = (fun i j => raw13433step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13433step1 raw13433step0; decide +kernel
      have hl : raw13433step1Labels = raw13433step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13433step0 raw13433step0Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40337 raw40337Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40337 raw40337Labels = mixedMoment B raw40337step0 raw40337step0Labels := by
      have hz : ∀ j, raw40337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40337step0 = (fun i j => raw40337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40337step0 raw40337; decide +kernel
      have hl : raw40337step0Labels = raw40337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40337 raw40337Labels permutation434 hz
    mixedMoment B raw40337step0 raw40337step0Labels = mixedMoment B raw40337step1 raw40337step1Labels := by
      have hz : ∀ j, raw40337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40337step1 = (fun i j => raw40337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40337step1 raw40337step0; decide +kernel
      have hl : raw40337step1Labels = raw40337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40337step0 raw40337step0Labels permutation80 hz
    mixedMoment B raw40337step1 raw40337step1Labels = mixedMoment B raw40337step2 raw40337step2Labels := by
      have ha : raw40337step2 = (fun i j => raw40337step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40337step2 raw40337step1; decide +kernel
      have hl : raw40337step2Labels = raw40337step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40337step1 raw40337step1Labels permutation8 permutation3
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical40338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40338 raw40338Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw40338 raw40338Labels = mixedMoment B raw40338step0 raw40338step0Labels := by
      have hz : ∀ j, raw40338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40338step0 = (fun i j => raw40338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40338step0 raw40338; decide +kernel
      have hl : raw40338step0Labels = raw40338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40338 raw40338Labels permutation434 hz
    mixedMoment B raw40338step0 raw40338step0Labels = mixedMoment B raw40338step1 raw40338step1Labels := by
      have hz : ∀ j, raw40338step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40338step1 = (fun i j => raw40338step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40338step1 raw40338step0; decide +kernel
      have hl : raw40338step1Labels = raw40338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40338step0 raw40338step0Labels permutation80 hz
    mixedMoment B raw40338step1 raw40338step1Labels = mixedMoment B raw40338step2 raw40338step2Labels := by
      have ha : raw40338step2 = (fun i j => raw40338step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40338step2 raw40338step1; decide +kernel
      have hl : raw40338step2Labels = raw40338step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40338step1 raw40338step1Labels permutation8 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical40339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40339 raw40339Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw40339 raw40339Labels = mixedMoment B raw40339step0 raw40339step0Labels := by
      have hz : ∀ j, raw40339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40339step0 = (fun i j => raw40339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40339step0 raw40339; decide +kernel
      have hl : raw40339step0Labels = raw40339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40339 raw40339Labels permutation434 hz
    mixedMoment B raw40339step0 raw40339step0Labels = mixedMoment B raw40339step1 raw40339step1Labels := by
      have hz : ∀ j, raw40339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40339step1 = (fun i j => raw40339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40339step1 raw40339step0; decide +kernel
      have hl : raw40339step1Labels = raw40339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40339step0 raw40339step0Labels permutation80 hz
    mixedMoment B raw40339step1 raw40339step1Labels = mixedMoment B raw40339step2 raw40339step2Labels := by
      have ha : raw40339step2 = (fun i j => raw40339step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40339step2 raw40339step1; decide +kernel
      have hl : raw40339step2Labels = raw40339step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40339step1 raw40339step1Labels permutation8 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

theorem canonical40340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40340 raw40340Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw40340 raw40340Labels = mixedMoment B raw40340step0 raw40340step0Labels := by
      have hz : ∀ j, raw40340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40340step0 = (fun i j => raw40340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40340step0 raw40340; decide +kernel
      have hl : raw40340step0Labels = raw40340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40340 raw40340Labels permutation434 hz
    mixedMoment B raw40340step0 raw40340step0Labels = mixedMoment B raw40340step1 raw40340step1Labels := by
      have hz : ∀ j, raw40340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40340step1 = (fun i j => raw40340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40340step1 raw40340step0; decide +kernel
      have hl : raw40340step1Labels = raw40340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40340step0 raw40340step0Labels permutation80 hz
    mixedMoment B raw40340step1 raw40340step1Labels = mixedMoment B raw40340step2 raw40340step2Labels := by
      have ha : raw40340step2 = (fun i j => raw40340step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40340step2 raw40340step1; decide +kernel
      have hl : raw40340step2Labels = raw40340step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40340step1 raw40340step1Labels permutation8 permutation3
    _ = mixedMoment B node3056 node3056Labels := by rfl

theorem canonical40341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40341 raw40341Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw40341 raw40341Labels = mixedMoment B raw40341step0 raw40341step0Labels := by
      have hz : ∀ j, raw40341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40341step0 = (fun i j => raw40341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40341step0 raw40341; decide +kernel
      have hl : raw40341step0Labels = raw40341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40341 raw40341Labels permutation346 hz
    mixedMoment B raw40341step0 raw40341step0Labels = mixedMoment B raw40341step1 raw40341step1Labels := by
      have ha : raw40341step1 = (fun i j => raw40341step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40341step1 raw40341step0; decide +kernel
      have hl : raw40341step1Labels = raw40341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40341step0 raw40341step0Labels permutation32 permutation3
    _ = mixedMoment B node3031 node3031Labels := by rfl

theorem canonical40342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40342 raw40342Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw40342 raw40342Labels = mixedMoment B raw40342step0 raw40342step0Labels := by
      have hz : ∀ j, raw40342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40342step0 = (fun i j => raw40342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40342step0 raw40342; decide +kernel
      have hl : raw40342step0Labels = raw40342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40342 raw40342Labels permutation346 hz
    mixedMoment B raw40342step0 raw40342step0Labels = mixedMoment B raw40342step1 raw40342step1Labels := by
      have ha : raw40342step1 = (fun i j => raw40342step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40342step1 raw40342step0; decide +kernel
      have hl : raw40342step1Labels = raw40342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40342step0 raw40342step0Labels permutation32 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

theorem canonical40343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40343 raw40343Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw40343 raw40343Labels = mixedMoment B raw40343step0 raw40343step0Labels := by
      have hz : ∀ j, raw40343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40343step0 = (fun i j => raw40343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40343step0 raw40343; decide +kernel
      have hl : raw40343step0Labels = raw40343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40343 raw40343Labels permutation346 hz
    mixedMoment B raw40343step0 raw40343step0Labels = mixedMoment B raw40343step1 raw40343step1Labels := by
      have ha : raw40343step1 = (fun i j => raw40343step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40343step1 raw40343step0; decide +kernel
      have hl : raw40343step1Labels = raw40343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40343step0 raw40343step0Labels permutation32 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical40344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40344 raw40344Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw40344 raw40344Labels = mixedMoment B raw40344step0 raw40344step0Labels := by
      have hz : ∀ j, raw40344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40344step0 = (fun i j => raw40344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40344step0 raw40344; decide +kernel
      have hl : raw40344step0Labels = raw40344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40344 raw40344Labels permutation346 hz
    mixedMoment B raw40344step0 raw40344step0Labels = mixedMoment B raw40344step1 raw40344step1Labels := by
      have ha : raw40344step1 = (fun i j => raw40344step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40344step1 raw40344step0; decide +kernel
      have hl : raw40344step1Labels = raw40344step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40344step0 raw40344step0Labels permutation32 permutation3
    _ = mixedMoment B node3040 node3040Labels := by rfl

theorem canonical40345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40345 raw40345Labels = mixedMoment B node3044 node3044Labels := by
  calc
    mixedMoment B raw40345 raw40345Labels = mixedMoment B raw40345step0 raw40345step0Labels := by
      have hz : ∀ j, raw40345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40345step0 = (fun i j => raw40345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40345step0 raw40345; decide +kernel
      have hl : raw40345step0Labels = raw40345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40345 raw40345Labels permutation346 hz
    mixedMoment B raw40345step0 raw40345step0Labels = mixedMoment B raw40345step1 raw40345step1Labels := by
      have ha : raw40345step1 = (fun i j => raw40345step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40345step1 raw40345step0; decide +kernel
      have hl : raw40345step1Labels = raw40345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40345step0 raw40345step0Labels permutation32 permutation3
    _ = mixedMoment B node3044 node3044Labels := by rfl

theorem canonical40346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40346 raw40346Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw40346 raw40346Labels = mixedMoment B raw40346step0 raw40346step0Labels := by
      have hz : ∀ j, raw40346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40346step0 = (fun i j => raw40346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40346step0 raw40346; decide +kernel
      have hl : raw40346step0Labels = raw40346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40346 raw40346Labels permutation346 hz
    mixedMoment B raw40346step0 raw40346step0Labels = mixedMoment B raw40346step1 raw40346step1Labels := by
      have ha : raw40346step1 = (fun i j => raw40346step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40346step1 raw40346step0; decide +kernel
      have hl : raw40346step1Labels = raw40346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40346step0 raw40346step0Labels permutation32 permutation3
    _ = mixedMoment B node3045 node3045Labels := by rfl

theorem canonical40347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40347 raw40347Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw40347 raw40347Labels = mixedMoment B raw40347step0 raw40347step0Labels := by
      have hz : ∀ j, raw40347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40347step0 = (fun i j => raw40347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40347step0 raw40347; decide +kernel
      have hl : raw40347step0Labels = raw40347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40347 raw40347Labels permutation346 hz
    mixedMoment B raw40347step0 raw40347step0Labels = mixedMoment B raw40347step1 raw40347step1Labels := by
      have ha : raw40347step1 = (fun i j => raw40347step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40347step1 raw40347step0; decide +kernel
      have hl : raw40347step1Labels = raw40347step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40347step0 raw40347step0Labels permutation32 permutation3
    _ = mixedMoment B node3050 node3050Labels := by rfl

theorem canonical40348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40348 raw40348Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw40348 raw40348Labels = mixedMoment B raw40348step0 raw40348step0Labels := by
      have hz : ∀ j, raw40348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40348step0 = (fun i j => raw40348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40348step0 raw40348; decide +kernel
      have hl : raw40348step0Labels = raw40348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40348 raw40348Labels permutation346 hz
    mixedMoment B raw40348step0 raw40348step0Labels = mixedMoment B raw40348step1 raw40348step1Labels := by
      have ha : raw40348step1 = (fun i j => raw40348step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40348step1 raw40348step0; decide +kernel
      have hl : raw40348step1Labels = raw40348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40348step0 raw40348step0Labels permutation32 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical40349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40349 raw40349Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw40349 raw40349Labels = mixedMoment B raw40349step0 raw40349step0Labels := by
      have hz : ∀ j, raw40349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40349step0 = (fun i j => raw40349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40349step0 raw40349; decide +kernel
      have hl : raw40349step0Labels = raw40349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40349 raw40349Labels permutation346 hz
    mixedMoment B raw40349step0 raw40349step0Labels = mixedMoment B raw40349step1 raw40349step1Labels := by
      have ha : raw40349step1 = (fun i j => raw40349step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40349step1 raw40349step0; decide +kernel
      have hl : raw40349step1Labels = raw40349step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40349step0 raw40349step0Labels permutation32 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

theorem canonical40350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40350 raw40350Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw40350 raw40350Labels = mixedMoment B raw40350step0 raw40350step0Labels := by
      have ha : raw40350step0 = (fun i j => raw40350 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40350step0 raw40350; decide +kernel
      have hl : raw40350step0Labels = raw40350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40350 raw40350Labels permutation152 permutation3
    _ = mixedMoment B node3029 node3029Labels := by rfl

theorem canonical40351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40351 raw40351Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw40351 raw40351Labels = mixedMoment B raw40351step0 raw40351step0Labels := by
      have ha : raw40351step0 = (fun i j => raw40351 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40351step0 raw40351; decide +kernel
      have hl : raw40351step0Labels = raw40351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40351 raw40351Labels permutation152 permutation3
    _ = mixedMoment B node3030 node3030Labels := by rfl

theorem canonical40352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40352 raw40352Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw40352 raw40352Labels = mixedMoment B raw40352step0 raw40352step0Labels := by
      have ha : raw40352step0 = (fun i j => raw40352 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40352step0 raw40352; decide +kernel
      have hl : raw40352step0Labels = raw40352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40352 raw40352Labels permutation152 permutation3
    _ = mixedMoment B node3036 node3036Labels := by rfl

theorem canonical40353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40353 raw40353Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw40353 raw40353Labels = mixedMoment B raw40353step0 raw40353step0Labels := by
      have ha : raw40353step0 = (fun i j => raw40353 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40353step0 raw40353; decide +kernel
      have hl : raw40353step0Labels = raw40353Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40353 raw40353Labels permutation152 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical40354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40354 raw40354Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw40354 raw40354Labels = mixedMoment B raw40354step0 raw40354step0Labels := by
      have ha : raw40354step0 = (fun i j => raw40354 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40354step0 raw40354; decide +kernel
      have hl : raw40354step0Labels = raw40354Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40354 raw40354Labels permutation152 permutation3
    _ = mixedMoment B node3043 node3043Labels := by rfl

theorem canonical40355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40355 raw40355Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw40355 raw40355Labels = mixedMoment B raw40355step0 raw40355step0Labels := by
      have hz : ∀ j, raw40355 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40355step0 = (fun i j => raw40355 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40355step0 raw40355; decide +kernel
      have hl : raw40355step0Labels = raw40355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40355 raw40355Labels permutation520 hz
    mixedMoment B raw40355step0 raw40355step0Labels = mixedMoment B raw40355step1 raw40355step1Labels := by
      have hz : ∀ j, raw40355step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40355step1 = (fun i j => raw40355step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40355step1 raw40355step0; decide +kernel
      have hl : raw40355step1Labels = raw40355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40355step0 raw40355step0Labels permutation104 hz
    mixedMoment B raw40355step1 raw40355step1Labels = mixedMoment B raw40355step2 raw40355step2Labels := by
      have ha : raw40355step2 = (fun i j => raw40355step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40355step2 raw40355step1; decide +kernel
      have hl : raw40355step2Labels = raw40355step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40355step1 raw40355step1Labels permutation29 permutation3
    mixedMoment B raw40355step2 raw40355step2Labels = mixedMoment B raw40355step3 raw40355step3Labels := by
      have ha : raw40355step3 = -raw40355step2 := by apply Matrix.ext; change ∀ i j, raw40355step3 i j = -(raw40355step2 i j); unfold raw40355step3 raw40355step2; decide +kernel
      have hl : raw40355step3Labels = raw40355step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical40356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40356 raw40356Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw40356 raw40356Labels = mixedMoment B raw40356step0 raw40356step0Labels := by
      have hz : ∀ j, raw40356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40356step0 = (fun i j => raw40356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40356step0 raw40356; decide +kernel
      have hl : raw40356step0Labels = raw40356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40356 raw40356Labels permutation434 hz
    mixedMoment B raw40356step0 raw40356step0Labels = mixedMoment B raw40356step1 raw40356step1Labels := by
      have ha : raw40356step1 = (fun i j => raw40356step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40356step1 raw40356step0; decide +kernel
      have hl : raw40356step1Labels = raw40356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40356step0 raw40356step0Labels permutation32 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical40357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40357 raw40357Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw40357 raw40357Labels = mixedMoment B raw40357step0 raw40357step0Labels := by
      have hz : ∀ j, raw40357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40357step0 = (fun i j => raw40357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40357step0 raw40357; decide +kernel
      have hl : raw40357step0Labels = raw40357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40357 raw40357Labels permutation434 hz
    mixedMoment B raw40357step0 raw40357step0Labels = mixedMoment B raw40357step1 raw40357step1Labels := by
      have ha : raw40357step1 = (fun i j => raw40357step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40357step1 raw40357step0; decide +kernel
      have hl : raw40357step1Labels = raw40357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40357step0 raw40357step0Labels permutation32 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

theorem canonical40358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40358 raw40358Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw40358 raw40358Labels = mixedMoment B raw40358step0 raw40358step0Labels := by
      have hz : ∀ j, raw40358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40358step0 = (fun i j => raw40358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40358step0 raw40358; decide +kernel
      have hl : raw40358step0Labels = raw40358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40358 raw40358Labels permutation434 hz
    mixedMoment B raw40358step0 raw40358step0Labels = mixedMoment B raw40358step1 raw40358step1Labels := by
      have ha : raw40358step1 = (fun i j => raw40358step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40358step1 raw40358step0; decide +kernel
      have hl : raw40358step1Labels = raw40358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40358step0 raw40358step0Labels permutation32 permutation3
    _ = mixedMoment B node3079 node3079Labels := by rfl

theorem canonical40359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40359 raw40359Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw40359 raw40359Labels = mixedMoment B raw40359step0 raw40359step0Labels := by
      have ha : raw40359step0 = (fun i j => raw40359 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40359step0 raw40359; decide +kernel
      have hl : raw40359step0Labels = raw40359Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40359 raw40359Labels permutation152 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

theorem canonical40360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40360 raw40360Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw40360 raw40360Labels = mixedMoment B raw40360step0 raw40360step0Labels := by
      have ha : raw40360step0 = (fun i j => raw40360 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40360step0 raw40360; decide +kernel
      have hl : raw40360step0Labels = raw40360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40360 raw40360Labels permutation152 permutation3
    _ = mixedMoment B node3066 node3066Labels := by rfl

theorem canonical40361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40361 raw40361Labels = mixedMoment B node3068 node3068Labels := by
  calc
    mixedMoment B raw40361 raw40361Labels = mixedMoment B raw40361step0 raw40361step0Labels := by
      have ha : raw40361step0 = (fun i j => raw40361 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40361step0 raw40361; decide +kernel
      have hl : raw40361step0Labels = raw40361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40361 raw40361Labels permutation152 permutation3
    _ = mixedMoment B node3068 node3068Labels := by rfl

theorem canonical40362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40362 raw40362Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw40362 raw40362Labels = mixedMoment B raw40362step0 raw40362step0Labels := by
      have ha : raw40362step0 = (fun i j => raw40362 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40362step0 raw40362; decide +kernel
      have hl : raw40362step0Labels = raw40362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40362 raw40362Labels permutation152 permutation3
    _ = mixedMoment B node3069 node3069Labels := by rfl

theorem canonical40363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40363 raw40363Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw40363 raw40363Labels = mixedMoment B raw40363step0 raw40363step0Labels := by
      have ha : raw40363step0 = (fun i j => raw40363 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40363step0 raw40363; decide +kernel
      have hl : raw40363step0Labels = raw40363Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40363 raw40363Labels permutation152 permutation3
    _ = mixedMoment B node3073 node3073Labels := by rfl

theorem canonical40364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40364 raw40364Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw40364 raw40364Labels = mixedMoment B raw40364step0 raw40364step0Labels := by
      have ha : raw40364step0 = (fun i j => raw40364 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40364step0 raw40364; decide +kernel
      have hl : raw40364step0Labels = raw40364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40364 raw40364Labels permutation152 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical40365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40365 raw40365Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw40365 raw40365Labels = mixedMoment B raw40365step0 raw40365step0Labels := by
      have hz : ∀ j, raw40365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40365step0 = (fun i j => raw40365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40365step0 raw40365; decide +kernel
      have hl : raw40365step0Labels = raw40365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40365 raw40365Labels permutation434 hz
    mixedMoment B raw40365step0 raw40365step0Labels = mixedMoment B raw40365step1 raw40365step1Labels := by
      have hz : ∀ j, raw40365step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40365step1 = (fun i j => raw40365step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40365step1 raw40365step0; decide +kernel
      have hl : raw40365step1Labels = raw40365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40365step0 raw40365step0Labels permutation80 hz
    mixedMoment B raw40365step1 raw40365step1Labels = mixedMoment B raw40365step2 raw40365step2Labels := by
      have ha : raw40365step2 = (fun i j => raw40365step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40365step2 raw40365step1; decide +kernel
      have hl : raw40365step2Labels = raw40365step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40365step1 raw40365step1Labels permutation8 permutation3
    _ = mixedMoment B node3098 node3098Labels := by rfl

theorem canonical40366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40366 raw40366Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw40366 raw40366Labels = mixedMoment B raw40366step0 raw40366step0Labels := by
      have hz : ∀ j, raw40366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40366step0 = (fun i j => raw40366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40366step0 raw40366; decide +kernel
      have hl : raw40366step0Labels = raw40366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40366 raw40366Labels permutation434 hz
    mixedMoment B raw40366step0 raw40366step0Labels = mixedMoment B raw40366step1 raw40366step1Labels := by
      have hz : ∀ j, raw40366step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40366step1 = (fun i j => raw40366step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40366step1 raw40366step0; decide +kernel
      have hl : raw40366step1Labels = raw40366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40366step0 raw40366step0Labels permutation80 hz
    mixedMoment B raw40366step1 raw40366step1Labels = mixedMoment B raw40366step2 raw40366step2Labels := by
      have ha : raw40366step2 = (fun i j => raw40366step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40366step2 raw40366step1; decide +kernel
      have hl : raw40366step2Labels = raw40366step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40366step1 raw40366step1Labels permutation28 permutation6
    _ = mixedMoment B node2967 node2967Labels := by rfl

theorem canonical40367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40367 raw40367Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw40367 raw40367Labels = mixedMoment B raw40367step0 raw40367step0Labels := by
      have hz : ∀ j, raw40367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40367step0 = (fun i j => raw40367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40367step0 raw40367; decide +kernel
      have hl : raw40367step0Labels = raw40367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40367 raw40367Labels permutation346 hz
    mixedMoment B raw40367step0 raw40367step0Labels = mixedMoment B raw40367step1 raw40367step1Labels := by
      have ha : raw40367step1 = (fun i j => raw40367step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40367step1 raw40367step0; decide +kernel
      have hl : raw40367step1Labels = raw40367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40367step0 raw40367step0Labels permutation32 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment896 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 896) =
      Integer.Sparse.eval keyMomentRow896 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 896).leftCharge (GramAssembly.key 896).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 896).leftCharge (GramAssembly.key 896).rightCharge = raw40337 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40337Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40337 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 896).leftCharge (GramAssembly.key 896).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow896, Integer.Sparse.eval]

theorem keyMoment897 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 897) =
      Integer.Sparse.eval keyMomentRow897 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 897).leftCharge (GramAssembly.key 897).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 897).leftCharge (GramAssembly.key 897).rightCharge = raw40338 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40338Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40338 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 897).leftCharge (GramAssembly.key 897).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow897, Integer.Sparse.eval]

theorem keyMoment898 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 898) =
      Integer.Sparse.eval keyMomentRow898 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 898).leftCharge (GramAssembly.key 898).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3055) := by
    have ha : gramCharges (GramAssembly.key 898).leftCharge (GramAssembly.key 898).rightCharge = raw40339 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40339Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40339 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 898).leftCharge (GramAssembly.key 898).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow898, Integer.Sparse.eval]

theorem keyMoment899 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 899) =
      Integer.Sparse.eval keyMomentRow899 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 899).leftCharge (GramAssembly.key 899).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3056) := by
    have ha : gramCharges (GramAssembly.key 899).leftCharge (GramAssembly.key 899).rightCharge = raw40340 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40340Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40340 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 899).leftCharge (GramAssembly.key 899).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow899, Integer.Sparse.eval]

theorem keyMoment900 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 900) =
      Integer.Sparse.eval keyMomentRow900 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 900).leftCharge (GramAssembly.key 900).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3031) := by
    have ha : gramCharges (GramAssembly.key 900).leftCharge (GramAssembly.key 900).rightCharge = raw40341 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40341Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40341 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 900).leftCharge (GramAssembly.key 900).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow900, Integer.Sparse.eval]

theorem keyMoment901 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 901) =
      Integer.Sparse.eval keyMomentRow901 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 901).leftCharge (GramAssembly.key 901).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3038) := by
    have ha : gramCharges (GramAssembly.key 901).leftCharge (GramAssembly.key 901).rightCharge = raw40342 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40342Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40342 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 901).leftCharge (GramAssembly.key 901).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow901, Integer.Sparse.eval]

theorem keyMoment902 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 902) =
      Integer.Sparse.eval keyMomentRow902 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 902).leftCharge (GramAssembly.key 902).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 902).leftCharge (GramAssembly.key 902).rightCharge = raw40343 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40343Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40343 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 902).leftCharge (GramAssembly.key 902).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow902, Integer.Sparse.eval]

theorem keyMoment903 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 903) =
      Integer.Sparse.eval keyMomentRow903 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 903).leftCharge (GramAssembly.key 903).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3040) := by
    have ha : gramCharges (GramAssembly.key 903).leftCharge (GramAssembly.key 903).rightCharge = raw40344 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40344Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40344 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 903).leftCharge (GramAssembly.key 903).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow903, Integer.Sparse.eval]

theorem keyMoment904 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 904) =
      Integer.Sparse.eval keyMomentRow904 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 904).leftCharge (GramAssembly.key 904).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3044) := by
    have ha : gramCharges (GramAssembly.key 904).leftCharge (GramAssembly.key 904).rightCharge = raw40345 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40345Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40345 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 904).leftCharge (GramAssembly.key 904).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow904, Integer.Sparse.eval]

theorem keyMoment905 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 905) =
      Integer.Sparse.eval keyMomentRow905 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 905).leftCharge (GramAssembly.key 905).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3045) := by
    have ha : gramCharges (GramAssembly.key 905).leftCharge (GramAssembly.key 905).rightCharge = raw40346 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40346Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40346 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 905).leftCharge (GramAssembly.key 905).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow905, Integer.Sparse.eval]

theorem keyMoment906 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 906) =
      Integer.Sparse.eval keyMomentRow906 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 906).leftCharge (GramAssembly.key 906).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3050) := by
    have ha : gramCharges (GramAssembly.key 906).leftCharge (GramAssembly.key 906).rightCharge = raw40347 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40347Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40347 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 906).leftCharge (GramAssembly.key 906).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow906, Integer.Sparse.eval]

theorem keyMoment907 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 907) =
      Integer.Sparse.eval keyMomentRow907 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 907).leftCharge (GramAssembly.key 907).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 907).leftCharge (GramAssembly.key 907).rightCharge = raw40348 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40348Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40348 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 907).leftCharge (GramAssembly.key 907).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow907, Integer.Sparse.eval]

theorem keyMoment908 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 908) =
      Integer.Sparse.eval keyMomentRow908 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 908).leftCharge (GramAssembly.key 908).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3053) := by
    have ha : gramCharges (GramAssembly.key 908).leftCharge (GramAssembly.key 908).rightCharge = raw40349 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40349Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40349 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 908).leftCharge (GramAssembly.key 908).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow908, Integer.Sparse.eval]

theorem keyMoment909 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 909) =
      Integer.Sparse.eval keyMomentRow909 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 909).leftCharge (GramAssembly.key 909).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3029) := by
    have ha : gramCharges (GramAssembly.key 909).leftCharge (GramAssembly.key 909).rightCharge = raw40350 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40350Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40350 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 909).leftCharge (GramAssembly.key 909).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow909, Integer.Sparse.eval]

theorem keyMoment910 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 910) =
      Integer.Sparse.eval keyMomentRow910 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 910).leftCharge (GramAssembly.key 910).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3030) := by
    have ha : gramCharges (GramAssembly.key 910).leftCharge (GramAssembly.key 910).rightCharge = raw40351 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40351Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40351 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 910).leftCharge (GramAssembly.key 910).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow910, Integer.Sparse.eval]

theorem keyMoment911 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 911) =
      Integer.Sparse.eval keyMomentRow911 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 911).leftCharge (GramAssembly.key 911).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3036) := by
    have ha : gramCharges (GramAssembly.key 911).leftCharge (GramAssembly.key 911).rightCharge = raw40352 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40352Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40352 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 911).leftCharge (GramAssembly.key 911).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow911, Integer.Sparse.eval]

theorem keyMoment912 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 912) =
      Integer.Sparse.eval keyMomentRow912 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 912).leftCharge (GramAssembly.key 912).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 912).leftCharge (GramAssembly.key 912).rightCharge = raw40353 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40353Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40353 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 912).leftCharge (GramAssembly.key 912).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow912, Integer.Sparse.eval]

theorem keyMoment913 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 913) =
      Integer.Sparse.eval keyMomentRow913 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 913).leftCharge (GramAssembly.key 913).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3043) := by
    have ha : gramCharges (GramAssembly.key 913).leftCharge (GramAssembly.key 913).rightCharge = raw40354 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40354Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40354 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 913).leftCharge (GramAssembly.key 913).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow913, Integer.Sparse.eval]

theorem keyMoment914 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 914) =
      Integer.Sparse.eval keyMomentRow914 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 914).leftCharge (GramAssembly.key 914).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 914).leftCharge (GramAssembly.key 914).rightCharge = raw40355 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40355Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40355 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 914).leftCharge (GramAssembly.key 914).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow914, Integer.Sparse.eval]

theorem keyMoment915 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 915) =
      Integer.Sparse.eval keyMomentRow915 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 915).leftCharge (GramAssembly.key 915).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 915).leftCharge (GramAssembly.key 915).rightCharge = raw40356 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40356Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40356 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 915).leftCharge (GramAssembly.key 915).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow915, Integer.Sparse.eval]

theorem keyMoment916 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 916) =
      Integer.Sparse.eval keyMomentRow916 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 916).leftCharge (GramAssembly.key 916).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 916).leftCharge (GramAssembly.key 916).rightCharge = raw13433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw13433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical13433 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 916).leftCharge (GramAssembly.key 916).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow916, Integer.Sparse.eval]

theorem keyMoment917 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 917) =
      Integer.Sparse.eval keyMomentRow917 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 917).leftCharge (GramAssembly.key 917).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3078) := by
    have ha : gramCharges (GramAssembly.key 917).leftCharge (GramAssembly.key 917).rightCharge = raw40357 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40357Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40357 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 917).leftCharge (GramAssembly.key 917).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow917, Integer.Sparse.eval]

theorem keyMoment918 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 918) =
      Integer.Sparse.eval keyMomentRow918 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 918).leftCharge (GramAssembly.key 918).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3079) := by
    have ha : gramCharges (GramAssembly.key 918).leftCharge (GramAssembly.key 918).rightCharge = raw40358 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40358Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40358 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 918).leftCharge (GramAssembly.key 918).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow918, Integer.Sparse.eval]

theorem keyMoment919 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 919) =
      Integer.Sparse.eval keyMomentRow919 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 919).leftCharge (GramAssembly.key 919).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3064) := by
    have ha : gramCharges (GramAssembly.key 919).leftCharge (GramAssembly.key 919).rightCharge = raw40359 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40359Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40359 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 919).leftCharge (GramAssembly.key 919).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow919, Integer.Sparse.eval]

theorem keyMoment920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 920) =
      Integer.Sparse.eval keyMomentRow920 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 920).leftCharge (GramAssembly.key 920).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3066) := by
    have ha : gramCharges (GramAssembly.key 920).leftCharge (GramAssembly.key 920).rightCharge = raw40360 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40360Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40360 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 920).leftCharge (GramAssembly.key 920).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow920, Integer.Sparse.eval]

theorem keyMoment921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 921) =
      Integer.Sparse.eval keyMomentRow921 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 921).leftCharge (GramAssembly.key 921).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3068) := by
    have ha : gramCharges (GramAssembly.key 921).leftCharge (GramAssembly.key 921).rightCharge = raw40361 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40361Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40361 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 921).leftCharge (GramAssembly.key 921).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow921, Integer.Sparse.eval]

theorem keyMoment922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 922) =
      Integer.Sparse.eval keyMomentRow922 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 922).leftCharge (GramAssembly.key 922).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3069) := by
    have ha : gramCharges (GramAssembly.key 922).leftCharge (GramAssembly.key 922).rightCharge = raw40362 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40362Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40362 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 922).leftCharge (GramAssembly.key 922).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow922, Integer.Sparse.eval]

theorem keyMoment923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 923) =
      Integer.Sparse.eval keyMomentRow923 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 923).leftCharge (GramAssembly.key 923).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3073) := by
    have ha : gramCharges (GramAssembly.key 923).leftCharge (GramAssembly.key 923).rightCharge = raw40363 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40363Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40363 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 923).leftCharge (GramAssembly.key 923).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow923, Integer.Sparse.eval]

theorem keyMoment924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 924) =
      Integer.Sparse.eval keyMomentRow924 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 924).leftCharge (GramAssembly.key 924).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 924).leftCharge (GramAssembly.key 924).rightCharge = raw40364 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40364Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40364 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 924).leftCharge (GramAssembly.key 924).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow924, Integer.Sparse.eval]

theorem keyMoment925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 925) =
      Integer.Sparse.eval keyMomentRow925 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 925).leftCharge (GramAssembly.key 925).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3098) := by
    have ha : gramCharges (GramAssembly.key 925).leftCharge (GramAssembly.key 925).rightCharge = raw40365 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40365Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40365 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 925).leftCharge (GramAssembly.key 925).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow925, Integer.Sparse.eval]

theorem keyMoment926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 926) =
      Integer.Sparse.eval keyMomentRow926 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 926).leftCharge (GramAssembly.key 926).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2967) := by
    have ha : gramCharges (GramAssembly.key 926).leftCharge (GramAssembly.key 926).rightCharge = raw40366 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40366Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40366 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 926).leftCharge (GramAssembly.key 926).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow926, Integer.Sparse.eval]

theorem keyMoment927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 927) =
      Integer.Sparse.eval keyMomentRow927 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 927).leftCharge (GramAssembly.key 927).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3086) := by
    have ha : gramCharges (GramAssembly.key 927).leftCharge (GramAssembly.key 927).rightCharge = raw40367 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40367Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40367 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 927).leftCharge (GramAssembly.key 927).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow927, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt896 : keyMomentRows (896 : Fin 2886) =
    keyMomentRow896 := by decide +kernel

theorem keyMomentRowsAt897 : keyMomentRows (897 : Fin 2886) =
    keyMomentRow897 := by decide +kernel

theorem keyMomentRowsAt898 : keyMomentRows (898 : Fin 2886) =
    keyMomentRow898 := by decide +kernel

theorem keyMomentRowsAt899 : keyMomentRows (899 : Fin 2886) =
    keyMomentRow899 := by decide +kernel

theorem keyMomentRowsAt900 : keyMomentRows (900 : Fin 2886) =
    keyMomentRow900 := by decide +kernel

theorem keyMomentRowsAt901 : keyMomentRows (901 : Fin 2886) =
    keyMomentRow901 := by decide +kernel

theorem keyMomentRowsAt902 : keyMomentRows (902 : Fin 2886) =
    keyMomentRow902 := by decide +kernel

theorem keyMomentRowsAt903 : keyMomentRows (903 : Fin 2886) =
    keyMomentRow903 := by decide +kernel

theorem keyMomentRowsAt904 : keyMomentRows (904 : Fin 2886) =
    keyMomentRow904 := by decide +kernel

theorem keyMomentRowsAt905 : keyMomentRows (905 : Fin 2886) =
    keyMomentRow905 := by decide +kernel

theorem keyMomentRowsAt906 : keyMomentRows (906 : Fin 2886) =
    keyMomentRow906 := by decide +kernel

theorem keyMomentRowsAt907 : keyMomentRows (907 : Fin 2886) =
    keyMomentRow907 := by decide +kernel

theorem keyMomentRowsAt908 : keyMomentRows (908 : Fin 2886) =
    keyMomentRow908 := by decide +kernel

theorem keyMomentRowsAt909 : keyMomentRows (909 : Fin 2886) =
    keyMomentRow909 := by decide +kernel

theorem keyMomentRowsAt910 : keyMomentRows (910 : Fin 2886) =
    keyMomentRow910 := by decide +kernel

theorem keyMomentRowsAt911 : keyMomentRows (911 : Fin 2886) =
    keyMomentRow911 := by decide +kernel

theorem keyMomentRowsAt912 : keyMomentRows (912 : Fin 2886) =
    keyMomentRow912 := by decide +kernel

theorem keyMomentRowsAt913 : keyMomentRows (913 : Fin 2886) =
    keyMomentRow913 := by decide +kernel

theorem keyMomentRowsAt914 : keyMomentRows (914 : Fin 2886) =
    keyMomentRow914 := by decide +kernel

theorem keyMomentRowsAt915 : keyMomentRows (915 : Fin 2886) =
    keyMomentRow915 := by decide +kernel

theorem keyMomentRowsAt916 : keyMomentRows (916 : Fin 2886) =
    keyMomentRow916 := by decide +kernel

theorem keyMomentRowsAt917 : keyMomentRows (917 : Fin 2886) =
    keyMomentRow917 := by decide +kernel

theorem keyMomentRowsAt918 : keyMomentRows (918 : Fin 2886) =
    keyMomentRow918 := by decide +kernel

theorem keyMomentRowsAt919 : keyMomentRows (919 : Fin 2886) =
    keyMomentRow919 := by decide +kernel

theorem keyMomentRowsAt920 : keyMomentRows (920 : Fin 2886) =
    keyMomentRow920 := by decide +kernel

theorem keyMomentRowsAt921 : keyMomentRows (921 : Fin 2886) =
    keyMomentRow921 := by decide +kernel

theorem keyMomentRowsAt922 : keyMomentRows (922 : Fin 2886) =
    keyMomentRow922 := by decide +kernel

theorem keyMomentRowsAt923 : keyMomentRows (923 : Fin 2886) =
    keyMomentRow923 := by decide +kernel

theorem keyMomentRowsAt924 : keyMomentRows (924 : Fin 2886) =
    keyMomentRow924 := by decide +kernel

theorem keyMomentRowsAt925 : keyMomentRows (925 : Fin 2886) =
    keyMomentRow925 := by decide +kernel

theorem keyMomentRowsAt926 : keyMomentRows (926 : Fin 2886) =
    keyMomentRow926 := by decide +kernel

theorem keyMomentRowsAt927 : keyMomentRows (927 : Fin 2886) =
    keyMomentRow927 := by decide +kernel

theorem keyMomentChunkSound28_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 28) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 896 ∨ k.val = 897 ∨ k.val = 898 ∨ k.val = 899 ∨ k.val = 900 ∨ k.val = 901 ∨ k.val = 902 ∨ k.val = 903 ∨ k.val = 904 ∨ k.val = 905 ∨ k.val = 906 ∨ k.val = 907 ∨ k.val = 908 ∨ k.val = 909 ∨ k.val = 910 ∨ k.val = 911 ∨ k.val = 912 ∨ k.val = 913 ∨ k.val = 914 ∨ k.val = 915 ∨ k.val = 916 ∨ k.val = 917 ∨ k.val = 918 ∨ k.val = 919 ∨ k.val = 920 ∨ k.val = 921 ∨ k.val = 922 ∨ k.val = 923 ∨ k.val = 924 ∨ k.val = 925 ∨ k.val = 926 ∨ k.val = 927 := by omega
  rcases heq with h896 | h897 | h898 | h899 | h900 | h901 | h902 | h903 | h904 | h905 | h906 | h907 | h908 | h909 | h910 | h911 | h912 | h913 | h914 | h915 | h916 | h917 | h918 | h919 | h920 | h921 | h922 | h923 | h924 | h925 | h926 | h927
  · have he : k = (896 : Fin 2886) := Fin.ext h896
    subst k
    rw [keyMomentRowsAt896]
    exact keyMoment896 B hB
  · have he : k = (897 : Fin 2886) := Fin.ext h897
    subst k
    rw [keyMomentRowsAt897]
    exact keyMoment897 B hB
  · have he : k = (898 : Fin 2886) := Fin.ext h898
    subst k
    rw [keyMomentRowsAt898]
    exact keyMoment898 B hB
  · have he : k = (899 : Fin 2886) := Fin.ext h899
    subst k
    rw [keyMomentRowsAt899]
    exact keyMoment899 B hB
  · have he : k = (900 : Fin 2886) := Fin.ext h900
    subst k
    rw [keyMomentRowsAt900]
    exact keyMoment900 B hB
  · have he : k = (901 : Fin 2886) := Fin.ext h901
    subst k
    rw [keyMomentRowsAt901]
    exact keyMoment901 B hB
  · have he : k = (902 : Fin 2886) := Fin.ext h902
    subst k
    rw [keyMomentRowsAt902]
    exact keyMoment902 B hB
  · have he : k = (903 : Fin 2886) := Fin.ext h903
    subst k
    rw [keyMomentRowsAt903]
    exact keyMoment903 B hB
  · have he : k = (904 : Fin 2886) := Fin.ext h904
    subst k
    rw [keyMomentRowsAt904]
    exact keyMoment904 B hB
  · have he : k = (905 : Fin 2886) := Fin.ext h905
    subst k
    rw [keyMomentRowsAt905]
    exact keyMoment905 B hB
  · have he : k = (906 : Fin 2886) := Fin.ext h906
    subst k
    rw [keyMomentRowsAt906]
    exact keyMoment906 B hB
  · have he : k = (907 : Fin 2886) := Fin.ext h907
    subst k
    rw [keyMomentRowsAt907]
    exact keyMoment907 B hB
  · have he : k = (908 : Fin 2886) := Fin.ext h908
    subst k
    rw [keyMomentRowsAt908]
    exact keyMoment908 B hB
  · have he : k = (909 : Fin 2886) := Fin.ext h909
    subst k
    rw [keyMomentRowsAt909]
    exact keyMoment909 B hB
  · have he : k = (910 : Fin 2886) := Fin.ext h910
    subst k
    rw [keyMomentRowsAt910]
    exact keyMoment910 B hB
  · have he : k = (911 : Fin 2886) := Fin.ext h911
    subst k
    rw [keyMomentRowsAt911]
    exact keyMoment911 B hB
  · have he : k = (912 : Fin 2886) := Fin.ext h912
    subst k
    rw [keyMomentRowsAt912]
    exact keyMoment912 B hB
  · have he : k = (913 : Fin 2886) := Fin.ext h913
    subst k
    rw [keyMomentRowsAt913]
    exact keyMoment913 B hB
  · have he : k = (914 : Fin 2886) := Fin.ext h914
    subst k
    rw [keyMomentRowsAt914]
    exact keyMoment914 B hB
  · have he : k = (915 : Fin 2886) := Fin.ext h915
    subst k
    rw [keyMomentRowsAt915]
    exact keyMoment915 B hB
  · have he : k = (916 : Fin 2886) := Fin.ext h916
    subst k
    rw [keyMomentRowsAt916]
    exact keyMoment916 B hB
  · have he : k = (917 : Fin 2886) := Fin.ext h917
    subst k
    rw [keyMomentRowsAt917]
    exact keyMoment917 B hB
  · have he : k = (918 : Fin 2886) := Fin.ext h918
    subst k
    rw [keyMomentRowsAt918]
    exact keyMoment918 B hB
  · have he : k = (919 : Fin 2886) := Fin.ext h919
    subst k
    rw [keyMomentRowsAt919]
    exact keyMoment919 B hB
  · have he : k = (920 : Fin 2886) := Fin.ext h920
    subst k
    rw [keyMomentRowsAt920]
    exact keyMoment920 B hB
  · have he : k = (921 : Fin 2886) := Fin.ext h921
    subst k
    rw [keyMomentRowsAt921]
    exact keyMoment921 B hB
  · have he : k = (922 : Fin 2886) := Fin.ext h922
    subst k
    rw [keyMomentRowsAt922]
    exact keyMoment922 B hB
  · have he : k = (923 : Fin 2886) := Fin.ext h923
    subst k
    rw [keyMomentRowsAt923]
    exact keyMoment923 B hB
  · have he : k = (924 : Fin 2886) := Fin.ext h924
    subst k
    rw [keyMomentRowsAt924]
    exact keyMoment924 B hB
  · have he : k = (925 : Fin 2886) := Fin.ext h925
    subst k
    rw [keyMomentRowsAt925]
    exact keyMoment925 B hB
  · have he : k = (926 : Fin 2886) := Fin.ext h926
    subst k
    rw [keyMomentRowsAt926]
    exact keyMoment926 B hB
  · have he : k = (927 : Fin 2886) := Fin.ext h927
    subst k
    rw [keyMomentRowsAt927]
    exact keyMoment927 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound28_e_oai
