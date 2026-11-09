-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:55:39.389739+00:00
-- url     : https://prove2.me/submissions/d938cd62-7545-45c5-87da-a4265f5d570e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E091
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E117
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical101
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical12968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12968 raw12968Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw12968 raw12968Labels = mixedMoment B raw12968step0 raw12968step0Labels := by
      have ha : raw12968step0 = (fun i j => raw12968 (permutation373 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12968step0 raw12968; decide +kernel
      have hl : raw12968step0Labels = raw12968Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12968 raw12968Labels permutation373 permutation6
    _ = mixedMoment B node3899 node3899Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical121
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15508 raw15508Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw15508 raw15508Labels = mixedMoment B raw15508step0 raw15508step0Labels := by
      have ha : raw15508step0 = (fun i j => raw15508 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15508step0 raw15508; decide +kernel
      have hl : raw15508step0Labels = raw15508Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15508 raw15508Labels permutation682 permutation3
    mixedMoment B raw15508step0 raw15508step0Labels = mixedMoment B raw15508step1 raw15508step1Labels := by
      have ha : raw15508step1 = -raw15508step0 := by apply Matrix.ext; change ∀ i j, raw15508step1 i j = -(raw15508step0 i j); unfold raw15508step1 raw15508step0; decide +kernel
      have hl : raw15508step1Labels = raw15508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2710 node2710Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical123
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical15791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15791 raw15791Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw15791 raw15791Labels = mixedMoment B raw15791step0 raw15791step0Labels := by
      have hz : ∀ j, raw15791 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15791step0 = (fun i j => raw15791 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15791step0 raw15791; decide +kernel
      have hl : raw15791step0Labels = raw15791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15791 raw15791Labels permutation520 hz
    mixedMoment B raw15791step0 raw15791step0Labels = mixedMoment B raw15791step1 raw15791step1Labels := by
      have ha : raw15791step1 = (fun i j => raw15791step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15791step1 raw15791step0; decide +kernel
      have hl : raw15791step1Labels = raw15791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15791step0 raw15791step0Labels permutation145 permutation3
    mixedMoment B raw15791step1 raw15791step1Labels = mixedMoment B raw15791step2 raw15791step2Labels := by
      have ha : raw15791step2 = -raw15791step1 := by apply Matrix.ext; change ∀ i j, raw15791step2 i j = -(raw15791step1 i j); unfold raw15791step2 raw15791step1; decide +kernel
      have hl : raw15791step2Labels = raw15791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2245 node2245Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40830 raw40830Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw40830 raw40830Labels = mixedMoment B raw40830step0 raw40830step0Labels := by
      have ha : raw40830step0 = (fun i j => raw40830 (permutation423 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40830step0 raw40830; decide +kernel
      have hl : raw40830step0Labels = raw40830Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40830 raw40830Labels permutation423 permutation6
    _ = mixedMoment B node3872 node3872Labels := by rfl

theorem canonical40831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40831 raw40831Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw40831 raw40831Labels = mixedMoment B raw40831step0 raw40831step0Labels := by
      have ha : raw40831step0 = (fun i j => raw40831 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40831step0 raw40831; decide +kernel
      have hl : raw40831step0Labels = raw40831Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40831 raw40831Labels permutation421 permutation6
    _ = mixedMoment B node3722 node3722Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical319
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40832 raw40832Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw40832 raw40832Labels = mixedMoment B raw40832step0 raw40832step0Labels := by
      have ha : raw40832step0 = (fun i j => raw40832 (permutation439 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40832step0 raw40832; decide +kernel
      have hl : raw40832step0Labels = raw40832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40832 raw40832Labels permutation439 permutation6
    mixedMoment B raw40832step0 raw40832step0Labels = mixedMoment B raw40832step1 raw40832step1Labels := by
      have ha : raw40832step1 = -raw40832step0 := by apply Matrix.ext; change ∀ i j, raw40832step1 i j = -(raw40832step0 i j); unfold raw40832step1 raw40832step0; decide +kernel
      have hl : raw40832step1Labels = raw40832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

theorem canonical40833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40833 raw40833Labels = mixedMoment B node3715 node3715Labels := by
  calc
    mixedMoment B raw40833 raw40833Labels = mixedMoment B raw40833step0 raw40833step0Labels := by
      have ha : raw40833step0 = (fun i j => raw40833 (permutation422 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40833step0 raw40833; decide +kernel
      have hl : raw40833step0Labels = raw40833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40833 raw40833Labels permutation422 permutation6
    _ = mixedMoment B node3715 node3715Labels := by rfl

theorem canonical40834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40834 raw40834Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw40834 raw40834Labels = mixedMoment B raw40834step0 raw40834step0Labels := by
      have ha : raw40834step0 = (fun i j => raw40834 (permutation387 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40834step0 raw40834; decide +kernel
      have hl : raw40834step0Labels = raw40834Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40834 raw40834Labels permutation387 permutation6
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical40835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40835 raw40835Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw40835 raw40835Labels = mixedMoment B raw40835step0 raw40835step0Labels := by
      have ha : raw40835step0 = (fun i j => raw40835 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40835step0 raw40835; decide +kernel
      have hl : raw40835step0Labels = raw40835Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40835 raw40835Labels permutation682 permutation3
    mixedMoment B raw40835step0 raw40835step0Labels = mixedMoment B raw40835step1 raw40835step1Labels := by
      have ha : raw40835step1 = -raw40835step0 := by apply Matrix.ext; change ∀ i j, raw40835step1 i j = -(raw40835step0 i j); unfold raw40835step1 raw40835step0; decide +kernel
      have hl : raw40835step1Labels = raw40835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3030 node3030Labels := by rfl

theorem canonical40836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40836 raw40836Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw40836 raw40836Labels = mixedMoment B raw40836step0 raw40836step0Labels := by
      have ha : raw40836step0 = (fun i j => raw40836 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40836step0 raw40836; decide +kernel
      have hl : raw40836step0Labels = raw40836Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40836 raw40836Labels permutation520 permutation6
    mixedMoment B raw40836step0 raw40836step0Labels = mixedMoment B raw40836step1 raw40836step1Labels := by
      have ha : raw40836step1 = -raw40836step0 := by apply Matrix.ext; change ∀ i j, raw40836step1 i j = -(raw40836step0 i j); unfold raw40836step1 raw40836step0; decide +kernel
      have hl : raw40836step1Labels = raw40836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

theorem canonical40837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40837 raw40837Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw40837 raw40837Labels = mixedMoment B raw40837step0 raw40837step0Labels := by
      have hz : ∀ j, raw40837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40837step0 = (fun i j => raw40837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40837step0 raw40837; decide +kernel
      have hl : raw40837step0Labels = raw40837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40837 raw40837Labels permutation434 hz
    mixedMoment B raw40837step0 raw40837step0Labels = mixedMoment B raw40837step1 raw40837step1Labels := by
      have ha : raw40837step1 = (fun i j => raw40837step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40837step1 raw40837step0; decide +kernel
      have hl : raw40837step1Labels = raw40837step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40837step0 raw40837step0Labels permutation142 permutation6
    _ = mixedMoment B node2930 node2930Labels := by rfl

theorem canonical40838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40838 raw40838Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw40838 raw40838Labels = mixedMoment B raw40838step0 raw40838step0Labels := by
      have ha : raw40838step0 = (fun i j => raw40838 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40838step0 raw40838; decide +kernel
      have hl : raw40838step0Labels = raw40838Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40838 raw40838Labels permutation632 permutation6
    _ = mixedMoment B node2928 node2928Labels := by rfl

theorem canonical40839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40839 raw40839Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw40839 raw40839Labels = mixedMoment B raw40839step0 raw40839step0Labels := by
      have ha : raw40839step0 = (fun i j => raw40839 (permutation633 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40839step0 raw40839; decide +kernel
      have hl : raw40839step0Labels = raw40839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40839 raw40839Labels permutation633 permutation6
    _ = mixedMoment B node2916 node2916Labels := by rfl

theorem canonical40840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40840 raw40840Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw40840 raw40840Labels = mixedMoment B raw40840step0 raw40840step0Labels := by
      have hz : ∀ j, raw40840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40840step0 = (fun i j => raw40840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40840step0 raw40840; decide +kernel
      have hl : raw40840step0Labels = raw40840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40840 raw40840Labels permutation434 hz
    mixedMoment B raw40840step0 raw40840step0Labels = mixedMoment B raw40840step1 raw40840step1Labels := by
      have hz : ∀ j, raw40840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40840step1 = (fun i j => raw40840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40840step1 raw40840step0; decide +kernel
      have hl : raw40840step1Labels = raw40840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40840step0 raw40840step0Labels permutation80 hz
    mixedMoment B raw40840step1 raw40840step1Labels = mixedMoment B raw40840step2 raw40840step2Labels := by
      have ha : raw40840step2 = (fun i j => raw40840step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40840step2 raw40840step1; decide +kernel
      have hl : raw40840step2Labels = raw40840step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40840step1 raw40840step1Labels permutation28 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

theorem canonical40841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40841 raw40841Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40841 raw40841Labels = mixedMoment B raw40841step0 raw40841step0Labels := by
      have hz : ∀ j, raw40841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40841step0 = (fun i j => raw40841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40841step0 raw40841; decide +kernel
      have hl : raw40841step0Labels = raw40841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40841 raw40841Labels permutation346 hz
    mixedMoment B raw40841step0 raw40841step0Labels = mixedMoment B raw40841step1 raw40841step1Labels := by
      have ha : raw40841step1 = (fun i j => raw40841step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40841step1 raw40841step0; decide +kernel
      have hl : raw40841step1Labels = raw40841step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40841step0 raw40841step0Labels permutation115 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical40842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40842 raw40842Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw40842 raw40842Labels = mixedMoment B raw40842step0 raw40842step0Labels := by
      have hz : ∀ j, raw40842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40842step0 = (fun i j => raw40842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40842step0 raw40842; decide +kernel
      have hl : raw40842step0Labels = raw40842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40842 raw40842Labels permutation346 hz
    mixedMoment B raw40842step0 raw40842step0Labels = mixedMoment B raw40842step1 raw40842step1Labels := by
      have ha : raw40842step1 = (fun i j => raw40842step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40842step1 raw40842step0; decide +kernel
      have hl : raw40842step1Labels = raw40842step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40842step0 raw40842step0Labels permutation137 permutation6
    _ = mixedMoment B node1241 node1241Labels := by rfl

theorem canonical40843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40843 raw40843Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw40843 raw40843Labels = mixedMoment B raw40843step0 raw40843step0Labels := by
      have hz : ∀ j, raw40843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40843step0 = (fun i j => raw40843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40843step0 raw40843; decide +kernel
      have hl : raw40843step0Labels = raw40843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40843 raw40843Labels permutation346 hz
    mixedMoment B raw40843step0 raw40843step0Labels = mixedMoment B raw40843step1 raw40843step1Labels := by
      have ha : raw40843step1 = (fun i j => raw40843step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40843step1 raw40843step0; decide +kernel
      have hl : raw40843step1Labels = raw40843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40843step0 raw40843step0Labels permutation124 permutation6
    _ = mixedMoment B node2620 node2620Labels := by rfl

theorem canonical40844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40844 raw40844Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw40844 raw40844Labels = mixedMoment B raw40844step0 raw40844step0Labels := by
      have hz : ∀ j, raw40844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40844step0 = (fun i j => raw40844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40844step0 raw40844; decide +kernel
      have hl : raw40844step0Labels = raw40844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40844 raw40844Labels permutation346 hz
    mixedMoment B raw40844step0 raw40844step0Labels = mixedMoment B raw40844step1 raw40844step1Labels := by
      have ha : raw40844step1 = (fun i j => raw40844step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40844step1 raw40844step0; decide +kernel
      have hl : raw40844step1Labels = raw40844step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40844step0 raw40844step0Labels permutation138 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

theorem canonical40845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40845 raw40845Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw40845 raw40845Labels = mixedMoment B raw40845step0 raw40845step0Labels := by
      have ha : raw40845step0 = (fun i j => raw40845 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40845step0 raw40845; decide +kernel
      have hl : raw40845step0Labels = raw40845Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40845 raw40845Labels permutation577 permutation6
    _ = mixedMoment B node2617 node2617Labels := by rfl

theorem canonical40846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40846 raw40846Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw40846 raw40846Labels = mixedMoment B raw40846step0 raw40846step0Labels := by
      have ha : raw40846step0 = (fun i j => raw40846 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40846step0 raw40846; decide +kernel
      have hl : raw40846step0Labels = raw40846Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40846 raw40846Labels permutation620 permutation6
    _ = mixedMoment B node1216 node1216Labels := by rfl

theorem canonical40847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40847 raw40847Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw40847 raw40847Labels = mixedMoment B raw40847step0 raw40847step0Labels := by
      have ha : raw40847step0 = (fun i j => raw40847 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40847step0 raw40847; decide +kernel
      have hl : raw40847step0Labels = raw40847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40847 raw40847Labels permutation492 permutation6
    _ = mixedMoment B node2557 node2557Labels := by rfl

theorem canonical40848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40848 raw40848Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw40848 raw40848Labels = mixedMoment B raw40848step0 raw40848step0Labels := by
      have ha : raw40848step0 = (fun i j => raw40848 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40848step0 raw40848; decide +kernel
      have hl : raw40848step0Labels = raw40848Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40848 raw40848Labels permutation463 permutation6
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical40849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40849 raw40849Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw40849 raw40849Labels = mixedMoment B raw40849step0 raw40849step0Labels := by
      have ha : raw40849step0 = (fun i j => raw40849 (permutation493 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40849step0 raw40849; decide +kernel
      have hl : raw40849step0Labels = raw40849Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40849 raw40849Labels permutation493 permutation6
    _ = mixedMoment B node2545 node2545Labels := by rfl

theorem canonical40850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40850 raw40850Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw40850 raw40850Labels = mixedMoment B raw40850step0 raw40850step0Labels := by
      have hz : ∀ j, raw40850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40850step0 = (fun i j => raw40850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40850step0 raw40850; decide +kernel
      have hl : raw40850step0Labels = raw40850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40850 raw40850Labels permutation520 hz
    mixedMoment B raw40850step0 raw40850step0Labels = mixedMoment B raw40850step1 raw40850step1Labels := by
      have hz : ∀ j, raw40850step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40850step1 = (fun i j => raw40850step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40850step1 raw40850step0; decide +kernel
      have hl : raw40850step1Labels = raw40850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40850step0 raw40850step0Labels permutation104 hz
    mixedMoment B raw40850step1 raw40850step1Labels = mixedMoment B raw40850step2 raw40850step2Labels := by
      have ha : raw40850step2 = (fun i j => raw40850step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40850step2 raw40850step1; decide +kernel
      have hl : raw40850step2Labels = raw40850step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40850step1 raw40850step1Labels permutation31 permutation3
    mixedMoment B raw40850step2 raw40850step2Labels = mixedMoment B raw40850step3 raw40850step3Labels := by
      have ha : raw40850step3 = -raw40850step2 := by apply Matrix.ext; change ∀ i j, raw40850step3 i j = -(raw40850step2 i j); unfold raw40850step3 raw40850step2; decide +kernel
      have hl : raw40850step3Labels = raw40850step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2284 node2284Labels := by rfl

theorem canonical40851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40851 raw40851Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw40851 raw40851Labels = mixedMoment B raw40851step0 raw40851step0Labels := by
      have hz : ∀ j, raw40851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40851step0 = (fun i j => raw40851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40851step0 raw40851; decide +kernel
      have hl : raw40851step0Labels = raw40851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40851 raw40851Labels permutation434 hz
    mixedMoment B raw40851step0 raw40851step0Labels = mixedMoment B raw40851step1 raw40851step1Labels := by
      have ha : raw40851step1 = (fun i j => raw40851step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40851step1 raw40851step0; decide +kernel
      have hl : raw40851step1Labels = raw40851step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40851step0 raw40851step0Labels permutation101 permutation6
    _ = mixedMoment B node2133 node2133Labels := by rfl

theorem canonical40852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40852 raw40852Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw40852 raw40852Labels = mixedMoment B raw40852step0 raw40852step0Labels := by
      have hz : ∀ j, raw40852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40852step0 = (fun i j => raw40852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40852step0 raw40852; decide +kernel
      have hl : raw40852step0Labels = raw40852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40852 raw40852Labels permutation434 hz
    mixedMoment B raw40852step0 raw40852step0Labels = mixedMoment B raw40852step1 raw40852step1Labels := by
      have ha : raw40852step1 = (fun i j => raw40852step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40852step1 raw40852step0; decide +kernel
      have hl : raw40852step1Labels = raw40852step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40852step0 raw40852step0Labels permutation100 permutation6
    _ = mixedMoment B node1826 node1826Labels := by rfl

theorem canonical40853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40853 raw40853Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw40853 raw40853Labels = mixedMoment B raw40853step0 raw40853step0Labels := by
      have hz : ∀ j, raw40853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40853step0 = (fun i j => raw40853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40853step0 raw40853; decide +kernel
      have hl : raw40853step0Labels = raw40853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40853 raw40853Labels permutation434 hz
    mixedMoment B raw40853step0 raw40853step0Labels = mixedMoment B raw40853step1 raw40853step1Labels := by
      have ha : raw40853step1 = (fun i j => raw40853step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40853step1 raw40853step0; decide +kernel
      have hl : raw40853step1Labels = raw40853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40853step0 raw40853step0Labels permutation97 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical40854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40854 raw40854Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw40854 raw40854Labels = mixedMoment B raw40854step0 raw40854step0Labels := by
      have hz : ∀ j, raw40854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40854step0 = (fun i j => raw40854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40854step0 raw40854; decide +kernel
      have hl : raw40854step0Labels = raw40854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40854 raw40854Labels permutation434 hz
    mixedMoment B raw40854step0 raw40854step0Labels = mixedMoment B raw40854step1 raw40854step1Labels := by
      have ha : raw40854step1 = (fun i j => raw40854step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40854step1 raw40854step0; decide +kernel
      have hl : raw40854step1Labels = raw40854step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40854step0 raw40854step0Labels permutation101 permutation6
    _ = mixedMoment B node2108 node2108Labels := by rfl

theorem canonical40855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40855 raw40855Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw40855 raw40855Labels = mixedMoment B raw40855step0 raw40855step0Labels := by
      have hz : ∀ j, raw40855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40855step0 = (fun i j => raw40855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40855step0 raw40855; decide +kernel
      have hl : raw40855step0Labels = raw40855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40855 raw40855Labels permutation434 hz
    mixedMoment B raw40855step0 raw40855step0Labels = mixedMoment B raw40855step1 raw40855step1Labels := by
      have ha : raw40855step1 = (fun i j => raw40855step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40855step1 raw40855step0; decide +kernel
      have hl : raw40855step1Labels = raw40855step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40855step0 raw40855step0Labels permutation100 permutation6
    _ = mixedMoment B node1809 node1809Labels := by rfl

theorem canonical40856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40856 raw40856Labels = mixedMoment B node1824 node1824Labels := by
  calc
    mixedMoment B raw40856 raw40856Labels = mixedMoment B raw40856step0 raw40856step0Labels := by
      have ha : raw40856step0 = (fun i j => raw40856 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40856step0 raw40856; decide +kernel
      have hl : raw40856step0Labels = raw40856Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40856 raw40856Labels permutation421 permutation6
    _ = mixedMoment B node1824 node1824Labels := by rfl

theorem canonical40857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40857 raw40857Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw40857 raw40857Labels = mixedMoment B raw40857step0 raw40857step0Labels := by
      have ha : raw40857step0 = (fun i j => raw40857 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40857step0 raw40857; decide +kernel
      have hl : raw40857step0Labels = raw40857Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40857 raw40857Labels permutation431 permutation6
    _ = mixedMoment B node2089 node2089Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical7731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7731 raw7731Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw7731 raw7731Labels = mixedMoment B raw7731step0 raw7731step0Labels := by
      have hz : ∀ j, raw7731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw7731step0 = (fun i j => raw7731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw7731step0 raw7731; decide +kernel
      have hl : raw7731step0Labels = raw7731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7731 raw7731Labels permutation434 hz
    mixedMoment B raw7731step0 raw7731step0Labels = mixedMoment B raw7731step1 raw7731step1Labels := by
      have hz : ∀ j, raw7731step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7731step1 = (fun i j => raw7731step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7731step1 raw7731step0; decide +kernel
      have hl : raw7731step1Labels = raw7731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7731step0 raw7731step0Labels permutation80 hz
    mixedMoment B raw7731step1 raw7731step1Labels = mixedMoment B raw7731step2 raw7731step2Labels := by
      have ha : raw7731step2 = (fun i j => raw7731step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7731step2 raw7731step1; decide +kernel
      have hl : raw7731step2Labels = raw7731step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7731step1 raw7731step1Labels permutation23 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1408 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1408) =
      Integer.Sparse.eval keyMomentRow1408 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1408).leftCharge (GramAssembly.key 1408).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3872) := by
    have ha : gramCharges (GramAssembly.key 1408).leftCharge (GramAssembly.key 1408).rightCharge = raw40830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40830 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1408).leftCharge (GramAssembly.key 1408).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1408, Integer.Sparse.eval]

theorem keyMoment1409 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1409) =
      Integer.Sparse.eval keyMomentRow1409 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1409).leftCharge (GramAssembly.key 1409).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3722) := by
    have ha : gramCharges (GramAssembly.key 1409).leftCharge (GramAssembly.key 1409).rightCharge = raw40831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40831 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1409).leftCharge (GramAssembly.key 1409).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1409, Integer.Sparse.eval]

theorem keyMoment1410 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1410) =
      Integer.Sparse.eval keyMomentRow1410 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1410).leftCharge (GramAssembly.key 1410).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3723) := by
    have ha : gramCharges (GramAssembly.key 1410).leftCharge (GramAssembly.key 1410).rightCharge = raw40832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40832 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1410).leftCharge (GramAssembly.key 1410).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1410, Integer.Sparse.eval]

theorem keyMoment1411 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1411) =
      Integer.Sparse.eval keyMomentRow1411 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1411).leftCharge (GramAssembly.key 1411).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3715) := by
    have ha : gramCharges (GramAssembly.key 1411).leftCharge (GramAssembly.key 1411).rightCharge = raw40833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40833 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1411).leftCharge (GramAssembly.key 1411).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1411, Integer.Sparse.eval]

theorem keyMoment1412 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1412) =
      Integer.Sparse.eval keyMomentRow1412 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1412).leftCharge (GramAssembly.key 1412).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1412).leftCharge (GramAssembly.key 1412).rightCharge = raw40834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40834 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1412).leftCharge (GramAssembly.key 1412).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1412, Integer.Sparse.eval]

theorem keyMoment1413 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1413) =
      Integer.Sparse.eval keyMomentRow1413 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1413).leftCharge (GramAssembly.key 1413).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3899) := by
    have ha : gramCharges (GramAssembly.key 1413).leftCharge (GramAssembly.key 1413).rightCharge = raw12968 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw12968Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical12968 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1413).leftCharge (GramAssembly.key 1413).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1413, Integer.Sparse.eval]

theorem keyMoment1414 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1414) =
      Integer.Sparse.eval keyMomentRow1414 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1414).leftCharge (GramAssembly.key 1414).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2245) := by
    have ha : gramCharges (GramAssembly.key 1414).leftCharge (GramAssembly.key 1414).rightCharge = raw15791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw15791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical15791 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1414).leftCharge (GramAssembly.key 1414).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1414, Integer.Sparse.eval]

theorem keyMoment1415 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1415) =
      Integer.Sparse.eval keyMomentRow1415 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1415).leftCharge (GramAssembly.key 1415).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 1415).leftCharge (GramAssembly.key 1415).rightCharge = raw15508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw15508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical15508 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1415).leftCharge (GramAssembly.key 1415).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1415, Integer.Sparse.eval]

theorem keyMoment1416 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1416) =
      Integer.Sparse.eval keyMomentRow1416 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1416).leftCharge (GramAssembly.key 1416).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3030) := by
    have ha : gramCharges (GramAssembly.key 1416).leftCharge (GramAssembly.key 1416).rightCharge = raw40835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40835 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1416).leftCharge (GramAssembly.key 1416).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1416, Integer.Sparse.eval]

theorem keyMoment1417 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1417) =
      Integer.Sparse.eval keyMomentRow1417 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1417).leftCharge (GramAssembly.key 1417).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3378) := by
    have ha : gramCharges (GramAssembly.key 1417).leftCharge (GramAssembly.key 1417).rightCharge = raw40836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40836 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1417).leftCharge (GramAssembly.key 1417).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1417, Integer.Sparse.eval]

theorem keyMoment1418 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1418) =
      Integer.Sparse.eval keyMomentRow1418 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1418).leftCharge (GramAssembly.key 1418).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2930) := by
    have ha : gramCharges (GramAssembly.key 1418).leftCharge (GramAssembly.key 1418).rightCharge = raw40837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40837 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1418).leftCharge (GramAssembly.key 1418).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1418, Integer.Sparse.eval]

theorem keyMoment1419 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1419) =
      Integer.Sparse.eval keyMomentRow1419 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1419).leftCharge (GramAssembly.key 1419).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2928) := by
    have ha : gramCharges (GramAssembly.key 1419).leftCharge (GramAssembly.key 1419).rightCharge = raw40838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40838 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1419).leftCharge (GramAssembly.key 1419).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1419, Integer.Sparse.eval]

theorem keyMoment1420 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1420) =
      Integer.Sparse.eval keyMomentRow1420 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1420).leftCharge (GramAssembly.key 1420).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2916) := by
    have ha : gramCharges (GramAssembly.key 1420).leftCharge (GramAssembly.key 1420).rightCharge = raw40839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40839 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1420).leftCharge (GramAssembly.key 1420).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1420, Integer.Sparse.eval]

theorem keyMoment1421 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1421) =
      Integer.Sparse.eval keyMomentRow1421 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1421).leftCharge (GramAssembly.key 1421).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 1421).leftCharge (GramAssembly.key 1421).rightCharge = raw7731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw7731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical7731 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1421).leftCharge (GramAssembly.key 1421).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1421, Integer.Sparse.eval]

theorem keyMoment1422 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1422) =
      Integer.Sparse.eval keyMomentRow1422 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1422).leftCharge (GramAssembly.key 1422).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1245) := by
    have ha : gramCharges (GramAssembly.key 1422).leftCharge (GramAssembly.key 1422).rightCharge = raw40840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40840 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1422).leftCharge (GramAssembly.key 1422).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1422, Integer.Sparse.eval]

theorem keyMoment1423 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1423) =
      Integer.Sparse.eval keyMomentRow1423 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1423).leftCharge (GramAssembly.key 1423).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 1423).leftCharge (GramAssembly.key 1423).rightCharge = raw40841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40841 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1423).leftCharge (GramAssembly.key 1423).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1423, Integer.Sparse.eval]

theorem keyMoment1424 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1424) =
      Integer.Sparse.eval keyMomentRow1424 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1424).leftCharge (GramAssembly.key 1424).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1241) := by
    have ha : gramCharges (GramAssembly.key 1424).leftCharge (GramAssembly.key 1424).rightCharge = raw40842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40842 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1424).leftCharge (GramAssembly.key 1424).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1424, Integer.Sparse.eval]

theorem keyMoment1425 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1425) =
      Integer.Sparse.eval keyMomentRow1425 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1425).leftCharge (GramAssembly.key 1425).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2620) := by
    have ha : gramCharges (GramAssembly.key 1425).leftCharge (GramAssembly.key 1425).rightCharge = raw40843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40843 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1425).leftCharge (GramAssembly.key 1425).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1425, Integer.Sparse.eval]

theorem keyMoment1426 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1426) =
      Integer.Sparse.eval keyMomentRow1426 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1426).leftCharge (GramAssembly.key 1426).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1219) := by
    have ha : gramCharges (GramAssembly.key 1426).leftCharge (GramAssembly.key 1426).rightCharge = raw40844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40844 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1426).leftCharge (GramAssembly.key 1426).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1426, Integer.Sparse.eval]

theorem keyMoment1427 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1427) =
      Integer.Sparse.eval keyMomentRow1427 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1427).leftCharge (GramAssembly.key 1427).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2617) := by
    have ha : gramCharges (GramAssembly.key 1427).leftCharge (GramAssembly.key 1427).rightCharge = raw40845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40845 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1427).leftCharge (GramAssembly.key 1427).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1427, Integer.Sparse.eval]

theorem keyMoment1428 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1428) =
      Integer.Sparse.eval keyMomentRow1428 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1428).leftCharge (GramAssembly.key 1428).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1216) := by
    have ha : gramCharges (GramAssembly.key 1428).leftCharge (GramAssembly.key 1428).rightCharge = raw40846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40846 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1428).leftCharge (GramAssembly.key 1428).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1428, Integer.Sparse.eval]

theorem keyMoment1429 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1429) =
      Integer.Sparse.eval keyMomentRow1429 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1429).leftCharge (GramAssembly.key 1429).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2557) := by
    have ha : gramCharges (GramAssembly.key 1429).leftCharge (GramAssembly.key 1429).rightCharge = raw40847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40847 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1429).leftCharge (GramAssembly.key 1429).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1429, Integer.Sparse.eval]

theorem keyMoment1430 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1430) =
      Integer.Sparse.eval keyMomentRow1430 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1430).leftCharge (GramAssembly.key 1430).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 1430).leftCharge (GramAssembly.key 1430).rightCharge = raw40848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40848 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1430).leftCharge (GramAssembly.key 1430).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1430, Integer.Sparse.eval]

theorem keyMoment1431 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1431) =
      Integer.Sparse.eval keyMomentRow1431 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1431).leftCharge (GramAssembly.key 1431).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2545) := by
    have ha : gramCharges (GramAssembly.key 1431).leftCharge (GramAssembly.key 1431).rightCharge = raw40849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40849 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1431).leftCharge (GramAssembly.key 1431).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1431, Integer.Sparse.eval]

theorem keyMoment1432 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1432) =
      Integer.Sparse.eval keyMomentRow1432 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1432).leftCharge (GramAssembly.key 1432).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2284) := by
    have ha : gramCharges (GramAssembly.key 1432).leftCharge (GramAssembly.key 1432).rightCharge = raw40850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40850 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1432).leftCharge (GramAssembly.key 1432).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1432, Integer.Sparse.eval]

theorem keyMoment1433 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1433) =
      Integer.Sparse.eval keyMomentRow1433 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1433).leftCharge (GramAssembly.key 1433).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2133) := by
    have ha : gramCharges (GramAssembly.key 1433).leftCharge (GramAssembly.key 1433).rightCharge = raw40851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40851 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1433).leftCharge (GramAssembly.key 1433).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1433, Integer.Sparse.eval]

theorem keyMoment1434 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1434) =
      Integer.Sparse.eval keyMomentRow1434 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1434).leftCharge (GramAssembly.key 1434).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1826) := by
    have ha : gramCharges (GramAssembly.key 1434).leftCharge (GramAssembly.key 1434).rightCharge = raw40852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40852 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1434).leftCharge (GramAssembly.key 1434).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1434, Integer.Sparse.eval]

theorem keyMoment1435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1435) =
      Integer.Sparse.eval keyMomentRow1435 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1435).leftCharge (GramAssembly.key 1435).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 1435).leftCharge (GramAssembly.key 1435).rightCharge = raw40853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40853 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1435).leftCharge (GramAssembly.key 1435).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1435, Integer.Sparse.eval]

theorem keyMoment1436 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1436) =
      Integer.Sparse.eval keyMomentRow1436 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1436).leftCharge (GramAssembly.key 1436).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2108) := by
    have ha : gramCharges (GramAssembly.key 1436).leftCharge (GramAssembly.key 1436).rightCharge = raw40854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40854 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1436).leftCharge (GramAssembly.key 1436).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1436, Integer.Sparse.eval]

theorem keyMoment1437 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1437) =
      Integer.Sparse.eval keyMomentRow1437 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1437).leftCharge (GramAssembly.key 1437).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1809) := by
    have ha : gramCharges (GramAssembly.key 1437).leftCharge (GramAssembly.key 1437).rightCharge = raw40855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40855 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1437).leftCharge (GramAssembly.key 1437).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1437, Integer.Sparse.eval]

theorem keyMoment1438 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1438) =
      Integer.Sparse.eval keyMomentRow1438 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1438).leftCharge (GramAssembly.key 1438).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1824) := by
    have ha : gramCharges (GramAssembly.key 1438).leftCharge (GramAssembly.key 1438).rightCharge = raw40856 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40856Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40856 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1438).leftCharge (GramAssembly.key 1438).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1438, Integer.Sparse.eval]

theorem keyMoment1439 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1439) =
      Integer.Sparse.eval keyMomentRow1439 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1439).leftCharge (GramAssembly.key 1439).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2089) := by
    have ha : gramCharges (GramAssembly.key 1439).leftCharge (GramAssembly.key 1439).rightCharge = raw40857 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40857Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40857 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1439).leftCharge (GramAssembly.key 1439).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1439, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1408 : keyMomentRows (1408 : Fin 2886) =
    keyMomentRow1408 := by decide +kernel

theorem keyMomentRowsAt1409 : keyMomentRows (1409 : Fin 2886) =
    keyMomentRow1409 := by decide +kernel

theorem keyMomentRowsAt1410 : keyMomentRows (1410 : Fin 2886) =
    keyMomentRow1410 := by decide +kernel

theorem keyMomentRowsAt1411 : keyMomentRows (1411 : Fin 2886) =
    keyMomentRow1411 := by decide +kernel

theorem keyMomentRowsAt1412 : keyMomentRows (1412 : Fin 2886) =
    keyMomentRow1412 := by decide +kernel

theorem keyMomentRowsAt1413 : keyMomentRows (1413 : Fin 2886) =
    keyMomentRow1413 := by decide +kernel

theorem keyMomentRowsAt1414 : keyMomentRows (1414 : Fin 2886) =
    keyMomentRow1414 := by decide +kernel

theorem keyMomentRowsAt1415 : keyMomentRows (1415 : Fin 2886) =
    keyMomentRow1415 := by decide +kernel

theorem keyMomentRowsAt1416 : keyMomentRows (1416 : Fin 2886) =
    keyMomentRow1416 := by decide +kernel

theorem keyMomentRowsAt1417 : keyMomentRows (1417 : Fin 2886) =
    keyMomentRow1417 := by decide +kernel

theorem keyMomentRowsAt1418 : keyMomentRows (1418 : Fin 2886) =
    keyMomentRow1418 := by decide +kernel

theorem keyMomentRowsAt1419 : keyMomentRows (1419 : Fin 2886) =
    keyMomentRow1419 := by decide +kernel

theorem keyMomentRowsAt1420 : keyMomentRows (1420 : Fin 2886) =
    keyMomentRow1420 := by decide +kernel

theorem keyMomentRowsAt1421 : keyMomentRows (1421 : Fin 2886) =
    keyMomentRow1421 := by decide +kernel

theorem keyMomentRowsAt1422 : keyMomentRows (1422 : Fin 2886) =
    keyMomentRow1422 := by decide +kernel

theorem keyMomentRowsAt1423 : keyMomentRows (1423 : Fin 2886) =
    keyMomentRow1423 := by decide +kernel

theorem keyMomentRowsAt1424 : keyMomentRows (1424 : Fin 2886) =
    keyMomentRow1424 := by decide +kernel

theorem keyMomentRowsAt1425 : keyMomentRows (1425 : Fin 2886) =
    keyMomentRow1425 := by decide +kernel

theorem keyMomentRowsAt1426 : keyMomentRows (1426 : Fin 2886) =
    keyMomentRow1426 := by decide +kernel

theorem keyMomentRowsAt1427 : keyMomentRows (1427 : Fin 2886) =
    keyMomentRow1427 := by decide +kernel

theorem keyMomentRowsAt1428 : keyMomentRows (1428 : Fin 2886) =
    keyMomentRow1428 := by decide +kernel

theorem keyMomentRowsAt1429 : keyMomentRows (1429 : Fin 2886) =
    keyMomentRow1429 := by decide +kernel

theorem keyMomentRowsAt1430 : keyMomentRows (1430 : Fin 2886) =
    keyMomentRow1430 := by decide +kernel

theorem keyMomentRowsAt1431 : keyMomentRows (1431 : Fin 2886) =
    keyMomentRow1431 := by decide +kernel

theorem keyMomentRowsAt1432 : keyMomentRows (1432 : Fin 2886) =
    keyMomentRow1432 := by decide +kernel

theorem keyMomentRowsAt1433 : keyMomentRows (1433 : Fin 2886) =
    keyMomentRow1433 := by decide +kernel

theorem keyMomentRowsAt1434 : keyMomentRows (1434 : Fin 2886) =
    keyMomentRow1434 := by decide +kernel

theorem keyMomentRowsAt1435 : keyMomentRows (1435 : Fin 2886) =
    keyMomentRow1435 := by decide +kernel

theorem keyMomentRowsAt1436 : keyMomentRows (1436 : Fin 2886) =
    keyMomentRow1436 := by decide +kernel

theorem keyMomentRowsAt1437 : keyMomentRows (1437 : Fin 2886) =
    keyMomentRow1437 := by decide +kernel

theorem keyMomentRowsAt1438 : keyMomentRows (1438 : Fin 2886) =
    keyMomentRow1438 := by decide +kernel

theorem keyMomentRowsAt1439 : keyMomentRows (1439 : Fin 2886) =
    keyMomentRow1439 := by decide +kernel

theorem keyMomentChunkSound44_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 44) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1408 ∨ k.val = 1409 ∨ k.val = 1410 ∨ k.val = 1411 ∨ k.val = 1412 ∨ k.val = 1413 ∨ k.val = 1414 ∨ k.val = 1415 ∨ k.val = 1416 ∨ k.val = 1417 ∨ k.val = 1418 ∨ k.val = 1419 ∨ k.val = 1420 ∨ k.val = 1421 ∨ k.val = 1422 ∨ k.val = 1423 ∨ k.val = 1424 ∨ k.val = 1425 ∨ k.val = 1426 ∨ k.val = 1427 ∨ k.val = 1428 ∨ k.val = 1429 ∨ k.val = 1430 ∨ k.val = 1431 ∨ k.val = 1432 ∨ k.val = 1433 ∨ k.val = 1434 ∨ k.val = 1435 ∨ k.val = 1436 ∨ k.val = 1437 ∨ k.val = 1438 ∨ k.val = 1439 := by omega
  rcases heq with h1408 | h1409 | h1410 | h1411 | h1412 | h1413 | h1414 | h1415 | h1416 | h1417 | h1418 | h1419 | h1420 | h1421 | h1422 | h1423 | h1424 | h1425 | h1426 | h1427 | h1428 | h1429 | h1430 | h1431 | h1432 | h1433 | h1434 | h1435 | h1436 | h1437 | h1438 | h1439
  · have he : k = (1408 : Fin 2886) := Fin.ext h1408
    subst k
    rw [keyMomentRowsAt1408]
    exact keyMoment1408 B hB
  · have he : k = (1409 : Fin 2886) := Fin.ext h1409
    subst k
    rw [keyMomentRowsAt1409]
    exact keyMoment1409 B hB
  · have he : k = (1410 : Fin 2886) := Fin.ext h1410
    subst k
    rw [keyMomentRowsAt1410]
    exact keyMoment1410 B hB
  · have he : k = (1411 : Fin 2886) := Fin.ext h1411
    subst k
    rw [keyMomentRowsAt1411]
    exact keyMoment1411 B hB
  · have he : k = (1412 : Fin 2886) := Fin.ext h1412
    subst k
    rw [keyMomentRowsAt1412]
    exact keyMoment1412 B hB
  · have he : k = (1413 : Fin 2886) := Fin.ext h1413
    subst k
    rw [keyMomentRowsAt1413]
    exact keyMoment1413 B hB
  · have he : k = (1414 : Fin 2886) := Fin.ext h1414
    subst k
    rw [keyMomentRowsAt1414]
    exact keyMoment1414 B hB
  · have he : k = (1415 : Fin 2886) := Fin.ext h1415
    subst k
    rw [keyMomentRowsAt1415]
    exact keyMoment1415 B hB
  · have he : k = (1416 : Fin 2886) := Fin.ext h1416
    subst k
    rw [keyMomentRowsAt1416]
    exact keyMoment1416 B hB
  · have he : k = (1417 : Fin 2886) := Fin.ext h1417
    subst k
    rw [keyMomentRowsAt1417]
    exact keyMoment1417 B hB
  · have he : k = (1418 : Fin 2886) := Fin.ext h1418
    subst k
    rw [keyMomentRowsAt1418]
    exact keyMoment1418 B hB
  · have he : k = (1419 : Fin 2886) := Fin.ext h1419
    subst k
    rw [keyMomentRowsAt1419]
    exact keyMoment1419 B hB
  · have he : k = (1420 : Fin 2886) := Fin.ext h1420
    subst k
    rw [keyMomentRowsAt1420]
    exact keyMoment1420 B hB
  · have he : k = (1421 : Fin 2886) := Fin.ext h1421
    subst k
    rw [keyMomentRowsAt1421]
    exact keyMoment1421 B hB
  · have he : k = (1422 : Fin 2886) := Fin.ext h1422
    subst k
    rw [keyMomentRowsAt1422]
    exact keyMoment1422 B hB
  · have he : k = (1423 : Fin 2886) := Fin.ext h1423
    subst k
    rw [keyMomentRowsAt1423]
    exact keyMoment1423 B hB
  · have he : k = (1424 : Fin 2886) := Fin.ext h1424
    subst k
    rw [keyMomentRowsAt1424]
    exact keyMoment1424 B hB
  · have he : k = (1425 : Fin 2886) := Fin.ext h1425
    subst k
    rw [keyMomentRowsAt1425]
    exact keyMoment1425 B hB
  · have he : k = (1426 : Fin 2886) := Fin.ext h1426
    subst k
    rw [keyMomentRowsAt1426]
    exact keyMoment1426 B hB
  · have he : k = (1427 : Fin 2886) := Fin.ext h1427
    subst k
    rw [keyMomentRowsAt1427]
    exact keyMoment1427 B hB
  · have he : k = (1428 : Fin 2886) := Fin.ext h1428
    subst k
    rw [keyMomentRowsAt1428]
    exact keyMoment1428 B hB
  · have he : k = (1429 : Fin 2886) := Fin.ext h1429
    subst k
    rw [keyMomentRowsAt1429]
    exact keyMoment1429 B hB
  · have he : k = (1430 : Fin 2886) := Fin.ext h1430
    subst k
    rw [keyMomentRowsAt1430]
    exact keyMoment1430 B hB
  · have he : k = (1431 : Fin 2886) := Fin.ext h1431
    subst k
    rw [keyMomentRowsAt1431]
    exact keyMoment1431 B hB
  · have he : k = (1432 : Fin 2886) := Fin.ext h1432
    subst k
    rw [keyMomentRowsAt1432]
    exact keyMoment1432 B hB
  · have he : k = (1433 : Fin 2886) := Fin.ext h1433
    subst k
    rw [keyMomentRowsAt1433]
    exact keyMoment1433 B hB
  · have he : k = (1434 : Fin 2886) := Fin.ext h1434
    subst k
    rw [keyMomentRowsAt1434]
    exact keyMoment1434 B hB
  · have he : k = (1435 : Fin 2886) := Fin.ext h1435
    subst k
    rw [keyMomentRowsAt1435]
    exact keyMoment1435 B hB
  · have he : k = (1436 : Fin 2886) := Fin.ext h1436
    subst k
    rw [keyMomentRowsAt1436]
    exact keyMoment1436 B hB
  · have he : k = (1437 : Fin 2886) := Fin.ext h1437
    subst k
    rw [keyMomentRowsAt1437]
    exact keyMoment1437 B hB
  · have he : k = (1438 : Fin 2886) := Fin.ext h1438
    subst k
    rw [keyMomentRowsAt1438]
    exact keyMoment1438 B hB
  · have he : k = (1439 : Fin 2886) := Fin.ext h1439
    subst k
    rw [keyMomentRowsAt1439]
    exact keyMoment1439 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound44_e_oai
