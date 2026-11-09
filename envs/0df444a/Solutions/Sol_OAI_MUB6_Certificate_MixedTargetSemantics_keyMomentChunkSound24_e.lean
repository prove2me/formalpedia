-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:29.799887+00:00
-- url     : https://prove2.me/submissions/77b00847-2038-494c-a0b8-b32b3135ade7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical314
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40215 raw40215Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw40215 raw40215Labels = mixedMoment B raw40215step0 raw40215step0Labels := by
      have ha : raw40215step0 = (fun i j => raw40215 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40215step0 raw40215; decide +kernel
      have hl : raw40215step0Labels = raw40215Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40215 raw40215Labels permutation639 permutation7
    _ = mixedMoment B node334 node334Labels := by rfl

theorem canonical40216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40216 raw40216Labels = mixedMoment B node310 node310Labels := by
  calc
    mixedMoment B raw40216 raw40216Labels = mixedMoment B raw40216step0 raw40216step0Labels := by
      have ha : raw40216step0 = (fun i j => raw40216 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40216step0 raw40216; decide +kernel
      have hl : raw40216step0Labels = raw40216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40216 raw40216Labels permutation541 permutation6
    _ = mixedMoment B node310 node310Labels := by rfl

theorem canonical40217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40217 raw40217Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40217 raw40217Labels = mixedMoment B raw40217step0 raw40217step0Labels := by
      have ha : raw40217step0 = (fun i j => raw40217 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40217step0 raw40217; decide +kernel
      have hl : raw40217step0Labels = raw40217Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40217 raw40217Labels permutation547 permutation6
    _ = mixedMoment B node520 node520Labels := by rfl

theorem canonical40218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40218 raw40218Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw40218 raw40218Labels = mixedMoment B raw40218step0 raw40218step0Labels := by
      have ha : raw40218step0 = (fun i j => raw40218 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40218step0 raw40218; decide +kernel
      have hl : raw40218step0Labels = raw40218Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40218 raw40218Labels permutation547 permutation6
    _ = mixedMoment B node301 node301Labels := by rfl

theorem canonical40219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40219 raw40219Labels = mixedMoment B node155 node155Labels := by
  calc
    mixedMoment B raw40219 raw40219Labels = mixedMoment B raw40219step0 raw40219step0Labels := by
      have hz : ∀ j, raw40219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40219step0 = (fun i j => raw40219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40219step0 raw40219; decide +kernel
      have hl : raw40219step0Labels = raw40219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40219 raw40219Labels permutation346 hz
    mixedMoment B raw40219step0 raw40219step0Labels = mixedMoment B raw40219step1 raw40219step1Labels := by
      have ha : raw40219step1 = (fun i j => raw40219step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40219step1 raw40219step0; decide +kernel
      have hl : raw40219step1Labels = raw40219step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40219step0 raw40219step0Labels permutation128 permutation6
    _ = mixedMoment B node155 node155Labels := by rfl

theorem canonical40220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40220 raw40220Labels = mixedMoment B node22 node22Labels := by
  calc
    mixedMoment B raw40220 raw40220Labels = mixedMoment B raw40220step0 raw40220step0Labels := by
      have ha : raw40220step0 = (fun i j => raw40220 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40220step0 raw40220; decide +kernel
      have hl : raw40220step0Labels = raw40220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40220 raw40220Labels permutation590 permutation6
    _ = mixedMoment B node22 node22Labels := by rfl

theorem canonical40221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40221 raw40221Labels = mixedMoment B node91 node91Labels := by
  calc
    mixedMoment B raw40221 raw40221Labels = mixedMoment B raw40221step0 raw40221step0Labels := by
      have ha : raw40221step0 = (fun i j => raw40221 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40221step0 raw40221; decide +kernel
      have hl : raw40221step0Labels = raw40221Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40221 raw40221Labels permutation569 permutation6
    _ = mixedMoment B node91 node91Labels := by rfl

theorem canonical40222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40222 raw40222Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw40222 raw40222Labels = mixedMoment B raw40222step0 raw40222step0Labels := by
      have hz : ∀ j, raw40222 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40222step0 = (fun i j => raw40222 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40222step0 raw40222; decide +kernel
      have hl : raw40222step0Labels = raw40222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40222 raw40222Labels permutation520 hz
    mixedMoment B raw40222step0 raw40222step0Labels = mixedMoment B raw40222step1 raw40222step1Labels := by
      have hz : ∀ j, raw40222step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40222step1 = (fun i j => raw40222step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40222step1 raw40222step0; decide +kernel
      have hl : raw40222step1Labels = raw40222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40222step0 raw40222step0Labels permutation104 hz
    mixedMoment B raw40222step1 raw40222step1Labels = mixedMoment B raw40222step2 raw40222step2Labels := by
      have ha : raw40222step2 = (fun i j => raw40222step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40222step2 raw40222step1; decide +kernel
      have hl : raw40222step2Labels = raw40222step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40222step1 raw40222step1Labels permutation20 permutation4
    mixedMoment B raw40222step2 raw40222step2Labels = mixedMoment B raw40222step3 raw40222step3Labels := by
      have ha : raw40222step3 = -raw40222step2 := by apply Matrix.ext; change ∀ i j, raw40222step3 i j = -(raw40222step2 i j); unfold raw40222step3 raw40222step2; decide +kernel
      have hl : raw40222step3Labels = raw40222step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical40223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40223 raw40223Labels = mixedMoment B node245 node245Labels := by
  calc
    mixedMoment B raw40223 raw40223Labels = mixedMoment B raw40223step0 raw40223step0Labels := by
      have hz : ∀ j, raw40223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40223step0 = (fun i j => raw40223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40223step0 raw40223; decide +kernel
      have hl : raw40223step0Labels = raw40223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40223 raw40223Labels permutation434 hz
    mixedMoment B raw40223step0 raw40223step0Labels = mixedMoment B raw40223step1 raw40223step1Labels := by
      have ha : raw40223step1 = (fun i j => raw40223step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40223step1 raw40223step0; decide +kernel
      have hl : raw40223step1Labels = raw40223step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40223step0 raw40223step0Labels permutation99 permutation6
    _ = mixedMoment B node245 node245Labels := by rfl

theorem canonical40224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40224 raw40224Labels = mixedMoment B node178 node178Labels := by
  calc
    mixedMoment B raw40224 raw40224Labels = mixedMoment B raw40224step0 raw40224step0Labels := by
      have hz : ∀ j, raw40224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40224step0 = (fun i j => raw40224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40224step0 raw40224; decide +kernel
      have hl : raw40224step0Labels = raw40224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40224 raw40224Labels permutation434 hz
    mixedMoment B raw40224step0 raw40224step0Labels = mixedMoment B raw40224step1 raw40224step1Labels := by
      have ha : raw40224step1 = (fun i j => raw40224step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40224step1 raw40224step0; decide +kernel
      have hl : raw40224step1Labels = raw40224step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40224step0 raw40224step0Labels permutation98 permutation6
    _ = mixedMoment B node178 node178Labels := by rfl

theorem canonical40225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40225 raw40225Labels = mixedMoment B node234 node234Labels := by
  calc
    mixedMoment B raw40225 raw40225Labels = mixedMoment B raw40225step0 raw40225step0Labels := by
      have hz : ∀ j, raw40225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40225step0 = (fun i j => raw40225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40225step0 raw40225; decide +kernel
      have hl : raw40225step0Labels = raw40225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40225 raw40225Labels permutation434 hz
    mixedMoment B raw40225step0 raw40225step0Labels = mixedMoment B raw40225step1 raw40225step1Labels := by
      have ha : raw40225step1 = (fun i j => raw40225step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40225step1 raw40225step0; decide +kernel
      have hl : raw40225step1Labels = raw40225step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40225step0 raw40225step0Labels permutation93 permutation6
    _ = mixedMoment B node234 node234Labels := by rfl

theorem canonical40226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40226 raw40226Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw40226 raw40226Labels = mixedMoment B raw40226step0 raw40226step0Labels := by
      have hz : ∀ j, raw40226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40226step0 = (fun i j => raw40226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40226step0 raw40226; decide +kernel
      have hl : raw40226step0Labels = raw40226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40226 raw40226Labels permutation434 hz
    mixedMoment B raw40226step0 raw40226step0Labels = mixedMoment B raw40226step1 raw40226step1Labels := by
      have ha : raw40226step1 = (fun i j => raw40226step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40226step1 raw40226step0; decide +kernel
      have hl : raw40226step1Labels = raw40226step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40226step0 raw40226step0Labels permutation96 permutation6
    _ = mixedMoment B node260 node260Labels := by rfl

theorem canonical40227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40227 raw40227Labels = mixedMoment B node174 node174Labels := by
  calc
    mixedMoment B raw40227 raw40227Labels = mixedMoment B raw40227step0 raw40227step0Labels := by
      have ha : raw40227step0 = (fun i j => raw40227 (permutation416 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40227step0 raw40227; decide +kernel
      have hl : raw40227step0Labels = raw40227Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40227 raw40227Labels permutation416 permutation6
    _ = mixedMoment B node174 node174Labels := by rfl

theorem canonical40228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40228 raw40228Labels = mixedMoment B node221 node221Labels := by
  calc
    mixedMoment B raw40228 raw40228Labels = mixedMoment B raw40228step0 raw40228step0Labels := by
      have ha : raw40228step0 = (fun i j => raw40228 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40228step0 raw40228; decide +kernel
      have hl : raw40228step0Labels = raw40228Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40228 raw40228Labels permutation410 permutation6
    _ = mixedMoment B node221 node221Labels := by rfl

theorem canonical40229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40229 raw40229Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw40229 raw40229Labels = mixedMoment B raw40229step0 raw40229step0Labels := by
      have hz : ∀ j, raw40229 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40229step0 = (fun i j => raw40229 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40229step0 raw40229; decide +kernel
      have hl : raw40229step0Labels = raw40229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40229 raw40229Labels permutation520 hz
    mixedMoment B raw40229step0 raw40229step0Labels = mixedMoment B raw40229step1 raw40229step1Labels := by
      have ha : raw40229step1 = (fun i j => raw40229step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40229step1 raw40229step0; decide +kernel
      have hl : raw40229step1Labels = raw40229step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40229step0 raw40229step0Labels permutation92 permutation4
    mixedMoment B raw40229step1 raw40229step1Labels = mixedMoment B raw40229step2 raw40229step2Labels := by
      have ha : raw40229step2 = -raw40229step1 := by apply Matrix.ext; change ∀ i j, raw40229step2 i j = -(raw40229step1 i j); unfold raw40229step2 raw40229step1; decide +kernel
      have hl : raw40229step2Labels = raw40229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

theorem canonical40230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40230 raw40230Labels = mixedMoment B node424 node424Labels := by
  calc
    mixedMoment B raw40230 raw40230Labels = mixedMoment B raw40230step0 raw40230step0Labels := by
      have ha : raw40230step0 = (fun i j => raw40230 (permutation530 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40230step0 raw40230; decide +kernel
      have hl : raw40230step0Labels = raw40230Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40230 raw40230Labels permutation530 permutation6
    mixedMoment B raw40230step0 raw40230step0Labels = mixedMoment B raw40230step1 raw40230step1Labels := by
      have ha : raw40230step1 = -raw40230step0 := by apply Matrix.ext; change ∀ i j, raw40230step1 i j = -(raw40230step0 i j); unfold raw40230step1 raw40230step0; decide +kernel
      have hl : raw40230step1Labels = raw40230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node424 node424Labels := by rfl

theorem canonical40231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40231 raw40231Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw40231 raw40231Labels = mixedMoment B raw40231step0 raw40231step0Labels := by
      have hz : ∀ j, raw40231 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40231step0 = (fun i j => raw40231 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40231step0 raw40231; decide +kernel
      have hl : raw40231step0Labels = raw40231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40231 raw40231Labels permutation520 hz
    mixedMoment B raw40231step0 raw40231step0Labels = mixedMoment B raw40231step1 raw40231step1Labels := by
      have hz : ∀ j, raw40231step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40231step1 = (fun i j => raw40231step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40231step1 raw40231step0; decide +kernel
      have hl : raw40231step1Labels = raw40231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40231step0 raw40231step0Labels permutation104 hz
    mixedMoment B raw40231step1 raw40231step1Labels = mixedMoment B raw40231step2 raw40231step2Labels := by
      have ha : raw40231step2 = (fun i j => raw40231step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40231step2 raw40231step1; decide +kernel
      have hl : raw40231step2Labels = raw40231step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40231step1 raw40231step1Labels permutation24 permutation6
    _ = mixedMoment B node503 node503Labels := by rfl

theorem canonical40232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40232 raw40232Labels = mixedMoment B node450 node450Labels := by
  calc
    mixedMoment B raw40232 raw40232Labels = mixedMoment B raw40232step0 raw40232step0Labels := by
      have hz : ∀ j, raw40232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40232step0 = (fun i j => raw40232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40232step0 raw40232; decide +kernel
      have hl : raw40232step0Labels = raw40232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40232 raw40232Labels permutation434 hz
    mixedMoment B raw40232step0 raw40232step0Labels = mixedMoment B raw40232step1 raw40232step1Labels := by
      have ha : raw40232step1 = (fun i j => raw40232step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40232step1 raw40232step0; decide +kernel
      have hl : raw40232step1Labels = raw40232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40232step0 raw40232step0Labels permutation99 permutation6
    _ = mixedMoment B node450 node450Labels := by rfl

theorem canonical40233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40233 raw40233Labels = mixedMoment B node289 node289Labels := by
  calc
    mixedMoment B raw40233 raw40233Labels = mixedMoment B raw40233step0 raw40233step0Labels := by
      have hz : ∀ j, raw40233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40233step0 = (fun i j => raw40233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40233step0 raw40233; decide +kernel
      have hl : raw40233step0Labels = raw40233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40233 raw40233Labels permutation434 hz
    mixedMoment B raw40233step0 raw40233step0Labels = mixedMoment B raw40233step1 raw40233step1Labels := by
      have ha : raw40233step1 = (fun i j => raw40233step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40233step1 raw40233step0; decide +kernel
      have hl : raw40233step1Labels = raw40233step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40233step0 raw40233step0Labels permutation141 permutation7
    _ = mixedMoment B node289 node289Labels := by rfl

theorem canonical40234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40234 raw40234Labels = mixedMoment B node437 node437Labels := by
  calc
    mixedMoment B raw40234 raw40234Labels = mixedMoment B raw40234step0 raw40234step0Labels := by
      have hz : ∀ j, raw40234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40234step0 = (fun i j => raw40234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40234step0 raw40234; decide +kernel
      have hl : raw40234step0Labels = raw40234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40234 raw40234Labels permutation434 hz
    mixedMoment B raw40234step0 raw40234step0Labels = mixedMoment B raw40234step1 raw40234step1Labels := by
      have ha : raw40234step1 = (fun i j => raw40234step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40234step1 raw40234step0; decide +kernel
      have hl : raw40234step1Labels = raw40234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40234step0 raw40234step0Labels permutation93 permutation6
    _ = mixedMoment B node437 node437Labels := by rfl

theorem canonical40235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40235 raw40235Labels = mixedMoment B node423 node423Labels := by
  calc
    mixedMoment B raw40235 raw40235Labels = mixedMoment B raw40235step0 raw40235step0Labels := by
      have ha : raw40235step0 = (fun i j => raw40235 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40235step0 raw40235; decide +kernel
      have hl : raw40235step0Labels = raw40235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40235 raw40235Labels permutation409 permutation6
    _ = mixedMoment B node423 node423Labels := by rfl

theorem canonical40236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40236 raw40236Labels = mixedMoment B node472 node472Labels := by
  calc
    mixedMoment B raw40236 raw40236Labels = mixedMoment B raw40236step0 raw40236step0Labels := by
      have ha : raw40236step0 = (fun i j => raw40236 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40236step0 raw40236; decide +kernel
      have hl : raw40236step0Labels = raw40236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40236 raw40236Labels permutation639 permutation7
    _ = mixedMoment B node472 node472Labels := by rfl

theorem canonical40237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40237 raw40237Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40237 raw40237Labels = mixedMoment B raw40237step0 raw40237step0Labels := by
      have ha : raw40237step0 = (fun i j => raw40237 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40237step0 raw40237; decide +kernel
      have hl : raw40237step0Labels = raw40237Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40237 raw40237Labels permutation283 permutation7
    mixedMoment B raw40237step0 raw40237step0Labels = mixedMoment B raw40237step1 raw40237step1Labels := by
      have ha : raw40237step1 = -raw40237step0 := by apply Matrix.ext; change ∀ i j, raw40237step1 i j = -(raw40237step0 i j); unfold raw40237step1 raw40237step0; decide +kernel
      have hl : raw40237step1Labels = raw40237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node520 node520Labels := by rfl

theorem canonical40238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40238 raw40238Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw40238 raw40238Labels = mixedMoment B raw40238step0 raw40238step0Labels := by
      have hz : ∀ j, raw40238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40238step0 = (fun i j => raw40238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40238step0 raw40238; decide +kernel
      have hl : raw40238step0Labels = raw40238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40238 raw40238Labels permutation434 hz
    mixedMoment B raw40238step0 raw40238step0Labels = mixedMoment B raw40238step1 raw40238step1Labels := by
      have ha : raw40238step1 = (fun i j => raw40238step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40238step1 raw40238step0; decide +kernel
      have hl : raw40238step1Labels = raw40238step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40238step0 raw40238step0Labels permutation144 permutation7
    _ = mixedMoment B node336 node336Labels := by rfl

theorem canonical40239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40239 raw40239Labels = mixedMoment B node124 node124Labels := by
  calc
    mixedMoment B raw40239 raw40239Labels = mixedMoment B raw40239step0 raw40239step0Labels := by
      have hz : ∀ j, raw40239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40239step0 = (fun i j => raw40239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40239step0 raw40239; decide +kernel
      have hl : raw40239step0Labels = raw40239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40239 raw40239Labels permutation434 hz
    mixedMoment B raw40239step0 raw40239step0Labels = mixedMoment B raw40239step1 raw40239step1Labels := by
      have ha : raw40239step1 = (fun i j => raw40239step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40239step1 raw40239step0; decide +kernel
      have hl : raw40239step1Labels = raw40239step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40239step0 raw40239step0Labels permutation140 permutation6
    _ = mixedMoment B node124 node124Labels := by rfl

theorem canonical40240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40240 raw40240Labels = mixedMoment B node312 node312Labels := by
  calc
    mixedMoment B raw40240 raw40240Labels = mixedMoment B raw40240step0 raw40240step0Labels := by
      have hz : ∀ j, raw40240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40240step0 = (fun i j => raw40240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40240step0 raw40240; decide +kernel
      have hl : raw40240step0Labels = raw40240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40240 raw40240Labels permutation434 hz
    mixedMoment B raw40240step0 raw40240step0Labels = mixedMoment B raw40240step1 raw40240step1Labels := by
      have ha : raw40240step1 = (fun i j => raw40240step0 (permutation117 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40240step1 raw40240step0; decide +kernel
      have hl : raw40240step1Labels = raw40240step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40240step0 raw40240step0Labels permutation117 permutation6
    _ = mixedMoment B node312 node312Labels := by rfl

theorem canonical40241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40241 raw40241Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw40241 raw40241Labels = mixedMoment B raw40241step0 raw40241step0Labels := by
      have hz : ∀ j, raw40241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40241step0 = (fun i j => raw40241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40241step0 raw40241; decide +kernel
      have hl : raw40241step0Labels = raw40241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40241 raw40241Labels permutation434 hz
    mixedMoment B raw40241step0 raw40241step0Labels = mixedMoment B raw40241step1 raw40241step1Labels := by
      have ha : raw40241step1 = (fun i j => raw40241step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40241step1 raw40241step0; decide +kernel
      have hl : raw40241step1Labels = raw40241step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40241step0 raw40241step0Labels permutation120 permutation6
    _ = mixedMoment B node521 node521Labels := by rfl

theorem canonical40242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40242 raw40242Labels = mixedMoment B node517 node517Labels := by
  calc
    mixedMoment B raw40242 raw40242Labels = mixedMoment B raw40242step0 raw40242step0Labels := by
      have ha : raw40242step0 = (fun i j => raw40242 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40242step0 raw40242; decide +kernel
      have hl : raw40242step0Labels = raw40242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40242 raw40242Labels permutation548 permutation6
    _ = mixedMoment B node517 node517Labels := by rfl

theorem canonical40243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40243 raw40243Labels = mixedMoment B node293 node293Labels := by
  calc
    mixedMoment B raw40243 raw40243Labels = mixedMoment B raw40243step0 raw40243step0Labels := by
      have ha : raw40243step0 = (fun i j => raw40243 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40243step0 raw40243; decide +kernel
      have hl : raw40243step0Labels = raw40243Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40243 raw40243Labels permutation547 permutation6
    _ = mixedMoment B node293 node293Labels := by rfl

theorem canonical40244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40244 raw40244Labels = mixedMoment B node157 node157Labels := by
  calc
    mixedMoment B raw40244 raw40244Labels = mixedMoment B raw40244step0 raw40244step0Labels := by
      have hz : ∀ j, raw40244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40244step0 = (fun i j => raw40244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40244step0 raw40244; decide +kernel
      have hl : raw40244step0Labels = raw40244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40244 raw40244Labels permutation434 hz
    mixedMoment B raw40244step0 raw40244step0Labels = mixedMoment B raw40244step1 raw40244step1Labels := by
      have hz : ∀ j, raw40244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40244step1 = (fun i j => raw40244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40244step1 raw40244step0; decide +kernel
      have hl : raw40244step1Labels = raw40244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40244step0 raw40244step0Labels permutation80 hz
    mixedMoment B raw40244step1 raw40244step1Labels = mixedMoment B raw40244step2 raw40244step2Labels := by
      have ha : raw40244step2 = (fun i j => raw40244step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40244step2 raw40244step1; decide +kernel
      have hl : raw40244step2Labels = raw40244step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40244step1 raw40244step1Labels permutation27 permutation6
    _ = mixedMoment B node157 node157Labels := by rfl

theorem canonical40245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40245 raw40245Labels = mixedMoment B node30 node30Labels := by
  calc
    mixedMoment B raw40245 raw40245Labels = mixedMoment B raw40245step0 raw40245step0Labels := by
      have hz : ∀ j, raw40245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40245step0 = (fun i j => raw40245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40245step0 raw40245; decide +kernel
      have hl : raw40245step0Labels = raw40245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40245 raw40245Labels permutation434 hz
    mixedMoment B raw40245step0 raw40245step0Labels = mixedMoment B raw40245step1 raw40245step1Labels := by
      have hz : ∀ j, raw40245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40245step1 = (fun i j => raw40245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40245step1 raw40245step0; decide +kernel
      have hl : raw40245step1Labels = raw40245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40245step0 raw40245step0Labels permutation80 hz
    mixedMoment B raw40245step1 raw40245step1Labels = mixedMoment B raw40245step2 raw40245step2Labels := by
      have ha : raw40245step2 = (fun i j => raw40245step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40245step2 raw40245step1; decide +kernel
      have hl : raw40245step2Labels = raw40245step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40245step1 raw40245step1Labels permutation26 permutation6
    _ = mixedMoment B node30 node30Labels := by rfl

theorem canonical40246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40246 raw40246Labels = mixedMoment B node26 node26Labels := by
  calc
    mixedMoment B raw40246 raw40246Labels = mixedMoment B raw40246step0 raw40246step0Labels := by
      have hz : ∀ j, raw40246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40246step0 = (fun i j => raw40246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40246step0 raw40246; decide +kernel
      have hl : raw40246step0Labels = raw40246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40246 raw40246Labels permutation346 hz
    mixedMoment B raw40246step0 raw40246step0Labels = mixedMoment B raw40246step1 raw40246step1Labels := by
      have ha : raw40246step1 = (fun i j => raw40246step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40246step1 raw40246step0; decide +kernel
      have hl : raw40246step1Labels = raw40246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40246step0 raw40246step0Labels permutation131 permutation6
    _ = mixedMoment B node26 node26Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment768 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 768) =
      Integer.Sparse.eval keyMomentRow768 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 768).leftCharge (GramAssembly.key 768).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 334) := by
    have ha : gramCharges (GramAssembly.key 768).leftCharge (GramAssembly.key 768).rightCharge = raw40215 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40215Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40215 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 768).leftCharge (GramAssembly.key 768).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow768, Integer.Sparse.eval]

theorem keyMoment769 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 769) =
      Integer.Sparse.eval keyMomentRow769 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 769).leftCharge (GramAssembly.key 769).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 310) := by
    have ha : gramCharges (GramAssembly.key 769).leftCharge (GramAssembly.key 769).rightCharge = raw40216 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40216Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40216 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 769).leftCharge (GramAssembly.key 769).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow769, Integer.Sparse.eval]

theorem keyMoment770 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 770) =
      Integer.Sparse.eval keyMomentRow770 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 770).leftCharge (GramAssembly.key 770).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 770).leftCharge (GramAssembly.key 770).rightCharge = raw40217 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40217Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40217 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 770).leftCharge (GramAssembly.key 770).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow770, Integer.Sparse.eval]

theorem keyMoment771 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 771) =
      Integer.Sparse.eval keyMomentRow771 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 771).leftCharge (GramAssembly.key 771).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 301) := by
    have ha : gramCharges (GramAssembly.key 771).leftCharge (GramAssembly.key 771).rightCharge = raw40218 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40218Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40218 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 771).leftCharge (GramAssembly.key 771).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow771, Integer.Sparse.eval]

theorem keyMoment772 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 772) =
      Integer.Sparse.eval keyMomentRow772 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 772).leftCharge (GramAssembly.key 772).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 155) := by
    have ha : gramCharges (GramAssembly.key 772).leftCharge (GramAssembly.key 772).rightCharge = raw40219 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40219Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40219 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 772).leftCharge (GramAssembly.key 772).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow772, Integer.Sparse.eval]

theorem keyMoment773 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 773) =
      Integer.Sparse.eval keyMomentRow773 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 773).leftCharge (GramAssembly.key 773).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 22) := by
    have ha : gramCharges (GramAssembly.key 773).leftCharge (GramAssembly.key 773).rightCharge = raw40220 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40220Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40220 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 773).leftCharge (GramAssembly.key 773).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow773, Integer.Sparse.eval]

theorem keyMoment774 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 774) =
      Integer.Sparse.eval keyMomentRow774 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 774).leftCharge (GramAssembly.key 774).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 91) := by
    have ha : gramCharges (GramAssembly.key 774).leftCharge (GramAssembly.key 774).rightCharge = raw40221 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40221Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40221 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 774).leftCharge (GramAssembly.key 774).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow774, Integer.Sparse.eval]

theorem keyMoment775 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 775) =
      Integer.Sparse.eval keyMomentRow775 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 775).leftCharge (GramAssembly.key 775).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 775).leftCharge (GramAssembly.key 775).rightCharge = raw40222 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40222Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40222 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 775).leftCharge (GramAssembly.key 775).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow775, Integer.Sparse.eval]

theorem keyMoment776 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 776) =
      Integer.Sparse.eval keyMomentRow776 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 776).leftCharge (GramAssembly.key 776).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 245) := by
    have ha : gramCharges (GramAssembly.key 776).leftCharge (GramAssembly.key 776).rightCharge = raw40223 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40223Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40223 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 776).leftCharge (GramAssembly.key 776).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow776, Integer.Sparse.eval]

theorem keyMoment777 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 777) =
      Integer.Sparse.eval keyMomentRow777 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 777).leftCharge (GramAssembly.key 777).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 178) := by
    have ha : gramCharges (GramAssembly.key 777).leftCharge (GramAssembly.key 777).rightCharge = raw40224 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40224Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40224 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 777).leftCharge (GramAssembly.key 777).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow777, Integer.Sparse.eval]

theorem keyMoment778 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 778) =
      Integer.Sparse.eval keyMomentRow778 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 778).leftCharge (GramAssembly.key 778).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 234) := by
    have ha : gramCharges (GramAssembly.key 778).leftCharge (GramAssembly.key 778).rightCharge = raw40225 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40225Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40225 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 778).leftCharge (GramAssembly.key 778).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow778, Integer.Sparse.eval]

theorem keyMoment779 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 779) =
      Integer.Sparse.eval keyMomentRow779 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 779).leftCharge (GramAssembly.key 779).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 779).leftCharge (GramAssembly.key 779).rightCharge = raw40226 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40226Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40226 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 779).leftCharge (GramAssembly.key 779).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow779, Integer.Sparse.eval]

theorem keyMoment780 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 780) =
      Integer.Sparse.eval keyMomentRow780 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 780).leftCharge (GramAssembly.key 780).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 174) := by
    have ha : gramCharges (GramAssembly.key 780).leftCharge (GramAssembly.key 780).rightCharge = raw40227 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40227Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40227 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 780).leftCharge (GramAssembly.key 780).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow780, Integer.Sparse.eval]

theorem keyMoment781 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 781) =
      Integer.Sparse.eval keyMomentRow781 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 781).leftCharge (GramAssembly.key 781).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 221) := by
    have ha : gramCharges (GramAssembly.key 781).leftCharge (GramAssembly.key 781).rightCharge = raw40228 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40228Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40228 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 781).leftCharge (GramAssembly.key 781).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow781, Integer.Sparse.eval]

theorem keyMoment782 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 782) =
      Integer.Sparse.eval keyMomentRow782 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 782).leftCharge (GramAssembly.key 782).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 467) := by
    have ha : gramCharges (GramAssembly.key 782).leftCharge (GramAssembly.key 782).rightCharge = raw40229 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40229Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40229 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 782).leftCharge (GramAssembly.key 782).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow782, Integer.Sparse.eval]

theorem keyMoment783 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 783) =
      Integer.Sparse.eval keyMomentRow783 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 783).leftCharge (GramAssembly.key 783).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 424) := by
    have ha : gramCharges (GramAssembly.key 783).leftCharge (GramAssembly.key 783).rightCharge = raw40230 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40230Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40230 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 783).leftCharge (GramAssembly.key 783).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow783, Integer.Sparse.eval]

theorem keyMoment784 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 784) =
      Integer.Sparse.eval keyMomentRow784 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 784).leftCharge (GramAssembly.key 784).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 784).leftCharge (GramAssembly.key 784).rightCharge = raw40231 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40231Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40231 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 784).leftCharge (GramAssembly.key 784).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow784, Integer.Sparse.eval]

theorem keyMoment785 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 785) =
      Integer.Sparse.eval keyMomentRow785 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 785).leftCharge (GramAssembly.key 785).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 450) := by
    have ha : gramCharges (GramAssembly.key 785).leftCharge (GramAssembly.key 785).rightCharge = raw40232 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40232Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40232 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 785).leftCharge (GramAssembly.key 785).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow785, Integer.Sparse.eval]

theorem keyMoment786 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 786) =
      Integer.Sparse.eval keyMomentRow786 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 786).leftCharge (GramAssembly.key 786).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 289) := by
    have ha : gramCharges (GramAssembly.key 786).leftCharge (GramAssembly.key 786).rightCharge = raw40233 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40233Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40233 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 786).leftCharge (GramAssembly.key 786).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow786, Integer.Sparse.eval]

theorem keyMoment787 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 787) =
      Integer.Sparse.eval keyMomentRow787 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 787).leftCharge (GramAssembly.key 787).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 437) := by
    have ha : gramCharges (GramAssembly.key 787).leftCharge (GramAssembly.key 787).rightCharge = raw40234 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40234Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40234 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 787).leftCharge (GramAssembly.key 787).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow787, Integer.Sparse.eval]

theorem keyMoment788 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 788) =
      Integer.Sparse.eval keyMomentRow788 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 788).leftCharge (GramAssembly.key 788).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 423) := by
    have ha : gramCharges (GramAssembly.key 788).leftCharge (GramAssembly.key 788).rightCharge = raw40235 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40235Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40235 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 788).leftCharge (GramAssembly.key 788).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow788, Integer.Sparse.eval]

theorem keyMoment789 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 789) =
      Integer.Sparse.eval keyMomentRow789 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 789).leftCharge (GramAssembly.key 789).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 472) := by
    have ha : gramCharges (GramAssembly.key 789).leftCharge (GramAssembly.key 789).rightCharge = raw40236 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40236Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40236 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 789).leftCharge (GramAssembly.key 789).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow789, Integer.Sparse.eval]

theorem keyMoment790 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 790) =
      Integer.Sparse.eval keyMomentRow790 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 790).leftCharge (GramAssembly.key 790).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 790).leftCharge (GramAssembly.key 790).rightCharge = raw40237 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40237Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40237 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 790).leftCharge (GramAssembly.key 790).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow790, Integer.Sparse.eval]

theorem keyMoment791 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 791) =
      Integer.Sparse.eval keyMomentRow791 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 791).leftCharge (GramAssembly.key 791).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 336) := by
    have ha : gramCharges (GramAssembly.key 791).leftCharge (GramAssembly.key 791).rightCharge = raw40238 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40238Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40238 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 791).leftCharge (GramAssembly.key 791).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow791, Integer.Sparse.eval]

theorem keyMoment792 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 792) =
      Integer.Sparse.eval keyMomentRow792 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 792).leftCharge (GramAssembly.key 792).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 124) := by
    have ha : gramCharges (GramAssembly.key 792).leftCharge (GramAssembly.key 792).rightCharge = raw40239 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40239Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40239 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 792).leftCharge (GramAssembly.key 792).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow792, Integer.Sparse.eval]

theorem keyMoment793 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 793) =
      Integer.Sparse.eval keyMomentRow793 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 793).leftCharge (GramAssembly.key 793).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 312) := by
    have ha : gramCharges (GramAssembly.key 793).leftCharge (GramAssembly.key 793).rightCharge = raw40240 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40240Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40240 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 793).leftCharge (GramAssembly.key 793).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow793, Integer.Sparse.eval]

theorem keyMoment794 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 794) =
      Integer.Sparse.eval keyMomentRow794 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 794).leftCharge (GramAssembly.key 794).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 794).leftCharge (GramAssembly.key 794).rightCharge = raw40241 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40241Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40241 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 794).leftCharge (GramAssembly.key 794).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow794, Integer.Sparse.eval]

theorem keyMoment795 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 795) =
      Integer.Sparse.eval keyMomentRow795 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 795).leftCharge (GramAssembly.key 795).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 517) := by
    have ha : gramCharges (GramAssembly.key 795).leftCharge (GramAssembly.key 795).rightCharge = raw40242 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40242Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40242 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 795).leftCharge (GramAssembly.key 795).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow795, Integer.Sparse.eval]

theorem keyMoment796 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 796) =
      Integer.Sparse.eval keyMomentRow796 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 796).leftCharge (GramAssembly.key 796).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 293) := by
    have ha : gramCharges (GramAssembly.key 796).leftCharge (GramAssembly.key 796).rightCharge = raw40243 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40243Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40243 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 796).leftCharge (GramAssembly.key 796).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow796, Integer.Sparse.eval]

theorem keyMoment797 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 797) =
      Integer.Sparse.eval keyMomentRow797 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 797).leftCharge (GramAssembly.key 797).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 157) := by
    have ha : gramCharges (GramAssembly.key 797).leftCharge (GramAssembly.key 797).rightCharge = raw40244 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40244Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40244 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 797).leftCharge (GramAssembly.key 797).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow797, Integer.Sparse.eval]

theorem keyMoment798 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 798) =
      Integer.Sparse.eval keyMomentRow798 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 798).leftCharge (GramAssembly.key 798).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 30) := by
    have ha : gramCharges (GramAssembly.key 798).leftCharge (GramAssembly.key 798).rightCharge = raw40245 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40245Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40245 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 798).leftCharge (GramAssembly.key 798).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow798, Integer.Sparse.eval]

theorem keyMoment799 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 799) =
      Integer.Sparse.eval keyMomentRow799 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 799).leftCharge (GramAssembly.key 799).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 26) := by
    have ha : gramCharges (GramAssembly.key 799).leftCharge (GramAssembly.key 799).rightCharge = raw40246 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40246Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40246 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 799).leftCharge (GramAssembly.key 799).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow799, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt768 : keyMomentRows (768 : Fin 2886) =
    keyMomentRow768 := by decide +kernel

theorem keyMomentRowsAt769 : keyMomentRows (769 : Fin 2886) =
    keyMomentRow769 := by decide +kernel

theorem keyMomentRowsAt770 : keyMomentRows (770 : Fin 2886) =
    keyMomentRow770 := by decide +kernel

theorem keyMomentRowsAt771 : keyMomentRows (771 : Fin 2886) =
    keyMomentRow771 := by decide +kernel

theorem keyMomentRowsAt772 : keyMomentRows (772 : Fin 2886) =
    keyMomentRow772 := by decide +kernel

theorem keyMomentRowsAt773 : keyMomentRows (773 : Fin 2886) =
    keyMomentRow773 := by decide +kernel

theorem keyMomentRowsAt774 : keyMomentRows (774 : Fin 2886) =
    keyMomentRow774 := by decide +kernel

theorem keyMomentRowsAt775 : keyMomentRows (775 : Fin 2886) =
    keyMomentRow775 := by decide +kernel

theorem keyMomentRowsAt776 : keyMomentRows (776 : Fin 2886) =
    keyMomentRow776 := by decide +kernel

theorem keyMomentRowsAt777 : keyMomentRows (777 : Fin 2886) =
    keyMomentRow777 := by decide +kernel

theorem keyMomentRowsAt778 : keyMomentRows (778 : Fin 2886) =
    keyMomentRow778 := by decide +kernel

theorem keyMomentRowsAt779 : keyMomentRows (779 : Fin 2886) =
    keyMomentRow779 := by decide +kernel

theorem keyMomentRowsAt780 : keyMomentRows (780 : Fin 2886) =
    keyMomentRow780 := by decide +kernel

theorem keyMomentRowsAt781 : keyMomentRows (781 : Fin 2886) =
    keyMomentRow781 := by decide +kernel

theorem keyMomentRowsAt782 : keyMomentRows (782 : Fin 2886) =
    keyMomentRow782 := by decide +kernel

theorem keyMomentRowsAt783 : keyMomentRows (783 : Fin 2886) =
    keyMomentRow783 := by decide +kernel

theorem keyMomentRowsAt784 : keyMomentRows (784 : Fin 2886) =
    keyMomentRow784 := by decide +kernel

theorem keyMomentRowsAt785 : keyMomentRows (785 : Fin 2886) =
    keyMomentRow785 := by decide +kernel

theorem keyMomentRowsAt786 : keyMomentRows (786 : Fin 2886) =
    keyMomentRow786 := by decide +kernel

theorem keyMomentRowsAt787 : keyMomentRows (787 : Fin 2886) =
    keyMomentRow787 := by decide +kernel

theorem keyMomentRowsAt788 : keyMomentRows (788 : Fin 2886) =
    keyMomentRow788 := by decide +kernel

theorem keyMomentRowsAt789 : keyMomentRows (789 : Fin 2886) =
    keyMomentRow789 := by decide +kernel

theorem keyMomentRowsAt790 : keyMomentRows (790 : Fin 2886) =
    keyMomentRow790 := by decide +kernel

theorem keyMomentRowsAt791 : keyMomentRows (791 : Fin 2886) =
    keyMomentRow791 := by decide +kernel

theorem keyMomentRowsAt792 : keyMomentRows (792 : Fin 2886) =
    keyMomentRow792 := by decide +kernel

theorem keyMomentRowsAt793 : keyMomentRows (793 : Fin 2886) =
    keyMomentRow793 := by decide +kernel

theorem keyMomentRowsAt794 : keyMomentRows (794 : Fin 2886) =
    keyMomentRow794 := by decide +kernel

theorem keyMomentRowsAt795 : keyMomentRows (795 : Fin 2886) =
    keyMomentRow795 := by decide +kernel

theorem keyMomentRowsAt796 : keyMomentRows (796 : Fin 2886) =
    keyMomentRow796 := by decide +kernel

theorem keyMomentRowsAt797 : keyMomentRows (797 : Fin 2886) =
    keyMomentRow797 := by decide +kernel

theorem keyMomentRowsAt798 : keyMomentRows (798 : Fin 2886) =
    keyMomentRow798 := by decide +kernel

theorem keyMomentRowsAt799 : keyMomentRows (799 : Fin 2886) =
    keyMomentRow799 := by decide +kernel

theorem keyMomentChunkSound24_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 24) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 768 ∨ k.val = 769 ∨ k.val = 770 ∨ k.val = 771 ∨ k.val = 772 ∨ k.val = 773 ∨ k.val = 774 ∨ k.val = 775 ∨ k.val = 776 ∨ k.val = 777 ∨ k.val = 778 ∨ k.val = 779 ∨ k.val = 780 ∨ k.val = 781 ∨ k.val = 782 ∨ k.val = 783 ∨ k.val = 784 ∨ k.val = 785 ∨ k.val = 786 ∨ k.val = 787 ∨ k.val = 788 ∨ k.val = 789 ∨ k.val = 790 ∨ k.val = 791 ∨ k.val = 792 ∨ k.val = 793 ∨ k.val = 794 ∨ k.val = 795 ∨ k.val = 796 ∨ k.val = 797 ∨ k.val = 798 ∨ k.val = 799 := by omega
  rcases heq with h768 | h769 | h770 | h771 | h772 | h773 | h774 | h775 | h776 | h777 | h778 | h779 | h780 | h781 | h782 | h783 | h784 | h785 | h786 | h787 | h788 | h789 | h790 | h791 | h792 | h793 | h794 | h795 | h796 | h797 | h798 | h799
  · have he : k = (768 : Fin 2886) := Fin.ext h768
    subst k
    rw [keyMomentRowsAt768]
    exact keyMoment768 B hB
  · have he : k = (769 : Fin 2886) := Fin.ext h769
    subst k
    rw [keyMomentRowsAt769]
    exact keyMoment769 B hB
  · have he : k = (770 : Fin 2886) := Fin.ext h770
    subst k
    rw [keyMomentRowsAt770]
    exact keyMoment770 B hB
  · have he : k = (771 : Fin 2886) := Fin.ext h771
    subst k
    rw [keyMomentRowsAt771]
    exact keyMoment771 B hB
  · have he : k = (772 : Fin 2886) := Fin.ext h772
    subst k
    rw [keyMomentRowsAt772]
    exact keyMoment772 B hB
  · have he : k = (773 : Fin 2886) := Fin.ext h773
    subst k
    rw [keyMomentRowsAt773]
    exact keyMoment773 B hB
  · have he : k = (774 : Fin 2886) := Fin.ext h774
    subst k
    rw [keyMomentRowsAt774]
    exact keyMoment774 B hB
  · have he : k = (775 : Fin 2886) := Fin.ext h775
    subst k
    rw [keyMomentRowsAt775]
    exact keyMoment775 B hB
  · have he : k = (776 : Fin 2886) := Fin.ext h776
    subst k
    rw [keyMomentRowsAt776]
    exact keyMoment776 B hB
  · have he : k = (777 : Fin 2886) := Fin.ext h777
    subst k
    rw [keyMomentRowsAt777]
    exact keyMoment777 B hB
  · have he : k = (778 : Fin 2886) := Fin.ext h778
    subst k
    rw [keyMomentRowsAt778]
    exact keyMoment778 B hB
  · have he : k = (779 : Fin 2886) := Fin.ext h779
    subst k
    rw [keyMomentRowsAt779]
    exact keyMoment779 B hB
  · have he : k = (780 : Fin 2886) := Fin.ext h780
    subst k
    rw [keyMomentRowsAt780]
    exact keyMoment780 B hB
  · have he : k = (781 : Fin 2886) := Fin.ext h781
    subst k
    rw [keyMomentRowsAt781]
    exact keyMoment781 B hB
  · have he : k = (782 : Fin 2886) := Fin.ext h782
    subst k
    rw [keyMomentRowsAt782]
    exact keyMoment782 B hB
  · have he : k = (783 : Fin 2886) := Fin.ext h783
    subst k
    rw [keyMomentRowsAt783]
    exact keyMoment783 B hB
  · have he : k = (784 : Fin 2886) := Fin.ext h784
    subst k
    rw [keyMomentRowsAt784]
    exact keyMoment784 B hB
  · have he : k = (785 : Fin 2886) := Fin.ext h785
    subst k
    rw [keyMomentRowsAt785]
    exact keyMoment785 B hB
  · have he : k = (786 : Fin 2886) := Fin.ext h786
    subst k
    rw [keyMomentRowsAt786]
    exact keyMoment786 B hB
  · have he : k = (787 : Fin 2886) := Fin.ext h787
    subst k
    rw [keyMomentRowsAt787]
    exact keyMoment787 B hB
  · have he : k = (788 : Fin 2886) := Fin.ext h788
    subst k
    rw [keyMomentRowsAt788]
    exact keyMoment788 B hB
  · have he : k = (789 : Fin 2886) := Fin.ext h789
    subst k
    rw [keyMomentRowsAt789]
    exact keyMoment789 B hB
  · have he : k = (790 : Fin 2886) := Fin.ext h790
    subst k
    rw [keyMomentRowsAt790]
    exact keyMoment790 B hB
  · have he : k = (791 : Fin 2886) := Fin.ext h791
    subst k
    rw [keyMomentRowsAt791]
    exact keyMoment791 B hB
  · have he : k = (792 : Fin 2886) := Fin.ext h792
    subst k
    rw [keyMomentRowsAt792]
    exact keyMoment792 B hB
  · have he : k = (793 : Fin 2886) := Fin.ext h793
    subst k
    rw [keyMomentRowsAt793]
    exact keyMoment793 B hB
  · have he : k = (794 : Fin 2886) := Fin.ext h794
    subst k
    rw [keyMomentRowsAt794]
    exact keyMoment794 B hB
  · have he : k = (795 : Fin 2886) := Fin.ext h795
    subst k
    rw [keyMomentRowsAt795]
    exact keyMoment795 B hB
  · have he : k = (796 : Fin 2886) := Fin.ext h796
    subst k
    rw [keyMomentRowsAt796]
    exact keyMoment796 B hB
  · have he : k = (797 : Fin 2886) := Fin.ext h797
    subst k
    rw [keyMomentRowsAt797]
    exact keyMoment797 B hB
  · have he : k = (798 : Fin 2886) := Fin.ext h798
    subst k
    rw [keyMomentRowsAt798]
    exact keyMoment798 B hB
  · have he : k = (799 : Fin 2886) := Fin.ext h799
    subst k
    rw [keyMomentRowsAt799]
    exact keyMoment799 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound24_e_oai
