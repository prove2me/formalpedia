-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:24.177353+00:00
-- url     : https://prove2.me/submissions/e8c95a7c-f4e2-4c32-a6d2-734ad5d5999d

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40152 raw40152Labels = mixedMoment B node532 node532Labels := by
  calc
    mixedMoment B raw40152 raw40152Labels = mixedMoment B raw40152step0 raw40152step0Labels := by
      have hz : ∀ j, raw40152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40152step0 = (fun i j => raw40152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40152step0 raw40152; decide +kernel
      have hl : raw40152step0Labels = raw40152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40152 raw40152Labels permutation434 hz
    mixedMoment B raw40152step0 raw40152step0Labels = mixedMoment B raw40152step1 raw40152step1Labels := by
      have ha : raw40152step1 = (fun i j => raw40152step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40152step1 raw40152step0; decide +kernel
      have hl : raw40152step1Labels = raw40152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40152step0 raw40152step0Labels permutation127 permutation3
    mixedMoment B raw40152step1 raw40152step1Labels = mixedMoment B raw40152step2 raw40152step2Labels := by
      have ha : raw40152step2 = -raw40152step1 := by apply Matrix.ext; change ∀ i j, raw40152step2 i j = -(raw40152step1 i j); unfold raw40152step2 raw40152step1; decide +kernel
      have hl : raw40152step2Labels = raw40152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node532 node532Labels := by rfl

theorem canonical40153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40153 raw40153Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw40153 raw40153Labels = mixedMoment B raw40153step0 raw40153step0Labels := by
      have ha : raw40153step0 = (fun i j => raw40153 (permutation626 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40153step0 raw40153; decide +kernel
      have hl : raw40153step0Labels = raw40153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40153 raw40153Labels permutation626 permutation7
    _ = mixedMoment B node488 node488Labels := by rfl

theorem canonical40154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40154 raw40154Labels = mixedMoment B node326 node326Labels := by
  calc
    mixedMoment B raw40154 raw40154Labels = mixedMoment B raw40154step0 raw40154step0Labels := by
      have ha : raw40154step0 = (fun i j => raw40154 (permutation625 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40154step0 raw40154; decide +kernel
      have hl : raw40154step0Labels = raw40154Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40154 raw40154Labels permutation625 permutation7
    _ = mixedMoment B node326 node326Labels := by rfl

theorem canonical40155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40155 raw40155Labels = mixedMoment B node533 node533Labels := by
  calc
    mixedMoment B raw40155 raw40155Labels = mixedMoment B raw40155step0 raw40155step0Labels := by
      have ha : raw40155step0 = (fun i j => raw40155 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40155step0 raw40155; decide +kernel
      have hl : raw40155step0Labels = raw40155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40155 raw40155Labels permutation272 permutation2
    _ = mixedMoment B node533 node533Labels := by rfl

theorem canonical40156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40156 raw40156Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40156 raw40156Labels = mixedMoment B raw40156step0 raw40156step0Labels := by
      have ha : raw40156step0 = (fun i j => raw40156 (permutation464 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40156step0 raw40156; decide +kernel
      have hl : raw40156step0Labels = raw40156Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40156 raw40156Labels permutation464 permutation6
    mixedMoment B raw40156step0 raw40156step0Labels = mixedMoment B raw40156step1 raw40156step1Labels := by
      have ha : raw40156step1 = -raw40156step0 := by apply Matrix.ext; change ∀ i j, raw40156step1 i j = -(raw40156step0 i j); unfold raw40156step1 raw40156step0; decide +kernel
      have hl : raw40156step1Labels = raw40156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

theorem canonical40157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40157 raw40157Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw40157 raw40157Labels = mixedMoment B raw40157step0 raw40157step0Labels := by
      have hz : ∀ j, raw40157 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40157step0 = (fun i j => raw40157 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40157step0 raw40157; decide +kernel
      have hl : raw40157step0Labels = raw40157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40157 raw40157Labels permutation434 hz
    mixedMoment B raw40157step0 raw40157step0Labels = mixedMoment B raw40157step1 raw40157step1Labels := by
      have hz : ∀ j, raw40157step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40157step1 = (fun i j => raw40157step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40157step1 raw40157step0; decide +kernel
      have hl : raw40157step1Labels = raw40157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40157step0 raw40157step0Labels permutation80 hz
    mixedMoment B raw40157step1 raw40157step1Labels = mixedMoment B raw40157step2 raw40157step2Labels := by
      have ha : raw40157step2 = (fun i j => raw40157step1 (permutation26 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40157step2 raw40157step1; decide +kernel
      have hl : raw40157step2Labels = raw40157step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40157step1 raw40157step1Labels permutation26 permutation7
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical40158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40158 raw40158Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw40158 raw40158Labels = mixedMoment B raw40158step0 raw40158step0Labels := by
      have hz : ∀ j, raw40158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40158step0 = (fun i j => raw40158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40158step0 raw40158; decide +kernel
      have hl : raw40158step0Labels = raw40158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40158 raw40158Labels permutation346 hz
    mixedMoment B raw40158step0 raw40158step0Labels = mixedMoment B raw40158step1 raw40158step1Labels := by
      have ha : raw40158step1 = (fun i j => raw40158step0 (permutation131 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40158step1 raw40158step0; decide +kernel
      have hl : raw40158step1Labels = raw40158step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40158step0 raw40158step0Labels permutation131 permutation7
    _ = mixedMoment B node403 node403Labels := by rfl

theorem canonical40159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40159 raw40159Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40159 raw40159Labels = mixedMoment B raw40159step0 raw40159step0Labels := by
      have hz : ∀ j, raw40159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40159step0 = (fun i j => raw40159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40159step0 raw40159; decide +kernel
      have hl : raw40159step0Labels = raw40159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40159 raw40159Labels permutation346 hz
    mixedMoment B raw40159step0 raw40159step0Labels = mixedMoment B raw40159step1 raw40159step1Labels := by
      have ha : raw40159step1 = (fun i j => raw40159step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40159step1 raw40159step0; decide +kernel
      have hl : raw40159step1Labels = raw40159step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40159step0 raw40159step0Labels permutation104 permutation6
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical40160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40160 raw40160Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw40160 raw40160Labels = mixedMoment B raw40160step0 raw40160step0Labels := by
      have hz : ∀ j, raw40160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40160step0 = (fun i j => raw40160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40160step0 raw40160; decide +kernel
      have hl : raw40160step0Labels = raw40160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40160 raw40160Labels permutation346 hz
    mixedMoment B raw40160step0 raw40160step0Labels = mixedMoment B raw40160step1 raw40160step1Labels := by
      have ha : raw40160step1 = (fun i j => raw40160step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40160step1 raw40160step0; decide +kernel
      have hl : raw40160step1Labels = raw40160step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40160step0 raw40160step0Labels permutation108 permutation6
    _ = mixedMoment B node526 node526Labels := by rfl

theorem canonical40161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40161 raw40161Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw40161 raw40161Labels = mixedMoment B raw40161step0 raw40161step0Labels := by
      have hz : ∀ j, raw40161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40161step0 = (fun i j => raw40161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40161step0 raw40161; decide +kernel
      have hl : raw40161step0Labels = raw40161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40161 raw40161Labels permutation346 hz
    mixedMoment B raw40161step0 raw40161step0Labels = mixedMoment B raw40161step1 raw40161step1Labels := by
      have ha : raw40161step1 = (fun i j => raw40161step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40161step1 raw40161step0; decide +kernel
      have hl : raw40161step1Labels = raw40161step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40161step0 raw40161step0Labels permutation108 permutation6
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical40162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40162 raw40162Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40162 raw40162Labels = mixedMoment B raw40162step0 raw40162step0Labels := by
      have ha : raw40162step0 = (fun i j => raw40162 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40162step0 raw40162; decide +kernel
      have hl : raw40162step0Labels = raw40162Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40162 raw40162Labels permutation572 permutation7
    _ = mixedMoment B node520 node520Labels := by rfl

theorem canonical40163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40163 raw40163Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw40163 raw40163Labels = mixedMoment B raw40163step0 raw40163step0Labels := by
      have hz : ∀ j, raw40163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40163step0 = (fun i j => raw40163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40163step0 raw40163; decide +kernel
      have hl : raw40163step0Labels = raw40163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40163 raw40163Labels permutation520 hz
    mixedMoment B raw40163step0 raw40163step0Labels = mixedMoment B raw40163step1 raw40163step1Labels := by
      have hz : ∀ j, raw40163step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40163step1 = (fun i j => raw40163step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40163step1 raw40163step0; decide +kernel
      have hl : raw40163step1Labels = raw40163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40163step0 raw40163step0Labels permutation104 hz
    mixedMoment B raw40163step1 raw40163step1Labels = mixedMoment B raw40163step2 raw40163step2Labels := by
      have ha : raw40163step2 = (fun i j => raw40163step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40163step2 raw40163step1; decide +kernel
      have hl : raw40163step2Labels = raw40163step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40163step1 raw40163step1Labels permutation20 permutation4
    mixedMoment B raw40163step2 raw40163step2Labels = mixedMoment B raw40163step3 raw40163step3Labels := by
      have ha : raw40163step3 = -raw40163step2 := by apply Matrix.ext; change ∀ i j, raw40163step3 i j = -(raw40163step2 i j); unfold raw40163step3 raw40163step2; decide +kernel
      have hl : raw40163step3Labels = raw40163step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical40164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40164 raw40164Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw40164 raw40164Labels = mixedMoment B raw40164step0 raw40164step0Labels := by
      have hz : ∀ j, raw40164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40164step0 = (fun i j => raw40164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40164step0 raw40164; decide +kernel
      have hl : raw40164step0Labels = raw40164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40164 raw40164Labels permutation434 hz
    mixedMoment B raw40164step0 raw40164step0Labels = mixedMoment B raw40164step1 raw40164step1Labels := by
      have ha : raw40164step1 = (fun i j => raw40164step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40164step1 raw40164step0; decide +kernel
      have hl : raw40164step1Labels = raw40164step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40164step0 raw40164step0Labels permutation111 permutation6
    mixedMoment B raw40164step1 raw40164step1Labels = mixedMoment B raw40164step2 raw40164step2Labels := by
      have ha : raw40164step2 = -raw40164step1 := by apply Matrix.ext; change ∀ i j, raw40164step2 i j = -(raw40164step1 i j); unfold raw40164step2 raw40164step1; decide +kernel
      have hl : raw40164step2Labels = raw40164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node432 node432Labels := by rfl

theorem canonical40165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40165 raw40165Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw40165 raw40165Labels = mixedMoment B raw40165step0 raw40165step0Labels := by
      have hz : ∀ j, raw40165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40165step0 = (fun i j => raw40165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40165step0 raw40165; decide +kernel
      have hl : raw40165step0Labels = raw40165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40165 raw40165Labels permutation434 hz
    mixedMoment B raw40165step0 raw40165step0Labels = mixedMoment B raw40165step1 raw40165step1Labels := by
      have ha : raw40165step1 = (fun i j => raw40165step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40165step1 raw40165step0; decide +kernel
      have hl : raw40165step1Labels = raw40165step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40165step0 raw40165step0Labels permutation82 permutation4
    mixedMoment B raw40165step1 raw40165step1Labels = mixedMoment B raw40165step2 raw40165step2Labels := by
      have ha : raw40165step2 = -raw40165step1 := by apply Matrix.ext; change ∀ i j, raw40165step2 i j = -(raw40165step1 i j); unfold raw40165step2 raw40165step1; decide +kernel
      have hl : raw40165step2Labels = raw40165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

theorem canonical40166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40166 raw40166Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw40166 raw40166Labels = mixedMoment B raw40166step0 raw40166step0Labels := by
      have ha : raw40166step0 = (fun i j => raw40166 (permutation454 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40166step0 raw40166; decide +kernel
      have hl : raw40166step0Labels = raw40166Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40166 raw40166Labels permutation454 permutation6
    mixedMoment B raw40166step0 raw40166step0Labels = mixedMoment B raw40166step1 raw40166step1Labels := by
      have ha : raw40166step1 = -raw40166step0 := by apply Matrix.ext; change ∀ i j, raw40166step1 i j = -(raw40166step0 i j); unfold raw40166step1 raw40166step0; decide +kernel
      have hl : raw40166step1Labels = raw40166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node429 node429Labels := by rfl

theorem canonical40167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40167 raw40167Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw40167 raw40167Labels = mixedMoment B raw40167step0 raw40167step0Labels := by
      have hz : ∀ j, raw40167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40167step0 = (fun i j => raw40167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40167step0 raw40167; decide +kernel
      have hl : raw40167step0Labels = raw40167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40167 raw40167Labels permutation434 hz
    mixedMoment B raw40167step0 raw40167step0Labels = mixedMoment B raw40167step1 raw40167step1Labels := by
      have ha : raw40167step1 = (fun i j => raw40167step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40167step1 raw40167step0; decide +kernel
      have hl : raw40167step1Labels = raw40167step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40167step0 raw40167step0Labels permutation141 permutation7
    _ = mixedMoment B node489 node489Labels := by rfl

theorem canonical40168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40168 raw40168Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw40168 raw40168Labels = mixedMoment B raw40168step0 raw40168step0Labels := by
      have hz : ∀ j, raw40168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40168step0 = (fun i j => raw40168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40168step0 raw40168; decide +kernel
      have hl : raw40168step0Labels = raw40168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40168 raw40168Labels permutation434 hz
    mixedMoment B raw40168step0 raw40168step0Labels = mixedMoment B raw40168step1 raw40168step1Labels := by
      have ha : raw40168step1 = (fun i j => raw40168step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40168step1 raw40168step0; decide +kernel
      have hl : raw40168step1Labels = raw40168step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40168step0 raw40168step0Labels permutation75 permutation6
    mixedMoment B raw40168step1 raw40168step1Labels = mixedMoment B raw40168step2 raw40168step2Labels := by
      have ha : raw40168step2 = -raw40168step1 := by apply Matrix.ext; change ∀ i j, raw40168step2 i j = -(raw40168step1 i j); unfold raw40168step2 raw40168step1; decide +kernel
      have hl : raw40168step2Labels = raw40168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node526 node526Labels := by rfl

theorem canonical40169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40169 raw40169Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40169 raw40169Labels = mixedMoment B raw40169step0 raw40169step0Labels := by
      have ha : raw40169step0 = (fun i j => raw40169 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40169step0 raw40169; decide +kernel
      have hl : raw40169step0Labels = raw40169Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40169 raw40169Labels permutation308 permutation6
    mixedMoment B raw40169step0 raw40169step0Labels = mixedMoment B raw40169step1 raw40169step1Labels := by
      have ha : raw40169step1 = -raw40169step0 := by apply Matrix.ext; change ∀ i j, raw40169step1 i j = -(raw40169step0 i j); unfold raw40169step1 raw40169step0; decide +kernel
      have hl : raw40169step1Labels = raw40169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node520 node520Labels := by rfl

theorem canonical40170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40170 raw40170Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw40170 raw40170Labels = mixedMoment B raw40170step0 raw40170step0Labels := by
      have hz : ∀ j, raw40170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40170step0 = (fun i j => raw40170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40170step0 raw40170; decide +kernel
      have hl : raw40170step0Labels = raw40170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40170 raw40170Labels permutation434 hz
    mixedMoment B raw40170step0 raw40170step0Labels = mixedMoment B raw40170step1 raw40170step1Labels := by
      have hz : ∀ j, raw40170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40170step1 = (fun i j => raw40170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40170step1 raw40170step0; decide +kernel
      have hl : raw40170step1Labels = raw40170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40170step0 raw40170step0Labels permutation80 hz
    mixedMoment B raw40170step1 raw40170step1Labels = mixedMoment B raw40170step2 raw40170step2Labels := by
      have ha : raw40170step2 = (fun i j => raw40170step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40170step2 raw40170step1; decide +kernel
      have hl : raw40170step2Labels = raw40170step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40170step1 raw40170step1Labels permutation27 permutation7
    _ = mixedMoment B node404 node404Labels := by rfl

theorem canonical40171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40171 raw40171Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw40171 raw40171Labels = mixedMoment B raw40171step0 raw40171step0Labels := by
      have hz : ∀ j, raw40171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40171step0 = (fun i j => raw40171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40171step0 raw40171; decide +kernel
      have hl : raw40171step0Labels = raw40171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40171 raw40171Labels permutation434 hz
    mixedMoment B raw40171step0 raw40171step0Labels = mixedMoment B raw40171step1 raw40171step1Labels := by
      have hz : ∀ j, raw40171step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40171step1 = (fun i j => raw40171step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40171step1 raw40171step0; decide +kernel
      have hl : raw40171step1Labels = raw40171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40171step0 raw40171step0Labels permutation80 hz
    mixedMoment B raw40171step1 raw40171step1Labels = mixedMoment B raw40171step2 raw40171step2Labels := by
      have ha : raw40171step2 = (fun i j => raw40171step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40171step2 raw40171step1; decide +kernel
      have hl : raw40171step2Labels = raw40171step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40171step1 raw40171step1Labels permutation26 permutation6
    _ = mixedMoment B node149 node149Labels := by rfl

theorem canonical40172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40172 raw40172Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw40172 raw40172Labels = mixedMoment B raw40172step0 raw40172step0Labels := by
      have hz : ∀ j, raw40172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40172step0 = (fun i j => raw40172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40172step0 raw40172; decide +kernel
      have hl : raw40172step0Labels = raw40172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40172 raw40172Labels permutation434 hz
    mixedMoment B raw40172step0 raw40172step0Labels = mixedMoment B raw40172step1 raw40172step1Labels := by
      have hz : ∀ j, raw40172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40172step1 = (fun i j => raw40172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40172step1 raw40172step0; decide +kernel
      have hl : raw40172step1Labels = raw40172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40172step0 raw40172step0Labels permutation80 hz
    mixedMoment B raw40172step1 raw40172step1Labels = mixedMoment B raw40172step2 raw40172step2Labels := by
      have ha : raw40172step2 = (fun i j => raw40172step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40172step2 raw40172step1; decide +kernel
      have hl : raw40172step2Labels = raw40172step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40172step1 raw40172step1Labels permutation21 permutation6
    _ = mixedMoment B node390 node390Labels := by rfl

theorem canonical40173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40173 raw40173Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw40173 raw40173Labels = mixedMoment B raw40173step0 raw40173step0Labels := by
      have hz : ∀ j, raw40173 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40173step0 = (fun i j => raw40173 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40173step0 raw40173; decide +kernel
      have hl : raw40173step0Labels = raw40173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40173 raw40173Labels permutation434 hz
    mixedMoment B raw40173step0 raw40173step0Labels = mixedMoment B raw40173step1 raw40173step1Labels := by
      have hz : ∀ j, raw40173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40173step1 = (fun i j => raw40173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40173step1 raw40173step0; decide +kernel
      have hl : raw40173step1Labels = raw40173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40173step0 raw40173step0Labels permutation80 hz
    mixedMoment B raw40173step1 raw40173step1Labels = mixedMoment B raw40173step2 raw40173step2Labels := by
      have ha : raw40173step2 = (fun i j => raw40173step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40173step2 raw40173step1; decide +kernel
      have hl : raw40173step2Labels = raw40173step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40173step1 raw40173step1Labels permutation21 permutation6
    _ = mixedMoment B node527 node527Labels := by rfl

theorem canonical40174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40174 raw40174Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw40174 raw40174Labels = mixedMoment B raw40174step0 raw40174step0Labels := by
      have hz : ∀ j, raw40174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40174step0 = (fun i j => raw40174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40174step0 raw40174; decide +kernel
      have hl : raw40174step0Labels = raw40174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40174 raw40174Labels permutation346 hz
    mixedMoment B raw40174step0 raw40174step0Labels = mixedMoment B raw40174step1 raw40174step1Labels := by
      have ha : raw40174step1 = (fun i j => raw40174step0 (permutation63 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40174step1 raw40174step0; decide +kernel
      have hl : raw40174step1Labels = raw40174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40174step0 raw40174step0Labels permutation63 permutation6
    mixedMoment B raw40174step1 raw40174step1Labels = mixedMoment B raw40174step2 raw40174step2Labels := by
      have ha : raw40174step2 = -raw40174step1 := by apply Matrix.ext; change ∀ i j, raw40174step2 i j = -(raw40174step1 i j); unfold raw40174step2 raw40174step1; decide +kernel
      have hl : raw40174step2Labels = raw40174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node521 node521Labels := by rfl

theorem canonical40175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40175 raw40175Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw40175 raw40175Labels = mixedMoment B raw40175step0 raw40175step0Labels := by
      have hz : ∀ j, raw40175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40175step0 = (fun i j => raw40175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40175step0 raw40175; decide +kernel
      have hl : raw40175step0Labels = raw40175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40175 raw40175Labels permutation346 hz
    mixedMoment B raw40175step0 raw40175step0Labels = mixedMoment B raw40175step1 raw40175step1Labels := by
      have ha : raw40175step1 = (fun i j => raw40175step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40175step1 raw40175step0; decide +kernel
      have hl : raw40175step1Labels = raw40175step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40175step0 raw40175step0Labels permutation122 permutation6
    _ = mixedMoment B node325 node325Labels := by rfl

theorem canonical40176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40176 raw40176Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw40176 raw40176Labels = mixedMoment B raw40176step0 raw40176step0Labels := by
      have hz : ∀ j, raw40176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40176step0 = (fun i j => raw40176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40176step0 raw40176; decide +kernel
      have hl : raw40176step0Labels = raw40176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40176 raw40176Labels permutation520 hz
    mixedMoment B raw40176step0 raw40176step0Labels = mixedMoment B raw40176step1 raw40176step1Labels := by
      have hz : ∀ j, raw40176step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40176step1 = (fun i j => raw40176step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40176step1 raw40176step0; decide +kernel
      have hl : raw40176step1Labels = raw40176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40176step0 raw40176step0Labels permutation104 hz
    mixedMoment B raw40176step1 raw40176step1Labels = mixedMoment B raw40176step2 raw40176step2Labels := by
      have ha : raw40176step2 = (fun i j => raw40176step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40176step2 raw40176step1; decide +kernel
      have hl : raw40176step2Labels = raw40176step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40176step1 raw40176step1Labels permutation15 permutation6
    mixedMoment B raw40176step2 raw40176step2Labels = mixedMoment B raw40176step3 raw40176step3Labels := by
      have ha : raw40176step3 = -raw40176step2 := by apply Matrix.ext; change ∀ i j, raw40176step3 i j = -(raw40176step2 i j); unfold raw40176step3 raw40176step2; decide +kernel
      have hl : raw40176step3Labels = raw40176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical40177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40177 raw40177Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw40177 raw40177Labels = mixedMoment B raw40177step0 raw40177step0Labels := by
      have hz : ∀ j, raw40177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40177step0 = (fun i j => raw40177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40177step0 raw40177; decide +kernel
      have hl : raw40177step0Labels = raw40177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40177 raw40177Labels permutation434 hz
    mixedMoment B raw40177step0 raw40177step0Labels = mixedMoment B raw40177step1 raw40177step1Labels := by
      have ha : raw40177step1 = (fun i j => raw40177step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40177step1 raw40177step0; decide +kernel
      have hl : raw40177step1Labels = raw40177step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40177step0 raw40177step0Labels permutation69 permutation6
    mixedMoment B raw40177step1 raw40177step1Labels = mixedMoment B raw40177step2 raw40177step2Labels := by
      have ha : raw40177step2 = -raw40177step1 := by apply Matrix.ext; change ∀ i j, raw40177step2 i j = -(raw40177step1 i j); unfold raw40177step2 raw40177step1; decide +kernel
      have hl : raw40177step2Labels = raw40177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node306 node306Labels := by rfl

theorem canonical40178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40178 raw40178Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw40178 raw40178Labels = mixedMoment B raw40178step0 raw40178step0Labels := by
      have hz : ∀ j, raw40178 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40178step0 = (fun i j => raw40178 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40178step0 raw40178; decide +kernel
      have hl : raw40178step0Labels = raw40178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40178 raw40178Labels permutation434 hz
    mixedMoment B raw40178step0 raw40178step0Labels = mixedMoment B raw40178step1 raw40178step1Labels := by
      have ha : raw40178step1 = (fun i j => raw40178step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40178step1 raw40178step0; decide +kernel
      have hl : raw40178step1Labels = raw40178step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40178step0 raw40178step0Labels permutation75 permutation6
    mixedMoment B raw40178step1 raw40178step1Labels = mixedMoment B raw40178step2 raw40178step2Labels := by
      have ha : raw40178step2 = -raw40178step1 := by apply Matrix.ext; change ∀ i j, raw40178step2 i j = -(raw40178step1 i j); unfold raw40178step2 raw40178step1; decide +kernel
      have hl : raw40178step2Labels = raw40178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical40179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40179 raw40179Labels = mixedMoment B node301 node301Labels := by
  calc
    mixedMoment B raw40179 raw40179Labels = mixedMoment B raw40179step0 raw40179step0Labels := by
      have ha : raw40179step0 = (fun i j => raw40179 (permutation308 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40179step0 raw40179; decide +kernel
      have hl : raw40179step0Labels = raw40179Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40179 raw40179Labels permutation308 permutation6
    mixedMoment B raw40179step0 raw40179step0Labels = mixedMoment B raw40179step1 raw40179step1Labels := by
      have ha : raw40179step1 = -raw40179step0 := by apply Matrix.ext; change ∀ i j, raw40179step1 i j = -(raw40179step0 i j); unfold raw40179step1 raw40179step0; decide +kernel
      have hl : raw40179step1Labels = raw40179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node301 node301Labels := by rfl

theorem canonical40180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40180 raw40180Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw40180 raw40180Labels = mixedMoment B raw40180step0 raw40180step0Labels := by
      have ha : raw40180step0 = (fun i j => raw40180 (permutation337 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40180step0 raw40180; decide +kernel
      have hl : raw40180step0Labels = raw40180Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40180 raw40180Labels permutation337 permutation6
    mixedMoment B raw40180step0 raw40180step0Labels = mixedMoment B raw40180step1 raw40180step1Labels := by
      have ha : raw40180step1 = -raw40180step0 := by apply Matrix.ext; change ∀ i j, raw40180step1 i j = -(raw40180step0 i j); unfold raw40180step1 raw40180step0; decide +kernel
      have hl : raw40180step1Labels = raw40180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node376 node376Labels := by rfl

theorem canonical40181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40181 raw40181Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw40181 raw40181Labels = mixedMoment B raw40181step0 raw40181step0Labels := by
      have hz : ∀ j, raw40181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40181step0 = (fun i j => raw40181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40181step0 raw40181; decide +kernel
      have hl : raw40181step0Labels = raw40181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40181 raw40181Labels permutation520 hz
    mixedMoment B raw40181step0 raw40181step0Labels = mixedMoment B raw40181step1 raw40181step1Labels := by
      have hz : ∀ j, raw40181step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40181step1 = (fun i j => raw40181step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40181step1 raw40181step0; decide +kernel
      have hl : raw40181step1Labels = raw40181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40181step0 raw40181step0Labels permutation104 hz
    mixedMoment B raw40181step1 raw40181step1Labels = mixedMoment B raw40181step2 raw40181step2Labels := by
      have ha : raw40181step2 = (fun i j => raw40181step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40181step2 raw40181step1; decide +kernel
      have hl : raw40181step2Labels = raw40181step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40181step1 raw40181step1Labels permutation14 permutation6
    mixedMoment B raw40181step2 raw40181step2Labels = mixedMoment B raw40181step3 raw40181step3Labels := by
      have ha : raw40181step3 = -raw40181step2 := by apply Matrix.ext; change ∀ i j, raw40181step3 i j = -(raw40181step2 i j); unfold raw40181step3 raw40181step2; decide +kernel
      have hl : raw40181step3Labels = raw40181step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical40182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40182 raw40182Labels = mixedMoment B node305 node305Labels := by
  calc
    mixedMoment B raw40182 raw40182Labels = mixedMoment B raw40182step0 raw40182step0Labels := by
      have hz : ∀ j, raw40182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40182step0 = (fun i j => raw40182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40182step0 raw40182; decide +kernel
      have hl : raw40182step0Labels = raw40182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40182 raw40182Labels permutation434 hz
    mixedMoment B raw40182step0 raw40182step0Labels = mixedMoment B raw40182step1 raw40182step1Labels := by
      have ha : raw40182step1 = (fun i j => raw40182step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40182step1 raw40182step0; decide +kernel
      have hl : raw40182step1Labels = raw40182step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40182step0 raw40182step0Labels permutation68 permutation6
    mixedMoment B raw40182step1 raw40182step1Labels = mixedMoment B raw40182step2 raw40182step2Labels := by
      have ha : raw40182step2 = -raw40182step1 := by apply Matrix.ext; change ∀ i j, raw40182step2 i j = -(raw40182step1 i j); unfold raw40182step2 raw40182step1; decide +kernel
      have hl : raw40182step2Labels = raw40182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node305 node305Labels := by rfl

theorem canonical40183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40183 raw40183Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw40183 raw40183Labels = mixedMoment B raw40183step0 raw40183step0Labels := by
      have hz : ∀ j, raw40183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40183step0 = (fun i j => raw40183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40183step0 raw40183; decide +kernel
      have hl : raw40183step0Labels = raw40183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40183 raw40183Labels permutation434 hz
    mixedMoment B raw40183step0 raw40183step0Labels = mixedMoment B raw40183step1 raw40183step1Labels := by
      have ha : raw40183step1 = (fun i j => raw40183step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40183step1 raw40183step0; decide +kernel
      have hl : raw40183step1Labels = raw40183step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40183step0 raw40183step0Labels permutation74 permutation6
    mixedMoment B raw40183step1 raw40183step1Labels = mixedMoment B raw40183step2 raw40183step2Labels := by
      have ha : raw40183step2 = -raw40183step1 := by apply Matrix.ext; change ∀ i j, raw40183step2 i j = -(raw40183step1 i j); unfold raw40183step2 raw40183step1; decide +kernel
      have hl : raw40183step2Labels = raw40183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node378 node378Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment704 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 704) =
      Integer.Sparse.eval keyMomentRow704 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 704).leftCharge (GramAssembly.key 704).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 532) := by
    have ha : gramCharges (GramAssembly.key 704).leftCharge (GramAssembly.key 704).rightCharge = raw40152 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40152Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40152 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 704).leftCharge (GramAssembly.key 704).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow704, Integer.Sparse.eval]

theorem keyMoment705 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 705) =
      Integer.Sparse.eval keyMomentRow705 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 705).leftCharge (GramAssembly.key 705).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 488) := by
    have ha : gramCharges (GramAssembly.key 705).leftCharge (GramAssembly.key 705).rightCharge = raw40153 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40153Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40153 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 705).leftCharge (GramAssembly.key 705).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow705, Integer.Sparse.eval]

theorem keyMoment706 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 706) =
      Integer.Sparse.eval keyMomentRow706 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 706).leftCharge (GramAssembly.key 706).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 326) := by
    have ha : gramCharges (GramAssembly.key 706).leftCharge (GramAssembly.key 706).rightCharge = raw40154 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40154Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40154 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 706).leftCharge (GramAssembly.key 706).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow706, Integer.Sparse.eval]

theorem keyMoment707 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 707) =
      Integer.Sparse.eval keyMomentRow707 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 707).leftCharge (GramAssembly.key 707).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 533) := by
    have ha : gramCharges (GramAssembly.key 707).leftCharge (GramAssembly.key 707).rightCharge = raw40155 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40155Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40155 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 707).leftCharge (GramAssembly.key 707).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow707, Integer.Sparse.eval]

theorem keyMoment708 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 708) =
      Integer.Sparse.eval keyMomentRow708 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 708).leftCharge (GramAssembly.key 708).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 708).leftCharge (GramAssembly.key 708).rightCharge = raw40156 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40156Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40156 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 708).leftCharge (GramAssembly.key 708).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow708, Integer.Sparse.eval]

theorem keyMoment709 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 709) =
      Integer.Sparse.eval keyMomentRow709 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 709).leftCharge (GramAssembly.key 709).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 709).leftCharge (GramAssembly.key 709).rightCharge = raw40157 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40157Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40157 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 709).leftCharge (GramAssembly.key 709).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow709, Integer.Sparse.eval]

theorem keyMoment710 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 710) =
      Integer.Sparse.eval keyMomentRow710 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 710).leftCharge (GramAssembly.key 710).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 403) := by
    have ha : gramCharges (GramAssembly.key 710).leftCharge (GramAssembly.key 710).rightCharge = raw40158 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40158Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40158 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 710).leftCharge (GramAssembly.key 710).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow710, Integer.Sparse.eval]

theorem keyMoment711 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 711) =
      Integer.Sparse.eval keyMomentRow711 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 711).leftCharge (GramAssembly.key 711).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 711).leftCharge (GramAssembly.key 711).rightCharge = raw40159 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40159Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40159 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 711).leftCharge (GramAssembly.key 711).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow711, Integer.Sparse.eval]

theorem keyMoment712 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 712) =
      Integer.Sparse.eval keyMomentRow712 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 712).leftCharge (GramAssembly.key 712).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 526) := by
    have ha : gramCharges (GramAssembly.key 712).leftCharge (GramAssembly.key 712).rightCharge = raw40160 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40160Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40160 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 712).leftCharge (GramAssembly.key 712).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow712, Integer.Sparse.eval]

theorem keyMoment713 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 713) =
      Integer.Sparse.eval keyMomentRow713 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 713).leftCharge (GramAssembly.key 713).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 713).leftCharge (GramAssembly.key 713).rightCharge = raw40161 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40161Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40161 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 713).leftCharge (GramAssembly.key 713).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow713, Integer.Sparse.eval]

theorem keyMoment714 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 714) =
      Integer.Sparse.eval keyMomentRow714 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 714).leftCharge (GramAssembly.key 714).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 714).leftCharge (GramAssembly.key 714).rightCharge = raw40162 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40162Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40162 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 714).leftCharge (GramAssembly.key 714).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow714, Integer.Sparse.eval]

theorem keyMoment715 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 715) =
      Integer.Sparse.eval keyMomentRow715 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 715).leftCharge (GramAssembly.key 715).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 715).leftCharge (GramAssembly.key 715).rightCharge = raw40163 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40163Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40163 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 715).leftCharge (GramAssembly.key 715).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow715, Integer.Sparse.eval]

theorem keyMoment716 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 716) =
      Integer.Sparse.eval keyMomentRow716 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 716).leftCharge (GramAssembly.key 716).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 432) := by
    have ha : gramCharges (GramAssembly.key 716).leftCharge (GramAssembly.key 716).rightCharge = raw40164 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40164Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40164 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 716).leftCharge (GramAssembly.key 716).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow716, Integer.Sparse.eval]

theorem keyMoment717 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 717) =
      Integer.Sparse.eval keyMomentRow717 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 717).leftCharge (GramAssembly.key 717).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 717).leftCharge (GramAssembly.key 717).rightCharge = raw40165 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40165Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40165 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 717).leftCharge (GramAssembly.key 717).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow717, Integer.Sparse.eval]

theorem keyMoment718 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 718) =
      Integer.Sparse.eval keyMomentRow718 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 718).leftCharge (GramAssembly.key 718).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 429) := by
    have ha : gramCharges (GramAssembly.key 718).leftCharge (GramAssembly.key 718).rightCharge = raw40166 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40166Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40166 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 718).leftCharge (GramAssembly.key 718).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow718, Integer.Sparse.eval]

theorem keyMoment719 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 719) =
      Integer.Sparse.eval keyMomentRow719 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 719).leftCharge (GramAssembly.key 719).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 719).leftCharge (GramAssembly.key 719).rightCharge = raw40167 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40167Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40167 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 719).leftCharge (GramAssembly.key 719).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow719, Integer.Sparse.eval]

theorem keyMoment720 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 720) =
      Integer.Sparse.eval keyMomentRow720 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 720).leftCharge (GramAssembly.key 720).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 526) := by
    have ha : gramCharges (GramAssembly.key 720).leftCharge (GramAssembly.key 720).rightCharge = raw40168 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40168Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40168 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 720).leftCharge (GramAssembly.key 720).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow720, Integer.Sparse.eval]

theorem keyMoment721 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 721) =
      Integer.Sparse.eval keyMomentRow721 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 721).leftCharge (GramAssembly.key 721).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 721).leftCharge (GramAssembly.key 721).rightCharge = raw40169 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40169Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40169 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 721).leftCharge (GramAssembly.key 721).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow721, Integer.Sparse.eval]

theorem keyMoment722 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 722) =
      Integer.Sparse.eval keyMomentRow722 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 722).leftCharge (GramAssembly.key 722).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 404) := by
    have ha : gramCharges (GramAssembly.key 722).leftCharge (GramAssembly.key 722).rightCharge = raw40170 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40170Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40170 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 722).leftCharge (GramAssembly.key 722).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow722, Integer.Sparse.eval]

theorem keyMoment723 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 723) =
      Integer.Sparse.eval keyMomentRow723 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 723).leftCharge (GramAssembly.key 723).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 149) := by
    have ha : gramCharges (GramAssembly.key 723).leftCharge (GramAssembly.key 723).rightCharge = raw40171 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40171Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40171 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 723).leftCharge (GramAssembly.key 723).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow723, Integer.Sparse.eval]

theorem keyMoment724 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 724) =
      Integer.Sparse.eval keyMomentRow724 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 724).leftCharge (GramAssembly.key 724).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 724).leftCharge (GramAssembly.key 724).rightCharge = raw40172 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40172Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40172 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 724).leftCharge (GramAssembly.key 724).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow724, Integer.Sparse.eval]

theorem keyMoment725 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 725) =
      Integer.Sparse.eval keyMomentRow725 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 725).leftCharge (GramAssembly.key 725).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 527) := by
    have ha : gramCharges (GramAssembly.key 725).leftCharge (GramAssembly.key 725).rightCharge = raw40173 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40173Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40173 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 725).leftCharge (GramAssembly.key 725).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow725, Integer.Sparse.eval]

theorem keyMoment726 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 726) =
      Integer.Sparse.eval keyMomentRow726 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 726).leftCharge (GramAssembly.key 726).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 521) := by
    have ha : gramCharges (GramAssembly.key 726).leftCharge (GramAssembly.key 726).rightCharge = raw40174 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40174Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40174 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 726).leftCharge (GramAssembly.key 726).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow726, Integer.Sparse.eval]

theorem keyMoment727 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 727) =
      Integer.Sparse.eval keyMomentRow727 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 727).leftCharge (GramAssembly.key 727).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 325) := by
    have ha : gramCharges (GramAssembly.key 727).leftCharge (GramAssembly.key 727).rightCharge = raw40175 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40175Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40175 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 727).leftCharge (GramAssembly.key 727).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow727, Integer.Sparse.eval]

theorem keyMoment728 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 728) =
      Integer.Sparse.eval keyMomentRow728 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 728).leftCharge (GramAssembly.key 728).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 728).leftCharge (GramAssembly.key 728).rightCharge = raw40176 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40176Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40176 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 728).leftCharge (GramAssembly.key 728).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow728, Integer.Sparse.eval]

theorem keyMoment729 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 729) =
      Integer.Sparse.eval keyMomentRow729 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 729).leftCharge (GramAssembly.key 729).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 306) := by
    have ha : gramCharges (GramAssembly.key 729).leftCharge (GramAssembly.key 729).rightCharge = raw40177 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40177Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40177 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 729).leftCharge (GramAssembly.key 729).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow729, Integer.Sparse.eval]

theorem keyMoment730 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 730) =
      Integer.Sparse.eval keyMomentRow730 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 730).leftCharge (GramAssembly.key 730).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 730).leftCharge (GramAssembly.key 730).rightCharge = raw40178 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40178Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40178 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 730).leftCharge (GramAssembly.key 730).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow730, Integer.Sparse.eval]

theorem keyMoment731 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 731) =
      Integer.Sparse.eval keyMomentRow731 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 731).leftCharge (GramAssembly.key 731).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 301) := by
    have ha : gramCharges (GramAssembly.key 731).leftCharge (GramAssembly.key 731).rightCharge = raw40179 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40179Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40179 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 731).leftCharge (GramAssembly.key 731).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow731, Integer.Sparse.eval]

theorem keyMoment732 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 732) =
      Integer.Sparse.eval keyMomentRow732 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 732).leftCharge (GramAssembly.key 732).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 732).leftCharge (GramAssembly.key 732).rightCharge = raw40180 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40180Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40180 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 732).leftCharge (GramAssembly.key 732).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow732, Integer.Sparse.eval]

theorem keyMoment733 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 733) =
      Integer.Sparse.eval keyMomentRow733 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 733).leftCharge (GramAssembly.key 733).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 733).leftCharge (GramAssembly.key 733).rightCharge = raw40181 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40181Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40181 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 733).leftCharge (GramAssembly.key 733).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow733, Integer.Sparse.eval]

theorem keyMoment734 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 734) =
      Integer.Sparse.eval keyMomentRow734 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 734).leftCharge (GramAssembly.key 734).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 305) := by
    have ha : gramCharges (GramAssembly.key 734).leftCharge (GramAssembly.key 734).rightCharge = raw40182 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40182Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40182 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 734).leftCharge (GramAssembly.key 734).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow734, Integer.Sparse.eval]

theorem keyMoment735 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 735) =
      Integer.Sparse.eval keyMomentRow735 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 735).leftCharge (GramAssembly.key 735).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 378) := by
    have ha : gramCharges (GramAssembly.key 735).leftCharge (GramAssembly.key 735).rightCharge = raw40183 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40183Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40183 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 735).leftCharge (GramAssembly.key 735).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow735, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt704 : keyMomentRows (704 : Fin 2886) =
    keyMomentRow704 := by decide +kernel

theorem keyMomentRowsAt705 : keyMomentRows (705 : Fin 2886) =
    keyMomentRow705 := by decide +kernel

theorem keyMomentRowsAt706 : keyMomentRows (706 : Fin 2886) =
    keyMomentRow706 := by decide +kernel

theorem keyMomentRowsAt707 : keyMomentRows (707 : Fin 2886) =
    keyMomentRow707 := by decide +kernel

theorem keyMomentRowsAt708 : keyMomentRows (708 : Fin 2886) =
    keyMomentRow708 := by decide +kernel

theorem keyMomentRowsAt709 : keyMomentRows (709 : Fin 2886) =
    keyMomentRow709 := by decide +kernel

theorem keyMomentRowsAt710 : keyMomentRows (710 : Fin 2886) =
    keyMomentRow710 := by decide +kernel

theorem keyMomentRowsAt711 : keyMomentRows (711 : Fin 2886) =
    keyMomentRow711 := by decide +kernel

theorem keyMomentRowsAt712 : keyMomentRows (712 : Fin 2886) =
    keyMomentRow712 := by decide +kernel

theorem keyMomentRowsAt713 : keyMomentRows (713 : Fin 2886) =
    keyMomentRow713 := by decide +kernel

theorem keyMomentRowsAt714 : keyMomentRows (714 : Fin 2886) =
    keyMomentRow714 := by decide +kernel

theorem keyMomentRowsAt715 : keyMomentRows (715 : Fin 2886) =
    keyMomentRow715 := by decide +kernel

theorem keyMomentRowsAt716 : keyMomentRows (716 : Fin 2886) =
    keyMomentRow716 := by decide +kernel

theorem keyMomentRowsAt717 : keyMomentRows (717 : Fin 2886) =
    keyMomentRow717 := by decide +kernel

theorem keyMomentRowsAt718 : keyMomentRows (718 : Fin 2886) =
    keyMomentRow718 := by decide +kernel

theorem keyMomentRowsAt719 : keyMomentRows (719 : Fin 2886) =
    keyMomentRow719 := by decide +kernel

theorem keyMomentRowsAt720 : keyMomentRows (720 : Fin 2886) =
    keyMomentRow720 := by decide +kernel

theorem keyMomentRowsAt721 : keyMomentRows (721 : Fin 2886) =
    keyMomentRow721 := by decide +kernel

theorem keyMomentRowsAt722 : keyMomentRows (722 : Fin 2886) =
    keyMomentRow722 := by decide +kernel

theorem keyMomentRowsAt723 : keyMomentRows (723 : Fin 2886) =
    keyMomentRow723 := by decide +kernel

theorem keyMomentRowsAt724 : keyMomentRows (724 : Fin 2886) =
    keyMomentRow724 := by decide +kernel

theorem keyMomentRowsAt725 : keyMomentRows (725 : Fin 2886) =
    keyMomentRow725 := by decide +kernel

theorem keyMomentRowsAt726 : keyMomentRows (726 : Fin 2886) =
    keyMomentRow726 := by decide +kernel

theorem keyMomentRowsAt727 : keyMomentRows (727 : Fin 2886) =
    keyMomentRow727 := by decide +kernel

theorem keyMomentRowsAt728 : keyMomentRows (728 : Fin 2886) =
    keyMomentRow728 := by decide +kernel

theorem keyMomentRowsAt729 : keyMomentRows (729 : Fin 2886) =
    keyMomentRow729 := by decide +kernel

theorem keyMomentRowsAt730 : keyMomentRows (730 : Fin 2886) =
    keyMomentRow730 := by decide +kernel

theorem keyMomentRowsAt731 : keyMomentRows (731 : Fin 2886) =
    keyMomentRow731 := by decide +kernel

theorem keyMomentRowsAt732 : keyMomentRows (732 : Fin 2886) =
    keyMomentRow732 := by decide +kernel

theorem keyMomentRowsAt733 : keyMomentRows (733 : Fin 2886) =
    keyMomentRow733 := by decide +kernel

theorem keyMomentRowsAt734 : keyMomentRows (734 : Fin 2886) =
    keyMomentRow734 := by decide +kernel

theorem keyMomentRowsAt735 : keyMomentRows (735 : Fin 2886) =
    keyMomentRow735 := by decide +kernel

theorem keyMomentChunkSound22_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 22) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 704 ∨ k.val = 705 ∨ k.val = 706 ∨ k.val = 707 ∨ k.val = 708 ∨ k.val = 709 ∨ k.val = 710 ∨ k.val = 711 ∨ k.val = 712 ∨ k.val = 713 ∨ k.val = 714 ∨ k.val = 715 ∨ k.val = 716 ∨ k.val = 717 ∨ k.val = 718 ∨ k.val = 719 ∨ k.val = 720 ∨ k.val = 721 ∨ k.val = 722 ∨ k.val = 723 ∨ k.val = 724 ∨ k.val = 725 ∨ k.val = 726 ∨ k.val = 727 ∨ k.val = 728 ∨ k.val = 729 ∨ k.val = 730 ∨ k.val = 731 ∨ k.val = 732 ∨ k.val = 733 ∨ k.val = 734 ∨ k.val = 735 := by omega
  rcases heq with h704 | h705 | h706 | h707 | h708 | h709 | h710 | h711 | h712 | h713 | h714 | h715 | h716 | h717 | h718 | h719 | h720 | h721 | h722 | h723 | h724 | h725 | h726 | h727 | h728 | h729 | h730 | h731 | h732 | h733 | h734 | h735
  · have he : k = (704 : Fin 2886) := Fin.ext h704
    subst k
    rw [keyMomentRowsAt704]
    exact keyMoment704 B hB
  · have he : k = (705 : Fin 2886) := Fin.ext h705
    subst k
    rw [keyMomentRowsAt705]
    exact keyMoment705 B hB
  · have he : k = (706 : Fin 2886) := Fin.ext h706
    subst k
    rw [keyMomentRowsAt706]
    exact keyMoment706 B hB
  · have he : k = (707 : Fin 2886) := Fin.ext h707
    subst k
    rw [keyMomentRowsAt707]
    exact keyMoment707 B hB
  · have he : k = (708 : Fin 2886) := Fin.ext h708
    subst k
    rw [keyMomentRowsAt708]
    exact keyMoment708 B hB
  · have he : k = (709 : Fin 2886) := Fin.ext h709
    subst k
    rw [keyMomentRowsAt709]
    exact keyMoment709 B hB
  · have he : k = (710 : Fin 2886) := Fin.ext h710
    subst k
    rw [keyMomentRowsAt710]
    exact keyMoment710 B hB
  · have he : k = (711 : Fin 2886) := Fin.ext h711
    subst k
    rw [keyMomentRowsAt711]
    exact keyMoment711 B hB
  · have he : k = (712 : Fin 2886) := Fin.ext h712
    subst k
    rw [keyMomentRowsAt712]
    exact keyMoment712 B hB
  · have he : k = (713 : Fin 2886) := Fin.ext h713
    subst k
    rw [keyMomentRowsAt713]
    exact keyMoment713 B hB
  · have he : k = (714 : Fin 2886) := Fin.ext h714
    subst k
    rw [keyMomentRowsAt714]
    exact keyMoment714 B hB
  · have he : k = (715 : Fin 2886) := Fin.ext h715
    subst k
    rw [keyMomentRowsAt715]
    exact keyMoment715 B hB
  · have he : k = (716 : Fin 2886) := Fin.ext h716
    subst k
    rw [keyMomentRowsAt716]
    exact keyMoment716 B hB
  · have he : k = (717 : Fin 2886) := Fin.ext h717
    subst k
    rw [keyMomentRowsAt717]
    exact keyMoment717 B hB
  · have he : k = (718 : Fin 2886) := Fin.ext h718
    subst k
    rw [keyMomentRowsAt718]
    exact keyMoment718 B hB
  · have he : k = (719 : Fin 2886) := Fin.ext h719
    subst k
    rw [keyMomentRowsAt719]
    exact keyMoment719 B hB
  · have he : k = (720 : Fin 2886) := Fin.ext h720
    subst k
    rw [keyMomentRowsAt720]
    exact keyMoment720 B hB
  · have he : k = (721 : Fin 2886) := Fin.ext h721
    subst k
    rw [keyMomentRowsAt721]
    exact keyMoment721 B hB
  · have he : k = (722 : Fin 2886) := Fin.ext h722
    subst k
    rw [keyMomentRowsAt722]
    exact keyMoment722 B hB
  · have he : k = (723 : Fin 2886) := Fin.ext h723
    subst k
    rw [keyMomentRowsAt723]
    exact keyMoment723 B hB
  · have he : k = (724 : Fin 2886) := Fin.ext h724
    subst k
    rw [keyMomentRowsAt724]
    exact keyMoment724 B hB
  · have he : k = (725 : Fin 2886) := Fin.ext h725
    subst k
    rw [keyMomentRowsAt725]
    exact keyMoment725 B hB
  · have he : k = (726 : Fin 2886) := Fin.ext h726
    subst k
    rw [keyMomentRowsAt726]
    exact keyMoment726 B hB
  · have he : k = (727 : Fin 2886) := Fin.ext h727
    subst k
    rw [keyMomentRowsAt727]
    exact keyMoment727 B hB
  · have he : k = (728 : Fin 2886) := Fin.ext h728
    subst k
    rw [keyMomentRowsAt728]
    exact keyMoment728 B hB
  · have he : k = (729 : Fin 2886) := Fin.ext h729
    subst k
    rw [keyMomentRowsAt729]
    exact keyMoment729 B hB
  · have he : k = (730 : Fin 2886) := Fin.ext h730
    subst k
    rw [keyMomentRowsAt730]
    exact keyMoment730 B hB
  · have he : k = (731 : Fin 2886) := Fin.ext h731
    subst k
    rw [keyMomentRowsAt731]
    exact keyMoment731 B hB
  · have he : k = (732 : Fin 2886) := Fin.ext h732
    subst k
    rw [keyMomentRowsAt732]
    exact keyMoment732 B hB
  · have he : k = (733 : Fin 2886) := Fin.ext h733
    subst k
    rw [keyMomentRowsAt733]
    exact keyMoment733 B hB
  · have he : k = (734 : Fin 2886) := Fin.ext h734
    subst k
    rw [keyMomentRowsAt734]
    exact keyMoment734 B hB
  · have he : k = (735 : Fin 2886) := Fin.ext h735
    subst k
    rw [keyMomentRowsAt735]
    exact keyMoment735 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound22_e_oai
