-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:55:40.735568+00:00
-- url     : https://prove2.me/submissions/ed9320e3-0f9d-402f-9c32-8768bd16c659

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E112
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical319
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40858 raw40858Labels = mixedMoment B node1806 node1806Labels := by
  calc
    mixedMoment B raw40858 raw40858Labels = mixedMoment B raw40858step0 raw40858step0Labels := by
      have ha : raw40858step0 = (fun i j => raw40858 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40858step0 raw40858; decide +kernel
      have hl : raw40858step0Labels = raw40858Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40858 raw40858Labels permutation421 permutation6
    _ = mixedMoment B node1806 node1806Labels := by rfl

theorem canonical40859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40859 raw40859Labels = mixedMoment B node1791 node1791Labels := by
  calc
    mixedMoment B raw40859 raw40859Labels = mixedMoment B raw40859step0 raw40859step0Labels := by
      have ha : raw40859step0 = (fun i j => raw40859 (permutation430 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40859step0 raw40859; decide +kernel
      have hl : raw40859step0Labels = raw40859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40859 raw40859Labels permutation430 permutation6
    _ = mixedMoment B node1791 node1791Labels := by rfl

theorem canonical40860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40860 raw40860Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw40860 raw40860Labels = mixedMoment B raw40860step0 raw40860step0Labels := by
      have hz : ∀ j, raw40860 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40860step0 = (fun i j => raw40860 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40860step0 raw40860; decide +kernel
      have hl : raw40860step0Labels = raw40860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40860 raw40860Labels permutation520 hz
    mixedMoment B raw40860step0 raw40860step0Labels = mixedMoment B raw40860step1 raw40860step1Labels := by
      have ha : raw40860step1 = (fun i j => raw40860step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40860step1 raw40860step0; decide +kernel
      have hl : raw40860step1Labels = raw40860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40860step0 raw40860step0Labels permutation151 permutation3
    mixedMoment B raw40860step1 raw40860step1Labels = mixedMoment B raw40860step2 raw40860step2Labels := by
      have ha : raw40860step2 = -raw40860step1 := by apply Matrix.ext; change ∀ i j, raw40860step2 i j = -(raw40860step1 i j); unfold raw40860step2 raw40860step1; decide +kernel
      have hl : raw40860step2Labels = raw40860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical40861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40861 raw40861Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw40861 raw40861Labels = mixedMoment B raw40861step0 raw40861step0Labels := by
      have ha : raw40861step0 = (fun i j => raw40861 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40861step0 raw40861; decide +kernel
      have hl : raw40861step0Labels = raw40861Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40861 raw40861Labels permutation688 permutation3
    mixedMoment B raw40861step0 raw40861step0Labels = mixedMoment B raw40861step1 raw40861step1Labels := by
      have ha : raw40861step1 = -raw40861step0 := by apply Matrix.ext; change ∀ i j, raw40861step1 i j = -(raw40861step0 i j); unfold raw40861step1 raw40861step0; decide +kernel
      have hl : raw40861step1Labels = raw40861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2714 node2714Labels := by rfl

theorem canonical40862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40862 raw40862Labels = mixedMoment B node3032 node3032Labels := by
  calc
    mixedMoment B raw40862 raw40862Labels = mixedMoment B raw40862step0 raw40862step0Labels := by
      have ha : raw40862step0 = (fun i j => raw40862 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40862step0 raw40862; decide +kernel
      have hl : raw40862step0Labels = raw40862Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40862 raw40862Labels permutation688 permutation3
    mixedMoment B raw40862step0 raw40862step0Labels = mixedMoment B raw40862step1 raw40862step1Labels := by
      have ha : raw40862step1 = -raw40862step0 := by apply Matrix.ext; change ∀ i j, raw40862step1 i j = -(raw40862step0 i j); unfold raw40862step1 raw40862step0; decide +kernel
      have hl : raw40862step1Labels = raw40862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3032 node3032Labels := by rfl

theorem canonical40863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40863 raw40863Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw40863 raw40863Labels = mixedMoment B raw40863step0 raw40863step0Labels := by
      have ha : raw40863step0 = (fun i j => raw40863 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40863step0 raw40863; decide +kernel
      have hl : raw40863step0Labels = raw40863Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40863 raw40863Labels permutation688 permutation3
    mixedMoment B raw40863step0 raw40863step0Labels = mixedMoment B raw40863step1 raw40863step1Labels := by
      have ha : raw40863step1 = -raw40863step0 := by apply Matrix.ext; change ∀ i j, raw40863step1 i j = -(raw40863step0 i j); unfold raw40863step1 raw40863step0; decide +kernel
      have hl : raw40863step1Labels = raw40863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical40864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40864 raw40864Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw40864 raw40864Labels = mixedMoment B raw40864step0 raw40864step0Labels := by
      have ha : raw40864step0 = (fun i j => raw40864 (permutation397 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40864step0 raw40864; decide +kernel
      have hl : raw40864step0Labels = raw40864Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40864 raw40864Labels permutation397 permutation6
    _ = mixedMoment B node3788 node3788Labels := by rfl

theorem canonical40865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40865 raw40865Labels = mixedMoment B node3365 node3365Labels := by
  calc
    mixedMoment B raw40865 raw40865Labels = mixedMoment B raw40865step0 raw40865step0Labels := by
      have ha : raw40865step0 = (fun i j => raw40865 (permutation523 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40865step0 raw40865; decide +kernel
      have hl : raw40865step0Labels = raw40865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40865 raw40865Labels permutation523 permutation6
    mixedMoment B raw40865step0 raw40865step0Labels = mixedMoment B raw40865step1 raw40865step1Labels := by
      have ha : raw40865step1 = -raw40865step0 := by apply Matrix.ext; change ∀ i j, raw40865step1 i j = -(raw40865step0 i j); unfold raw40865step1 raw40865step0; decide +kernel
      have hl : raw40865step1Labels = raw40865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3365 node3365Labels := by rfl

theorem canonical40866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40866 raw40866Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw40866 raw40866Labels = mixedMoment B raw40866step0 raw40866step0Labels := by
      have hz : ∀ j, raw40866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40866step0 = (fun i j => raw40866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40866step0 raw40866; decide +kernel
      have hl : raw40866step0Labels = raw40866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40866 raw40866Labels permutation434 hz
    mixedMoment B raw40866step0 raw40866step0Labels = mixedMoment B raw40866step1 raw40866step1Labels := by
      have ha : raw40866step1 = (fun i j => raw40866step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40866step1 raw40866step0; decide +kernel
      have hl : raw40866step1Labels = raw40866step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40866step0 raw40866step0Labels permutation151 permutation3
    mixedMoment B raw40866step1 raw40866step1Labels = mixedMoment B raw40866step2 raw40866step2Labels := by
      have ha : raw40866step2 = -raw40866step1 := by apply Matrix.ext; change ∀ i j, raw40866step2 i j = -(raw40866step1 i j); unfold raw40866step2 raw40866step1; decide +kernel
      have hl : raw40866step2Labels = raw40866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3577 node3577Labels := by rfl

theorem canonical40867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40867 raw40867Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw40867 raw40867Labels = mixedMoment B raw40867step0 raw40867step0Labels := by
      have hz : ∀ j, raw40867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40867step0 = (fun i j => raw40867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40867step0 raw40867; decide +kernel
      have hl : raw40867step0Labels = raw40867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40867 raw40867Labels permutation434 hz
    mixedMoment B raw40867step0 raw40867step0Labels = mixedMoment B raw40867step1 raw40867step1Labels := by
      have ha : raw40867step1 = (fun i j => raw40867step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40867step1 raw40867step0; decide +kernel
      have hl : raw40867step1Labels = raw40867step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40867step0 raw40867step0Labels permutation142 permutation6
    _ = mixedMoment B node2812 node2812Labels := by rfl

theorem canonical40868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40868 raw40868Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw40868 raw40868Labels = mixedMoment B raw40868step0 raw40868step0Labels := by
      have ha : raw40868step0 = (fun i j => raw40868 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40868step0 raw40868; decide +kernel
      have hl : raw40868step0Labels = raw40868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40868 raw40868Labels permutation412 permutation6
    _ = mixedMoment B node3698 node3698Labels := by rfl

theorem canonical40869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40869 raw40869Labels = mixedMoment B node2810 node2810Labels := by
  calc
    mixedMoment B raw40869 raw40869Labels = mixedMoment B raw40869step0 raw40869step0Labels := by
      have ha : raw40869step0 = (fun i j => raw40869 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40869step0 raw40869; decide +kernel
      have hl : raw40869step0Labels = raw40869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40869 raw40869Labels permutation632 permutation6
    _ = mixedMoment B node2810 node2810Labels := by rfl

theorem canonical40870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40870 raw40870Labels = mixedMoment B node3674 node3674Labels := by
  calc
    mixedMoment B raw40870 raw40870Labels = mixedMoment B raw40870step0 raw40870step0Labels := by
      have ha : raw40870step0 = (fun i j => raw40870 (permutation411 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40870step0 raw40870; decide +kernel
      have hl : raw40870step0Labels = raw40870Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40870 raw40870Labels permutation411 permutation6
    _ = mixedMoment B node3674 node3674Labels := by rfl

theorem canonical40871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40871 raw40871Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw40871 raw40871Labels = mixedMoment B raw40871step0 raw40871step0Labels := by
      have ha : raw40871step0 = (fun i j => raw40871 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40871step0 raw40871; decide +kernel
      have hl : raw40871step0Labels = raw40871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40871 raw40871Labels permutation643 permutation6
    _ = mixedMoment B node2798 node2798Labels := by rfl

theorem canonical40872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40872 raw40872Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw40872 raw40872Labels = mixedMoment B raw40872step0 raw40872step0Labels := by
      have ha : raw40872step0 = (fun i j => raw40872 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40872step0 raw40872; decide +kernel
      have hl : raw40872step0Labels = raw40872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40872 raw40872Labels permutation640 permutation3
    mixedMoment B raw40872step0 raw40872step0Labels = mixedMoment B raw40872step1 raw40872step1Labels := by
      have ha : raw40872step1 = -raw40872step0 := by apply Matrix.ext; change ∀ i j, raw40872step1 i j = -(raw40872step0 i j); unfold raw40872step1 raw40872step0; decide +kernel
      have hl : raw40872step1Labels = raw40872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2233 node2233Labels := by rfl

theorem canonical40873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40873 raw40873Labels = mixedMoment B node2892 node2892Labels := by
  calc
    mixedMoment B raw40873 raw40873Labels = mixedMoment B raw40873step0 raw40873step0Labels := by
      have ha : raw40873step0 = (fun i j => raw40873 (permutation637 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40873step0 raw40873; decide +kernel
      have hl : raw40873step0Labels = raw40873Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40873 raw40873Labels permutation637 permutation6
    _ = mixedMoment B node2892 node2892Labels := by rfl

theorem canonical40874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40874 raw40874Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw40874 raw40874Labels = mixedMoment B raw40874step0 raw40874step0Labels := by
      have hz : ∀ j, raw40874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40874step0 = (fun i j => raw40874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40874step0 raw40874; decide +kernel
      have hl : raw40874step0Labels = raw40874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40874 raw40874Labels permutation434 hz
    mixedMoment B raw40874step0 raw40874step0Labels = mixedMoment B raw40874step1 raw40874step1Labels := by
      have ha : raw40874step1 = (fun i j => raw40874step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40874step1 raw40874step0; decide +kernel
      have hl : raw40874step1Labels = raw40874step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40874step0 raw40874step0Labels permutation119 permutation6
    _ = mixedMoment B node2513 node2513Labels := by rfl

theorem canonical40875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40875 raw40875Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw40875 raw40875Labels = mixedMoment B raw40875step0 raw40875step0Labels := by
      have hz : ∀ j, raw40875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40875step0 = (fun i j => raw40875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40875step0 raw40875; decide +kernel
      have hl : raw40875step0Labels = raw40875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40875 raw40875Labels permutation434 hz
    mixedMoment B raw40875step0 raw40875step0Labels = mixedMoment B raw40875step1 raw40875step1Labels := by
      have ha : raw40875step1 = (fun i j => raw40875step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40875step1 raw40875step0; decide +kernel
      have hl : raw40875step1Labels = raw40875step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40875step0 raw40875step0Labels permutation142 permutation6
    _ = mixedMoment B node1133 node1133Labels := by rfl

theorem canonical40876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40876 raw40876Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw40876 raw40876Labels = mixedMoment B raw40876step0 raw40876step0Labels := by
      have ha : raw40876step0 = (fun i j => raw40876 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40876step0 raw40876; decide +kernel
      have hl : raw40876step0Labels = raw40876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40876 raw40876Labels permutation550 permutation6
    _ = mixedMoment B node2494 node2494Labels := by rfl

theorem canonical40877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40877 raw40877Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw40877 raw40877Labels = mixedMoment B raw40877step0 raw40877step0Labels := by
      have ha : raw40877step0 = (fun i j => raw40877 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40877step0 raw40877; decide +kernel
      have hl : raw40877step0Labels = raw40877Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40877 raw40877Labels permutation632 permutation6
    _ = mixedMoment B node1130 node1130Labels := by rfl

theorem canonical40878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40878 raw40878Labels = mixedMoment B node2438 node2438Labels := by
  calc
    mixedMoment B raw40878 raw40878Labels = mixedMoment B raw40878step0 raw40878step0Labels := by
      have ha : raw40878step0 = (fun i j => raw40878 (permutation549 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40878step0 raw40878; decide +kernel
      have hl : raw40878step0Labels = raw40878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40878 raw40878Labels permutation549 permutation6
    _ = mixedMoment B node2438 node2438Labels := by rfl

theorem canonical40879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40879 raw40879Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw40879 raw40879Labels = mixedMoment B raw40879step0 raw40879step0Labels := by
      have ha : raw40879step0 = (fun i j => raw40879 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40879step0 raw40879; decide +kernel
      have hl : raw40879step0Labels = raw40879Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40879 raw40879Labels permutation643 permutation6
    _ = mixedMoment B node1113 node1113Labels := by rfl

theorem canonical40880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40880 raw40880Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw40880 raw40880Labels = mixedMoment B raw40880step0 raw40880step0Labels := by
      have hz : ∀ j, raw40880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40880step0 = (fun i j => raw40880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40880step0 raw40880; decide +kernel
      have hl : raw40880step0Labels = raw40880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40880 raw40880Labels permutation434 hz
    mixedMoment B raw40880step0 raw40880step0Labels = mixedMoment B raw40880step1 raw40880step1Labels := by
      have hz : ∀ j, raw40880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40880step1 = (fun i j => raw40880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40880step1 raw40880step0; decide +kernel
      have hl : raw40880step1Labels = raw40880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40880step0 raw40880step0Labels permutation80 hz
    mixedMoment B raw40880step1 raw40880step1Labels = mixedMoment B raw40880step2 raw40880step2Labels := by
      have ha : raw40880step2 = (fun i j => raw40880step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40880step2 raw40880step1; decide +kernel
      have hl : raw40880step2Labels = raw40880step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40880step1 raw40880step1Labels permutation28 permutation6
    _ = mixedMoment B node607 node607Labels := by rfl

theorem canonical40881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40881 raw40881Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw40881 raw40881Labels = mixedMoment B raw40881step0 raw40881step0Labels := by
      have hz : ∀ j, raw40881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40881step0 = (fun i j => raw40881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40881step0 raw40881; decide +kernel
      have hl : raw40881step0Labels = raw40881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40881 raw40881Labels permutation346 hz
    mixedMoment B raw40881step0 raw40881step0Labels = mixedMoment B raw40881step1 raw40881step1Labels := by
      have ha : raw40881step1 = (fun i j => raw40881step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40881step1 raw40881step0; decide +kernel
      have hl : raw40881step1Labels = raw40881step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40881step0 raw40881step0Labels permutation125 permutation6
    _ = mixedMoment B node1058 node1058Labels := by rfl

theorem canonical40882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40882 raw40882Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw40882 raw40882Labels = mixedMoment B raw40882step0 raw40882step0Labels := by
      have hz : ∀ j, raw40882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40882step0 = (fun i j => raw40882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40882step0 raw40882; decide +kernel
      have hl : raw40882step0Labels = raw40882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40882 raw40882Labels permutation346 hz
    mixedMoment B raw40882step0 raw40882step0Labels = mixedMoment B raw40882step1 raw40882step1Labels := by
      have ha : raw40882step1 = (fun i j => raw40882step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40882step1 raw40882step0; decide +kernel
      have hl : raw40882step1Labels = raw40882step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40882step0 raw40882step0Labels permutation137 permutation6
    _ = mixedMoment B node604 node604Labels := by rfl

theorem canonical40883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40883 raw40883Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw40883 raw40883Labels = mixedMoment B raw40883step0 raw40883step0Labels := by
      have hz : ∀ j, raw40883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40883step0 = (fun i j => raw40883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40883step0 raw40883; decide +kernel
      have hl : raw40883step0Labels = raw40883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40883 raw40883Labels permutation346 hz
    mixedMoment B raw40883step0 raw40883step0Labels = mixedMoment B raw40883step1 raw40883step1Labels := by
      have ha : raw40883step1 = (fun i j => raw40883step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40883step1 raw40883step0; decide +kernel
      have hl : raw40883step1Labels = raw40883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40883step0 raw40883step0Labels permutation124 permutation6
    _ = mixedMoment B node946 node946Labels := by rfl

theorem canonical40884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40884 raw40884Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw40884 raw40884Labels = mixedMoment B raw40884step0 raw40884step0Labels := by
      have hz : ∀ j, raw40884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40884step0 = (fun i j => raw40884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40884step0 raw40884; decide +kernel
      have hl : raw40884step0Labels = raw40884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40884 raw40884Labels permutation346 hz
    mixedMoment B raw40884step0 raw40884step0Labels = mixedMoment B raw40884step1 raw40884step1Labels := by
      have ha : raw40884step1 = (fun i j => raw40884step0 (permutation148 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40884step1 raw40884step0; decide +kernel
      have hl : raw40884step1Labels = raw40884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40884step0 raw40884step0Labels permutation148 permutation6
    _ = mixedMoment B node582 node582Labels := by rfl

theorem canonical40885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40885 raw40885Labels = mixedMoment B node944 node944Labels := by
  calc
    mixedMoment B raw40885 raw40885Labels = mixedMoment B raw40885step0 raw40885step0Labels := by
      have ha : raw40885step0 = (fun i j => raw40885 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40885step0 raw40885; decide +kernel
      have hl : raw40885step0Labels = raw40885Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40885 raw40885Labels permutation577 permutation6
    _ = mixedMoment B node944 node944Labels := by rfl

theorem canonical40886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40886 raw40886Labels = mixedMoment B node580 node580Labels := by
  calc
    mixedMoment B raw40886 raw40886Labels = mixedMoment B raw40886step0 raw40886step0Labels := by
      have ha : raw40886step0 = (fun i j => raw40886 (permutation674 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40886step0 raw40886; decide +kernel
      have hl : raw40886step0Labels = raw40886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40886 raw40886Labels permutation674 permutation6
    _ = mixedMoment B node580 node580Labels := by rfl

theorem canonical40887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40887 raw40887Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw40887 raw40887Labels = mixedMoment B raw40887step0 raw40887step0Labels := by
      have hz : ∀ j, raw40887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40887step0 = (fun i j => raw40887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40887step0 raw40887; decide +kernel
      have hl : raw40887step0Labels = raw40887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40887 raw40887Labels permutation520 hz
    mixedMoment B raw40887step0 raw40887step0Labels = mixedMoment B raw40887step1 raw40887step1Labels := by
      have hz : ∀ j, raw40887step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40887step1 = (fun i j => raw40887step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40887step1 raw40887step0; decide +kernel
      have hl : raw40887step1Labels = raw40887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40887step0 raw40887step0Labels permutation104 hz
    mixedMoment B raw40887step1 raw40887step1Labels = mixedMoment B raw40887step2 raw40887step2Labels := by
      have ha : raw40887step2 = (fun i j => raw40887step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40887step2 raw40887step1; decide +kernel
      have hl : raw40887step2Labels = raw40887step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40887step1 raw40887step1Labels permutation24 permutation6
    _ = mixedMoment B node2138 node2138Labels := by rfl

theorem canonical40888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40888 raw40888Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw40888 raw40888Labels = mixedMoment B raw40888step0 raw40888step0Labels := by
      have hz : ∀ j, raw40888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40888step0 = (fun i j => raw40888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40888step0 raw40888; decide +kernel
      have hl : raw40888step0Labels = raw40888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40888 raw40888Labels permutation434 hz
    mixedMoment B raw40888step0 raw40888step0Labels = mixedMoment B raw40888step1 raw40888step1Labels := by
      have ha : raw40888step1 = (fun i j => raw40888step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40888step1 raw40888step0; decide +kernel
      have hl : raw40888step1Labels = raw40888step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40888step0 raw40888step0Labels permutation102 permutation6
    _ = mixedMoment B node1829 node1829Labels := by rfl

theorem canonical40889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40889 raw40889Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw40889 raw40889Labels = mixedMoment B raw40889step0 raw40889step0Labels := by
      have hz : ∀ j, raw40889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40889step0 = (fun i j => raw40889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40889step0 raw40889; decide +kernel
      have hl : raw40889step0Labels = raw40889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40889 raw40889Labels permutation434 hz
    mixedMoment B raw40889step0 raw40889step0Labels = mixedMoment B raw40889step1 raw40889step1Labels := by
      have ha : raw40889step1 = (fun i j => raw40889step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40889step1 raw40889step0; decide +kernel
      have hl : raw40889step1Labels = raw40889step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40889step0 raw40889step0Labels permutation96 permutation6
    _ = mixedMoment B node2039 node2039Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1440 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1440) =
      Integer.Sparse.eval keyMomentRow1440 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1440).leftCharge (GramAssembly.key 1440).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1806) := by
    have ha : gramCharges (GramAssembly.key 1440).leftCharge (GramAssembly.key 1440).rightCharge = raw40858 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40858Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40858 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1440).leftCharge (GramAssembly.key 1440).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1440, Integer.Sparse.eval]

theorem keyMoment1441 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1441) =
      Integer.Sparse.eval keyMomentRow1441 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1441).leftCharge (GramAssembly.key 1441).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1791) := by
    have ha : gramCharges (GramAssembly.key 1441).leftCharge (GramAssembly.key 1441).rightCharge = raw40859 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40859Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40859 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1441).leftCharge (GramAssembly.key 1441).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1441, Integer.Sparse.eval]

theorem keyMoment1442 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1442) =
      Integer.Sparse.eval keyMomentRow1442 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1442).leftCharge (GramAssembly.key 1442).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 1442).leftCharge (GramAssembly.key 1442).rightCharge = raw40860 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40860Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40860 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1442).leftCharge (GramAssembly.key 1442).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1442, Integer.Sparse.eval]

theorem keyMoment1443 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1443) =
      Integer.Sparse.eval keyMomentRow1443 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1443).leftCharge (GramAssembly.key 1443).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2714) := by
    have ha : gramCharges (GramAssembly.key 1443).leftCharge (GramAssembly.key 1443).rightCharge = raw40861 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40861Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40861 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1443).leftCharge (GramAssembly.key 1443).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1443, Integer.Sparse.eval]

theorem keyMoment1444 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1444) =
      Integer.Sparse.eval keyMomentRow1444 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1444).leftCharge (GramAssembly.key 1444).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3032) := by
    have ha : gramCharges (GramAssembly.key 1444).leftCharge (GramAssembly.key 1444).rightCharge = raw40862 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40862Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40862 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1444).leftCharge (GramAssembly.key 1444).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1444, Integer.Sparse.eval]

theorem keyMoment1445 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1445) =
      Integer.Sparse.eval keyMomentRow1445 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1445).leftCharge (GramAssembly.key 1445).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3803) := by
    have ha : gramCharges (GramAssembly.key 1445).leftCharge (GramAssembly.key 1445).rightCharge = raw40863 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40863Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40863 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1445).leftCharge (GramAssembly.key 1445).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1445, Integer.Sparse.eval]

theorem keyMoment1446 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1446) =
      Integer.Sparse.eval keyMomentRow1446 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1446).leftCharge (GramAssembly.key 1446).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3788) := by
    have ha : gramCharges (GramAssembly.key 1446).leftCharge (GramAssembly.key 1446).rightCharge = raw40864 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40864Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40864 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1446).leftCharge (GramAssembly.key 1446).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1446, Integer.Sparse.eval]

theorem keyMoment1447 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1447) =
      Integer.Sparse.eval keyMomentRow1447 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1447).leftCharge (GramAssembly.key 1447).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3365) := by
    have ha : gramCharges (GramAssembly.key 1447).leftCharge (GramAssembly.key 1447).rightCharge = raw40865 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40865Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40865 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1447).leftCharge (GramAssembly.key 1447).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1447, Integer.Sparse.eval]

theorem keyMoment1448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1448) =
      Integer.Sparse.eval keyMomentRow1448 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1448).leftCharge (GramAssembly.key 1448).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3577) := by
    have ha : gramCharges (GramAssembly.key 1448).leftCharge (GramAssembly.key 1448).rightCharge = raw40866 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40866Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40866 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1448).leftCharge (GramAssembly.key 1448).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1448, Integer.Sparse.eval]

theorem keyMoment1449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1449) =
      Integer.Sparse.eval keyMomentRow1449 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1449).leftCharge (GramAssembly.key 1449).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2812) := by
    have ha : gramCharges (GramAssembly.key 1449).leftCharge (GramAssembly.key 1449).rightCharge = raw40867 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40867Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40867 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1449).leftCharge (GramAssembly.key 1449).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1449, Integer.Sparse.eval]

theorem keyMoment1450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1450) =
      Integer.Sparse.eval keyMomentRow1450 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1450).leftCharge (GramAssembly.key 1450).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3698) := by
    have ha : gramCharges (GramAssembly.key 1450).leftCharge (GramAssembly.key 1450).rightCharge = raw40868 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40868Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40868 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1450).leftCharge (GramAssembly.key 1450).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1450, Integer.Sparse.eval]

theorem keyMoment1451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1451) =
      Integer.Sparse.eval keyMomentRow1451 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1451).leftCharge (GramAssembly.key 1451).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2810) := by
    have ha : gramCharges (GramAssembly.key 1451).leftCharge (GramAssembly.key 1451).rightCharge = raw40869 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40869Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40869 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1451).leftCharge (GramAssembly.key 1451).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1451, Integer.Sparse.eval]

theorem keyMoment1452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1452) =
      Integer.Sparse.eval keyMomentRow1452 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1452).leftCharge (GramAssembly.key 1452).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3674) := by
    have ha : gramCharges (GramAssembly.key 1452).leftCharge (GramAssembly.key 1452).rightCharge = raw40870 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40870Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40870 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1452).leftCharge (GramAssembly.key 1452).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1452, Integer.Sparse.eval]

theorem keyMoment1453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1453) =
      Integer.Sparse.eval keyMomentRow1453 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1453).leftCharge (GramAssembly.key 1453).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2798) := by
    have ha : gramCharges (GramAssembly.key 1453).leftCharge (GramAssembly.key 1453).rightCharge = raw40871 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40871Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40871 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1453).leftCharge (GramAssembly.key 1453).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1453, Integer.Sparse.eval]

theorem keyMoment1454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1454) =
      Integer.Sparse.eval keyMomentRow1454 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1454).leftCharge (GramAssembly.key 1454).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2233) := by
    have ha : gramCharges (GramAssembly.key 1454).leftCharge (GramAssembly.key 1454).rightCharge = raw40872 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40872Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40872 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1454).leftCharge (GramAssembly.key 1454).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1454, Integer.Sparse.eval]

theorem keyMoment1455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1455) =
      Integer.Sparse.eval keyMomentRow1455 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1455).leftCharge (GramAssembly.key 1455).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2892) := by
    have ha : gramCharges (GramAssembly.key 1455).leftCharge (GramAssembly.key 1455).rightCharge = raw40873 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40873Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40873 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1455).leftCharge (GramAssembly.key 1455).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1455, Integer.Sparse.eval]

theorem keyMoment1456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1456) =
      Integer.Sparse.eval keyMomentRow1456 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1456).leftCharge (GramAssembly.key 1456).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2513) := by
    have ha : gramCharges (GramAssembly.key 1456).leftCharge (GramAssembly.key 1456).rightCharge = raw40874 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40874Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40874 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1456).leftCharge (GramAssembly.key 1456).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1456, Integer.Sparse.eval]

theorem keyMoment1457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1457) =
      Integer.Sparse.eval keyMomentRow1457 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1457).leftCharge (GramAssembly.key 1457).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1133) := by
    have ha : gramCharges (GramAssembly.key 1457).leftCharge (GramAssembly.key 1457).rightCharge = raw40875 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40875Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40875 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1457).leftCharge (GramAssembly.key 1457).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1457, Integer.Sparse.eval]

theorem keyMoment1458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1458) =
      Integer.Sparse.eval keyMomentRow1458 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1458).leftCharge (GramAssembly.key 1458).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2494) := by
    have ha : gramCharges (GramAssembly.key 1458).leftCharge (GramAssembly.key 1458).rightCharge = raw40876 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40876Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40876 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1458).leftCharge (GramAssembly.key 1458).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1458, Integer.Sparse.eval]

theorem keyMoment1459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1459) =
      Integer.Sparse.eval keyMomentRow1459 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1459).leftCharge (GramAssembly.key 1459).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1130) := by
    have ha : gramCharges (GramAssembly.key 1459).leftCharge (GramAssembly.key 1459).rightCharge = raw40877 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40877Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40877 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1459).leftCharge (GramAssembly.key 1459).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1459, Integer.Sparse.eval]

theorem keyMoment1460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1460) =
      Integer.Sparse.eval keyMomentRow1460 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1460).leftCharge (GramAssembly.key 1460).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2438) := by
    have ha : gramCharges (GramAssembly.key 1460).leftCharge (GramAssembly.key 1460).rightCharge = raw40878 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40878Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40878 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1460).leftCharge (GramAssembly.key 1460).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1460, Integer.Sparse.eval]

theorem keyMoment1461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1461) =
      Integer.Sparse.eval keyMomentRow1461 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1461).leftCharge (GramAssembly.key 1461).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1113) := by
    have ha : gramCharges (GramAssembly.key 1461).leftCharge (GramAssembly.key 1461).rightCharge = raw40879 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40879Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40879 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1461).leftCharge (GramAssembly.key 1461).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1461, Integer.Sparse.eval]

theorem keyMoment1462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1462) =
      Integer.Sparse.eval keyMomentRow1462 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1462).leftCharge (GramAssembly.key 1462).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 607) := by
    have ha : gramCharges (GramAssembly.key 1462).leftCharge (GramAssembly.key 1462).rightCharge = raw40880 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40880Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40880 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1462).leftCharge (GramAssembly.key 1462).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1462, Integer.Sparse.eval]

theorem keyMoment1463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1463) =
      Integer.Sparse.eval keyMomentRow1463 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1463).leftCharge (GramAssembly.key 1463).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1058) := by
    have ha : gramCharges (GramAssembly.key 1463).leftCharge (GramAssembly.key 1463).rightCharge = raw40881 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40881Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40881 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1463).leftCharge (GramAssembly.key 1463).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1463, Integer.Sparse.eval]

theorem keyMoment1464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1464) =
      Integer.Sparse.eval keyMomentRow1464 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1464).leftCharge (GramAssembly.key 1464).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 604) := by
    have ha : gramCharges (GramAssembly.key 1464).leftCharge (GramAssembly.key 1464).rightCharge = raw40882 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40882Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40882 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1464).leftCharge (GramAssembly.key 1464).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1464, Integer.Sparse.eval]

theorem keyMoment1465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1465) =
      Integer.Sparse.eval keyMomentRow1465 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1465).leftCharge (GramAssembly.key 1465).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 946) := by
    have ha : gramCharges (GramAssembly.key 1465).leftCharge (GramAssembly.key 1465).rightCharge = raw40883 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40883Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40883 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1465).leftCharge (GramAssembly.key 1465).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1465, Integer.Sparse.eval]

theorem keyMoment1466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1466) =
      Integer.Sparse.eval keyMomentRow1466 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1466).leftCharge (GramAssembly.key 1466).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 582) := by
    have ha : gramCharges (GramAssembly.key 1466).leftCharge (GramAssembly.key 1466).rightCharge = raw40884 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40884Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40884 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1466).leftCharge (GramAssembly.key 1466).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1466, Integer.Sparse.eval]

theorem keyMoment1467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1467) =
      Integer.Sparse.eval keyMomentRow1467 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1467).leftCharge (GramAssembly.key 1467).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 944) := by
    have ha : gramCharges (GramAssembly.key 1467).leftCharge (GramAssembly.key 1467).rightCharge = raw40885 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40885Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40885 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1467).leftCharge (GramAssembly.key 1467).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1467, Integer.Sparse.eval]

theorem keyMoment1468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1468) =
      Integer.Sparse.eval keyMomentRow1468 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1468).leftCharge (GramAssembly.key 1468).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 580) := by
    have ha : gramCharges (GramAssembly.key 1468).leftCharge (GramAssembly.key 1468).rightCharge = raw40886 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40886Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40886 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1468).leftCharge (GramAssembly.key 1468).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1468, Integer.Sparse.eval]

theorem keyMoment1469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1469) =
      Integer.Sparse.eval keyMomentRow1469 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1469).leftCharge (GramAssembly.key 1469).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2138) := by
    have ha : gramCharges (GramAssembly.key 1469).leftCharge (GramAssembly.key 1469).rightCharge = raw40887 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40887Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40887 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1469).leftCharge (GramAssembly.key 1469).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1469, Integer.Sparse.eval]

theorem keyMoment1470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1470) =
      Integer.Sparse.eval keyMomentRow1470 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1470).leftCharge (GramAssembly.key 1470).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1829) := by
    have ha : gramCharges (GramAssembly.key 1470).leftCharge (GramAssembly.key 1470).rightCharge = raw40888 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40888Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40888 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1470).leftCharge (GramAssembly.key 1470).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1470, Integer.Sparse.eval]

theorem keyMoment1471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1471) =
      Integer.Sparse.eval keyMomentRow1471 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1471).leftCharge (GramAssembly.key 1471).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2039) := by
    have ha : gramCharges (GramAssembly.key 1471).leftCharge (GramAssembly.key 1471).rightCharge = raw40889 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40889Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40889 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1471).leftCharge (GramAssembly.key 1471).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1471, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk45
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1440 : keyMomentRows (1440 : Fin 2886) =
    keyMomentRow1440 := by decide +kernel

theorem keyMomentRowsAt1441 : keyMomentRows (1441 : Fin 2886) =
    keyMomentRow1441 := by decide +kernel

theorem keyMomentRowsAt1442 : keyMomentRows (1442 : Fin 2886) =
    keyMomentRow1442 := by decide +kernel

theorem keyMomentRowsAt1443 : keyMomentRows (1443 : Fin 2886) =
    keyMomentRow1443 := by decide +kernel

theorem keyMomentRowsAt1444 : keyMomentRows (1444 : Fin 2886) =
    keyMomentRow1444 := by decide +kernel

theorem keyMomentRowsAt1445 : keyMomentRows (1445 : Fin 2886) =
    keyMomentRow1445 := by decide +kernel

theorem keyMomentRowsAt1446 : keyMomentRows (1446 : Fin 2886) =
    keyMomentRow1446 := by decide +kernel

theorem keyMomentRowsAt1447 : keyMomentRows (1447 : Fin 2886) =
    keyMomentRow1447 := by decide +kernel

theorem keyMomentRowsAt1448 : keyMomentRows (1448 : Fin 2886) =
    keyMomentRow1448 := by decide +kernel

theorem keyMomentRowsAt1449 : keyMomentRows (1449 : Fin 2886) =
    keyMomentRow1449 := by decide +kernel

theorem keyMomentRowsAt1450 : keyMomentRows (1450 : Fin 2886) =
    keyMomentRow1450 := by decide +kernel

theorem keyMomentRowsAt1451 : keyMomentRows (1451 : Fin 2886) =
    keyMomentRow1451 := by decide +kernel

theorem keyMomentRowsAt1452 : keyMomentRows (1452 : Fin 2886) =
    keyMomentRow1452 := by decide +kernel

theorem keyMomentRowsAt1453 : keyMomentRows (1453 : Fin 2886) =
    keyMomentRow1453 := by decide +kernel

theorem keyMomentRowsAt1454 : keyMomentRows (1454 : Fin 2886) =
    keyMomentRow1454 := by decide +kernel

theorem keyMomentRowsAt1455 : keyMomentRows (1455 : Fin 2886) =
    keyMomentRow1455 := by decide +kernel

theorem keyMomentRowsAt1456 : keyMomentRows (1456 : Fin 2886) =
    keyMomentRow1456 := by decide +kernel

theorem keyMomentRowsAt1457 : keyMomentRows (1457 : Fin 2886) =
    keyMomentRow1457 := by decide +kernel

theorem keyMomentRowsAt1458 : keyMomentRows (1458 : Fin 2886) =
    keyMomentRow1458 := by decide +kernel

theorem keyMomentRowsAt1459 : keyMomentRows (1459 : Fin 2886) =
    keyMomentRow1459 := by decide +kernel

theorem keyMomentRowsAt1460 : keyMomentRows (1460 : Fin 2886) =
    keyMomentRow1460 := by decide +kernel

theorem keyMomentRowsAt1461 : keyMomentRows (1461 : Fin 2886) =
    keyMomentRow1461 := by decide +kernel

theorem keyMomentRowsAt1462 : keyMomentRows (1462 : Fin 2886) =
    keyMomentRow1462 := by decide +kernel

theorem keyMomentRowsAt1463 : keyMomentRows (1463 : Fin 2886) =
    keyMomentRow1463 := by decide +kernel

theorem keyMomentRowsAt1464 : keyMomentRows (1464 : Fin 2886) =
    keyMomentRow1464 := by decide +kernel

theorem keyMomentRowsAt1465 : keyMomentRows (1465 : Fin 2886) =
    keyMomentRow1465 := by decide +kernel

theorem keyMomentRowsAt1466 : keyMomentRows (1466 : Fin 2886) =
    keyMomentRow1466 := by decide +kernel

theorem keyMomentRowsAt1467 : keyMomentRows (1467 : Fin 2886) =
    keyMomentRow1467 := by decide +kernel

theorem keyMomentRowsAt1468 : keyMomentRows (1468 : Fin 2886) =
    keyMomentRow1468 := by decide +kernel

theorem keyMomentRowsAt1469 : keyMomentRows (1469 : Fin 2886) =
    keyMomentRow1469 := by decide +kernel

theorem keyMomentRowsAt1470 : keyMomentRows (1470 : Fin 2886) =
    keyMomentRow1470 := by decide +kernel

theorem keyMomentRowsAt1471 : keyMomentRows (1471 : Fin 2886) =
    keyMomentRow1471 := by decide +kernel

theorem keyMomentChunkSound45_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 45) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1440 ∨ k.val = 1441 ∨ k.val = 1442 ∨ k.val = 1443 ∨ k.val = 1444 ∨ k.val = 1445 ∨ k.val = 1446 ∨ k.val = 1447 ∨ k.val = 1448 ∨ k.val = 1449 ∨ k.val = 1450 ∨ k.val = 1451 ∨ k.val = 1452 ∨ k.val = 1453 ∨ k.val = 1454 ∨ k.val = 1455 ∨ k.val = 1456 ∨ k.val = 1457 ∨ k.val = 1458 ∨ k.val = 1459 ∨ k.val = 1460 ∨ k.val = 1461 ∨ k.val = 1462 ∨ k.val = 1463 ∨ k.val = 1464 ∨ k.val = 1465 ∨ k.val = 1466 ∨ k.val = 1467 ∨ k.val = 1468 ∨ k.val = 1469 ∨ k.val = 1470 ∨ k.val = 1471 := by omega
  rcases heq with h1440 | h1441 | h1442 | h1443 | h1444 | h1445 | h1446 | h1447 | h1448 | h1449 | h1450 | h1451 | h1452 | h1453 | h1454 | h1455 | h1456 | h1457 | h1458 | h1459 | h1460 | h1461 | h1462 | h1463 | h1464 | h1465 | h1466 | h1467 | h1468 | h1469 | h1470 | h1471
  · have he : k = (1440 : Fin 2886) := Fin.ext h1440
    subst k
    rw [keyMomentRowsAt1440]
    exact keyMoment1440 B hB
  · have he : k = (1441 : Fin 2886) := Fin.ext h1441
    subst k
    rw [keyMomentRowsAt1441]
    exact keyMoment1441 B hB
  · have he : k = (1442 : Fin 2886) := Fin.ext h1442
    subst k
    rw [keyMomentRowsAt1442]
    exact keyMoment1442 B hB
  · have he : k = (1443 : Fin 2886) := Fin.ext h1443
    subst k
    rw [keyMomentRowsAt1443]
    exact keyMoment1443 B hB
  · have he : k = (1444 : Fin 2886) := Fin.ext h1444
    subst k
    rw [keyMomentRowsAt1444]
    exact keyMoment1444 B hB
  · have he : k = (1445 : Fin 2886) := Fin.ext h1445
    subst k
    rw [keyMomentRowsAt1445]
    exact keyMoment1445 B hB
  · have he : k = (1446 : Fin 2886) := Fin.ext h1446
    subst k
    rw [keyMomentRowsAt1446]
    exact keyMoment1446 B hB
  · have he : k = (1447 : Fin 2886) := Fin.ext h1447
    subst k
    rw [keyMomentRowsAt1447]
    exact keyMoment1447 B hB
  · have he : k = (1448 : Fin 2886) := Fin.ext h1448
    subst k
    rw [keyMomentRowsAt1448]
    exact keyMoment1448 B hB
  · have he : k = (1449 : Fin 2886) := Fin.ext h1449
    subst k
    rw [keyMomentRowsAt1449]
    exact keyMoment1449 B hB
  · have he : k = (1450 : Fin 2886) := Fin.ext h1450
    subst k
    rw [keyMomentRowsAt1450]
    exact keyMoment1450 B hB
  · have he : k = (1451 : Fin 2886) := Fin.ext h1451
    subst k
    rw [keyMomentRowsAt1451]
    exact keyMoment1451 B hB
  · have he : k = (1452 : Fin 2886) := Fin.ext h1452
    subst k
    rw [keyMomentRowsAt1452]
    exact keyMoment1452 B hB
  · have he : k = (1453 : Fin 2886) := Fin.ext h1453
    subst k
    rw [keyMomentRowsAt1453]
    exact keyMoment1453 B hB
  · have he : k = (1454 : Fin 2886) := Fin.ext h1454
    subst k
    rw [keyMomentRowsAt1454]
    exact keyMoment1454 B hB
  · have he : k = (1455 : Fin 2886) := Fin.ext h1455
    subst k
    rw [keyMomentRowsAt1455]
    exact keyMoment1455 B hB
  · have he : k = (1456 : Fin 2886) := Fin.ext h1456
    subst k
    rw [keyMomentRowsAt1456]
    exact keyMoment1456 B hB
  · have he : k = (1457 : Fin 2886) := Fin.ext h1457
    subst k
    rw [keyMomentRowsAt1457]
    exact keyMoment1457 B hB
  · have he : k = (1458 : Fin 2886) := Fin.ext h1458
    subst k
    rw [keyMomentRowsAt1458]
    exact keyMoment1458 B hB
  · have he : k = (1459 : Fin 2886) := Fin.ext h1459
    subst k
    rw [keyMomentRowsAt1459]
    exact keyMoment1459 B hB
  · have he : k = (1460 : Fin 2886) := Fin.ext h1460
    subst k
    rw [keyMomentRowsAt1460]
    exact keyMoment1460 B hB
  · have he : k = (1461 : Fin 2886) := Fin.ext h1461
    subst k
    rw [keyMomentRowsAt1461]
    exact keyMoment1461 B hB
  · have he : k = (1462 : Fin 2886) := Fin.ext h1462
    subst k
    rw [keyMomentRowsAt1462]
    exact keyMoment1462 B hB
  · have he : k = (1463 : Fin 2886) := Fin.ext h1463
    subst k
    rw [keyMomentRowsAt1463]
    exact keyMoment1463 B hB
  · have he : k = (1464 : Fin 2886) := Fin.ext h1464
    subst k
    rw [keyMomentRowsAt1464]
    exact keyMoment1464 B hB
  · have he : k = (1465 : Fin 2886) := Fin.ext h1465
    subst k
    rw [keyMomentRowsAt1465]
    exact keyMoment1465 B hB
  · have he : k = (1466 : Fin 2886) := Fin.ext h1466
    subst k
    rw [keyMomentRowsAt1466]
    exact keyMoment1466 B hB
  · have he : k = (1467 : Fin 2886) := Fin.ext h1467
    subst k
    rw [keyMomentRowsAt1467]
    exact keyMoment1467 B hB
  · have he : k = (1468 : Fin 2886) := Fin.ext h1468
    subst k
    rw [keyMomentRowsAt1468]
    exact keyMoment1468 B hB
  · have he : k = (1469 : Fin 2886) := Fin.ext h1469
    subst k
    rw [keyMomentRowsAt1469]
    exact keyMoment1469 B hB
  · have he : k = (1470 : Fin 2886) := Fin.ext h1470
    subst k
    rw [keyMomentRowsAt1470]
    exact keyMoment1470 B hB
  · have he : k = (1471 : Fin 2886) := Fin.ext h1471
    subst k
    rw [keyMomentRowsAt1471]
    exact keyMoment1471 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound45_e_oai
