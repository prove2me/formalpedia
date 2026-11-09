-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:49.648805+00:00
-- url     : https://prove2.me/submissions/9ef799d5-3471-435b-895a-075e012ef017

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical311
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39896 raw39896Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39896 raw39896Labels = mixedMoment B raw39896step0 raw39896step0Labels := by
      have hz : ∀ j, raw39896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39896step0 = (fun i j => raw39896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39896step0 raw39896; decide +kernel
      have hl : raw39896step0Labels = raw39896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39896 raw39896Labels permutation434 hz
    mixedMoment B raw39896step0 raw39896step0Labels = mixedMoment B raw39896step1 raw39896step1Labels := by
      have hz : ∀ j, raw39896step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39896step1 = (fun i j => raw39896step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39896step1 raw39896step0; decide +kernel
      have hl : raw39896step1Labels = raw39896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39896step0 raw39896step0Labels permutation80 hz
    mixedMoment B raw39896step1 raw39896step1Labels = mixedMoment B raw39896step2 raw39896step2Labels := by
      have ha : raw39896step2 = (fun i j => raw39896step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39896step2 raw39896step1; decide +kernel
      have hl : raw39896step2Labels = raw39896step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39896step1 raw39896step1Labels permutation11 permutation7
    mixedMoment B raw39896step2 raw39896step2Labels = mixedMoment B raw39896step3 raw39896step3Labels := by
      have ha : raw39896step3 = -raw39896step2 := by apply Matrix.ext; change ∀ i j, raw39896step3 i j = -(raw39896step2 i j); unfold raw39896step3 raw39896step2; decide +kernel
      have hl : raw39896step3Labels = raw39896step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical39897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39897 raw39897Labels = mixedMoment B node451 node451Labels := by
  calc
    mixedMoment B raw39897 raw39897Labels = mixedMoment B raw39897step0 raw39897step0Labels := by
      have hz : ∀ j, raw39897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39897step0 = (fun i j => raw39897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39897step0 raw39897; decide +kernel
      have hl : raw39897step0Labels = raw39897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39897 raw39897Labels permutation434 hz
    mixedMoment B raw39897step0 raw39897step0Labels = mixedMoment B raw39897step1 raw39897step1Labels := by
      have hz : ∀ j, raw39897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39897step1 = (fun i j => raw39897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39897step1 raw39897step0; decide +kernel
      have hl : raw39897step1Labels = raw39897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39897step0 raw39897step0Labels permutation80 hz
    mixedMoment B raw39897step1 raw39897step1Labels = mixedMoment B raw39897step2 raw39897step2Labels := by
      have ha : raw39897step2 = (fun i j => raw39897step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39897step2 raw39897step1; decide +kernel
      have hl : raw39897step2Labels = raw39897step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39897step1 raw39897step1Labels permutation18 permutation6
    _ = mixedMoment B node451 node451Labels := by rfl

theorem canonical39898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39898 raw39898Labels = mixedMoment B node369 node369Labels := by
  calc
    mixedMoment B raw39898 raw39898Labels = mixedMoment B raw39898step0 raw39898step0Labels := by
      have hz : ∀ j, raw39898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39898step0 = (fun i j => raw39898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39898step0 raw39898; decide +kernel
      have hl : raw39898step0Labels = raw39898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39898 raw39898Labels permutation434 hz
    mixedMoment B raw39898step0 raw39898step0Labels = mixedMoment B raw39898step1 raw39898step1Labels := by
      have hz : ∀ j, raw39898step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39898step1 = (fun i j => raw39898step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39898step1 raw39898step0; decide +kernel
      have hl : raw39898step1Labels = raw39898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39898step0 raw39898step0Labels permutation80 hz
    mixedMoment B raw39898step1 raw39898step1Labels = mixedMoment B raw39898step2 raw39898step2Labels := by
      have ha : raw39898step2 = (fun i j => raw39898step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39898step2 raw39898step1; decide +kernel
      have hl : raw39898step2Labels = raw39898step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39898step1 raw39898step1Labels permutation27 permutation4
    _ = mixedMoment B node369 node369Labels := by rfl

theorem canonical39899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39899 raw39899Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39899 raw39899Labels = mixedMoment B raw39899step0 raw39899step0Labels := by
      have hz : ∀ j, raw39899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39899step0 = (fun i j => raw39899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39899step0 raw39899; decide +kernel
      have hl : raw39899step0Labels = raw39899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39899 raw39899Labels permutation434 hz
    mixedMoment B raw39899step0 raw39899step0Labels = mixedMoment B raw39899step1 raw39899step1Labels := by
      have hz : ∀ j, raw39899step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39899step1 = (fun i j => raw39899step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39899step1 raw39899step0; decide +kernel
      have hl : raw39899step1Labels = raw39899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39899step0 raw39899step0Labels permutation80 hz
    mixedMoment B raw39899step1 raw39899step1Labels = mixedMoment B raw39899step2 raw39899step2Labels := by
      have ha : raw39899step2 = (fun i j => raw39899step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39899step2 raw39899step1; decide +kernel
      have hl : raw39899step2Labels = raw39899step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39899step1 raw39899step1Labels permutation17 permutation6
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical39900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39900 raw39900Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw39900 raw39900Labels = mixedMoment B raw39900step0 raw39900step0Labels := by
      have hz : ∀ j, raw39900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39900step0 = (fun i j => raw39900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39900step0 raw39900; decide +kernel
      have hl : raw39900step0Labels = raw39900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39900 raw39900Labels permutation434 hz
    mixedMoment B raw39900step0 raw39900step0Labels = mixedMoment B raw39900step1 raw39900step1Labels := by
      have hz : ∀ j, raw39900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39900step1 = (fun i j => raw39900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39900step1 raw39900step0; decide +kernel
      have hl : raw39900step1Labels = raw39900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39900step0 raw39900step0Labels permutation80 hz
    mixedMoment B raw39900step1 raw39900step1Labels = mixedMoment B raw39900step2 raw39900step2Labels := by
      have ha : raw39900step2 = (fun i j => raw39900step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39900step2 raw39900step1; decide +kernel
      have hl : raw39900step2Labels = raw39900step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39900step1 raw39900step1Labels permutation17 permutation6
    _ = mixedMoment B node505 node505Labels := by rfl

theorem canonical39901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39901 raw39901Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw39901 raw39901Labels = mixedMoment B raw39901step0 raw39901step0Labels := by
      have hz : ∀ j, raw39901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39901step0 = (fun i j => raw39901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39901step0 raw39901; decide +kernel
      have hl : raw39901step0Labels = raw39901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39901 raw39901Labels permutation346 hz
    mixedMoment B raw39901step0 raw39901step0Labels = mixedMoment B raw39901step1 raw39901step1Labels := by
      have ha : raw39901step1 = (fun i j => raw39901step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39901step1 raw39901step0; decide +kernel
      have hl : raw39901step1Labels = raw39901step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39901step0 raw39901step0Labels permutation137 permutation7
    _ = mixedMoment B node449 node449Labels := by rfl

theorem canonical39902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39902 raw39902Labels = mixedMoment B node286 node286Labels := by
  calc
    mixedMoment B raw39902 raw39902Labels = mixedMoment B raw39902step0 raw39902step0Labels := by
      have hz : ∀ j, raw39902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39902step0 = (fun i j => raw39902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39902step0 raw39902; decide +kernel
      have hl : raw39902step0Labels = raw39902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39902 raw39902Labels permutation346 hz
    mixedMoment B raw39902step0 raw39902step0Labels = mixedMoment B raw39902step1 raw39902step1Labels := by
      have ha : raw39902step1 = (fun i j => raw39902step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39902step1 raw39902step0; decide +kernel
      have hl : raw39902step1Labels = raw39902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39902step0 raw39902step0Labels permutation137 permutation7
    _ = mixedMoment B node286 node286Labels := by rfl

theorem canonical39903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39903 raw39903Labels = mixedMoment B node438 node438Labels := by
  calc
    mixedMoment B raw39903 raw39903Labels = mixedMoment B raw39903step0 raw39903step0Labels := by
      have hz : ∀ j, raw39903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39903step0 = (fun i j => raw39903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39903step0 raw39903; decide +kernel
      have hl : raw39903step0Labels = raw39903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39903 raw39903Labels permutation346 hz
    mixedMoment B raw39903step0 raw39903step0Labels = mixedMoment B raw39903step1 raw39903step1Labels := by
      have ha : raw39903step1 = (fun i j => raw39903step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39903step1 raw39903step0; decide +kernel
      have hl : raw39903step1Labels = raw39903step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39903step0 raw39903step0Labels permutation71 permutation6
    _ = mixedMoment B node438 node438Labels := by rfl

theorem canonical39904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39904 raw39904Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw39904 raw39904Labels = mixedMoment B raw39904step0 raw39904step0Labels := by
      have hz : ∀ j, raw39904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39904step0 = (fun i j => raw39904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39904step0 raw39904; decide +kernel
      have hl : raw39904step0Labels = raw39904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39904 raw39904Labels permutation346 hz
    mixedMoment B raw39904step0 raw39904step0Labels = mixedMoment B raw39904step1 raw39904step1Labels := by
      have ha : raw39904step1 = (fun i j => raw39904step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39904step1 raw39904step0; decide +kernel
      have hl : raw39904step1Labels = raw39904step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39904step0 raw39904step0Labels permutation73 permutation6
    _ = mixedMoment B node490 node490Labels := by rfl

theorem canonical39905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39905 raw39905Labels = mixedMoment B node432 node432Labels := by
  calc
    mixedMoment B raw39905 raw39905Labels = mixedMoment B raw39905step0 raw39905step0Labels := by
      have hz : ∀ j, raw39905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39905step0 = (fun i j => raw39905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39905step0 raw39905; decide +kernel
      have hl : raw39905step0Labels = raw39905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39905 raw39905Labels permutation346 hz
    mixedMoment B raw39905step0 raw39905step0Labels = mixedMoment B raw39905step1 raw39905step1Labels := by
      have ha : raw39905step1 = (fun i j => raw39905step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39905step1 raw39905step0; decide +kernel
      have hl : raw39905step1Labels = raw39905step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39905step0 raw39905step0Labels permutation72 permutation6
    _ = mixedMoment B node432 node432Labels := by rfl

theorem canonical39906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39906 raw39906Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw39906 raw39906Labels = mixedMoment B raw39906step0 raw39906step0Labels := by
      have hz : ∀ j, raw39906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39906step0 = (fun i j => raw39906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39906step0 raw39906; decide +kernel
      have hl : raw39906step0Labels = raw39906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39906 raw39906Labels permutation346 hz
    mixedMoment B raw39906step0 raw39906step0Labels = mixedMoment B raw39906step1 raw39906step1Labels := by
      have ha : raw39906step1 = (fun i j => raw39906step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39906step1 raw39906step0; decide +kernel
      have hl : raw39906step1Labels = raw39906step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39906step0 raw39906step0Labels permutation83 permutation6
    mixedMoment B raw39906step1 raw39906step1Labels = mixedMoment B raw39906step2 raw39906step2Labels := by
      have ha : raw39906step2 = -raw39906step1 := by apply Matrix.ext; change ∀ i j, raw39906step2 i j = -(raw39906step1 i j); unfold raw39906step2 raw39906step1; decide +kernel
      have hl : raw39906step2Labels = raw39906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node449 node449Labels := by rfl

theorem canonical39907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39907 raw39907Labels = mixedMoment B node178 node178Labels := by
  calc
    mixedMoment B raw39907 raw39907Labels = mixedMoment B raw39907step0 raw39907step0Labels := by
      have hz : ∀ j, raw39907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39907step0 = (fun i j => raw39907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39907step0 raw39907; decide +kernel
      have hl : raw39907step0Labels = raw39907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39907 raw39907Labels permutation346 hz
    mixedMoment B raw39907step0 raw39907step0Labels = mixedMoment B raw39907step1 raw39907step1Labels := by
      have ha : raw39907step1 = (fun i j => raw39907step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39907step1 raw39907step0; decide +kernel
      have hl : raw39907step1Labels = raw39907step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39907step0 raw39907step0Labels permutation85 permutation6
    mixedMoment B raw39907step1 raw39907step1Labels = mixedMoment B raw39907step2 raw39907step2Labels := by
      have ha : raw39907step2 = -raw39907step1 := by apply Matrix.ext; change ∀ i j, raw39907step2 i j = -(raw39907step1 i j); unfold raw39907step2 raw39907step1; decide +kernel
      have hl : raw39907step2Labels = raw39907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node178 node178Labels := by rfl

theorem canonical39908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39908 raw39908Labels = mixedMoment B node424 node424Labels := by
  calc
    mixedMoment B raw39908 raw39908Labels = mixedMoment B raw39908step0 raw39908step0Labels := by
      have ha : raw39908step0 = (fun i j => raw39908 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39908step0 raw39908; decide +kernel
      have hl : raw39908step0Labels = raw39908Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39908 raw39908Labels permutation331 permutation6
    _ = mixedMoment B node424 node424Labels := by rfl

theorem canonical39909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39909 raw39909Labels = mixedMoment B node492 node492Labels := by
  calc
    mixedMoment B raw39909 raw39909Labels = mixedMoment B raw39909step0 raw39909step0Labels := by
      have ha : raw39909step0 = (fun i j => raw39909 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39909step0 raw39909; decide +kernel
      have hl : raw39909step0Labels = raw39909Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39909 raw39909Labels permutation665 permutation5
    _ = mixedMoment B node492 node492Labels := by rfl

theorem canonical39910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39910 raw39910Labels = mixedMoment B node179 node179Labels := by
  calc
    mixedMoment B raw39910 raw39910Labels = mixedMoment B raw39910step0 raw39910step0Labels := by
      have ha : raw39910step0 = (fun i j => raw39910 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39910step0 raw39910; decide +kernel
      have hl : raw39910step0Labels = raw39910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39910 raw39910Labels permutation520 permutation6
    mixedMoment B raw39910step0 raw39910step0Labels = mixedMoment B raw39910step1 raw39910step1Labels := by
      have ha : raw39910step1 = -raw39910step0 := by apply Matrix.ext; change ∀ i j, raw39910step1 i j = -(raw39910step0 i j); unfold raw39910step1 raw39910step0; decide +kernel
      have hl : raw39910step1Labels = raw39910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node179 node179Labels := by rfl

theorem canonical39911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39911 raw39911Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw39911 raw39911Labels = mixedMoment B raw39911step0 raw39911step0Labels := by
      have hz : ∀ j, raw39911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39911step0 = (fun i j => raw39911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39911step0 raw39911; decide +kernel
      have hl : raw39911step0Labels = raw39911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39911 raw39911Labels permutation520 hz
    mixedMoment B raw39911step0 raw39911step0Labels = mixedMoment B raw39911step1 raw39911step1Labels := by
      have hz : ∀ j, raw39911step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39911step1 = (fun i j => raw39911step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39911step1 raw39911step0; decide +kernel
      have hl : raw39911step1Labels = raw39911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39911step0 raw39911step0Labels permutation104 hz
    _ = mixedMoment B node505 node505Labels := by rfl

theorem canonical39912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39912 raw39912Labels = mixedMoment B node449 node449Labels := by
  calc
    mixedMoment B raw39912 raw39912Labels = mixedMoment B raw39912step0 raw39912step0Labels := by
      have hz : ∀ j, raw39912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39912step0 = (fun i j => raw39912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39912step0 raw39912; decide +kernel
      have hl : raw39912step0Labels = raw39912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39912 raw39912Labels permutation434 hz
    mixedMoment B raw39912step0 raw39912step0Labels = mixedMoment B raw39912step1 raw39912step1Labels := by
      have ha : raw39912step1 = (fun i j => raw39912step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39912step1 raw39912step0; decide +kernel
      have hl : raw39912step1Labels = raw39912step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39912step0 raw39912step0Labels permutation44 permutation7
    mixedMoment B raw39912step1 raw39912step1Labels = mixedMoment B raw39912step2 raw39912step2Labels := by
      have ha : raw39912step2 = -raw39912step1 := by apply Matrix.ext; change ∀ i j, raw39912step2 i j = -(raw39912step1 i j); unfold raw39912step2 raw39912step1; decide +kernel
      have hl : raw39912step2Labels = raw39912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node449 node449Labels := by rfl

theorem canonical39913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39913 raw39913Labels = mixedMoment B node180 node180Labels := by
  calc
    mixedMoment B raw39913 raw39913Labels = mixedMoment B raw39913step0 raw39913step0Labels := by
      have hz : ∀ j, raw39913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39913step0 = (fun i j => raw39913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39913step0 raw39913; decide +kernel
      have hl : raw39913step0Labels = raw39913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39913 raw39913Labels permutation434 hz
    mixedMoment B raw39913step0 raw39913step0Labels = mixedMoment B raw39913step1 raw39913step1Labels := by
      have ha : raw39913step1 = (fun i j => raw39913step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39913step1 raw39913step0; decide +kernel
      have hl : raw39913step1Labels = raw39913step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39913step0 raw39913step0Labels permutation104 permutation6
    mixedMoment B raw39913step1 raw39913step1Labels = mixedMoment B raw39913step2 raw39913step2Labels := by
      have ha : raw39913step2 = -raw39913step1 := by apply Matrix.ext; change ∀ i j, raw39913step2 i j = -(raw39913step1 i j); unfold raw39913step2 raw39913step1; decide +kernel
      have hl : raw39913step2Labels = raw39913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node180 node180Labels := by rfl

theorem canonical39914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39914 raw39914Labels = mixedMoment B node471 node471Labels := by
  calc
    mixedMoment B raw39914 raw39914Labels = mixedMoment B raw39914step0 raw39914step0Labels := by
      have ha : raw39914step0 = (fun i j => raw39914 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39914step0 raw39914; decide +kernel
      have hl : raw39914step0Labels = raw39914Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39914 raw39914Labels permutation609 permutation7
    _ = mixedMoment B node471 node471Labels := by rfl

theorem canonical39915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39915 raw39915Labels = mixedMoment B node317 node317Labels := by
  calc
    mixedMoment B raw39915 raw39915Labels = mixedMoment B raw39915step0 raw39915step0Labels := by
      have ha : raw39915step0 = (fun i j => raw39915 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39915step0 raw39915; decide +kernel
      have hl : raw39915step0Labels = raw39915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39915 raw39915Labels permutation609 permutation7
    _ = mixedMoment B node317 node317Labels := by rfl

theorem canonical39916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39916 raw39916Labels = mixedMoment B node448 node448Labels := by
  calc
    mixedMoment B raw39916 raw39916Labels = mixedMoment B raw39916step0 raw39916step0Labels := by
      have ha : raw39916step0 = (fun i j => raw39916 (permutation446 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39916step0 raw39916; decide +kernel
      have hl : raw39916step0Labels = raw39916Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39916 raw39916Labels permutation446 permutation6
    mixedMoment B raw39916step0 raw39916step0Labels = mixedMoment B raw39916step1 raw39916step1Labels := by
      have ha : raw39916step1 = -raw39916step0 := by apply Matrix.ext; change ∀ i j, raw39916step1 i j = -(raw39916step0 i j); unfold raw39916step1 raw39916step0; decide +kernel
      have hl : raw39916step1Labels = raw39916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node448 node448Labels := by rfl

theorem canonical39917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39917 raw39917Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw39917 raw39917Labels = mixedMoment B raw39917step0 raw39917step0Labels := by
      have hz : ∀ j, raw39917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39917step0 = (fun i j => raw39917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39917step0 raw39917; decide +kernel
      have hl : raw39917step0Labels = raw39917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39917 raw39917Labels permutation434 hz
    mixedMoment B raw39917step0 raw39917step0Labels = mixedMoment B raw39917step1 raw39917step1Labels := by
      have hz : ∀ j, raw39917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39917step1 = (fun i j => raw39917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39917step1 raw39917step0; decide +kernel
      have hl : raw39917step1Labels = raw39917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39917step0 raw39917step0Labels permutation80 hz
    mixedMoment B raw39917step1 raw39917step1Labels = mixedMoment B raw39917step2 raw39917step2Labels := by
      have ha : raw39917step2 = (fun i j => raw39917step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39917step2 raw39917step1; decide +kernel
      have hl : raw39917step2Labels = raw39917step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39917step1 raw39917step1Labels permutation29 permutation7
    _ = mixedMoment B node343 node343Labels := by rfl

theorem canonical39918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39918 raw39918Labels = mixedMoment B node316 node316Labels := by
  calc
    mixedMoment B raw39918 raw39918Labels = mixedMoment B raw39918step0 raw39918step0Labels := by
      have hz : ∀ j, raw39918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39918step0 = (fun i j => raw39918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39918step0 raw39918; decide +kernel
      have hl : raw39918step0Labels = raw39918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39918 raw39918Labels permutation434 hz
    mixedMoment B raw39918step0 raw39918step0Labels = mixedMoment B raw39918step1 raw39918step1Labels := by
      have hz : ∀ j, raw39918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39918step1 = (fun i j => raw39918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39918step1 raw39918step0; decide +kernel
      have hl : raw39918step1Labels = raw39918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39918step0 raw39918step0Labels permutation80 hz
    mixedMoment B raw39918step1 raw39918step1Labels = mixedMoment B raw39918step2 raw39918step2Labels := by
      have ha : raw39918step2 = (fun i j => raw39918step1 (permutation22 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39918step2 raw39918step1; decide +kernel
      have hl : raw39918step2Labels = raw39918step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39918step1 raw39918step1Labels permutation22 permutation6
    _ = mixedMoment B node316 node316Labels := by rfl

theorem canonical39919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39919 raw39919Labels = mixedMoment B node335 node335Labels := by
  calc
    mixedMoment B raw39919 raw39919Labels = mixedMoment B raw39919step0 raw39919step0Labels := by
      have hz : ∀ j, raw39919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39919step0 = (fun i j => raw39919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39919step0 raw39919; decide +kernel
      have hl : raw39919step0Labels = raw39919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39919 raw39919Labels permutation346 hz
    mixedMoment B raw39919step0 raw39919step0Labels = mixedMoment B raw39919step1 raw39919step1Labels := by
      have ha : raw39919step1 = (fun i j => raw39919step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39919step1 raw39919step0; decide +kernel
      have hl : raw39919step1Labels = raw39919step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39919step0 raw39919step0Labels permutation137 permutation7
    _ = mixedMoment B node335 node335Labels := by rfl

theorem canonical39920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39920 raw39920Labels = mixedMoment B node127 node127Labels := by
  calc
    mixedMoment B raw39920 raw39920Labels = mixedMoment B raw39920step0 raw39920step0Labels := by
      have hz : ∀ j, raw39920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39920step0 = (fun i j => raw39920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39920step0 raw39920; decide +kernel
      have hl : raw39920step0Labels = raw39920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39920 raw39920Labels permutation346 hz
    mixedMoment B raw39920step0 raw39920step0Labels = mixedMoment B raw39920step1 raw39920step1Labels := by
      have ha : raw39920step1 = (fun i j => raw39920step0 (permutation136 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39920step1 raw39920step0; decide +kernel
      have hl : raw39920step1Labels = raw39920step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39920step0 raw39920step0Labels permutation136 permutation6
    _ = mixedMoment B node127 node127Labels := by rfl

theorem canonical39921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39921 raw39921Labels = mixedMoment B node314 node314Labels := by
  calc
    mixedMoment B raw39921 raw39921Labels = mixedMoment B raw39921step0 raw39921step0Labels := by
      have hz : ∀ j, raw39921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39921step0 = (fun i j => raw39921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39921step0 raw39921; decide +kernel
      have hl : raw39921step0Labels = raw39921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39921 raw39921Labels permutation346 hz
    mixedMoment B raw39921step0 raw39921step0Labels = mixedMoment B raw39921step1 raw39921step1Labels := by
      have ha : raw39921step1 = (fun i j => raw39921step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39921step1 raw39921step0; decide +kernel
      have hl : raw39921step1Labels = raw39921step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39921step0 raw39921step0Labels permutation113 permutation6
    _ = mixedMoment B node314 node314Labels := by rfl

theorem canonical39922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39922 raw39922Labels = mixedMoment B node306 node306Labels := by
  calc
    mixedMoment B raw39922 raw39922Labels = mixedMoment B raw39922step0 raw39922step0Labels := by
      have hz : ∀ j, raw39922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39922step0 = (fun i j => raw39922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39922step0 raw39922; decide +kernel
      have hl : raw39922step0Labels = raw39922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39922 raw39922Labels permutation346 hz
    mixedMoment B raw39922step0 raw39922step0Labels = mixedMoment B raw39922step1 raw39922step1Labels := by
      have ha : raw39922step1 = (fun i j => raw39922step0 (permutation114 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39922step1 raw39922step0; decide +kernel
      have hl : raw39922step1Labels = raw39922step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39922step0 raw39922step0Labels permutation114 permutation6
    _ = mixedMoment B node306 node306Labels := by rfl

theorem canonical39923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39923 raw39923Labels = mixedMoment B node450 node450Labels := by
  calc
    mixedMoment B raw39923 raw39923Labels = mixedMoment B raw39923step0 raw39923step0Labels := by
      have hz : ∀ j, raw39923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39923step0 = (fun i j => raw39923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39923step0 raw39923; decide +kernel
      have hl : raw39923step0Labels = raw39923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39923 raw39923Labels permutation346 hz
    mixedMoment B raw39923step0 raw39923step0Labels = mixedMoment B raw39923step1 raw39923step1Labels := by
      have ha : raw39923step1 = (fun i j => raw39923step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39923step1 raw39923step0; decide +kernel
      have hl : raw39923step1Labels = raw39923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39923step0 raw39923step0Labels permutation84 permutation6
    mixedMoment B raw39923step1 raw39923step1Labels = mixedMoment B raw39923step2 raw39923step2Labels := by
      have ha : raw39923step2 = -raw39923step1 := by apply Matrix.ext; change ∀ i j, raw39923step2 i j = -(raw39923step1 i j); unfold raw39923step2 raw39923step1; decide +kernel
      have hl : raw39923step2Labels = raw39923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node450 node450Labels := by rfl

theorem canonical39924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39924 raw39924Labels = mixedMoment B node175 node175Labels := by
  calc
    mixedMoment B raw39924 raw39924Labels = mixedMoment B raw39924step0 raw39924step0Labels := by
      have hz : ∀ j, raw39924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39924step0 = (fun i j => raw39924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39924step0 raw39924; decide +kernel
      have hl : raw39924step0Labels = raw39924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39924 raw39924Labels permutation346 hz
    mixedMoment B raw39924step0 raw39924step0Labels = mixedMoment B raw39924step1 raw39924step1Labels := by
      have ha : raw39924step1 = (fun i j => raw39924step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39924step1 raw39924step0; decide +kernel
      have hl : raw39924step1Labels = raw39924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39924step0 raw39924step0Labels permutation84 permutation6
    mixedMoment B raw39924step1 raw39924step1Labels = mixedMoment B raw39924step2 raw39924step2Labels := by
      have ha : raw39924step2 = -raw39924step1 := by apply Matrix.ext; change ∀ i j, raw39924step2 i j = -(raw39924step1 i j); unfold raw39924step2 raw39924step1; decide +kernel
      have hl : raw39924step2Labels = raw39924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node175 node175Labels := by rfl

theorem canonical39925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39925 raw39925Labels = mixedMoment B node295 node295Labels := by
  calc
    mixedMoment B raw39925 raw39925Labels = mixedMoment B raw39925step0 raw39925step0Labels := by
      have ha : raw39925step0 = (fun i j => raw39925 (permutation539 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39925step0 raw39925; decide +kernel
      have hl : raw39925step0Labels = raw39925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39925 raw39925Labels permutation539 permutation6
    _ = mixedMoment B node295 node295Labels := by rfl

theorem canonical39926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39926 raw39926Labels = mixedMoment B node160 node160Labels := by
  calc
    mixedMoment B raw39926 raw39926Labels = mixedMoment B raw39926step0 raw39926step0Labels := by
      have hz : ∀ j, raw39926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39926step0 = (fun i j => raw39926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39926step0 raw39926; decide +kernel
      have hl : raw39926step0Labels = raw39926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39926 raw39926Labels permutation434 hz
    mixedMoment B raw39926step0 raw39926step0Labels = mixedMoment B raw39926step1 raw39926step1Labels := by
      have hz : ∀ j, raw39926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39926step1 = (fun i j => raw39926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39926step1 raw39926step0; decide +kernel
      have hl : raw39926step1Labels = raw39926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39926step0 raw39926step0Labels permutation80 hz
    mixedMoment B raw39926step1 raw39926step1Labels = mixedMoment B raw39926step2 raw39926step2Labels := by
      have hz : ∀ j, raw39926step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39926step2 = (fun i j => raw39926step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39926step2 raw39926step1; decide +kernel
      have hl : raw39926step2Labels = raw39926step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39926step1 raw39926step1Labels permutation14 hz
    mixedMoment B raw39926step2 raw39926step2Labels = mixedMoment B raw39926step3 raw39926step3Labels := by
      have ha : raw39926step3 = (fun i j => raw39926step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39926step3 raw39926step2; decide +kernel
      have hl : raw39926step3Labels = raw39926step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39926step2 raw39926step2Labels permutation6 permutation6
    _ = mixedMoment B node160 node160Labels := by rfl

theorem canonical39927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39927 raw39927Labels = mixedMoment B node38 node38Labels := by
  calc
    mixedMoment B raw39927 raw39927Labels = mixedMoment B raw39927step0 raw39927step0Labels := by
      have hz : ∀ j, raw39927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39927step0 = (fun i j => raw39927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39927step0 raw39927; decide +kernel
      have hl : raw39927step0Labels = raw39927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39927 raw39927Labels permutation434 hz
    mixedMoment B raw39927step0 raw39927step0Labels = mixedMoment B raw39927step1 raw39927step1Labels := by
      have hz : ∀ j, raw39927step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39927step1 = (fun i j => raw39927step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39927step1 raw39927step0; decide +kernel
      have hl : raw39927step1Labels = raw39927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39927step0 raw39927step0Labels permutation80 hz
    mixedMoment B raw39927step1 raw39927step1Labels = mixedMoment B raw39927step2 raw39927step2Labels := by
      have hz : ∀ j, raw39927step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39927step2 = (fun i j => raw39927step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39927step2 raw39927step1; decide +kernel
      have hl : raw39927step2Labels = raw39927step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39927step1 raw39927step1Labels permutation14 hz
    mixedMoment B raw39927step2 raw39927step2Labels = mixedMoment B raw39927step3 raw39927step3Labels := by
      have ha : raw39927step3 = (fun i j => raw39927step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39927step3 raw39927step2; decide +kernel
      have hl : raw39927step3Labels = raw39927step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39927step2 raw39927step2Labels permutation6 permutation6
    _ = mixedMoment B node38 node38Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment448 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 448) =
      Integer.Sparse.eval keyMomentRow448 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 448).leftCharge (GramAssembly.key 448).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 448).leftCharge (GramAssembly.key 448).rightCharge = raw39896 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39896Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39896 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 448).leftCharge (GramAssembly.key 448).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow448, Integer.Sparse.eval]

theorem keyMoment449 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 449) =
      Integer.Sparse.eval keyMomentRow449 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 449).leftCharge (GramAssembly.key 449).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 451) := by
    have ha : gramCharges (GramAssembly.key 449).leftCharge (GramAssembly.key 449).rightCharge = raw39897 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39897Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39897 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 449).leftCharge (GramAssembly.key 449).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow449, Integer.Sparse.eval]

theorem keyMoment450 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 450) =
      Integer.Sparse.eval keyMomentRow450 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 450).leftCharge (GramAssembly.key 450).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 369) := by
    have ha : gramCharges (GramAssembly.key 450).leftCharge (GramAssembly.key 450).rightCharge = raw39898 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39898Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39898 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 450).leftCharge (GramAssembly.key 450).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow450, Integer.Sparse.eval]

theorem keyMoment451 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 451) =
      Integer.Sparse.eval keyMomentRow451 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 451).leftCharge (GramAssembly.key 451).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 451).leftCharge (GramAssembly.key 451).rightCharge = raw39899 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39899Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39899 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 451).leftCharge (GramAssembly.key 451).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow451, Integer.Sparse.eval]

theorem keyMoment452 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 452) =
      Integer.Sparse.eval keyMomentRow452 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 452).leftCharge (GramAssembly.key 452).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 452).leftCharge (GramAssembly.key 452).rightCharge = raw39900 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39900Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39900 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 452).leftCharge (GramAssembly.key 452).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow452, Integer.Sparse.eval]

theorem keyMoment453 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 453) =
      Integer.Sparse.eval keyMomentRow453 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 453).leftCharge (GramAssembly.key 453).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 453).leftCharge (GramAssembly.key 453).rightCharge = raw39901 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39901Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39901 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 453).leftCharge (GramAssembly.key 453).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow453, Integer.Sparse.eval]

theorem keyMoment454 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 454) =
      Integer.Sparse.eval keyMomentRow454 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 454).leftCharge (GramAssembly.key 454).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 286) := by
    have ha : gramCharges (GramAssembly.key 454).leftCharge (GramAssembly.key 454).rightCharge = raw39902 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39902Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39902 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 454).leftCharge (GramAssembly.key 454).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow454, Integer.Sparse.eval]

theorem keyMoment455 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 455) =
      Integer.Sparse.eval keyMomentRow455 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 455).leftCharge (GramAssembly.key 455).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 438) := by
    have ha : gramCharges (GramAssembly.key 455).leftCharge (GramAssembly.key 455).rightCharge = raw39903 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39903Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39903 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 455).leftCharge (GramAssembly.key 455).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow455, Integer.Sparse.eval]

theorem keyMoment456 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 456) =
      Integer.Sparse.eval keyMomentRow456 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 456).leftCharge (GramAssembly.key 456).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 456).leftCharge (GramAssembly.key 456).rightCharge = raw39904 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39904Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39904 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 456).leftCharge (GramAssembly.key 456).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow456, Integer.Sparse.eval]

theorem keyMoment457 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 457) =
      Integer.Sparse.eval keyMomentRow457 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 457).leftCharge (GramAssembly.key 457).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 432) := by
    have ha : gramCharges (GramAssembly.key 457).leftCharge (GramAssembly.key 457).rightCharge = raw39905 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39905Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39905 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 457).leftCharge (GramAssembly.key 457).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow457, Integer.Sparse.eval]

theorem keyMoment458 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 458) =
      Integer.Sparse.eval keyMomentRow458 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 458).leftCharge (GramAssembly.key 458).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 458).leftCharge (GramAssembly.key 458).rightCharge = raw39906 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39906Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39906 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 458).leftCharge (GramAssembly.key 458).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow458, Integer.Sparse.eval]

theorem keyMoment459 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 459) =
      Integer.Sparse.eval keyMomentRow459 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 459).leftCharge (GramAssembly.key 459).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 178) := by
    have ha : gramCharges (GramAssembly.key 459).leftCharge (GramAssembly.key 459).rightCharge = raw39907 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39907Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39907 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 459).leftCharge (GramAssembly.key 459).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow459, Integer.Sparse.eval]

theorem keyMoment460 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 460) =
      Integer.Sparse.eval keyMomentRow460 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 460).leftCharge (GramAssembly.key 460).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 424) := by
    have ha : gramCharges (GramAssembly.key 460).leftCharge (GramAssembly.key 460).rightCharge = raw39908 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39908Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39908 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 460).leftCharge (GramAssembly.key 460).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow460, Integer.Sparse.eval]

theorem keyMoment461 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 461) =
      Integer.Sparse.eval keyMomentRow461 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 461).leftCharge (GramAssembly.key 461).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 492) := by
    have ha : gramCharges (GramAssembly.key 461).leftCharge (GramAssembly.key 461).rightCharge = raw39909 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39909Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39909 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 461).leftCharge (GramAssembly.key 461).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow461, Integer.Sparse.eval]

theorem keyMoment462 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 462) =
      Integer.Sparse.eval keyMomentRow462 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 462).leftCharge (GramAssembly.key 462).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 179) := by
    have ha : gramCharges (GramAssembly.key 462).leftCharge (GramAssembly.key 462).rightCharge = raw39910 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39910Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39910 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 462).leftCharge (GramAssembly.key 462).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow462, Integer.Sparse.eval]

theorem keyMoment463 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 463) =
      Integer.Sparse.eval keyMomentRow463 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 463).leftCharge (GramAssembly.key 463).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 463).leftCharge (GramAssembly.key 463).rightCharge = raw39911 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39911Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39911 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 463).leftCharge (GramAssembly.key 463).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow463, Integer.Sparse.eval]

theorem keyMoment464 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 464) =
      Integer.Sparse.eval keyMomentRow464 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 464).leftCharge (GramAssembly.key 464).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 449) := by
    have ha : gramCharges (GramAssembly.key 464).leftCharge (GramAssembly.key 464).rightCharge = raw39912 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39912Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39912 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 464).leftCharge (GramAssembly.key 464).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow464, Integer.Sparse.eval]

theorem keyMoment465 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 465) =
      Integer.Sparse.eval keyMomentRow465 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 465).leftCharge (GramAssembly.key 465).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 180) := by
    have ha : gramCharges (GramAssembly.key 465).leftCharge (GramAssembly.key 465).rightCharge = raw39913 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39913Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39913 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 465).leftCharge (GramAssembly.key 465).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow465, Integer.Sparse.eval]

theorem keyMoment466 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 466) =
      Integer.Sparse.eval keyMomentRow466 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 466).leftCharge (GramAssembly.key 466).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 471) := by
    have ha : gramCharges (GramAssembly.key 466).leftCharge (GramAssembly.key 466).rightCharge = raw39914 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39914Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39914 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 466).leftCharge (GramAssembly.key 466).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow466, Integer.Sparse.eval]

theorem keyMoment467 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 467) =
      Integer.Sparse.eval keyMomentRow467 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 467).leftCharge (GramAssembly.key 467).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 317) := by
    have ha : gramCharges (GramAssembly.key 467).leftCharge (GramAssembly.key 467).rightCharge = raw39915 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39915Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39915 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 467).leftCharge (GramAssembly.key 467).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow467, Integer.Sparse.eval]

theorem keyMoment468 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 468) =
      Integer.Sparse.eval keyMomentRow468 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 468).leftCharge (GramAssembly.key 468).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 448) := by
    have ha : gramCharges (GramAssembly.key 468).leftCharge (GramAssembly.key 468).rightCharge = raw39916 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39916Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39916 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 468).leftCharge (GramAssembly.key 468).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow468, Integer.Sparse.eval]

theorem keyMoment469 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 469) =
      Integer.Sparse.eval keyMomentRow469 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 469).leftCharge (GramAssembly.key 469).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 343) := by
    have ha : gramCharges (GramAssembly.key 469).leftCharge (GramAssembly.key 469).rightCharge = raw39917 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39917Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39917 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 469).leftCharge (GramAssembly.key 469).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow469, Integer.Sparse.eval]

theorem keyMoment470 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 470) =
      Integer.Sparse.eval keyMomentRow470 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 470).leftCharge (GramAssembly.key 470).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 316) := by
    have ha : gramCharges (GramAssembly.key 470).leftCharge (GramAssembly.key 470).rightCharge = raw39918 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39918Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39918 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 470).leftCharge (GramAssembly.key 470).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow470, Integer.Sparse.eval]

theorem keyMoment471 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 471) =
      Integer.Sparse.eval keyMomentRow471 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 471).leftCharge (GramAssembly.key 471).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 335) := by
    have ha : gramCharges (GramAssembly.key 471).leftCharge (GramAssembly.key 471).rightCharge = raw39919 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39919Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39919 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 471).leftCharge (GramAssembly.key 471).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow471, Integer.Sparse.eval]

theorem keyMoment472 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 472) =
      Integer.Sparse.eval keyMomentRow472 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 472).leftCharge (GramAssembly.key 472).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 127) := by
    have ha : gramCharges (GramAssembly.key 472).leftCharge (GramAssembly.key 472).rightCharge = raw39920 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39920Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39920 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 472).leftCharge (GramAssembly.key 472).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow472, Integer.Sparse.eval]

theorem keyMoment473 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 473) =
      Integer.Sparse.eval keyMomentRow473 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 473).leftCharge (GramAssembly.key 473).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 314) := by
    have ha : gramCharges (GramAssembly.key 473).leftCharge (GramAssembly.key 473).rightCharge = raw39921 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39921Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39921 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 473).leftCharge (GramAssembly.key 473).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow473, Integer.Sparse.eval]

theorem keyMoment474 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 474) =
      Integer.Sparse.eval keyMomentRow474 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 474).leftCharge (GramAssembly.key 474).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 306) := by
    have ha : gramCharges (GramAssembly.key 474).leftCharge (GramAssembly.key 474).rightCharge = raw39922 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39922Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39922 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 474).leftCharge (GramAssembly.key 474).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow474, Integer.Sparse.eval]

theorem keyMoment475 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 475) =
      Integer.Sparse.eval keyMomentRow475 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 475).leftCharge (GramAssembly.key 475).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 450) := by
    have ha : gramCharges (GramAssembly.key 475).leftCharge (GramAssembly.key 475).rightCharge = raw39923 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39923Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39923 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 475).leftCharge (GramAssembly.key 475).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow475, Integer.Sparse.eval]

theorem keyMoment476 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 476) =
      Integer.Sparse.eval keyMomentRow476 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 476).leftCharge (GramAssembly.key 476).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 175) := by
    have ha : gramCharges (GramAssembly.key 476).leftCharge (GramAssembly.key 476).rightCharge = raw39924 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39924Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39924 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 476).leftCharge (GramAssembly.key 476).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow476, Integer.Sparse.eval]

theorem keyMoment477 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 477) =
      Integer.Sparse.eval keyMomentRow477 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 477).leftCharge (GramAssembly.key 477).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 295) := by
    have ha : gramCharges (GramAssembly.key 477).leftCharge (GramAssembly.key 477).rightCharge = raw39925 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39925Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39925 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 477).leftCharge (GramAssembly.key 477).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow477, Integer.Sparse.eval]

theorem keyMoment478 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 478) =
      Integer.Sparse.eval keyMomentRow478 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 478).leftCharge (GramAssembly.key 478).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 160) := by
    have ha : gramCharges (GramAssembly.key 478).leftCharge (GramAssembly.key 478).rightCharge = raw39926 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39926Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39926 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 478).leftCharge (GramAssembly.key 478).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow478, Integer.Sparse.eval]

theorem keyMoment479 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 479) =
      Integer.Sparse.eval keyMomentRow479 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 479).leftCharge (GramAssembly.key 479).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 38) := by
    have ha : gramCharges (GramAssembly.key 479).leftCharge (GramAssembly.key 479).rightCharge = raw39927 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39927Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39927 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 479).leftCharge (GramAssembly.key 479).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow479, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt448 : keyMomentRows (448 : Fin 2886) =
    keyMomentRow448 := by decide +kernel

theorem keyMomentRowsAt449 : keyMomentRows (449 : Fin 2886) =
    keyMomentRow449 := by decide +kernel

theorem keyMomentRowsAt450 : keyMomentRows (450 : Fin 2886) =
    keyMomentRow450 := by decide +kernel

theorem keyMomentRowsAt451 : keyMomentRows (451 : Fin 2886) =
    keyMomentRow451 := by decide +kernel

theorem keyMomentRowsAt452 : keyMomentRows (452 : Fin 2886) =
    keyMomentRow452 := by decide +kernel

theorem keyMomentRowsAt453 : keyMomentRows (453 : Fin 2886) =
    keyMomentRow453 := by decide +kernel

theorem keyMomentRowsAt454 : keyMomentRows (454 : Fin 2886) =
    keyMomentRow454 := by decide +kernel

theorem keyMomentRowsAt455 : keyMomentRows (455 : Fin 2886) =
    keyMomentRow455 := by decide +kernel

theorem keyMomentRowsAt456 : keyMomentRows (456 : Fin 2886) =
    keyMomentRow456 := by decide +kernel

theorem keyMomentRowsAt457 : keyMomentRows (457 : Fin 2886) =
    keyMomentRow457 := by decide +kernel

theorem keyMomentRowsAt458 : keyMomentRows (458 : Fin 2886) =
    keyMomentRow458 := by decide +kernel

theorem keyMomentRowsAt459 : keyMomentRows (459 : Fin 2886) =
    keyMomentRow459 := by decide +kernel

theorem keyMomentRowsAt460 : keyMomentRows (460 : Fin 2886) =
    keyMomentRow460 := by decide +kernel

theorem keyMomentRowsAt461 : keyMomentRows (461 : Fin 2886) =
    keyMomentRow461 := by decide +kernel

theorem keyMomentRowsAt462 : keyMomentRows (462 : Fin 2886) =
    keyMomentRow462 := by decide +kernel

theorem keyMomentRowsAt463 : keyMomentRows (463 : Fin 2886) =
    keyMomentRow463 := by decide +kernel

theorem keyMomentRowsAt464 : keyMomentRows (464 : Fin 2886) =
    keyMomentRow464 := by decide +kernel

theorem keyMomentRowsAt465 : keyMomentRows (465 : Fin 2886) =
    keyMomentRow465 := by decide +kernel

theorem keyMomentRowsAt466 : keyMomentRows (466 : Fin 2886) =
    keyMomentRow466 := by decide +kernel

theorem keyMomentRowsAt467 : keyMomentRows (467 : Fin 2886) =
    keyMomentRow467 := by decide +kernel

theorem keyMomentRowsAt468 : keyMomentRows (468 : Fin 2886) =
    keyMomentRow468 := by decide +kernel

theorem keyMomentRowsAt469 : keyMomentRows (469 : Fin 2886) =
    keyMomentRow469 := by decide +kernel

theorem keyMomentRowsAt470 : keyMomentRows (470 : Fin 2886) =
    keyMomentRow470 := by decide +kernel

theorem keyMomentRowsAt471 : keyMomentRows (471 : Fin 2886) =
    keyMomentRow471 := by decide +kernel

theorem keyMomentRowsAt472 : keyMomentRows (472 : Fin 2886) =
    keyMomentRow472 := by decide +kernel

theorem keyMomentRowsAt473 : keyMomentRows (473 : Fin 2886) =
    keyMomentRow473 := by decide +kernel

theorem keyMomentRowsAt474 : keyMomentRows (474 : Fin 2886) =
    keyMomentRow474 := by decide +kernel

theorem keyMomentRowsAt475 : keyMomentRows (475 : Fin 2886) =
    keyMomentRow475 := by decide +kernel

theorem keyMomentRowsAt476 : keyMomentRows (476 : Fin 2886) =
    keyMomentRow476 := by decide +kernel

theorem keyMomentRowsAt477 : keyMomentRows (477 : Fin 2886) =
    keyMomentRow477 := by decide +kernel

theorem keyMomentRowsAt478 : keyMomentRows (478 : Fin 2886) =
    keyMomentRow478 := by decide +kernel

theorem keyMomentRowsAt479 : keyMomentRows (479 : Fin 2886) =
    keyMomentRow479 := by decide +kernel

theorem keyMomentChunkSound14_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 14) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 448 ∨ k.val = 449 ∨ k.val = 450 ∨ k.val = 451 ∨ k.val = 452 ∨ k.val = 453 ∨ k.val = 454 ∨ k.val = 455 ∨ k.val = 456 ∨ k.val = 457 ∨ k.val = 458 ∨ k.val = 459 ∨ k.val = 460 ∨ k.val = 461 ∨ k.val = 462 ∨ k.val = 463 ∨ k.val = 464 ∨ k.val = 465 ∨ k.val = 466 ∨ k.val = 467 ∨ k.val = 468 ∨ k.val = 469 ∨ k.val = 470 ∨ k.val = 471 ∨ k.val = 472 ∨ k.val = 473 ∨ k.val = 474 ∨ k.val = 475 ∨ k.val = 476 ∨ k.val = 477 ∨ k.val = 478 ∨ k.val = 479 := by omega
  rcases heq with h448 | h449 | h450 | h451 | h452 | h453 | h454 | h455 | h456 | h457 | h458 | h459 | h460 | h461 | h462 | h463 | h464 | h465 | h466 | h467 | h468 | h469 | h470 | h471 | h472 | h473 | h474 | h475 | h476 | h477 | h478 | h479
  · have he : k = (448 : Fin 2886) := Fin.ext h448
    subst k
    rw [keyMomentRowsAt448]
    exact keyMoment448 B hB
  · have he : k = (449 : Fin 2886) := Fin.ext h449
    subst k
    rw [keyMomentRowsAt449]
    exact keyMoment449 B hB
  · have he : k = (450 : Fin 2886) := Fin.ext h450
    subst k
    rw [keyMomentRowsAt450]
    exact keyMoment450 B hB
  · have he : k = (451 : Fin 2886) := Fin.ext h451
    subst k
    rw [keyMomentRowsAt451]
    exact keyMoment451 B hB
  · have he : k = (452 : Fin 2886) := Fin.ext h452
    subst k
    rw [keyMomentRowsAt452]
    exact keyMoment452 B hB
  · have he : k = (453 : Fin 2886) := Fin.ext h453
    subst k
    rw [keyMomentRowsAt453]
    exact keyMoment453 B hB
  · have he : k = (454 : Fin 2886) := Fin.ext h454
    subst k
    rw [keyMomentRowsAt454]
    exact keyMoment454 B hB
  · have he : k = (455 : Fin 2886) := Fin.ext h455
    subst k
    rw [keyMomentRowsAt455]
    exact keyMoment455 B hB
  · have he : k = (456 : Fin 2886) := Fin.ext h456
    subst k
    rw [keyMomentRowsAt456]
    exact keyMoment456 B hB
  · have he : k = (457 : Fin 2886) := Fin.ext h457
    subst k
    rw [keyMomentRowsAt457]
    exact keyMoment457 B hB
  · have he : k = (458 : Fin 2886) := Fin.ext h458
    subst k
    rw [keyMomentRowsAt458]
    exact keyMoment458 B hB
  · have he : k = (459 : Fin 2886) := Fin.ext h459
    subst k
    rw [keyMomentRowsAt459]
    exact keyMoment459 B hB
  · have he : k = (460 : Fin 2886) := Fin.ext h460
    subst k
    rw [keyMomentRowsAt460]
    exact keyMoment460 B hB
  · have he : k = (461 : Fin 2886) := Fin.ext h461
    subst k
    rw [keyMomentRowsAt461]
    exact keyMoment461 B hB
  · have he : k = (462 : Fin 2886) := Fin.ext h462
    subst k
    rw [keyMomentRowsAt462]
    exact keyMoment462 B hB
  · have he : k = (463 : Fin 2886) := Fin.ext h463
    subst k
    rw [keyMomentRowsAt463]
    exact keyMoment463 B hB
  · have he : k = (464 : Fin 2886) := Fin.ext h464
    subst k
    rw [keyMomentRowsAt464]
    exact keyMoment464 B hB
  · have he : k = (465 : Fin 2886) := Fin.ext h465
    subst k
    rw [keyMomentRowsAt465]
    exact keyMoment465 B hB
  · have he : k = (466 : Fin 2886) := Fin.ext h466
    subst k
    rw [keyMomentRowsAt466]
    exact keyMoment466 B hB
  · have he : k = (467 : Fin 2886) := Fin.ext h467
    subst k
    rw [keyMomentRowsAt467]
    exact keyMoment467 B hB
  · have he : k = (468 : Fin 2886) := Fin.ext h468
    subst k
    rw [keyMomentRowsAt468]
    exact keyMoment468 B hB
  · have he : k = (469 : Fin 2886) := Fin.ext h469
    subst k
    rw [keyMomentRowsAt469]
    exact keyMoment469 B hB
  · have he : k = (470 : Fin 2886) := Fin.ext h470
    subst k
    rw [keyMomentRowsAt470]
    exact keyMoment470 B hB
  · have he : k = (471 : Fin 2886) := Fin.ext h471
    subst k
    rw [keyMomentRowsAt471]
    exact keyMoment471 B hB
  · have he : k = (472 : Fin 2886) := Fin.ext h472
    subst k
    rw [keyMomentRowsAt472]
    exact keyMoment472 B hB
  · have he : k = (473 : Fin 2886) := Fin.ext h473
    subst k
    rw [keyMomentRowsAt473]
    exact keyMoment473 B hB
  · have he : k = (474 : Fin 2886) := Fin.ext h474
    subst k
    rw [keyMomentRowsAt474]
    exact keyMoment474 B hB
  · have he : k = (475 : Fin 2886) := Fin.ext h475
    subst k
    rw [keyMomentRowsAt475]
    exact keyMoment475 B hB
  · have he : k = (476 : Fin 2886) := Fin.ext h476
    subst k
    rw [keyMomentRowsAt476]
    exact keyMoment476 B hB
  · have he : k = (477 : Fin 2886) := Fin.ext h477
    subst k
    rw [keyMomentRowsAt477]
    exact keyMoment477 B hB
  · have he : k = (478 : Fin 2886) := Fin.ext h478
    subst k
    rw [keyMomentRowsAt478]
    exact keyMoment478 B hB
  · have he : k = (479 : Fin 2886) := Fin.ext h479
    subst k
    rw [keyMomentRowsAt479]
    exact keyMoment479 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound14_e_oai
