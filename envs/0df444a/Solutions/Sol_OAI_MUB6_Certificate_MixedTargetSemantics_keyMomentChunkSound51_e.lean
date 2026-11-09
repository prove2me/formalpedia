-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:03.893193+00:00
-- url     : https://prove2.me/submissions/32bddfda-4989-4da6-b10a-9f5d3cf6e7f8

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical320
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41046 raw41046Labels = mixedMoment B node2846 node2846Labels := by
  calc
    mixedMoment B raw41046 raw41046Labels = mixedMoment B raw41046step0 raw41046step0Labels := by
      have ha : raw41046step0 = (fun i j => raw41046 (permutation251 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41046step0 raw41046; decide +kernel
      have hl : raw41046step0Labels = raw41046Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41046 raw41046Labels permutation251 permutation6
    mixedMoment B raw41046step0 raw41046step0Labels = mixedMoment B raw41046step1 raw41046step1Labels := by
      have ha : raw41046step1 = -raw41046step0 := by apply Matrix.ext; change ∀ i j, raw41046step1 i j = -(raw41046step0 i j); unfold raw41046step1 raw41046step0; decide +kernel
      have hl : raw41046step1Labels = raw41046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2846 node2846Labels := by rfl

theorem canonical41047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41047 raw41047Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw41047 raw41047Labels = mixedMoment B raw41047step0 raw41047step0Labels := by
      have ha : raw41047step0 = (fun i j => raw41047 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41047step0 raw41047; decide +kernel
      have hl : raw41047step0Labels = raw41047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41047 raw41047Labels permutation169 permutation6
    mixedMoment B raw41047step0 raw41047step0Labels = mixedMoment B raw41047step1 raw41047step1Labels := by
      have ha : raw41047step1 = -raw41047step0 := by apply Matrix.ext; change ∀ i j, raw41047step1 i j = -(raw41047step0 i j); unfold raw41047step1 raw41047step0; decide +kernel
      have hl : raw41047step1Labels = raw41047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2981 node2981Labels := by rfl

theorem canonical41048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41048 raw41048Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw41048 raw41048Labels = mixedMoment B raw41048step0 raw41048step0Labels := by
      have ha : raw41048step0 = (fun i j => raw41048 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41048step0 raw41048; decide +kernel
      have hl : raw41048step0Labels = raw41048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41048 raw41048Labels permutation640 permutation3
    mixedMoment B raw41048step0 raw41048step0Labels = mixedMoment B raw41048step1 raw41048step1Labels := by
      have ha : raw41048step1 = -raw41048step0 := by apply Matrix.ext; change ∀ i j, raw41048step1 i j = -(raw41048step0 i j); unfold raw41048step1 raw41048step0; decide +kernel
      have hl : raw41048step1Labels = raw41048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2746 node2746Labels := by rfl

theorem canonical41049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41049 raw41049Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw41049 raw41049Labels = mixedMoment B raw41049step0 raw41049step0Labels := by
      have ha : raw41049step0 = (fun i j => raw41049 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41049step0 raw41049; decide +kernel
      have hl : raw41049step0Labels = raw41049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41049 raw41049Labels permutation224 permutation6
    mixedMoment B raw41049step0 raw41049step0Labels = mixedMoment B raw41049step1 raw41049step1Labels := by
      have ha : raw41049step1 = -raw41049step0 := by apply Matrix.ext; change ∀ i j, raw41049step1 i j = -(raw41049step0 i j); unfold raw41049step1 raw41049step0; decide +kernel
      have hl : raw41049step1Labels = raw41049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2847 node2847Labels := by rfl

theorem canonical41050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41050 raw41050Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw41050 raw41050Labels = mixedMoment B raw41050step0 raw41050step0Labels := by
      have hz : ∀ j, raw41050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41050step0 = (fun i j => raw41050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41050step0 raw41050; decide +kernel
      have hl : raw41050step0Labels = raw41050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41050 raw41050Labels permutation434 hz
    mixedMoment B raw41050step0 raw41050step0Labels = mixedMoment B raw41050step1 raw41050step1Labels := by
      have ha : raw41050step1 = (fun i j => raw41050step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41050step1 raw41050step0; decide +kernel
      have hl : raw41050step1Labels = raw41050step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41050step0 raw41050step0Labels permutation121 permutation6
    _ = mixedMoment B node2495 node2495Labels := by rfl

theorem canonical41051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41051 raw41051Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw41051 raw41051Labels = mixedMoment B raw41051step0 raw41051step0Labels := by
      have hz : ∀ j, raw41051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41051step0 = (fun i j => raw41051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41051step0 raw41051; decide +kernel
      have hl : raw41051step0Labels = raw41051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41051 raw41051Labels permutation434 hz
    mixedMoment B raw41051step0 raw41051step0Labels = mixedMoment B raw41051step1 raw41051step1Labels := by
      have ha : raw41051step1 = (fun i j => raw41051step0 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41051step1 raw41051step0; decide +kernel
      have hl : raw41051step1Labels = raw41051step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41051step0 raw41051step0Labels permutation143 permutation6
    _ = mixedMoment B node1132 node1132Labels := by rfl

theorem canonical41052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41052 raw41052Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw41052 raw41052Labels = mixedMoment B raw41052step0 raw41052step0Labels := by
      have ha : raw41052step0 = (fun i j => raw41052 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41052step0 raw41052; decide +kernel
      have hl : raw41052step0Labels = raw41052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41052 raw41052Labels permutation550 permutation6
    _ = mixedMoment B node2437 node2437Labels := by rfl

theorem canonical41053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41053 raw41053Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw41053 raw41053Labels = mixedMoment B raw41053step0 raw41053step0Labels := by
      have ha : raw41053step0 = (fun i j => raw41053 (permutation644 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41053step0 raw41053; decide +kernel
      have hl : raw41053step0Labels = raw41053Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41053 raw41053Labels permutation644 permutation6
    _ = mixedMoment B node1112 node1112Labels := by rfl

theorem canonical41054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41054 raw41054Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw41054 raw41054Labels = mixedMoment B raw41054step0 raw41054step0Labels := by
      have ha : raw41054step0 = (fun i j => raw41054 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41054step0 raw41054; decide +kernel
      have hl : raw41054step0Labels = raw41054Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41054 raw41054Labels permutation478 permutation6
    _ = mixedMoment B node2426 node2426Labels := by rfl

theorem canonical41055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41055 raw41055Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw41055 raw41055Labels = mixedMoment B raw41055step0 raw41055step0Labels := by
      have ha : raw41055step0 = (fun i j => raw41055 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41055step0 raw41055; decide +kernel
      have hl : raw41055step0Labels = raw41055Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41055 raw41055Labels permutation480 permutation6
    _ = mixedMoment B node2470 node2470Labels := by rfl

theorem canonical41056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41056 raw41056Labels = mixedMoment B node606 node606Labels := by
  calc
    mixedMoment B raw41056 raw41056Labels = mixedMoment B raw41056step0 raw41056step0Labels := by
      have hz : ∀ j, raw41056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41056step0 = (fun i j => raw41056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41056step0 raw41056; decide +kernel
      have hl : raw41056step0Labels = raw41056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41056 raw41056Labels permutation434 hz
    mixedMoment B raw41056step0 raw41056step0Labels = mixedMoment B raw41056step1 raw41056step1Labels := by
      have hz : ∀ j, raw41056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41056step1 = (fun i j => raw41056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41056step1 raw41056step0; decide +kernel
      have hl : raw41056step1Labels = raw41056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41056step0 raw41056step0Labels permutation80 hz
    mixedMoment B raw41056step1 raw41056step1Labels = mixedMoment B raw41056step2 raw41056step2Labels := by
      have ha : raw41056step2 = (fun i j => raw41056step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41056step2 raw41056step1; decide +kernel
      have hl : raw41056step2Labels = raw41056step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41056step1 raw41056step1Labels permutation29 permutation6
    _ = mixedMoment B node606 node606Labels := by rfl

theorem canonical41057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41057 raw41057Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw41057 raw41057Labels = mixedMoment B raw41057step0 raw41057step0Labels := by
      have hz : ∀ j, raw41057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41057step0 = (fun i j => raw41057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41057step0 raw41057; decide +kernel
      have hl : raw41057step0Labels = raw41057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41057 raw41057Labels permutation346 hz
    mixedMoment B raw41057step0 raw41057step0Labels = mixedMoment B raw41057step1 raw41057step1Labels := by
      have ha : raw41057step1 = (fun i j => raw41057step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41057step1 raw41057step0; decide +kernel
      have hl : raw41057step1Labels = raw41057step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41057step0 raw41057step0Labels permutation125 permutation6
    _ = mixedMoment B node945 node945Labels := by rfl

theorem canonical41058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41058 raw41058Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw41058 raw41058Labels = mixedMoment B raw41058step0 raw41058step0Labels := by
      have hz : ∀ j, raw41058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41058step0 = (fun i j => raw41058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41058step0 raw41058; decide +kernel
      have hl : raw41058step0Labels = raw41058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41058 raw41058Labels permutation346 hz
    mixedMoment B raw41058step0 raw41058step0Labels = mixedMoment B raw41058step1 raw41058step1Labels := by
      have ha : raw41058step1 = (fun i j => raw41058step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41058step1 raw41058step0; decide +kernel
      have hl : raw41058step1Labels = raw41058step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41058step0 raw41058step0Labels permutation149 permutation6
    _ = mixedMoment B node581 node581Labels := by rfl

theorem canonical41059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41059 raw41059Labels = mixedMoment B node1831 node1831Labels := by
  calc
    mixedMoment B raw41059 raw41059Labels = mixedMoment B raw41059step0 raw41059step0Labels := by
      have hz : ∀ j, raw41059 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41059step0 = (fun i j => raw41059 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41059step0 raw41059; decide +kernel
      have hl : raw41059step0Labels = raw41059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41059 raw41059Labels permutation520 hz
    mixedMoment B raw41059step0 raw41059step0Labels = mixedMoment B raw41059step1 raw41059step1Labels := by
      have hz : ∀ j, raw41059step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41059step1 = (fun i j => raw41059step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41059step1 raw41059step0; decide +kernel
      have hl : raw41059step1Labels = raw41059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41059step0 raw41059step0Labels permutation104 hz
    mixedMoment B raw41059step1 raw41059step1Labels = mixedMoment B raw41059step2 raw41059step2Labels := by
      have ha : raw41059step2 = (fun i j => raw41059step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41059step2 raw41059step1; decide +kernel
      have hl : raw41059step2Labels = raw41059step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41059step1 raw41059step1Labels permutation25 permutation6
    _ = mixedMoment B node1831 node1831Labels := by rfl

theorem canonical41060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41060 raw41060Labels = mixedMoment B node1979 node1979Labels := by
  calc
    mixedMoment B raw41060 raw41060Labels = mixedMoment B raw41060step0 raw41060step0Labels := by
      have hz : ∀ j, raw41060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41060step0 = (fun i j => raw41060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41060step0 raw41060; decide +kernel
      have hl : raw41060step0Labels = raw41060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41060 raw41060Labels permutation434 hz
    mixedMoment B raw41060step0 raw41060step0Labels = mixedMoment B raw41060step1 raw41060step1Labels := by
      have ha : raw41060step1 = (fun i j => raw41060step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41060step1 raw41060step0; decide +kernel
      have hl : raw41060step1Labels = raw41060step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41060step0 raw41060step0Labels permutation97 permutation6
    _ = mixedMoment B node1979 node1979Labels := by rfl

theorem canonical41061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41061 raw41061Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw41061 raw41061Labels = mixedMoment B raw41061step0 raw41061step0Labels := by
      have hz : ∀ j, raw41061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41061step0 = (fun i j => raw41061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41061step0 raw41061; decide +kernel
      have hl : raw41061step0Labels = raw41061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41061 raw41061Labels permutation434 hz
    mixedMoment B raw41061step0 raw41061step0Labels = mixedMoment B raw41061step1 raw41061step1Labels := by
      have ha : raw41061step1 = (fun i j => raw41061step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41061step1 raw41061step0; decide +kernel
      have hl : raw41061step1Labels = raw41061step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41061step0 raw41061step0Labels permutation103 permutation6
    _ = mixedMoment B node1796 node1796Labels := by rfl

theorem canonical41062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41062 raw41062Labels = mixedMoment B node2826 node2826Labels := by
  calc
    mixedMoment B raw41062 raw41062Labels = mixedMoment B raw41062step0 raw41062step0Labels := by
      have ha : raw41062step0 = (fun i j => raw41062 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41062step0 raw41062; decide +kernel
      have hl : raw41062step0Labels = raw41062Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41062 raw41062Labels permutation175 permutation6
    mixedMoment B raw41062step0 raw41062step0Labels = mixedMoment B raw41062step1 raw41062step1Labels := by
      have ha : raw41062step1 = -raw41062step0 := by apply Matrix.ext; change ∀ i j, raw41062step1 i j = -(raw41062step0 i j); unfold raw41062step1 raw41062step0; decide +kernel
      have hl : raw41062step1Labels = raw41062step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2826 node2826Labels := by rfl

theorem canonical41063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41063 raw41063Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw41063 raw41063Labels = mixedMoment B raw41063step0 raw41063step0Labels := by
      have ha : raw41063step0 = (fun i j => raw41063 (permutation167 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41063step0 raw41063; decide +kernel
      have hl : raw41063step0Labels = raw41063Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41063 raw41063Labels permutation167 permutation6
    mixedMoment B raw41063step0 raw41063step0Labels = mixedMoment B raw41063step1 raw41063step1Labels := by
      have ha : raw41063step1 = -raw41063step0 := by apply Matrix.ext; change ∀ i j, raw41063step1 i j = -(raw41063step0 i j); unfold raw41063step1 raw41063step0; decide +kernel
      have hl : raw41063step1Labels = raw41063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

theorem canonical41064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41064 raw41064Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw41064 raw41064Labels = mixedMoment B raw41064step0 raw41064step0Labels := by
      have hz : ∀ j, raw41064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41064step0 = (fun i j => raw41064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41064step0 raw41064; decide +kernel
      have hl : raw41064step0Labels = raw41064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41064 raw41064Labels permutation434 hz
    mixedMoment B raw41064step0 raw41064step0Labels = mixedMoment B raw41064step1 raw41064step1Labels := by
      have ha : raw41064step1 = (fun i j => raw41064step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41064step1 raw41064step0; decide +kernel
      have hl : raw41064step1Labels = raw41064step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41064step0 raw41064step0Labels permutation37 permutation6
    mixedMoment B raw41064step1 raw41064step1Labels = mixedMoment B raw41064step2 raw41064step2Labels := by
      have ha : raw41064step2 = -raw41064step1 := by apply Matrix.ext; change ∀ i j, raw41064step2 i j = -(raw41064step1 i j); unfold raw41064step2 raw41064step1; decide +kernel
      have hl : raw41064step2Labels = raw41064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2827 node2827Labels := by rfl

theorem canonical41065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41065 raw41065Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw41065 raw41065Labels = mixedMoment B raw41065step0 raw41065step0Labels := by
      have hz : ∀ j, raw41065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41065step0 = (fun i j => raw41065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41065step0 raw41065; decide +kernel
      have hl : raw41065step0Labels = raw41065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41065 raw41065Labels permutation434 hz
    mixedMoment B raw41065step0 raw41065step0Labels = mixedMoment B raw41065step1 raw41065step1Labels := by
      have ha : raw41065step1 = (fun i j => raw41065step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41065step1 raw41065step0; decide +kernel
      have hl : raw41065step1Labels = raw41065step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41065step0 raw41065step0Labels permutation145 permutation6
    _ = mixedMoment B node2802 node2802Labels := by rfl

theorem canonical41066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41066 raw41066Labels = mixedMoment B node2442 node2442Labels := by
  calc
    mixedMoment B raw41066 raw41066Labels = mixedMoment B raw41066step0 raw41066step0Labels := by
      have hz : ∀ j, raw41066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41066step0 = (fun i j => raw41066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41066step0 raw41066; decide +kernel
      have hl : raw41066step0Labels = raw41066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41066 raw41066Labels permutation434 hz
    mixedMoment B raw41066step0 raw41066step0Labels = mixedMoment B raw41066step1 raw41066step1Labels := by
      have ha : raw41066step1 = (fun i j => raw41066step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41066step1 raw41066step0; decide +kernel
      have hl : raw41066step1Labels = raw41066step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41066step0 raw41066step0Labels permutation121 permutation6
    _ = mixedMoment B node2442 node2442Labels := by rfl

theorem canonical41067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41067 raw41067Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw41067 raw41067Labels = mixedMoment B raw41067step0 raw41067step0Labels := by
      have hz : ∀ j, raw41067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41067step0 = (fun i j => raw41067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41067step0 raw41067; decide +kernel
      have hl : raw41067step0Labels = raw41067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41067 raw41067Labels permutation434 hz
    mixedMoment B raw41067step0 raw41067step0Labels = mixedMoment B raw41067step1 raw41067step1Labels := by
      have ha : raw41067step1 = (fun i j => raw41067step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41067step1 raw41067step0; decide +kernel
      have hl : raw41067step1Labels = raw41067step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41067step0 raw41067step0Labels permutation145 permutation6
    _ = mixedMoment B node1120 node1120Labels := by rfl

theorem canonical41068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41068 raw41068Labels = mixedMoment B node953 node953Labels := by
  calc
    mixedMoment B raw41068 raw41068Labels = mixedMoment B raw41068step0 raw41068step0Labels := by
      have hz : ∀ j, raw41068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41068step0 = (fun i j => raw41068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41068step0 raw41068; decide +kernel
      have hl : raw41068step0Labels = raw41068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41068 raw41068Labels permutation434 hz
    mixedMoment B raw41068step0 raw41068step0Labels = mixedMoment B raw41068step1 raw41068step1Labels := by
      have hz : ∀ j, raw41068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41068step1 = (fun i j => raw41068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41068step1 raw41068step0; decide +kernel
      have hl : raw41068step1Labels = raw41068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41068step0 raw41068step0Labels permutation80 hz
    mixedMoment B raw41068step1 raw41068step1Labels = mixedMoment B raw41068step2 raw41068step2Labels := by
      have ha : raw41068step2 = (fun i j => raw41068step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41068step2 raw41068step1; decide +kernel
      have hl : raw41068step2Labels = raw41068step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41068step1 raw41068step1Labels permutation25 permutation6
    _ = mixedMoment B node953 node953Labels := by rfl

theorem canonical41069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41069 raw41069Labels = mixedMoment B node589 node589Labels := by
  calc
    mixedMoment B raw41069 raw41069Labels = mixedMoment B raw41069step0 raw41069step0Labels := by
      have hz : ∀ j, raw41069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41069step0 = (fun i j => raw41069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41069step0 raw41069; decide +kernel
      have hl : raw41069step0Labels = raw41069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41069 raw41069Labels permutation434 hz
    mixedMoment B raw41069step0 raw41069step0Labels = mixedMoment B raw41069step1 raw41069step1Labels := by
      have hz : ∀ j, raw41069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41069step1 = (fun i j => raw41069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41069step1 raw41069step0; decide +kernel
      have hl : raw41069step1Labels = raw41069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41069step0 raw41069step0Labels permutation80 hz
    mixedMoment B raw41069step1 raw41069step1Labels = mixedMoment B raw41069step2 raw41069step2Labels := by
      have ha : raw41069step2 = (fun i j => raw41069step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41069step2 raw41069step1; decide +kernel
      have hl : raw41069step2Labels = raw41069step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41069step1 raw41069step1Labels permutation31 permutation6
    _ = mixedMoment B node589 node589Labels := by rfl

theorem canonical41070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41070 raw41070Labels = mixedMoment B node2281 node2281Labels := by
  calc
    mixedMoment B raw41070 raw41070Labels = mixedMoment B raw41070step0 raw41070step0Labels := by
      have hz : ∀ j, raw41070 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41070step0 = (fun i j => raw41070 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41070step0 raw41070; decide +kernel
      have hl : raw41070step0Labels = raw41070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41070 raw41070Labels permutation520 hz
    mixedMoment B raw41070step0 raw41070step0Labels = mixedMoment B raw41070step1 raw41070step1Labels := by
      have hz : ∀ j, raw41070step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41070step1 = (fun i j => raw41070step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41070step1 raw41070step0; decide +kernel
      have hl : raw41070step1Labels = raw41070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41070step0 raw41070step0Labels permutation104 hz
    mixedMoment B raw41070step1 raw41070step1Labels = mixedMoment B raw41070step2 raw41070step2Labels := by
      have hz : ∀ j, raw41070step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41070step2 = (fun i j => raw41070step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41070step2 raw41070step1; decide +kernel
      have hl : raw41070step2Labels = raw41070step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41070step1 raw41070step1Labels permutation20 hz
    mixedMoment B raw41070step2 raw41070step2Labels = mixedMoment B raw41070step3 raw41070step3Labels := by
      have ha : raw41070step3 = (fun i j => raw41070step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41070step3 raw41070step2; decide +kernel
      have hl : raw41070step3Labels = raw41070step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41070step2 raw41070step2Labels permutation5 permutation6
    _ = mixedMoment B node2281 node2281Labels := by rfl

theorem canonical41071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41071 raw41071Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw41071 raw41071Labels = mixedMoment B raw41071step0 raw41071step0Labels := by
      have hz : ∀ j, raw41071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41071step0 = (fun i j => raw41071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41071step0 raw41071; decide +kernel
      have hl : raw41071step0Labels = raw41071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41071 raw41071Labels permutation434 hz
    mixedMoment B raw41071step0 raw41071step0Labels = mixedMoment B raw41071step1 raw41071step1Labels := by
      have hz : ∀ j, raw41071step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41071step1 = (fun i j => raw41071step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41071step1 raw41071step0; decide +kernel
      have hl : raw41071step1Labels = raw41071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41071step0 raw41071step0Labels permutation80 hz
    mixedMoment B raw41071step1 raw41071step1Labels = mixedMoment B raw41071step2 raw41071step2Labels := by
      have ha : raw41071step2 = (fun i j => raw41071step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41071step2 raw41071step1; decide +kernel
      have hl : raw41071step2Labels = raw41071step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41071step1 raw41071step1Labels permutation19 permutation6
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical41072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41072 raw41072Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw41072 raw41072Labels = mixedMoment B raw41072step0 raw41072step0Labels := by
      have hz : ∀ j, raw41072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41072step0 = (fun i j => raw41072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41072step0 raw41072; decide +kernel
      have hl : raw41072step0Labels = raw41072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41072 raw41072Labels permutation434 hz
    mixedMoment B raw41072step0 raw41072step0Labels = mixedMoment B raw41072step1 raw41072step1Labels := by
      have hz : ∀ j, raw41072step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41072step1 = (fun i j => raw41072step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41072step1 raw41072step0; decide +kernel
      have hl : raw41072step1Labels = raw41072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41072step0 raw41072step0Labels permutation80 hz
    mixedMoment B raw41072step1 raw41072step1Labels = mixedMoment B raw41072step2 raw41072step2Labels := by
      have ha : raw41072step2 = (fun i j => raw41072step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41072step2 raw41072step1; decide +kernel
      have hl : raw41072step2Labels = raw41072step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41072step1 raw41072step1Labels permutation19 permutation6
    _ = mixedMoment B node1819 node1819Labels := by rfl

theorem canonical41073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41073 raw41073Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw41073 raw41073Labels = mixedMoment B raw41073step0 raw41073step0Labels := by
      have hz : ∀ j, raw41073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41073step0 = (fun i j => raw41073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41073step0 raw41073; decide +kernel
      have hl : raw41073step0Labels = raw41073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41073 raw41073Labels permutation434 hz
    mixedMoment B raw41073step0 raw41073step0Labels = mixedMoment B raw41073step1 raw41073step1Labels := by
      have hz : ∀ j, raw41073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41073step1 = (fun i j => raw41073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41073step1 raw41073step0; decide +kernel
      have hl : raw41073step1Labels = raw41073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41073step0 raw41073step0Labels permutation80 hz
    mixedMoment B raw41073step1 raw41073step1Labels = mixedMoment B raw41073step2 raw41073step2Labels := by
      have ha : raw41073step2 = (fun i j => raw41073step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41073step2 raw41073step1; decide +kernel
      have hl : raw41073step2Labels = raw41073step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41073step1 raw41073step1Labels permutation17 permutation6
    _ = mixedMoment B node2062 node2062Labels := by rfl

theorem canonical41074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41074 raw41074Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw41074 raw41074Labels = mixedMoment B raw41074step0 raw41074step0Labels := by
      have hz : ∀ j, raw41074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41074step0 = (fun i j => raw41074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41074step0 raw41074; decide +kernel
      have hl : raw41074step0Labels = raw41074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41074 raw41074Labels permutation434 hz
    mixedMoment B raw41074step0 raw41074step0Labels = mixedMoment B raw41074step1 raw41074step1Labels := by
      have hz : ∀ j, raw41074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41074step1 = (fun i j => raw41074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41074step1 raw41074step0; decide +kernel
      have hl : raw41074step1Labels = raw41074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41074step0 raw41074step0Labels permutation80 hz
    mixedMoment B raw41074step1 raw41074step1Labels = mixedMoment B raw41074step2 raw41074step2Labels := by
      have ha : raw41074step2 = (fun i j => raw41074step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41074step2 raw41074step1; decide +kernel
      have hl : raw41074step2Labels = raw41074step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41074step1 raw41074step1Labels permutation17 permutation6
    _ = mixedMoment B node2247 node2247Labels := by rfl

theorem canonical41075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41075 raw41075Labels = mixedMoment B node1812 node1812Labels := by
  calc
    mixedMoment B raw41075 raw41075Labels = mixedMoment B raw41075step0 raw41075step0Labels := by
      have hz : ∀ j, raw41075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41075step0 = (fun i j => raw41075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41075step0 raw41075; decide +kernel
      have hl : raw41075step0Labels = raw41075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41075 raw41075Labels permutation346 hz
    mixedMoment B raw41075step0 raw41075step0Labels = mixedMoment B raw41075step1 raw41075step1Labels := by
      have ha : raw41075step1 = (fun i j => raw41075step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41075step1 raw41075step0; decide +kernel
      have hl : raw41075step1Labels = raw41075step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41075step0 raw41075step0Labels permutation77 permutation6
    _ = mixedMoment B node1812 node1812Labels := by rfl

theorem canonical41076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41076 raw41076Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw41076 raw41076Labels = mixedMoment B raw41076step0 raw41076step0Labels := by
      have hz : ∀ j, raw41076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41076step0 = (fun i j => raw41076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41076step0 raw41076; decide +kernel
      have hl : raw41076step0Labels = raw41076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41076 raw41076Labels permutation346 hz
    mixedMoment B raw41076step0 raw41076step0Labels = mixedMoment B raw41076step1 raw41076step1Labels := by
      have ha : raw41076step1 = (fun i j => raw41076step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41076step1 raw41076step0; decide +kernel
      have hl : raw41076step1Labels = raw41076step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41076step0 raw41076step0Labels permutation73 permutation6
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical41077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41077 raw41077Labels = mixedMoment B node1970 node1970Labels := by
  calc
    mixedMoment B raw41077 raw41077Labels = mixedMoment B raw41077step0 raw41077step0Labels := by
      have hz : ∀ j, raw41077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41077step0 = (fun i j => raw41077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41077step0 raw41077; decide +kernel
      have hl : raw41077step0Labels = raw41077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41077 raw41077Labels permutation346 hz
    mixedMoment B raw41077step0 raw41077step0Labels = mixedMoment B raw41077step1 raw41077step1Labels := by
      have ha : raw41077step1 = (fun i j => raw41077step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41077step1 raw41077step0; decide +kernel
      have hl : raw41077step1Labels = raw41077step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41077step0 raw41077step0Labels permutation73 permutation6
    _ = mixedMoment B node1970 node1970Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1632) =
      Integer.Sparse.eval keyMomentRow1632 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1632).leftCharge (GramAssembly.key 1632).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2846) := by
    have ha : gramCharges (GramAssembly.key 1632).leftCharge (GramAssembly.key 1632).rightCharge = raw41046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41046 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1632).leftCharge (GramAssembly.key 1632).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1632, Integer.Sparse.eval]

theorem keyMoment1633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1633) =
      Integer.Sparse.eval keyMomentRow1633 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1633).leftCharge (GramAssembly.key 1633).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2981) := by
    have ha : gramCharges (GramAssembly.key 1633).leftCharge (GramAssembly.key 1633).rightCharge = raw41047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41047 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1633).leftCharge (GramAssembly.key 1633).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1633, Integer.Sparse.eval]

theorem keyMoment1634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1634) =
      Integer.Sparse.eval keyMomentRow1634 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1634).leftCharge (GramAssembly.key 1634).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2746) := by
    have ha : gramCharges (GramAssembly.key 1634).leftCharge (GramAssembly.key 1634).rightCharge = raw41048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41048 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1634).leftCharge (GramAssembly.key 1634).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1634, Integer.Sparse.eval]

theorem keyMoment1635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1635) =
      Integer.Sparse.eval keyMomentRow1635 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1635).leftCharge (GramAssembly.key 1635).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2847) := by
    have ha : gramCharges (GramAssembly.key 1635).leftCharge (GramAssembly.key 1635).rightCharge = raw41049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41049 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1635).leftCharge (GramAssembly.key 1635).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1635, Integer.Sparse.eval]

theorem keyMoment1636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1636) =
      Integer.Sparse.eval keyMomentRow1636 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1636).leftCharge (GramAssembly.key 1636).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2495) := by
    have ha : gramCharges (GramAssembly.key 1636).leftCharge (GramAssembly.key 1636).rightCharge = raw41050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41050 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1636).leftCharge (GramAssembly.key 1636).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1636, Integer.Sparse.eval]

theorem keyMoment1637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1637) =
      Integer.Sparse.eval keyMomentRow1637 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1637).leftCharge (GramAssembly.key 1637).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1132) := by
    have ha : gramCharges (GramAssembly.key 1637).leftCharge (GramAssembly.key 1637).rightCharge = raw41051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41051 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1637).leftCharge (GramAssembly.key 1637).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1637, Integer.Sparse.eval]

theorem keyMoment1638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1638) =
      Integer.Sparse.eval keyMomentRow1638 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1638).leftCharge (GramAssembly.key 1638).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2437) := by
    have ha : gramCharges (GramAssembly.key 1638).leftCharge (GramAssembly.key 1638).rightCharge = raw41052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41052 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1638).leftCharge (GramAssembly.key 1638).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1638, Integer.Sparse.eval]

theorem keyMoment1639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1639) =
      Integer.Sparse.eval keyMomentRow1639 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1639).leftCharge (GramAssembly.key 1639).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1112) := by
    have ha : gramCharges (GramAssembly.key 1639).leftCharge (GramAssembly.key 1639).rightCharge = raw41053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41053 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1639).leftCharge (GramAssembly.key 1639).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1639, Integer.Sparse.eval]

theorem keyMoment1640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1640) =
      Integer.Sparse.eval keyMomentRow1640 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1640).leftCharge (GramAssembly.key 1640).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2426) := by
    have ha : gramCharges (GramAssembly.key 1640).leftCharge (GramAssembly.key 1640).rightCharge = raw41054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41054 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1640).leftCharge (GramAssembly.key 1640).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1640, Integer.Sparse.eval]

theorem keyMoment1641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1641) =
      Integer.Sparse.eval keyMomentRow1641 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1641).leftCharge (GramAssembly.key 1641).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2470) := by
    have ha : gramCharges (GramAssembly.key 1641).leftCharge (GramAssembly.key 1641).rightCharge = raw41055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41055 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1641).leftCharge (GramAssembly.key 1641).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1641, Integer.Sparse.eval]

theorem keyMoment1642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1642) =
      Integer.Sparse.eval keyMomentRow1642 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1642).leftCharge (GramAssembly.key 1642).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 606) := by
    have ha : gramCharges (GramAssembly.key 1642).leftCharge (GramAssembly.key 1642).rightCharge = raw41056 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41056Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41056 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1642).leftCharge (GramAssembly.key 1642).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1642, Integer.Sparse.eval]

theorem keyMoment1643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1643) =
      Integer.Sparse.eval keyMomentRow1643 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1643).leftCharge (GramAssembly.key 1643).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 945) := by
    have ha : gramCharges (GramAssembly.key 1643).leftCharge (GramAssembly.key 1643).rightCharge = raw41057 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41057Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41057 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1643).leftCharge (GramAssembly.key 1643).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1643, Integer.Sparse.eval]

theorem keyMoment1644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1644) =
      Integer.Sparse.eval keyMomentRow1644 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1644).leftCharge (GramAssembly.key 1644).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 581) := by
    have ha : gramCharges (GramAssembly.key 1644).leftCharge (GramAssembly.key 1644).rightCharge = raw41058 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41058Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41058 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1644).leftCharge (GramAssembly.key 1644).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1644, Integer.Sparse.eval]

theorem keyMoment1645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1645) =
      Integer.Sparse.eval keyMomentRow1645 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1645).leftCharge (GramAssembly.key 1645).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1831) := by
    have ha : gramCharges (GramAssembly.key 1645).leftCharge (GramAssembly.key 1645).rightCharge = raw41059 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41059Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41059 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1645).leftCharge (GramAssembly.key 1645).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1645, Integer.Sparse.eval]

theorem keyMoment1646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1646) =
      Integer.Sparse.eval keyMomentRow1646 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1646).leftCharge (GramAssembly.key 1646).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1979) := by
    have ha : gramCharges (GramAssembly.key 1646).leftCharge (GramAssembly.key 1646).rightCharge = raw41060 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41060Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41060 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1646).leftCharge (GramAssembly.key 1646).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1646, Integer.Sparse.eval]

theorem keyMoment1647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1647) =
      Integer.Sparse.eval keyMomentRow1647 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1647).leftCharge (GramAssembly.key 1647).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1796) := by
    have ha : gramCharges (GramAssembly.key 1647).leftCharge (GramAssembly.key 1647).rightCharge = raw41061 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41061Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41061 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1647).leftCharge (GramAssembly.key 1647).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1647, Integer.Sparse.eval]

theorem keyMoment1648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1648) =
      Integer.Sparse.eval keyMomentRow1648 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1648).leftCharge (GramAssembly.key 1648).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2826) := by
    have ha : gramCharges (GramAssembly.key 1648).leftCharge (GramAssembly.key 1648).rightCharge = raw41062 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41062Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41062 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1648).leftCharge (GramAssembly.key 1648).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1648, Integer.Sparse.eval]

theorem keyMoment1649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1649) =
      Integer.Sparse.eval keyMomentRow1649 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1649).leftCharge (GramAssembly.key 1649).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2824) := by
    have ha : gramCharges (GramAssembly.key 1649).leftCharge (GramAssembly.key 1649).rightCharge = raw41063 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41063Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41063 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1649).leftCharge (GramAssembly.key 1649).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1649, Integer.Sparse.eval]

theorem keyMoment1650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1650) =
      Integer.Sparse.eval keyMomentRow1650 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1650).leftCharge (GramAssembly.key 1650).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2827) := by
    have ha : gramCharges (GramAssembly.key 1650).leftCharge (GramAssembly.key 1650).rightCharge = raw41064 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41064Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41064 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1650).leftCharge (GramAssembly.key 1650).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1650, Integer.Sparse.eval]

theorem keyMoment1651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1651) =
      Integer.Sparse.eval keyMomentRow1651 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1651).leftCharge (GramAssembly.key 1651).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2802) := by
    have ha : gramCharges (GramAssembly.key 1651).leftCharge (GramAssembly.key 1651).rightCharge = raw41065 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41065Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41065 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1651).leftCharge (GramAssembly.key 1651).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1651, Integer.Sparse.eval]

theorem keyMoment1652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1652) =
      Integer.Sparse.eval keyMomentRow1652 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1652).leftCharge (GramAssembly.key 1652).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2442) := by
    have ha : gramCharges (GramAssembly.key 1652).leftCharge (GramAssembly.key 1652).rightCharge = raw41066 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41066Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41066 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1652).leftCharge (GramAssembly.key 1652).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1652, Integer.Sparse.eval]

theorem keyMoment1653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1653) =
      Integer.Sparse.eval keyMomentRow1653 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1653).leftCharge (GramAssembly.key 1653).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1120) := by
    have ha : gramCharges (GramAssembly.key 1653).leftCharge (GramAssembly.key 1653).rightCharge = raw41067 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41067Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41067 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1653).leftCharge (GramAssembly.key 1653).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1653, Integer.Sparse.eval]

theorem keyMoment1654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1654) =
      Integer.Sparse.eval keyMomentRow1654 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1654).leftCharge (GramAssembly.key 1654).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 953) := by
    have ha : gramCharges (GramAssembly.key 1654).leftCharge (GramAssembly.key 1654).rightCharge = raw41068 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41068Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41068 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1654).leftCharge (GramAssembly.key 1654).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1654, Integer.Sparse.eval]

theorem keyMoment1655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1655) =
      Integer.Sparse.eval keyMomentRow1655 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1655).leftCharge (GramAssembly.key 1655).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 589) := by
    have ha : gramCharges (GramAssembly.key 1655).leftCharge (GramAssembly.key 1655).rightCharge = raw41069 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41069Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41069 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1655).leftCharge (GramAssembly.key 1655).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1655, Integer.Sparse.eval]

theorem keyMoment1656 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1656) =
      Integer.Sparse.eval keyMomentRow1656 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1656).leftCharge (GramAssembly.key 1656).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2281) := by
    have ha : gramCharges (GramAssembly.key 1656).leftCharge (GramAssembly.key 1656).rightCharge = raw41070 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41070Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41070 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1656).leftCharge (GramAssembly.key 1656).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1656, Integer.Sparse.eval]

theorem keyMoment1657 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1657) =
      Integer.Sparse.eval keyMomentRow1657 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1657).leftCharge (GramAssembly.key 1657).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2112) := by
    have ha : gramCharges (GramAssembly.key 1657).leftCharge (GramAssembly.key 1657).rightCharge = raw41071 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41071Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41071 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1657).leftCharge (GramAssembly.key 1657).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1657, Integer.Sparse.eval]

theorem keyMoment1658 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1658) =
      Integer.Sparse.eval keyMomentRow1658 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1658).leftCharge (GramAssembly.key 1658).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1819) := by
    have ha : gramCharges (GramAssembly.key 1658).leftCharge (GramAssembly.key 1658).rightCharge = raw41072 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41072Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41072 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1658).leftCharge (GramAssembly.key 1658).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1658, Integer.Sparse.eval]

theorem keyMoment1659 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1659) =
      Integer.Sparse.eval keyMomentRow1659 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1659).leftCharge (GramAssembly.key 1659).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2062) := by
    have ha : gramCharges (GramAssembly.key 1659).leftCharge (GramAssembly.key 1659).rightCharge = raw41073 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41073Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41073 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1659).leftCharge (GramAssembly.key 1659).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1659, Integer.Sparse.eval]

theorem keyMoment1660 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1660) =
      Integer.Sparse.eval keyMomentRow1660 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1660).leftCharge (GramAssembly.key 1660).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2247) := by
    have ha : gramCharges (GramAssembly.key 1660).leftCharge (GramAssembly.key 1660).rightCharge = raw41074 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41074Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41074 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1660).leftCharge (GramAssembly.key 1660).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1660, Integer.Sparse.eval]

theorem keyMoment1661 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1661) =
      Integer.Sparse.eval keyMomentRow1661 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1661).leftCharge (GramAssembly.key 1661).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1812) := by
    have ha : gramCharges (GramAssembly.key 1661).leftCharge (GramAssembly.key 1661).rightCharge = raw41075 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41075Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41075 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1661).leftCharge (GramAssembly.key 1661).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1661, Integer.Sparse.eval]

theorem keyMoment1662 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1662) =
      Integer.Sparse.eval keyMomentRow1662 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1662).leftCharge (GramAssembly.key 1662).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2025) := by
    have ha : gramCharges (GramAssembly.key 1662).leftCharge (GramAssembly.key 1662).rightCharge = raw41076 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41076Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41076 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1662).leftCharge (GramAssembly.key 1662).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1662, Integer.Sparse.eval]

theorem keyMoment1663 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1663) =
      Integer.Sparse.eval keyMomentRow1663 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1663).leftCharge (GramAssembly.key 1663).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1970) := by
    have ha : gramCharges (GramAssembly.key 1663).leftCharge (GramAssembly.key 1663).rightCharge = raw41077 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41077Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41077 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1663).leftCharge (GramAssembly.key 1663).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1663, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1632 : keyMomentRows (1632 : Fin 2886) =
    keyMomentRow1632 := by decide +kernel

theorem keyMomentRowsAt1633 : keyMomentRows (1633 : Fin 2886) =
    keyMomentRow1633 := by decide +kernel

theorem keyMomentRowsAt1634 : keyMomentRows (1634 : Fin 2886) =
    keyMomentRow1634 := by decide +kernel

theorem keyMomentRowsAt1635 : keyMomentRows (1635 : Fin 2886) =
    keyMomentRow1635 := by decide +kernel

theorem keyMomentRowsAt1636 : keyMomentRows (1636 : Fin 2886) =
    keyMomentRow1636 := by decide +kernel

theorem keyMomentRowsAt1637 : keyMomentRows (1637 : Fin 2886) =
    keyMomentRow1637 := by decide +kernel

theorem keyMomentRowsAt1638 : keyMomentRows (1638 : Fin 2886) =
    keyMomentRow1638 := by decide +kernel

theorem keyMomentRowsAt1639 : keyMomentRows (1639 : Fin 2886) =
    keyMomentRow1639 := by decide +kernel

theorem keyMomentRowsAt1640 : keyMomentRows (1640 : Fin 2886) =
    keyMomentRow1640 := by decide +kernel

theorem keyMomentRowsAt1641 : keyMomentRows (1641 : Fin 2886) =
    keyMomentRow1641 := by decide +kernel

theorem keyMomentRowsAt1642 : keyMomentRows (1642 : Fin 2886) =
    keyMomentRow1642 := by decide +kernel

theorem keyMomentRowsAt1643 : keyMomentRows (1643 : Fin 2886) =
    keyMomentRow1643 := by decide +kernel

theorem keyMomentRowsAt1644 : keyMomentRows (1644 : Fin 2886) =
    keyMomentRow1644 := by decide +kernel

theorem keyMomentRowsAt1645 : keyMomentRows (1645 : Fin 2886) =
    keyMomentRow1645 := by decide +kernel

theorem keyMomentRowsAt1646 : keyMomentRows (1646 : Fin 2886) =
    keyMomentRow1646 := by decide +kernel

theorem keyMomentRowsAt1647 : keyMomentRows (1647 : Fin 2886) =
    keyMomentRow1647 := by decide +kernel

theorem keyMomentRowsAt1648 : keyMomentRows (1648 : Fin 2886) =
    keyMomentRow1648 := by decide +kernel

theorem keyMomentRowsAt1649 : keyMomentRows (1649 : Fin 2886) =
    keyMomentRow1649 := by decide +kernel

theorem keyMomentRowsAt1650 : keyMomentRows (1650 : Fin 2886) =
    keyMomentRow1650 := by decide +kernel

theorem keyMomentRowsAt1651 : keyMomentRows (1651 : Fin 2886) =
    keyMomentRow1651 := by decide +kernel

theorem keyMomentRowsAt1652 : keyMomentRows (1652 : Fin 2886) =
    keyMomentRow1652 := by decide +kernel

theorem keyMomentRowsAt1653 : keyMomentRows (1653 : Fin 2886) =
    keyMomentRow1653 := by decide +kernel

theorem keyMomentRowsAt1654 : keyMomentRows (1654 : Fin 2886) =
    keyMomentRow1654 := by decide +kernel

theorem keyMomentRowsAt1655 : keyMomentRows (1655 : Fin 2886) =
    keyMomentRow1655 := by decide +kernel

theorem keyMomentRowsAt1656 : keyMomentRows (1656 : Fin 2886) =
    keyMomentRow1656 := by decide +kernel

theorem keyMomentRowsAt1657 : keyMomentRows (1657 : Fin 2886) =
    keyMomentRow1657 := by decide +kernel

theorem keyMomentRowsAt1658 : keyMomentRows (1658 : Fin 2886) =
    keyMomentRow1658 := by decide +kernel

theorem keyMomentRowsAt1659 : keyMomentRows (1659 : Fin 2886) =
    keyMomentRow1659 := by decide +kernel

theorem keyMomentRowsAt1660 : keyMomentRows (1660 : Fin 2886) =
    keyMomentRow1660 := by decide +kernel

theorem keyMomentRowsAt1661 : keyMomentRows (1661 : Fin 2886) =
    keyMomentRow1661 := by decide +kernel

theorem keyMomentRowsAt1662 : keyMomentRows (1662 : Fin 2886) =
    keyMomentRow1662 := by decide +kernel

theorem keyMomentRowsAt1663 : keyMomentRows (1663 : Fin 2886) =
    keyMomentRow1663 := by decide +kernel

theorem keyMomentChunkSound51_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 51) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1632 ∨ k.val = 1633 ∨ k.val = 1634 ∨ k.val = 1635 ∨ k.val = 1636 ∨ k.val = 1637 ∨ k.val = 1638 ∨ k.val = 1639 ∨ k.val = 1640 ∨ k.val = 1641 ∨ k.val = 1642 ∨ k.val = 1643 ∨ k.val = 1644 ∨ k.val = 1645 ∨ k.val = 1646 ∨ k.val = 1647 ∨ k.val = 1648 ∨ k.val = 1649 ∨ k.val = 1650 ∨ k.val = 1651 ∨ k.val = 1652 ∨ k.val = 1653 ∨ k.val = 1654 ∨ k.val = 1655 ∨ k.val = 1656 ∨ k.val = 1657 ∨ k.val = 1658 ∨ k.val = 1659 ∨ k.val = 1660 ∨ k.val = 1661 ∨ k.val = 1662 ∨ k.val = 1663 := by omega
  rcases heq with h1632 | h1633 | h1634 | h1635 | h1636 | h1637 | h1638 | h1639 | h1640 | h1641 | h1642 | h1643 | h1644 | h1645 | h1646 | h1647 | h1648 | h1649 | h1650 | h1651 | h1652 | h1653 | h1654 | h1655 | h1656 | h1657 | h1658 | h1659 | h1660 | h1661 | h1662 | h1663
  · have he : k = (1632 : Fin 2886) := Fin.ext h1632
    subst k
    rw [keyMomentRowsAt1632]
    exact keyMoment1632 B hB
  · have he : k = (1633 : Fin 2886) := Fin.ext h1633
    subst k
    rw [keyMomentRowsAt1633]
    exact keyMoment1633 B hB
  · have he : k = (1634 : Fin 2886) := Fin.ext h1634
    subst k
    rw [keyMomentRowsAt1634]
    exact keyMoment1634 B hB
  · have he : k = (1635 : Fin 2886) := Fin.ext h1635
    subst k
    rw [keyMomentRowsAt1635]
    exact keyMoment1635 B hB
  · have he : k = (1636 : Fin 2886) := Fin.ext h1636
    subst k
    rw [keyMomentRowsAt1636]
    exact keyMoment1636 B hB
  · have he : k = (1637 : Fin 2886) := Fin.ext h1637
    subst k
    rw [keyMomentRowsAt1637]
    exact keyMoment1637 B hB
  · have he : k = (1638 : Fin 2886) := Fin.ext h1638
    subst k
    rw [keyMomentRowsAt1638]
    exact keyMoment1638 B hB
  · have he : k = (1639 : Fin 2886) := Fin.ext h1639
    subst k
    rw [keyMomentRowsAt1639]
    exact keyMoment1639 B hB
  · have he : k = (1640 : Fin 2886) := Fin.ext h1640
    subst k
    rw [keyMomentRowsAt1640]
    exact keyMoment1640 B hB
  · have he : k = (1641 : Fin 2886) := Fin.ext h1641
    subst k
    rw [keyMomentRowsAt1641]
    exact keyMoment1641 B hB
  · have he : k = (1642 : Fin 2886) := Fin.ext h1642
    subst k
    rw [keyMomentRowsAt1642]
    exact keyMoment1642 B hB
  · have he : k = (1643 : Fin 2886) := Fin.ext h1643
    subst k
    rw [keyMomentRowsAt1643]
    exact keyMoment1643 B hB
  · have he : k = (1644 : Fin 2886) := Fin.ext h1644
    subst k
    rw [keyMomentRowsAt1644]
    exact keyMoment1644 B hB
  · have he : k = (1645 : Fin 2886) := Fin.ext h1645
    subst k
    rw [keyMomentRowsAt1645]
    exact keyMoment1645 B hB
  · have he : k = (1646 : Fin 2886) := Fin.ext h1646
    subst k
    rw [keyMomentRowsAt1646]
    exact keyMoment1646 B hB
  · have he : k = (1647 : Fin 2886) := Fin.ext h1647
    subst k
    rw [keyMomentRowsAt1647]
    exact keyMoment1647 B hB
  · have he : k = (1648 : Fin 2886) := Fin.ext h1648
    subst k
    rw [keyMomentRowsAt1648]
    exact keyMoment1648 B hB
  · have he : k = (1649 : Fin 2886) := Fin.ext h1649
    subst k
    rw [keyMomentRowsAt1649]
    exact keyMoment1649 B hB
  · have he : k = (1650 : Fin 2886) := Fin.ext h1650
    subst k
    rw [keyMomentRowsAt1650]
    exact keyMoment1650 B hB
  · have he : k = (1651 : Fin 2886) := Fin.ext h1651
    subst k
    rw [keyMomentRowsAt1651]
    exact keyMoment1651 B hB
  · have he : k = (1652 : Fin 2886) := Fin.ext h1652
    subst k
    rw [keyMomentRowsAt1652]
    exact keyMoment1652 B hB
  · have he : k = (1653 : Fin 2886) := Fin.ext h1653
    subst k
    rw [keyMomentRowsAt1653]
    exact keyMoment1653 B hB
  · have he : k = (1654 : Fin 2886) := Fin.ext h1654
    subst k
    rw [keyMomentRowsAt1654]
    exact keyMoment1654 B hB
  · have he : k = (1655 : Fin 2886) := Fin.ext h1655
    subst k
    rw [keyMomentRowsAt1655]
    exact keyMoment1655 B hB
  · have he : k = (1656 : Fin 2886) := Fin.ext h1656
    subst k
    rw [keyMomentRowsAt1656]
    exact keyMoment1656 B hB
  · have he : k = (1657 : Fin 2886) := Fin.ext h1657
    subst k
    rw [keyMomentRowsAt1657]
    exact keyMoment1657 B hB
  · have he : k = (1658 : Fin 2886) := Fin.ext h1658
    subst k
    rw [keyMomentRowsAt1658]
    exact keyMoment1658 B hB
  · have he : k = (1659 : Fin 2886) := Fin.ext h1659
    subst k
    rw [keyMomentRowsAt1659]
    exact keyMoment1659 B hB
  · have he : k = (1660 : Fin 2886) := Fin.ext h1660
    subst k
    rw [keyMomentRowsAt1660]
    exact keyMoment1660 B hB
  · have he : k = (1661 : Fin 2886) := Fin.ext h1661
    subst k
    rw [keyMomentRowsAt1661]
    exact keyMoment1661 B hB
  · have he : k = (1662 : Fin 2886) := Fin.ext h1662
    subst k
    rw [keyMomentRowsAt1662]
    exact keyMoment1662 B hB
  · have he : k = (1663 : Fin 2886) := Fin.ext h1663
    subst k
    rw [keyMomentRowsAt1663]
    exact keyMoment1663 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound51_e_oai
