-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:39.952267+00:00
-- url     : https://prove2.me/submissions/03ce8217-2d03-4407-8fb0-fe53efccf94e

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical322
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41269 raw41269Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw41269 raw41269Labels = mixedMoment B raw41269step0 raw41269step0Labels := by
      have ha : raw41269step0 = (fun i j => raw41269 (permutation556 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41269step0 raw41269; decide +kernel
      have hl : raw41269step0Labels = raw41269Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41269 raw41269Labels permutation556 permutation6
    mixedMoment B raw41269step0 raw41269step0Labels = mixedMoment B raw41269step1 raw41269step1Labels := by
      have ha : raw41269step1 = -raw41269step0 := by apply Matrix.ext; change ∀ i j, raw41269step1 i j = -(raw41269step0 i j); unfold raw41269step1 raw41269step0; decide +kernel
      have hl : raw41269step1Labels = raw41269step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

theorem canonical41270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41270 raw41270Labels = mixedMoment B node4044 node4044Labels := by
  calc
    mixedMoment B raw41270 raw41270Labels = mixedMoment B raw41270step0 raw41270step0Labels := by
      have ha : raw41270step0 = (fun i j => raw41270 (permutation188 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41270step0 raw41270; decide +kernel
      have hl : raw41270step0Labels = raw41270Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41270 raw41270Labels permutation188 permutation6
    _ = mixedMoment B node4044 node4044Labels := by rfl

theorem canonical41271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41271 raw41271Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw41271 raw41271Labels = mixedMoment B raw41271step0 raw41271step0Labels := by
      have ha : raw41271step0 = (fun i j => raw41271 (permutation192 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41271step0 raw41271; decide +kernel
      have hl : raw41271step0Labels = raw41271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41271 raw41271Labels permutation192 permutation6
    _ = mixedMoment B node4046 node4046Labels := by rfl

theorem canonical41272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41272 raw41272Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw41272 raw41272Labels = mixedMoment B raw41272step0 raw41272step0Labels := by
      have ha : raw41272step0 = (fun i j => raw41272 (permutation466 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41272step0 raw41272; decide +kernel
      have hl : raw41272step0Labels = raw41272Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41272 raw41272Labels permutation466 permutation6
    mixedMoment B raw41272step0 raw41272step0Labels = mixedMoment B raw41272step1 raw41272step1Labels := by
      have ha : raw41272step1 = -raw41272step0 := by apply Matrix.ext; change ∀ i j, raw41272step1 i j = -(raw41272step0 i j); unfold raw41272step1 raw41272step0; decide +kernel
      have hl : raw41272step1Labels = raw41272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical41273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41273 raw41273Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw41273 raw41273Labels = mixedMoment B raw41273step0 raw41273step0Labels := by
      have hz : ∀ j, raw41273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41273step0 = (fun i j => raw41273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41273step0 raw41273; decide +kernel
      have hl : raw41273step0Labels = raw41273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41273 raw41273Labels permutation346 hz
    mixedMoment B raw41273step0 raw41273step0Labels = mixedMoment B raw41273step1 raw41273step1Labels := by
      have ha : raw41273step1 = (fun i j => raw41273step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41273step1 raw41273step0; decide +kernel
      have hl : raw41273step1Labels = raw41273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41273step0 raw41273step0Labels permutation128 permutation6
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical41274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41274 raw41274Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw41274 raw41274Labels = mixedMoment B raw41274step0 raw41274step0Labels := by
      have hz : ∀ j, raw41274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41274step0 = (fun i j => raw41274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41274step0 raw41274; decide +kernel
      have hl : raw41274step0Labels = raw41274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41274 raw41274Labels permutation346 hz
    mixedMoment B raw41274step0 raw41274step0Labels = mixedMoment B raw41274step1 raw41274step1Labels := by
      have ha : raw41274step1 = (fun i j => raw41274step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41274step1 raw41274step0; decide +kernel
      have hl : raw41274step1Labels = raw41274step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41274step0 raw41274step0Labels permutation104 permutation6
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical41275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41275 raw41275Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw41275 raw41275Labels = mixedMoment B raw41275step0 raw41275step0Labels := by
      have hz : ∀ j, raw41275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41275step0 = (fun i j => raw41275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41275step0 raw41275; decide +kernel
      have hl : raw41275step0Labels = raw41275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41275 raw41275Labels permutation346 hz
    mixedMoment B raw41275step0 raw41275step0Labels = mixedMoment B raw41275step1 raw41275step1Labels := by
      have ha : raw41275step1 = (fun i j => raw41275step0 (permutation90 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41275step1 raw41275step0; decide +kernel
      have hl : raw41275step1Labels = raw41275step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41275step0 raw41275step0Labels permutation90 permutation6
    mixedMoment B raw41275step1 raw41275step1Labels = mixedMoment B raw41275step2 raw41275step2Labels := by
      have ha : raw41275step2 = -raw41275step1 := by apply Matrix.ext; change ∀ i j, raw41275step2 i j = -(raw41275step1 i j); unfold raw41275step2 raw41275step1; decide +kernel
      have hl : raw41275step2Labels = raw41275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical41276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41276 raw41276Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw41276 raw41276Labels = mixedMoment B raw41276step0 raw41276step0Labels := by
      have ha : raw41276step0 = (fun i j => raw41276 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41276step0 raw41276; decide +kernel
      have hl : raw41276step0Labels = raw41276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41276 raw41276Labels permutation590 permutation6
    _ = mixedMoment B node2880 node2880Labels := by rfl

theorem canonical41277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41277 raw41277Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw41277 raw41277Labels = mixedMoment B raw41277step0 raw41277step0Labels := by
      have ha : raw41277step0 = (fun i j => raw41277 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41277step0 raw41277; decide +kernel
      have hl : raw41277step0Labels = raw41277Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41277 raw41277Labels permutation526 permutation6
    _ = mixedMoment B node3957 node3957Labels := by rfl

theorem canonical41278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41278 raw41278Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw41278 raw41278Labels = mixedMoment B raw41278step0 raw41278step0Labels := by
      have hz : ∀ j, raw41278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41278step0 = (fun i j => raw41278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41278step0 raw41278; decide +kernel
      have hl : raw41278step0Labels = raw41278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41278 raw41278Labels permutation520 hz
    mixedMoment B raw41278step0 raw41278step0Labels = mixedMoment B raw41278step1 raw41278step1Labels := by
      have ha : raw41278step1 = (fun i j => raw41278step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41278step1 raw41278step0; decide +kernel
      have hl : raw41278step1Labels = raw41278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41278step0 raw41278step0Labels permutation149 permutation3
    mixedMoment B raw41278step1 raw41278step1Labels = mixedMoment B raw41278step2 raw41278step2Labels := by
      have ha : raw41278step2 = -raw41278step1 := by apply Matrix.ext; change ∀ i j, raw41278step2 i j = -(raw41278step1 i j); unfold raw41278step2 raw41278step1; decide +kernel
      have hl : raw41278step2Labels = raw41278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3108 node3108Labels := by rfl

theorem canonical41279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41279 raw41279Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw41279 raw41279Labels = mixedMoment B raw41279step0 raw41279step0Labels := by
      have ha : raw41279step0 = (fun i j => raw41279 (permutation300 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41279step0 raw41279; decide +kernel
      have hl : raw41279step0Labels = raw41279Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41279 raw41279Labels permutation300 permutation6
    mixedMoment B raw41279step0 raw41279step0Labels = mixedMoment B raw41279step1 raw41279step1Labels := by
      have ha : raw41279step1 = -raw41279step0 := by apply Matrix.ext; change ∀ i j, raw41279step1 i j = -(raw41279step0 i j); unfold raw41279step1 raw41279step0; decide +kernel
      have hl : raw41279step1Labels = raw41279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3922 node3922Labels := by rfl

theorem canonical41280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41280 raw41280Labels = mixedMoment B node2868 node2868Labels := by
  calc
    mixedMoment B raw41280 raw41280Labels = mixedMoment B raw41280step0 raw41280step0Labels := by
      have hz : ∀ j, raw41280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41280step0 = (fun i j => raw41280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41280step0 raw41280; decide +kernel
      have hl : raw41280step0Labels = raw41280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41280 raw41280Labels permutation434 hz
    mixedMoment B raw41280step0 raw41280step0Labels = mixedMoment B raw41280step1 raw41280step1Labels := by
      have ha : raw41280step1 = (fun i j => raw41280step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41280step1 raw41280step0; decide +kernel
      have hl : raw41280step1Labels = raw41280step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41280step0 raw41280step0Labels permutation132 permutation6
    _ = mixedMoment B node2868 node2868Labels := by rfl

theorem canonical41281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41281 raw41281Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw41281 raw41281Labels = mixedMoment B raw41281step0 raw41281step0Labels := by
      have hz : ∀ j, raw41281 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41281step0 = (fun i j => raw41281 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41281step0 raw41281; decide +kernel
      have hl : raw41281step0Labels = raw41281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41281 raw41281Labels permutation520 hz
    mixedMoment B raw41281step0 raw41281step0Labels = mixedMoment B raw41281step1 raw41281step1Labels := by
      have hz : ∀ j, raw41281step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41281step1 = (fun i j => raw41281step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41281step1 raw41281step0; decide +kernel
      have hl : raw41281step1Labels = raw41281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41281step0 raw41281step0Labels permutation104 hz
    mixedMoment B raw41281step1 raw41281step1Labels = mixedMoment B raw41281step2 raw41281step2Labels := by
      have ha : raw41281step2 = (fun i j => raw41281step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41281step2 raw41281step1; decide +kernel
      have hl : raw41281step2Labels = raw41281step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41281step1 raw41281step1Labels permutation31 permutation3
    mixedMoment B raw41281step2 raw41281step2Labels = mixedMoment B raw41281step3 raw41281step3Labels := by
      have ha : raw41281step3 = -raw41281step2 := by apply Matrix.ext; change ∀ i j, raw41281step3 i j = -(raw41281step2 i j); unfold raw41281step3 raw41281step2; decide +kernel
      have hl : raw41281step3Labels = raw41281step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical41282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41282 raw41282Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw41282 raw41282Labels = mixedMoment B raw41282step0 raw41282step0Labels := by
      have hz : ∀ j, raw41282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41282step0 = (fun i j => raw41282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41282step0 raw41282; decide +kernel
      have hl : raw41282step0Labels = raw41282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41282 raw41282Labels permutation434 hz
    mixedMoment B raw41282step0 raw41282step0Labels = mixedMoment B raw41282step1 raw41282step1Labels := by
      have ha : raw41282step1 = (fun i j => raw41282step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41282step1 raw41282step0; decide +kernel
      have hl : raw41282step1Labels = raw41282step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41282step0 raw41282step0Labels permutation73 permutation6
    mixedMoment B raw41282step1 raw41282step1Labels = mixedMoment B raw41282step2 raw41282step2Labels := by
      have ha : raw41282step2 = -raw41282step1 := by apply Matrix.ext; change ∀ i j, raw41282step2 i j = -(raw41282step1 i j); unfold raw41282step2 raw41282step1; decide +kernel
      have hl : raw41282step2Labels = raw41282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

theorem canonical41283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41283 raw41283Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw41283 raw41283Labels = mixedMoment B raw41283step0 raw41283step0Labels := by
      have hz : ∀ j, raw41283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41283step0 = (fun i j => raw41283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41283step0 raw41283; decide +kernel
      have hl : raw41283step0Labels = raw41283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41283 raw41283Labels permutation434 hz
    mixedMoment B raw41283step0 raw41283step0Labels = mixedMoment B raw41283step1 raw41283step1Labels := by
      have ha : raw41283step1 = (fun i j => raw41283step0 (permutation112 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41283step1 raw41283step0; decide +kernel
      have hl : raw41283step1Labels = raw41283step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41283step0 raw41283step0Labels permutation112 permutation6
    mixedMoment B raw41283step1 raw41283step1Labels = mixedMoment B raw41283step2 raw41283step2Labels := by
      have ha : raw41283step2 = -raw41283step1 := by apply Matrix.ext; change ∀ i j, raw41283step2 i j = -(raw41283step1 i j); unfold raw41283step2 raw41283step1; decide +kernel
      have hl : raw41283step2Labels = raw41283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

theorem canonical41284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41284 raw41284Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw41284 raw41284Labels = mixedMoment B raw41284step0 raw41284step0Labels := by
      have hz : ∀ j, raw41284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41284step0 = (fun i j => raw41284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41284step0 raw41284; decide +kernel
      have hl : raw41284step0Labels = raw41284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41284 raw41284Labels permutation434 hz
    mixedMoment B raw41284step0 raw41284step0Labels = mixedMoment B raw41284step1 raw41284step1Labels := by
      have ha : raw41284step1 = (fun i j => raw41284step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41284step1 raw41284step0; decide +kernel
      have hl : raw41284step1Labels = raw41284step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41284step0 raw41284step0Labels permutation79 permutation6
    mixedMoment B raw41284step1 raw41284step1Labels = mixedMoment B raw41284step2 raw41284step2Labels := by
      have ha : raw41284step2 = -raw41284step1 := by apply Matrix.ext; change ∀ i j, raw41284step2 i j = -(raw41284step1 i j); unfold raw41284step2 raw41284step1; decide +kernel
      have hl : raw41284step2Labels = raw41284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

theorem canonical41285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41285 raw41285Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw41285 raw41285Labels = mixedMoment B raw41285step0 raw41285step0Labels := by
      have hz : ∀ j, raw41285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41285step0 = (fun i j => raw41285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41285step0 raw41285; decide +kernel
      have hl : raw41285step0Labels = raw41285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41285 raw41285Labels permutation434 hz
    mixedMoment B raw41285step0 raw41285step0Labels = mixedMoment B raw41285step1 raw41285step1Labels := by
      have ha : raw41285step1 = (fun i j => raw41285step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41285step1 raw41285step0; decide +kernel
      have hl : raw41285step1Labels = raw41285step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41285step0 raw41285step0Labels permutation73 permutation6
    mixedMoment B raw41285step1 raw41285step1Labels = mixedMoment B raw41285step2 raw41285step2Labels := by
      have ha : raw41285step2 = -raw41285step1 := by apply Matrix.ext; change ∀ i j, raw41285step2 i j = -(raw41285step1 i j); unfold raw41285step2 raw41285step1; decide +kernel
      have hl : raw41285step2Labels = raw41285step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical41286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41286 raw41286Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw41286 raw41286Labels = mixedMoment B raw41286step0 raw41286step0Labels := by
      have ha : raw41286step0 = (fun i j => raw41286 (permutation315 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41286step0 raw41286; decide +kernel
      have hl : raw41286step0Labels = raw41286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41286 raw41286Labels permutation315 permutation6
    mixedMoment B raw41286step0 raw41286step0Labels = mixedMoment B raw41286step1 raw41286step1Labels := by
      have ha : raw41286step1 = -raw41286step0 := by apply Matrix.ext; change ∀ i j, raw41286step1 i j = -(raw41286step0 i j); unfold raw41286step1 raw41286step0; decide +kernel
      have hl : raw41286step1Labels = raw41286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

theorem canonical41287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41287 raw41287Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw41287 raw41287Labels = mixedMoment B raw41287step0 raw41287step0Labels := by
      have ha : raw41287step0 = (fun i j => raw41287 (permutation321 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41287step0 raw41287; decide +kernel
      have hl : raw41287step0Labels = raw41287Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41287 raw41287Labels permutation321 permutation6
    mixedMoment B raw41287step0 raw41287step0Labels = mixedMoment B raw41287step1 raw41287step1Labels := by
      have ha : raw41287step1 = -raw41287step0 := by apply Matrix.ext; change ∀ i j, raw41287step1 i j = -(raw41287step0 i j); unfold raw41287step1 raw41287step0; decide +kernel
      have hl : raw41287step1Labels = raw41287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical41288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41288 raw41288Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw41288 raw41288Labels = mixedMoment B raw41288step0 raw41288step0Labels := by
      have ha : raw41288step0 = (fun i j => raw41288 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41288step0 raw41288; decide +kernel
      have hl : raw41288step0Labels = raw41288Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41288 raw41288Labels permutation463 permutation6
    mixedMoment B raw41288step0 raw41288step0Labels = mixedMoment B raw41288step1 raw41288step1Labels := by
      have ha : raw41288step1 = -raw41288step0 := by apply Matrix.ext; change ∀ i j, raw41288step1 i j = -(raw41288step0 i j); unfold raw41288step1 raw41288step0; decide +kernel
      have hl : raw41288step1Labels = raw41288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3703 node3703Labels := by rfl

theorem canonical41289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41289 raw41289Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw41289 raw41289Labels = mixedMoment B raw41289step0 raw41289step0Labels := by
      have hz : ∀ j, raw41289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41289step0 = (fun i j => raw41289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41289step0 raw41289; decide +kernel
      have hl : raw41289step0Labels = raw41289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41289 raw41289Labels permutation434 hz
    mixedMoment B raw41289step0 raw41289step0Labels = mixedMoment B raw41289step1 raw41289step1Labels := by
      have hz : ∀ j, raw41289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41289step1 = (fun i j => raw41289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41289step1 raw41289step0; decide +kernel
      have hl : raw41289step1Labels = raw41289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41289step0 raw41289step0Labels permutation80 hz
    mixedMoment B raw41289step1 raw41289step1Labels = mixedMoment B raw41289step2 raw41289step2Labels := by
      have ha : raw41289step2 = (fun i j => raw41289step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41289step2 raw41289step1; decide +kernel
      have hl : raw41289step2Labels = raw41289step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41289step1 raw41289step1Labels permutation26 permutation6
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical41290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41290 raw41290Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw41290 raw41290Labels = mixedMoment B raw41290step0 raw41290step0Labels := by
      have hz : ∀ j, raw41290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41290step0 = (fun i j => raw41290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41290step0 raw41290; decide +kernel
      have hl : raw41290step0Labels = raw41290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41290 raw41290Labels permutation434 hz
    mixedMoment B raw41290step0 raw41290step0Labels = mixedMoment B raw41290step1 raw41290step1Labels := by
      have hz : ∀ j, raw41290step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41290step1 = (fun i j => raw41290step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41290step1 raw41290step0; decide +kernel
      have hl : raw41290step1Labels = raw41290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41290step0 raw41290step0Labels permutation80 hz
    mixedMoment B raw41290step1 raw41290step1Labels = mixedMoment B raw41290step2 raw41290step2Labels := by
      have ha : raw41290step2 = (fun i j => raw41290step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41290step2 raw41290step1; decide +kernel
      have hl : raw41290step2Labels = raw41290step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41290step1 raw41290step1Labels permutation21 permutation6
    _ = mixedMoment B node3963 node3963Labels := by rfl

theorem canonical41291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41291 raw41291Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw41291 raw41291Labels = mixedMoment B raw41291step0 raw41291step0Labels := by
      have hz : ∀ j, raw41291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41291step0 = (fun i j => raw41291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41291step0 raw41291; decide +kernel
      have hl : raw41291step0Labels = raw41291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41291 raw41291Labels permutation346 hz
    mixedMoment B raw41291step0 raw41291step0Labels = mixedMoment B raw41291step1 raw41291step1Labels := by
      have ha : raw41291step1 = (fun i j => raw41291step0 (permutation131 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41291step1 raw41291step0; decide +kernel
      have hl : raw41291step1Labels = raw41291step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41291step0 raw41291step0Labels permutation131 permutation6
    _ = mixedMoment B node2884 node2884Labels := by rfl

theorem canonical41292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41292 raw41292Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw41292 raw41292Labels = mixedMoment B raw41292step0 raw41292step0Labels := by
      have hz : ∀ j, raw41292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41292step0 = (fun i j => raw41292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41292step0 raw41292; decide +kernel
      have hl : raw41292step0Labels = raw41292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41292 raw41292Labels permutation346 hz
    mixedMoment B raw41292step0 raw41292step0Labels = mixedMoment B raw41292step1 raw41292step1Labels := by
      have ha : raw41292step1 = (fun i j => raw41292step0 (permutation109 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41292step1 raw41292step0; decide +kernel
      have hl : raw41292step1Labels = raw41292step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41292step0 raw41292step0Labels permutation109 permutation6
    _ = mixedMoment B node3958 node3958Labels := by rfl

theorem canonical41293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41293 raw41293Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw41293 raw41293Labels = mixedMoment B raw41293step0 raw41293step0Labels := by
      have hz : ∀ j, raw41293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41293step0 = (fun i j => raw41293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41293step0 raw41293; decide +kernel
      have hl : raw41293step0Labels = raw41293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41293 raw41293Labels permutation346 hz
    mixedMoment B raw41293step0 raw41293step0Labels = mixedMoment B raw41293step1 raw41293step1Labels := by
      have ha : raw41293step1 = (fun i j => raw41293step0 (permutation90 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41293step1 raw41293step0; decide +kernel
      have hl : raw41293step1Labels = raw41293step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41293step0 raw41293step0Labels permutation90 permutation6
    mixedMoment B raw41293step1 raw41293step1Labels = mixedMoment B raw41293step2 raw41293step2Labels := by
      have ha : raw41293step2 = -raw41293step1 := by apply Matrix.ext; change ∀ i j, raw41293step2 i j = -(raw41293step1 i j); unfold raw41293step2 raw41293step1; decide +kernel
      have hl : raw41293step2Labels = raw41293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical41294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41294 raw41294Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw41294 raw41294Labels = mixedMoment B raw41294step0 raw41294step0Labels := by
      have ha : raw41294step0 = (fun i j => raw41294 (permutation528 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41294step0 raw41294; decide +kernel
      have hl : raw41294step0Labels = raw41294Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41294 raw41294Labels permutation528 permutation6
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical41295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41295 raw41295Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw41295 raw41295Labels = mixedMoment B raw41295step0 raw41295step0Labels := by
      have hz : ∀ j, raw41295 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41295step0 = (fun i j => raw41295 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41295step0 raw41295; decide +kernel
      have hl : raw41295step0Labels = raw41295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41295 raw41295Labels permutation520 hz
    mixedMoment B raw41295step0 raw41295step0Labels = mixedMoment B raw41295step1 raw41295step1Labels := by
      have hz : ∀ j, raw41295step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41295step1 = (fun i j => raw41295step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41295step1 raw41295step0; decide +kernel
      have hl : raw41295step1Labels = raw41295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41295step0 raw41295step0Labels permutation104 hz
    mixedMoment B raw41295step1 raw41295step1Labels = mixedMoment B raw41295step2 raw41295step2Labels := by
      have ha : raw41295step2 = (fun i j => raw41295step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41295step2 raw41295step1; decide +kernel
      have hl : raw41295step2Labels = raw41295step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41295step1 raw41295step1Labels permutation19 permutation6
    mixedMoment B raw41295step2 raw41295step2Labels = mixedMoment B raw41295step3 raw41295step3Labels := by
      have ha : raw41295step3 = -raw41295step2 := by apply Matrix.ext; change ∀ i j, raw41295step3 i j = -(raw41295step2 i j); unfold raw41295step3 raw41295step2; decide +kernel
      have hl : raw41295step3Labels = raw41295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical41296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41296 raw41296Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw41296 raw41296Labels = mixedMoment B raw41296step0 raw41296step0Labels := by
      have hz : ∀ j, raw41296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41296step0 = (fun i j => raw41296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41296step0 raw41296; decide +kernel
      have hl : raw41296step0Labels = raw41296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41296 raw41296Labels permutation434 hz
    mixedMoment B raw41296step0 raw41296step0Labels = mixedMoment B raw41296step1 raw41296step1Labels := by
      have ha : raw41296step1 = (fun i j => raw41296step0 (permutation70 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41296step1 raw41296step0; decide +kernel
      have hl : raw41296step1Labels = raw41296step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41296step0 raw41296step0Labels permutation70 permutation6
    mixedMoment B raw41296step1 raw41296step1Labels = mixedMoment B raw41296step2 raw41296step2Labels := by
      have ha : raw41296step2 = -raw41296step1 := by apply Matrix.ext; change ∀ i j, raw41296step2 i j = -(raw41296step1 i j); unfold raw41296step2 raw41296step1; decide +kernel
      have hl : raw41296step2Labels = raw41296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

theorem canonical41297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41297 raw41297Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw41297 raw41297Labels = mixedMoment B raw41297step0 raw41297step0Labels := by
      have hz : ∀ j, raw41297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41297step0 = (fun i j => raw41297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41297step0 raw41297; decide +kernel
      have hl : raw41297step0Labels = raw41297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41297 raw41297Labels permutation434 hz
    mixedMoment B raw41297step0 raw41297step0Labels = mixedMoment B raw41297step1 raw41297step1Labels := by
      have ha : raw41297step1 = (fun i j => raw41297step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41297step1 raw41297step0; decide +kernel
      have hl : raw41297step1Labels = raw41297step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41297step0 raw41297step0Labels permutation79 permutation6
    mixedMoment B raw41297step1 raw41297step1Labels = mixedMoment B raw41297step2 raw41297step2Labels := by
      have ha : raw41297step2 = -raw41297step1 := by apply Matrix.ext; change ∀ i j, raw41297step2 i j = -(raw41297step1 i j); unfold raw41297step2 raw41297step1; decide +kernel
      have hl : raw41297step2Labels = raw41297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical41298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41298 raw41298Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw41298 raw41298Labels = mixedMoment B raw41298step0 raw41298step0Labels := by
      have ha : raw41298step0 = (fun i j => raw41298 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41298step0 raw41298; decide +kernel
      have hl : raw41298step0Labels = raw41298Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41298 raw41298Labels permutation317 permutation6
    mixedMoment B raw41298step0 raw41298step0Labels = mixedMoment B raw41298step1 raw41298step1Labels := by
      have ha : raw41298step1 = -raw41298step0 := by apply Matrix.ext; change ∀ i j, raw41298step1 i j = -(raw41298step0 i j); unfold raw41298step1 raw41298step0; decide +kernel
      have hl : raw41298step1Labels = raw41298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2508 node2508Labels := by rfl

theorem canonical41299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41299 raw41299Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw41299 raw41299Labels = mixedMoment B raw41299step0 raw41299step0Labels := by
      have hz : ∀ j, raw41299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41299step0 = (fun i j => raw41299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41299step0 raw41299; decide +kernel
      have hl : raw41299step0Labels = raw41299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41299 raw41299Labels permutation434 hz
    mixedMoment B raw41299step0 raw41299step0Labels = mixedMoment B raw41299step1 raw41299step1Labels := by
      have hz : ∀ j, raw41299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41299step1 = (fun i j => raw41299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41299step1 raw41299step0; decide +kernel
      have hl : raw41299step1Labels = raw41299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41299step0 raw41299step0Labels permutation80 hz
    mixedMoment B raw41299step1 raw41299step1Labels = mixedMoment B raw41299step2 raw41299step2Labels := by
      have ha : raw41299step2 = (fun i j => raw41299step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41299step2 raw41299step1; decide +kernel
      have hl : raw41299step2Labels = raw41299step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41299step1 raw41299step1Labels permutation16 permutation6
    mixedMoment B raw41299step2 raw41299step2Labels = mixedMoment B raw41299step3 raw41299step3Labels := by
      have ha : raw41299step3 = -raw41299step2 := by apply Matrix.ext; change ∀ i j, raw41299step3 i j = -(raw41299step2 i j); unfold raw41299step3 raw41299step2; decide +kernel
      have hl : raw41299step3Labels = raw41299step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical41300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41300 raw41300Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw41300 raw41300Labels = mixedMoment B raw41300step0 raw41300step0Labels := by
      have hz : ∀ j, raw41300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41300step0 = (fun i j => raw41300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41300step0 raw41300; decide +kernel
      have hl : raw41300step0Labels = raw41300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41300 raw41300Labels permutation434 hz
    mixedMoment B raw41300step0 raw41300step0Labels = mixedMoment B raw41300step1 raw41300step1Labels := by
      have hz : ∀ j, raw41300step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41300step1 = (fun i j => raw41300step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41300step1 raw41300step0; decide +kernel
      have hl : raw41300step1Labels = raw41300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41300step0 raw41300step0Labels permutation80 hz
    mixedMoment B raw41300step1 raw41300step1Labels = mixedMoment B raw41300step2 raw41300step2Labels := by
      have ha : raw41300step2 = (fun i j => raw41300step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41300step2 raw41300step1; decide +kernel
      have hl : raw41300step2Labels = raw41300step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41300step1 raw41300step1Labels permutation18 permutation6
    mixedMoment B raw41300step2 raw41300step2Labels = mixedMoment B raw41300step3 raw41300step3Labels := by
      have ha : raw41300step3 = -raw41300step2 := by apply Matrix.ext; change ∀ i j, raw41300step3 i j = -(raw41300step2 i j); unfold raw41300step3 raw41300step2; decide +kernel
      have hl : raw41300step3Labels = raw41300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2743 node2743Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1856 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1856) =
      Integer.Sparse.eval keyMomentRow1856 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1856).leftCharge (GramAssembly.key 1856).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3782) := by
    have ha : gramCharges (GramAssembly.key 1856).leftCharge (GramAssembly.key 1856).rightCharge = raw41269 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41269Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41269 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1856).leftCharge (GramAssembly.key 1856).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1856, Integer.Sparse.eval]

theorem keyMoment1857 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1857) =
      Integer.Sparse.eval keyMomentRow1857 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1857).leftCharge (GramAssembly.key 1857).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4044) := by
    have ha : gramCharges (GramAssembly.key 1857).leftCharge (GramAssembly.key 1857).rightCharge = raw41270 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41270Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41270 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1857).leftCharge (GramAssembly.key 1857).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1857, Integer.Sparse.eval]

theorem keyMoment1858 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1858) =
      Integer.Sparse.eval keyMomentRow1858 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1858).leftCharge (GramAssembly.key 1858).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4046) := by
    have ha : gramCharges (GramAssembly.key 1858).leftCharge (GramAssembly.key 1858).rightCharge = raw41271 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41271Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41271 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1858).leftCharge (GramAssembly.key 1858).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1858, Integer.Sparse.eval]

theorem keyMoment1859 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1859) =
      Integer.Sparse.eval keyMomentRow1859 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1859).leftCharge (GramAssembly.key 1859).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3843) := by
    have ha : gramCharges (GramAssembly.key 1859).leftCharge (GramAssembly.key 1859).rightCharge = raw41272 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41272Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41272 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1859).leftCharge (GramAssembly.key 1859).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1859, Integer.Sparse.eval]

theorem keyMoment1860 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1860) =
      Integer.Sparse.eval keyMomentRow1860 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1860).leftCharge (GramAssembly.key 1860).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2881) := by
    have ha : gramCharges (GramAssembly.key 1860).leftCharge (GramAssembly.key 1860).rightCharge = raw41273 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41273Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41273 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1860).leftCharge (GramAssembly.key 1860).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1860, Integer.Sparse.eval]

theorem keyMoment1861 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1861) =
      Integer.Sparse.eval keyMomentRow1861 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1861).leftCharge (GramAssembly.key 1861).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1861).leftCharge (GramAssembly.key 1861).rightCharge = raw41274 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41274Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41274 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1861).leftCharge (GramAssembly.key 1861).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1861, Integer.Sparse.eval]

theorem keyMoment1862 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1862) =
      Integer.Sparse.eval keyMomentRow1862 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1862).leftCharge (GramAssembly.key 1862).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1862).leftCharge (GramAssembly.key 1862).rightCharge = raw41275 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41275Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41275 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1862).leftCharge (GramAssembly.key 1862).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1862, Integer.Sparse.eval]

theorem keyMoment1863 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1863) =
      Integer.Sparse.eval keyMomentRow1863 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1863).leftCharge (GramAssembly.key 1863).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2880) := by
    have ha : gramCharges (GramAssembly.key 1863).leftCharge (GramAssembly.key 1863).rightCharge = raw41276 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41276Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41276 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1863).leftCharge (GramAssembly.key 1863).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1863, Integer.Sparse.eval]

theorem keyMoment1864 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1864) =
      Integer.Sparse.eval keyMomentRow1864 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1864).leftCharge (GramAssembly.key 1864).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3957) := by
    have ha : gramCharges (GramAssembly.key 1864).leftCharge (GramAssembly.key 1864).rightCharge = raw41277 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41277Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41277 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1864).leftCharge (GramAssembly.key 1864).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1864, Integer.Sparse.eval]

theorem keyMoment1865 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1865) =
      Integer.Sparse.eval keyMomentRow1865 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1865).leftCharge (GramAssembly.key 1865).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3108) := by
    have ha : gramCharges (GramAssembly.key 1865).leftCharge (GramAssembly.key 1865).rightCharge = raw41278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41278 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1865).leftCharge (GramAssembly.key 1865).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1865, Integer.Sparse.eval]

theorem keyMoment1866 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1866) =
      Integer.Sparse.eval keyMomentRow1866 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1866).leftCharge (GramAssembly.key 1866).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3922) := by
    have ha : gramCharges (GramAssembly.key 1866).leftCharge (GramAssembly.key 1866).rightCharge = raw41279 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41279Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41279 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1866).leftCharge (GramAssembly.key 1866).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1866, Integer.Sparse.eval]

theorem keyMoment1867 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1867) =
      Integer.Sparse.eval keyMomentRow1867 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1867).leftCharge (GramAssembly.key 1867).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2868) := by
    have ha : gramCharges (GramAssembly.key 1867).leftCharge (GramAssembly.key 1867).rightCharge = raw41280 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41280Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41280 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1867).leftCharge (GramAssembly.key 1867).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1867, Integer.Sparse.eval]

theorem keyMoment1868 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1868) =
      Integer.Sparse.eval keyMomentRow1868 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1868).leftCharge (GramAssembly.key 1868).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1868).leftCharge (GramAssembly.key 1868).rightCharge = raw41281 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41281Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41281 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1868).leftCharge (GramAssembly.key 1868).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1868, Integer.Sparse.eval]

theorem keyMoment1869 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1869) =
      Integer.Sparse.eval keyMomentRow1869 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1869).leftCharge (GramAssembly.key 1869).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3983) := by
    have ha : gramCharges (GramAssembly.key 1869).leftCharge (GramAssembly.key 1869).rightCharge = raw41282 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41282Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41282 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1869).leftCharge (GramAssembly.key 1869).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1869, Integer.Sparse.eval]

theorem keyMoment1870 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1870) =
      Integer.Sparse.eval keyMomentRow1870 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1870).leftCharge (GramAssembly.key 1870).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3706) := by
    have ha : gramCharges (GramAssembly.key 1870).leftCharge (GramAssembly.key 1870).rightCharge = raw41283 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41283Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41283 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1870).leftCharge (GramAssembly.key 1870).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1870, Integer.Sparse.eval]

theorem keyMoment1871 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1871) =
      Integer.Sparse.eval keyMomentRow1871 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1871).leftCharge (GramAssembly.key 1871).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3961) := by
    have ha : gramCharges (GramAssembly.key 1871).leftCharge (GramAssembly.key 1871).rightCharge = raw41284 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41284Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41284 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1871).leftCharge (GramAssembly.key 1871).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1871, Integer.Sparse.eval]

theorem keyMoment1872 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1872) =
      Integer.Sparse.eval keyMomentRow1872 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1872).leftCharge (GramAssembly.key 1872).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1872).leftCharge (GramAssembly.key 1872).rightCharge = raw41285 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41285Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41285 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1872).leftCharge (GramAssembly.key 1872).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1872, Integer.Sparse.eval]

theorem keyMoment1873 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1873) =
      Integer.Sparse.eval keyMomentRow1873 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1873).leftCharge (GramAssembly.key 1873).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3964) := by
    have ha : gramCharges (GramAssembly.key 1873).leftCharge (GramAssembly.key 1873).rightCharge = raw41286 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41286Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41286 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1873).leftCharge (GramAssembly.key 1873).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1873, Integer.Sparse.eval]

theorem keyMoment1874 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1874) =
      Integer.Sparse.eval keyMomentRow1874 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1874).leftCharge (GramAssembly.key 1874).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3974) := by
    have ha : gramCharges (GramAssembly.key 1874).leftCharge (GramAssembly.key 1874).rightCharge = raw41287 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41287Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41287 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1874).leftCharge (GramAssembly.key 1874).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1874, Integer.Sparse.eval]

theorem keyMoment1875 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1875) =
      Integer.Sparse.eval keyMomentRow1875 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1875).leftCharge (GramAssembly.key 1875).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3703) := by
    have ha : gramCharges (GramAssembly.key 1875).leftCharge (GramAssembly.key 1875).rightCharge = raw41288 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41288Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41288 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1875).leftCharge (GramAssembly.key 1875).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1875, Integer.Sparse.eval]

theorem keyMoment1876 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1876) =
      Integer.Sparse.eval keyMomentRow1876 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1876).leftCharge (GramAssembly.key 1876).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2889) := by
    have ha : gramCharges (GramAssembly.key 1876).leftCharge (GramAssembly.key 1876).rightCharge = raw41289 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41289Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41289 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1876).leftCharge (GramAssembly.key 1876).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1876, Integer.Sparse.eval]

theorem keyMoment1877 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1877) =
      Integer.Sparse.eval keyMomentRow1877 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1877).leftCharge (GramAssembly.key 1877).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3963) := by
    have ha : gramCharges (GramAssembly.key 1877).leftCharge (GramAssembly.key 1877).rightCharge = raw41290 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41290Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41290 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1877).leftCharge (GramAssembly.key 1877).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1877, Integer.Sparse.eval]

theorem keyMoment1878 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1878) =
      Integer.Sparse.eval keyMomentRow1878 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1878).leftCharge (GramAssembly.key 1878).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2884) := by
    have ha : gramCharges (GramAssembly.key 1878).leftCharge (GramAssembly.key 1878).rightCharge = raw41291 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41291Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41291 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1878).leftCharge (GramAssembly.key 1878).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1878, Integer.Sparse.eval]

theorem keyMoment1879 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1879) =
      Integer.Sparse.eval keyMomentRow1879 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1879).leftCharge (GramAssembly.key 1879).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3958) := by
    have ha : gramCharges (GramAssembly.key 1879).leftCharge (GramAssembly.key 1879).rightCharge = raw41292 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41292Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41292 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1879).leftCharge (GramAssembly.key 1879).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1879, Integer.Sparse.eval]

theorem keyMoment1880 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1880) =
      Integer.Sparse.eval keyMomentRow1880 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1880).leftCharge (GramAssembly.key 1880).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3705) := by
    have ha : gramCharges (GramAssembly.key 1880).leftCharge (GramAssembly.key 1880).rightCharge = raw41293 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41293Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41293 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1880).leftCharge (GramAssembly.key 1880).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1880, Integer.Sparse.eval]

theorem keyMoment1881 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1881) =
      Integer.Sparse.eval keyMomentRow1881 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1881).leftCharge (GramAssembly.key 1881).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3945) := by
    have ha : gramCharges (GramAssembly.key 1881).leftCharge (GramAssembly.key 1881).rightCharge = raw41294 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41294Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41294 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1881).leftCharge (GramAssembly.key 1881).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1881, Integer.Sparse.eval]

theorem keyMoment1882 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1882) =
      Integer.Sparse.eval keyMomentRow1882 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1882).leftCharge (GramAssembly.key 1882).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 1882).leftCharge (GramAssembly.key 1882).rightCharge = raw41295 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41295Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41295 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1882).leftCharge (GramAssembly.key 1882).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1882, Integer.Sparse.eval]

theorem keyMoment1883 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1883) =
      Integer.Sparse.eval keyMomentRow1883 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1883).leftCharge (GramAssembly.key 1883).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2515) := by
    have ha : gramCharges (GramAssembly.key 1883).leftCharge (GramAssembly.key 1883).rightCharge = raw41296 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41296Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41296 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1883).leftCharge (GramAssembly.key 1883).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1883, Integer.Sparse.eval]

theorem keyMoment1884 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1884) =
      Integer.Sparse.eval keyMomentRow1884 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1884).leftCharge (GramAssembly.key 1884).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 1884).leftCharge (GramAssembly.key 1884).rightCharge = raw41297 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41297Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41297 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1884).leftCharge (GramAssembly.key 1884).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1884, Integer.Sparse.eval]

theorem keyMoment1885 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1885) =
      Integer.Sparse.eval keyMomentRow1885 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1885).leftCharge (GramAssembly.key 1885).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2508) := by
    have ha : gramCharges (GramAssembly.key 1885).leftCharge (GramAssembly.key 1885).rightCharge = raw41298 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41298Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41298 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1885).leftCharge (GramAssembly.key 1885).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1885, Integer.Sparse.eval]

theorem keyMoment1886 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1886) =
      Integer.Sparse.eval keyMomentRow1886 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1886).leftCharge (GramAssembly.key 1886).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2519) := by
    have ha : gramCharges (GramAssembly.key 1886).leftCharge (GramAssembly.key 1886).rightCharge = raw41299 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41299Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41299 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1886).leftCharge (GramAssembly.key 1886).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1886, Integer.Sparse.eval]

theorem keyMoment1887 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1887) =
      Integer.Sparse.eval keyMomentRow1887 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1887).leftCharge (GramAssembly.key 1887).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2743) := by
    have ha : gramCharges (GramAssembly.key 1887).leftCharge (GramAssembly.key 1887).rightCharge = raw41300 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41300Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41300 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1887).leftCharge (GramAssembly.key 1887).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1887, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1856 : keyMomentRows (1856 : Fin 2886) =
    keyMomentRow1856 := by decide +kernel

theorem keyMomentRowsAt1857 : keyMomentRows (1857 : Fin 2886) =
    keyMomentRow1857 := by decide +kernel

theorem keyMomentRowsAt1858 : keyMomentRows (1858 : Fin 2886) =
    keyMomentRow1858 := by decide +kernel

theorem keyMomentRowsAt1859 : keyMomentRows (1859 : Fin 2886) =
    keyMomentRow1859 := by decide +kernel

theorem keyMomentRowsAt1860 : keyMomentRows (1860 : Fin 2886) =
    keyMomentRow1860 := by decide +kernel

theorem keyMomentRowsAt1861 : keyMomentRows (1861 : Fin 2886) =
    keyMomentRow1861 := by decide +kernel

theorem keyMomentRowsAt1862 : keyMomentRows (1862 : Fin 2886) =
    keyMomentRow1862 := by decide +kernel

theorem keyMomentRowsAt1863 : keyMomentRows (1863 : Fin 2886) =
    keyMomentRow1863 := by decide +kernel

theorem keyMomentRowsAt1864 : keyMomentRows (1864 : Fin 2886) =
    keyMomentRow1864 := by decide +kernel

theorem keyMomentRowsAt1865 : keyMomentRows (1865 : Fin 2886) =
    keyMomentRow1865 := by decide +kernel

theorem keyMomentRowsAt1866 : keyMomentRows (1866 : Fin 2886) =
    keyMomentRow1866 := by decide +kernel

theorem keyMomentRowsAt1867 : keyMomentRows (1867 : Fin 2886) =
    keyMomentRow1867 := by decide +kernel

theorem keyMomentRowsAt1868 : keyMomentRows (1868 : Fin 2886) =
    keyMomentRow1868 := by decide +kernel

theorem keyMomentRowsAt1869 : keyMomentRows (1869 : Fin 2886) =
    keyMomentRow1869 := by decide +kernel

theorem keyMomentRowsAt1870 : keyMomentRows (1870 : Fin 2886) =
    keyMomentRow1870 := by decide +kernel

theorem keyMomentRowsAt1871 : keyMomentRows (1871 : Fin 2886) =
    keyMomentRow1871 := by decide +kernel

theorem keyMomentRowsAt1872 : keyMomentRows (1872 : Fin 2886) =
    keyMomentRow1872 := by decide +kernel

theorem keyMomentRowsAt1873 : keyMomentRows (1873 : Fin 2886) =
    keyMomentRow1873 := by decide +kernel

theorem keyMomentRowsAt1874 : keyMomentRows (1874 : Fin 2886) =
    keyMomentRow1874 := by decide +kernel

theorem keyMomentRowsAt1875 : keyMomentRows (1875 : Fin 2886) =
    keyMomentRow1875 := by decide +kernel

theorem keyMomentRowsAt1876 : keyMomentRows (1876 : Fin 2886) =
    keyMomentRow1876 := by decide +kernel

theorem keyMomentRowsAt1877 : keyMomentRows (1877 : Fin 2886) =
    keyMomentRow1877 := by decide +kernel

theorem keyMomentRowsAt1878 : keyMomentRows (1878 : Fin 2886) =
    keyMomentRow1878 := by decide +kernel

theorem keyMomentRowsAt1879 : keyMomentRows (1879 : Fin 2886) =
    keyMomentRow1879 := by decide +kernel

theorem keyMomentRowsAt1880 : keyMomentRows (1880 : Fin 2886) =
    keyMomentRow1880 := by decide +kernel

theorem keyMomentRowsAt1881 : keyMomentRows (1881 : Fin 2886) =
    keyMomentRow1881 := by decide +kernel

theorem keyMomentRowsAt1882 : keyMomentRows (1882 : Fin 2886) =
    keyMomentRow1882 := by decide +kernel

theorem keyMomentRowsAt1883 : keyMomentRows (1883 : Fin 2886) =
    keyMomentRow1883 := by decide +kernel

theorem keyMomentRowsAt1884 : keyMomentRows (1884 : Fin 2886) =
    keyMomentRow1884 := by decide +kernel

theorem keyMomentRowsAt1885 : keyMomentRows (1885 : Fin 2886) =
    keyMomentRow1885 := by decide +kernel

theorem keyMomentRowsAt1886 : keyMomentRows (1886 : Fin 2886) =
    keyMomentRow1886 := by decide +kernel

theorem keyMomentRowsAt1887 : keyMomentRows (1887 : Fin 2886) =
    keyMomentRow1887 := by decide +kernel

theorem keyMomentChunkSound58_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 58) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1856 ∨ k.val = 1857 ∨ k.val = 1858 ∨ k.val = 1859 ∨ k.val = 1860 ∨ k.val = 1861 ∨ k.val = 1862 ∨ k.val = 1863 ∨ k.val = 1864 ∨ k.val = 1865 ∨ k.val = 1866 ∨ k.val = 1867 ∨ k.val = 1868 ∨ k.val = 1869 ∨ k.val = 1870 ∨ k.val = 1871 ∨ k.val = 1872 ∨ k.val = 1873 ∨ k.val = 1874 ∨ k.val = 1875 ∨ k.val = 1876 ∨ k.val = 1877 ∨ k.val = 1878 ∨ k.val = 1879 ∨ k.val = 1880 ∨ k.val = 1881 ∨ k.val = 1882 ∨ k.val = 1883 ∨ k.val = 1884 ∨ k.val = 1885 ∨ k.val = 1886 ∨ k.val = 1887 := by omega
  rcases heq with h1856 | h1857 | h1858 | h1859 | h1860 | h1861 | h1862 | h1863 | h1864 | h1865 | h1866 | h1867 | h1868 | h1869 | h1870 | h1871 | h1872 | h1873 | h1874 | h1875 | h1876 | h1877 | h1878 | h1879 | h1880 | h1881 | h1882 | h1883 | h1884 | h1885 | h1886 | h1887
  · have he : k = (1856 : Fin 2886) := Fin.ext h1856
    subst k
    rw [keyMomentRowsAt1856]
    exact keyMoment1856 B hB
  · have he : k = (1857 : Fin 2886) := Fin.ext h1857
    subst k
    rw [keyMomentRowsAt1857]
    exact keyMoment1857 B hB
  · have he : k = (1858 : Fin 2886) := Fin.ext h1858
    subst k
    rw [keyMomentRowsAt1858]
    exact keyMoment1858 B hB
  · have he : k = (1859 : Fin 2886) := Fin.ext h1859
    subst k
    rw [keyMomentRowsAt1859]
    exact keyMoment1859 B hB
  · have he : k = (1860 : Fin 2886) := Fin.ext h1860
    subst k
    rw [keyMomentRowsAt1860]
    exact keyMoment1860 B hB
  · have he : k = (1861 : Fin 2886) := Fin.ext h1861
    subst k
    rw [keyMomentRowsAt1861]
    exact keyMoment1861 B hB
  · have he : k = (1862 : Fin 2886) := Fin.ext h1862
    subst k
    rw [keyMomentRowsAt1862]
    exact keyMoment1862 B hB
  · have he : k = (1863 : Fin 2886) := Fin.ext h1863
    subst k
    rw [keyMomentRowsAt1863]
    exact keyMoment1863 B hB
  · have he : k = (1864 : Fin 2886) := Fin.ext h1864
    subst k
    rw [keyMomentRowsAt1864]
    exact keyMoment1864 B hB
  · have he : k = (1865 : Fin 2886) := Fin.ext h1865
    subst k
    rw [keyMomentRowsAt1865]
    exact keyMoment1865 B hB
  · have he : k = (1866 : Fin 2886) := Fin.ext h1866
    subst k
    rw [keyMomentRowsAt1866]
    exact keyMoment1866 B hB
  · have he : k = (1867 : Fin 2886) := Fin.ext h1867
    subst k
    rw [keyMomentRowsAt1867]
    exact keyMoment1867 B hB
  · have he : k = (1868 : Fin 2886) := Fin.ext h1868
    subst k
    rw [keyMomentRowsAt1868]
    exact keyMoment1868 B hB
  · have he : k = (1869 : Fin 2886) := Fin.ext h1869
    subst k
    rw [keyMomentRowsAt1869]
    exact keyMoment1869 B hB
  · have he : k = (1870 : Fin 2886) := Fin.ext h1870
    subst k
    rw [keyMomentRowsAt1870]
    exact keyMoment1870 B hB
  · have he : k = (1871 : Fin 2886) := Fin.ext h1871
    subst k
    rw [keyMomentRowsAt1871]
    exact keyMoment1871 B hB
  · have he : k = (1872 : Fin 2886) := Fin.ext h1872
    subst k
    rw [keyMomentRowsAt1872]
    exact keyMoment1872 B hB
  · have he : k = (1873 : Fin 2886) := Fin.ext h1873
    subst k
    rw [keyMomentRowsAt1873]
    exact keyMoment1873 B hB
  · have he : k = (1874 : Fin 2886) := Fin.ext h1874
    subst k
    rw [keyMomentRowsAt1874]
    exact keyMoment1874 B hB
  · have he : k = (1875 : Fin 2886) := Fin.ext h1875
    subst k
    rw [keyMomentRowsAt1875]
    exact keyMoment1875 B hB
  · have he : k = (1876 : Fin 2886) := Fin.ext h1876
    subst k
    rw [keyMomentRowsAt1876]
    exact keyMoment1876 B hB
  · have he : k = (1877 : Fin 2886) := Fin.ext h1877
    subst k
    rw [keyMomentRowsAt1877]
    exact keyMoment1877 B hB
  · have he : k = (1878 : Fin 2886) := Fin.ext h1878
    subst k
    rw [keyMomentRowsAt1878]
    exact keyMoment1878 B hB
  · have he : k = (1879 : Fin 2886) := Fin.ext h1879
    subst k
    rw [keyMomentRowsAt1879]
    exact keyMoment1879 B hB
  · have he : k = (1880 : Fin 2886) := Fin.ext h1880
    subst k
    rw [keyMomentRowsAt1880]
    exact keyMoment1880 B hB
  · have he : k = (1881 : Fin 2886) := Fin.ext h1881
    subst k
    rw [keyMomentRowsAt1881]
    exact keyMoment1881 B hB
  · have he : k = (1882 : Fin 2886) := Fin.ext h1882
    subst k
    rw [keyMomentRowsAt1882]
    exact keyMoment1882 B hB
  · have he : k = (1883 : Fin 2886) := Fin.ext h1883
    subst k
    rw [keyMomentRowsAt1883]
    exact keyMoment1883 B hB
  · have he : k = (1884 : Fin 2886) := Fin.ext h1884
    subst k
    rw [keyMomentRowsAt1884]
    exact keyMoment1884 B hB
  · have he : k = (1885 : Fin 2886) := Fin.ext h1885
    subst k
    rw [keyMomentRowsAt1885]
    exact keyMoment1885 B hB
  · have he : k = (1886 : Fin 2886) := Fin.ext h1886
    subst k
    rw [keyMomentRowsAt1886]
    exact keyMoment1886 B hB
  · have he : k = (1887 : Fin 2886) := Fin.ext h1887
    subst k
    rw [keyMomentRowsAt1887]
    exact keyMoment1887 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound58_e_oai
