-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:53.902205+00:00
-- url     : https://prove2.me/submissions/cb9dceff-fbbd-4665-92c3-76e708ff29ac

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical312
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39992 raw39992Labels = mixedMoment B node224 node224Labels := by
  calc
    mixedMoment B raw39992 raw39992Labels = mixedMoment B raw39992step0 raw39992step0Labels := by
      have hz : ∀ j, raw39992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39992step0 = (fun i j => raw39992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39992step0 raw39992; decide +kernel
      have hl : raw39992step0Labels = raw39992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39992 raw39992Labels permutation346 hz
    mixedMoment B raw39992step0 raw39992step0Labels = mixedMoment B raw39992step1 raw39992step1Labels := by
      have ha : raw39992step1 = (fun i j => raw39992step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39992step1 raw39992step0; decide +kernel
      have hl : raw39992step1Labels = raw39992step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39992step0 raw39992step0Labels permutation73 permutation6
    _ = mixedMoment B node224 node224Labels := by rfl

theorem canonical39993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39993 raw39993Labels = mixedMoment B node211 node211Labels := by
  calc
    mixedMoment B raw39993 raw39993Labels = mixedMoment B raw39993step0 raw39993step0Labels := by
      have hz : ∀ j, raw39993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39993step0 = (fun i j => raw39993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39993step0 raw39993; decide +kernel
      have hl : raw39993step0Labels = raw39993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39993 raw39993Labels permutation346 hz
    mixedMoment B raw39993step0 raw39993step0Labels = mixedMoment B raw39993step1 raw39993step1Labels := by
      have ha : raw39993step1 = (fun i j => raw39993step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39993step1 raw39993step0; decide +kernel
      have hl : raw39993step1Labels = raw39993step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39993step0 raw39993step0Labels permutation73 permutation6
    _ = mixedMoment B node211 node211Labels := by rfl

theorem canonical39994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39994 raw39994Labels = mixedMoment B node207 node207Labels := by
  calc
    mixedMoment B raw39994 raw39994Labels = mixedMoment B raw39994step0 raw39994step0Labels := by
      have ha : raw39994step0 = (fun i j => raw39994 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39994step0 raw39994; decide +kernel
      have hl : raw39994step0Labels = raw39994Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39994 raw39994Labels permutation332 permutation6
    _ = mixedMoment B node207 node207Labels := by rfl

theorem canonical39995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39995 raw39995Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39995 raw39995Labels = mixedMoment B raw39995step0 raw39995step0Labels := by
      have hz : ∀ j, raw39995 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39995step0 = (fun i j => raw39995 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39995step0 raw39995; decide +kernel
      have hl : raw39995step0Labels = raw39995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39995 raw39995Labels permutation520 hz
    mixedMoment B raw39995step0 raw39995step0Labels = mixedMoment B raw39995step1 raw39995step1Labels := by
      have hz : ∀ j, raw39995step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39995step1 = (fun i j => raw39995step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39995step1 raw39995step0; decide +kernel
      have hl : raw39995step1Labels = raw39995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39995step0 raw39995step0Labels permutation104 hz
    mixedMoment B raw39995step1 raw39995step1Labels = mixedMoment B raw39995step2 raw39995step2Labels := by
      have ha : raw39995step2 = (fun i j => raw39995step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39995step2 raw39995step1; decide +kernel
      have hl : raw39995step2Labels = raw39995step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39995step1 raw39995step1Labels permutation13 permutation7
    mixedMoment B raw39995step2 raw39995step2Labels = mixedMoment B raw39995step3 raw39995step3Labels := by
      have ha : raw39995step3 = -raw39995step2 := by apply Matrix.ext; change ∀ i j, raw39995step3 i j = -(raw39995step2 i j); unfold raw39995step3 raw39995step2; decide +kernel
      have hl : raw39995step3Labels = raw39995step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node412 node412Labels := by rfl

theorem canonical39996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39996 raw39996Labels = mixedMoment B node286 node286Labels := by
  calc
    mixedMoment B raw39996 raw39996Labels = mixedMoment B raw39996step0 raw39996step0Labels := by
      have hz : ∀ j, raw39996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39996step0 = (fun i j => raw39996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39996step0 raw39996; decide +kernel
      have hl : raw39996step0Labels = raw39996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39996 raw39996Labels permutation434 hz
    mixedMoment B raw39996step0 raw39996step0Labels = mixedMoment B raw39996step1 raw39996step1Labels := by
      have ha : raw39996step1 = (fun i j => raw39996step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39996step1 raw39996step0; decide +kernel
      have hl : raw39996step1Labels = raw39996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39996step0 raw39996step0Labels permutation46 permutation7
    mixedMoment B raw39996step1 raw39996step1Labels = mixedMoment B raw39996step2 raw39996step2Labels := by
      have ha : raw39996step2 = -raw39996step1 := by apply Matrix.ext; change ∀ i j, raw39996step2 i j = -(raw39996step1 i j); unfold raw39996step2 raw39996step1; decide +kernel
      have hl : raw39996step2Labels = raw39996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node286 node286Labels := by rfl

theorem canonical39997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39997 raw39997Labels = mixedMoment B node353 node353Labels := by
  calc
    mixedMoment B raw39997 raw39997Labels = mixedMoment B raw39997step0 raw39997step0Labels := by
      have hz : ∀ j, raw39997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39997step0 = (fun i j => raw39997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39997step0 raw39997; decide +kernel
      have hl : raw39997step0Labels = raw39997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39997 raw39997Labels permutation434 hz
    mixedMoment B raw39997step0 raw39997step0Labels = mixedMoment B raw39997step1 raw39997step1Labels := by
      have ha : raw39997step1 = (fun i j => raw39997step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39997step1 raw39997step0; decide +kernel
      have hl : raw39997step1Labels = raw39997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39997step0 raw39997step0Labels permutation53 permutation7
    mixedMoment B raw39997step1 raw39997step1Labels = mixedMoment B raw39997step2 raw39997step2Labels := by
      have ha : raw39997step2 = -raw39997step1 := by apply Matrix.ext; change ∀ i j, raw39997step2 i j = -(raw39997step1 i j); unfold raw39997step2 raw39997step1; decide +kernel
      have hl : raw39997step2Labels = raw39997step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node353 node353Labels := by rfl

theorem canonical39998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39998 raw39998Labels = mixedMoment B node290 node290Labels := by
  calc
    mixedMoment B raw39998 raw39998Labels = mixedMoment B raw39998step0 raw39998step0Labels := by
      have hz : ∀ j, raw39998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39998step0 = (fun i j => raw39998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39998step0 raw39998; decide +kernel
      have hl : raw39998step0Labels = raw39998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39998 raw39998Labels permutation434 hz
    mixedMoment B raw39998step0 raw39998step0Labels = mixedMoment B raw39998step1 raw39998step1Labels := by
      have hz : ∀ j, raw39998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39998step1 = (fun i j => raw39998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39998step1 raw39998step0; decide +kernel
      have hl : raw39998step1Labels = raw39998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39998step0 raw39998step0Labels permutation80 hz
    mixedMoment B raw39998step1 raw39998step1Labels = mixedMoment B raw39998step2 raw39998step2Labels := by
      have ha : raw39998step2 = (fun i j => raw39998step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39998step2 raw39998step1; decide +kernel
      have hl : raw39998step2Labels = raw39998step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39998step1 raw39998step1Labels permutation29 permutation7
    _ = mixedMoment B node290 node290Labels := by rfl

theorem canonical39999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39999 raw39999Labels = mixedMoment B node355 node355Labels := by
  calc
    mixedMoment B raw39999 raw39999Labels = mixedMoment B raw39999step0 raw39999step0Labels := by
      have hz : ∀ j, raw39999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39999step0 = (fun i j => raw39999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39999step0 raw39999; decide +kernel
      have hl : raw39999step0Labels = raw39999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39999 raw39999Labels permutation434 hz
    mixedMoment B raw39999step0 raw39999step0Labels = mixedMoment B raw39999step1 raw39999step1Labels := by
      have hz : ∀ j, raw39999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39999step1 = (fun i j => raw39999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39999step1 raw39999step0; decide +kernel
      have hl : raw39999step1Labels = raw39999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39999step0 raw39999step0Labels permutation80 hz
    mixedMoment B raw39999step1 raw39999step1Labels = mixedMoment B raw39999step2 raw39999step2Labels := by
      have ha : raw39999step2 = (fun i j => raw39999step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39999step2 raw39999step1; decide +kernel
      have hl : raw39999step2Labels = raw39999step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39999step1 raw39999step1Labels permutation12 permutation7
    mixedMoment B raw39999step2 raw39999step2Labels = mixedMoment B raw39999step3 raw39999step3Labels := by
      have ha : raw39999step3 = -raw39999step2 := by apply Matrix.ext; change ∀ i j, raw39999step3 i j = -(raw39999step2 i j); unfold raw39999step3 raw39999step2; decide +kernel
      have hl : raw39999step3Labels = raw39999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node355 node355Labels := by rfl

theorem canonical40000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40000 raw40000Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw40000 raw40000Labels = mixedMoment B raw40000step0 raw40000step0Labels := by
      have hz : ∀ j, raw40000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40000step0 = (fun i j => raw40000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40000step0 raw40000; decide +kernel
      have hl : raw40000step0Labels = raw40000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40000 raw40000Labels permutation434 hz
    mixedMoment B raw40000step0 raw40000step0Labels = mixedMoment B raw40000step1 raw40000step1Labels := by
      have hz : ∀ j, raw40000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40000step1 = (fun i j => raw40000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40000step1 raw40000step0; decide +kernel
      have hl : raw40000step1Labels = raw40000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40000step0 raw40000step0Labels permutation80 hz
    mixedMoment B raw40000step1 raw40000step1Labels = mixedMoment B raw40000step2 raw40000step2Labels := by
      have ha : raw40000step2 = (fun i j => raw40000step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40000step2 raw40000step1; decide +kernel
      have hl : raw40000step2Labels = raw40000step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40000step1 raw40000step1Labels permutation13 permutation7
    mixedMoment B raw40000step2 raw40000step2Labels = mixedMoment B raw40000step3 raw40000step3Labels := by
      have ha : raw40000step3 = -raw40000step2 := by apply Matrix.ext; change ∀ i j, raw40000step3 i j = -(raw40000step2 i j); unfold raw40000step3 raw40000step2; decide +kernel
      have hl : raw40000step3Labels = raw40000step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical40001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40001 raw40001Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw40001 raw40001Labels = mixedMoment B raw40001step0 raw40001step0Labels := by
      have hz : ∀ j, raw40001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40001step0 = (fun i j => raw40001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40001step0 raw40001; decide +kernel
      have hl : raw40001step0Labels = raw40001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40001 raw40001Labels permutation346 hz
    mixedMoment B raw40001step0 raw40001step0Labels = mixedMoment B raw40001step1 raw40001step1Labels := by
      have ha : raw40001step1 = (fun i j => raw40001step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40001step1 raw40001step0; decide +kernel
      have hl : raw40001step1Labels = raw40001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40001step0 raw40001step0Labels permutation41 permutation7
    mixedMoment B raw40001step1 raw40001step1Labels = mixedMoment B raw40001step2 raw40001step2Labels := by
      have ha : raw40001step2 = -raw40001step1 := by apply Matrix.ext; change ∀ i j, raw40001step2 i j = -(raw40001step1 i j); unfold raw40001step2 raw40001step1; decide +kernel
      have hl : raw40001step2Labels = raw40001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node339 node339Labels := by rfl

theorem canonical40002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40002 raw40002Labels = mixedMoment B node351 node351Labels := by
  calc
    mixedMoment B raw40002 raw40002Labels = mixedMoment B raw40002step0 raw40002step0Labels := by
      have ha : raw40002step0 = (fun i j => raw40002 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40002step0 raw40002; decide +kernel
      have hl : raw40002step0Labels = raw40002Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40002 raw40002Labels permutation246 permutation7
    mixedMoment B raw40002step0 raw40002step0Labels = mixedMoment B raw40002step1 raw40002step1Labels := by
      have ha : raw40002step1 = -raw40002step0 := by apply Matrix.ext; change ∀ i j, raw40002step1 i j = -(raw40002step0 i j); unfold raw40002step1 raw40002step0; decide +kernel
      have hl : raw40002step1Labels = raw40002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node351 node351Labels := by rfl

theorem canonical40003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40003 raw40003Labels = mixedMoment B node352 node352Labels := by
  calc
    mixedMoment B raw40003 raw40003Labels = mixedMoment B raw40003step0 raw40003step0Labels := by
      have hz : ∀ j, raw40003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40003step0 = (fun i j => raw40003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40003step0 raw40003; decide +kernel
      have hl : raw40003step0Labels = raw40003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40003 raw40003Labels permutation434 hz
    mixedMoment B raw40003step0 raw40003step0Labels = mixedMoment B raw40003step1 raw40003step1Labels := by
      have ha : raw40003step1 = (fun i j => raw40003step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40003step1 raw40003step0; decide +kernel
      have hl : raw40003step1Labels = raw40003step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40003step0 raw40003step0Labels permutation50 permutation7
    mixedMoment B raw40003step1 raw40003step1Labels = mixedMoment B raw40003step2 raw40003step2Labels := by
      have ha : raw40003step2 = -raw40003step1 := by apply Matrix.ext; change ∀ i j, raw40003step2 i j = -(raw40003step1 i j); unfold raw40003step2 raw40003step1; decide +kernel
      have hl : raw40003step2Labels = raw40003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node352 node352Labels := by rfl

theorem canonical40004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40004 raw40004Labels = mixedMoment B node334 node334Labels := by
  calc
    mixedMoment B raw40004 raw40004Labels = mixedMoment B raw40004step0 raw40004step0Labels := by
      have ha : raw40004step0 = (fun i j => raw40004 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40004step0 raw40004; decide +kernel
      have hl : raw40004step0Labels = raw40004Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40004 raw40004Labels permutation200 permutation7
    mixedMoment B raw40004step0 raw40004step0Labels = mixedMoment B raw40004step1 raw40004step1Labels := by
      have ha : raw40004step1 = -raw40004step0 := by apply Matrix.ext; change ∀ i j, raw40004step1 i j = -(raw40004step0 i j); unfold raw40004step1 raw40004step0; decide +kernel
      have hl : raw40004step1Labels = raw40004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node334 node334Labels := by rfl

theorem canonical40005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40005 raw40005Labels = mixedMoment B node283 node283Labels := by
  calc
    mixedMoment B raw40005 raw40005Labels = mixedMoment B raw40005step0 raw40005step0Labels := by
      have ha : raw40005step0 = (fun i j => raw40005 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40005step0 raw40005; decide +kernel
      have hl : raw40005step0Labels = raw40005Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40005 raw40005Labels permutation201 permutation7
    mixedMoment B raw40005step0 raw40005step0Labels = mixedMoment B raw40005step1 raw40005step1Labels := by
      have ha : raw40005step1 = -raw40005step0 := by apply Matrix.ext; change ∀ i j, raw40005step1 i j = -(raw40005step0 i j); unfold raw40005step1 raw40005step0; decide +kernel
      have hl : raw40005step1Labels = raw40005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node283 node283Labels := by rfl

theorem canonical40006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40006 raw40006Labels = mixedMoment B node133 node133Labels := by
  calc
    mixedMoment B raw40006 raw40006Labels = mixedMoment B raw40006step0 raw40006step0Labels := by
      have hz : ∀ j, raw40006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40006step0 = (fun i j => raw40006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40006step0 raw40006; decide +kernel
      have hl : raw40006step0Labels = raw40006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40006 raw40006Labels permutation434 hz
    mixedMoment B raw40006step0 raw40006step0Labels = mixedMoment B raw40006step1 raw40006step1Labels := by
      have hz : ∀ j, raw40006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40006step1 = (fun i j => raw40006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40006step1 raw40006step0; decide +kernel
      have hl : raw40006step1Labels = raw40006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40006step0 raw40006step0Labels permutation80 hz
    mixedMoment B raw40006step1 raw40006step1Labels = mixedMoment B raw40006step2 raw40006step2Labels := by
      have ha : raw40006step2 = (fun i j => raw40006step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40006step2 raw40006step1; decide +kernel
      have hl : raw40006step2Labels = raw40006step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40006step1 raw40006step1Labels permutation29 permutation6
    _ = mixedMoment B node133 node133Labels := by rfl

theorem canonical40007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40007 raw40007Labels = mixedMoment B node336 node336Labels := by
  calc
    mixedMoment B raw40007 raw40007Labels = mixedMoment B raw40007step0 raw40007step0Labels := by
      have hz : ∀ j, raw40007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40007step0 = (fun i j => raw40007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40007step0 raw40007; decide +kernel
      have hl : raw40007step0Labels = raw40007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40007 raw40007Labels permutation346 hz
    mixedMoment B raw40007step0 raw40007step0Labels = mixedMoment B raw40007step1 raw40007step1Labels := by
      have ha : raw40007step1 = (fun i j => raw40007step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40007step1 raw40007step0; decide +kernel
      have hl : raw40007step1Labels = raw40007step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40007step0 raw40007step0Labels permutation39 permutation7
    mixedMoment B raw40007step1 raw40007step1Labels = mixedMoment B raw40007step2 raw40007step2Labels := by
      have ha : raw40007step2 = -raw40007step1 := by apply Matrix.ext; change ∀ i j, raw40007step2 i j = -(raw40007step1 i j); unfold raw40007step2 raw40007step1; decide +kernel
      have hl : raw40007step2Labels = raw40007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node336 node336Labels := by rfl

theorem canonical40008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40008 raw40008Labels = mixedMoment B node287 node287Labels := by
  calc
    mixedMoment B raw40008 raw40008Labels = mixedMoment B raw40008step0 raw40008step0Labels := by
      have hz : ∀ j, raw40008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40008step0 = (fun i j => raw40008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40008step0 raw40008; decide +kernel
      have hl : raw40008step0Labels = raw40008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40008 raw40008Labels permutation346 hz
    mixedMoment B raw40008step0 raw40008step0Labels = mixedMoment B raw40008step1 raw40008step1Labels := by
      have ha : raw40008step1 = (fun i j => raw40008step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40008step1 raw40008step0; decide +kernel
      have hl : raw40008step1Labels = raw40008step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40008step0 raw40008step0Labels permutation38 permutation7
    mixedMoment B raw40008step1 raw40008step1Labels = mixedMoment B raw40008step2 raw40008step2Labels := by
      have ha : raw40008step2 = -raw40008step1 := by apply Matrix.ext; change ∀ i j, raw40008step2 i j = -(raw40008step1 i j); unfold raw40008step2 raw40008step1; decide +kernel
      have hl : raw40008step2Labels = raw40008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node287 node287Labels := by rfl

theorem canonical40009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40009 raw40009Labels = mixedMoment B node40 node40Labels := by
  calc
    mixedMoment B raw40009 raw40009Labels = mixedMoment B raw40009step0 raw40009step0Labels := by
      have hz : ∀ j, raw40009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40009step0 = (fun i j => raw40009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40009step0 raw40009; decide +kernel
      have hl : raw40009step0Labels = raw40009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40009 raw40009Labels permutation434 hz
    mixedMoment B raw40009step0 raw40009step0Labels = mixedMoment B raw40009step1 raw40009step1Labels := by
      have hz : ∀ j, raw40009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40009step1 = (fun i j => raw40009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40009step1 raw40009step0; decide +kernel
      have hl : raw40009step1Labels = raw40009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40009step0 raw40009step0Labels permutation80 hz
    mixedMoment B raw40009step1 raw40009step1Labels = mixedMoment B raw40009step2 raw40009step2Labels := by
      have hz : ∀ j, raw40009step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40009step2 = (fun i j => raw40009step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40009step2 raw40009step1; decide +kernel
      have hl : raw40009step2Labels = raw40009step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40009step1 raw40009step1Labels permutation14 hz
    mixedMoment B raw40009step2 raw40009step2Labels = mixedMoment B raw40009step3 raw40009step3Labels := by
      have ha : raw40009step3 = (fun i j => raw40009step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40009step3 raw40009step2; decide +kernel
      have hl : raw40009step3Labels = raw40009step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40009step2 raw40009step2Labels permutation7 permutation6
    _ = mixedMoment B node40 node40Labels := by rfl

theorem canonical40010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40010 raw40010Labels = mixedMoment B node112 node112Labels := by
  calc
    mixedMoment B raw40010 raw40010Labels = mixedMoment B raw40010step0 raw40010step0Labels := by
      have hz : ∀ j, raw40010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40010step0 = (fun i j => raw40010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40010step0 raw40010; decide +kernel
      have hl : raw40010step0Labels = raw40010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40010 raw40010Labels permutation434 hz
    mixedMoment B raw40010step0 raw40010step0Labels = mixedMoment B raw40010step1 raw40010step1Labels := by
      have hz : ∀ j, raw40010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40010step1 = (fun i j => raw40010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40010step1 raw40010step0; decide +kernel
      have hl : raw40010step1Labels = raw40010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40010step0 raw40010step0Labels permutation80 hz
    mixedMoment B raw40010step1 raw40010step1Labels = mixedMoment B raw40010step2 raw40010step2Labels := by
      have hz : ∀ j, raw40010step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40010step2 = (fun i j => raw40010step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40010step2 raw40010step1; decide +kernel
      have hl : raw40010step2Labels = raw40010step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40010step1 raw40010step1Labels permutation14 hz
    mixedMoment B raw40010step2 raw40010step2Labels = mixedMoment B raw40010step3 raw40010step3Labels := by
      have ha : raw40010step3 = (fun i j => raw40010step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40010step3 raw40010step2; decide +kernel
      have hl : raw40010step3Labels = raw40010step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40010step2 raw40010step2Labels permutation5 permutation6
    _ = mixedMoment B node112 node112Labels := by rfl

theorem canonical40011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40011 raw40011Labels = mixedMoment B node407 node407Labels := by
  calc
    mixedMoment B raw40011 raw40011Labels = mixedMoment B raw40011step0 raw40011step0Labels := by
      have hz : ∀ j, raw40011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40011step0 = (fun i j => raw40011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40011step0 raw40011; decide +kernel
      have hl : raw40011step0Labels = raw40011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40011 raw40011Labels permutation434 hz
    mixedMoment B raw40011step0 raw40011step0Labels = mixedMoment B raw40011step1 raw40011step1Labels := by
      have hz : ∀ j, raw40011step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40011step1 = (fun i j => raw40011step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40011step1 raw40011step0; decide +kernel
      have hl : raw40011step1Labels = raw40011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40011step0 raw40011step0Labels permutation80 hz
    mixedMoment B raw40011step1 raw40011step1Labels = mixedMoment B raw40011step2 raw40011step2Labels := by
      have hz : ∀ j, raw40011step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40011step2 = (fun i j => raw40011step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40011step2 raw40011step1; decide +kernel
      have hl : raw40011step2Labels = raw40011step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40011step1 raw40011step1Labels permutation14 hz
    mixedMoment B raw40011step2 raw40011step2Labels = mixedMoment B raw40011step3 raw40011step3Labels := by
      have ha : raw40011step3 = (fun i j => raw40011step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40011step3 raw40011step2; decide +kernel
      have hl : raw40011step3Labels = raw40011step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40011step2 raw40011step2Labels permutation5 permutation6
    _ = mixedMoment B node407 node407Labels := by rfl

theorem canonical40012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40012 raw40012Labels = mixedMoment B node96 node96Labels := by
  calc
    mixedMoment B raw40012 raw40012Labels = mixedMoment B raw40012step0 raw40012step0Labels := by
      have hz : ∀ j, raw40012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40012step0 = (fun i j => raw40012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40012step0 raw40012; decide +kernel
      have hl : raw40012step0Labels = raw40012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40012 raw40012Labels permutation346 hz
    mixedMoment B raw40012step0 raw40012step0Labels = mixedMoment B raw40012step1 raw40012step1Labels := by
      have hz : ∀ j, raw40012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40012step1 = (fun i j => raw40012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40012step1 raw40012step0; decide +kernel
      have hl : raw40012step1Labels = raw40012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40012step0 raw40012step0Labels permutation56 hz
    mixedMoment B raw40012step1 raw40012step1Labels = mixedMoment B raw40012step2 raw40012step2Labels := by
      have ha : raw40012step2 = (fun i j => raw40012step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40012step2 raw40012step1; decide +kernel
      have hl : raw40012step2Labels = raw40012step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40012step1 raw40012step1Labels permutation25 permutation6
    _ = mixedMoment B node96 node96Labels := by rfl

theorem canonical40013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40013 raw40013Labels = mixedMoment B node341 node341Labels := by
  calc
    mixedMoment B raw40013 raw40013Labels = mixedMoment B raw40013step0 raw40013step0Labels := by
      have hz : ∀ j, raw40013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40013step0 = (fun i j => raw40013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40013step0 raw40013; decide +kernel
      have hl : raw40013step0Labels = raw40013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40013 raw40013Labels permutation346 hz
    mixedMoment B raw40013step0 raw40013step0Labels = mixedMoment B raw40013step1 raw40013step1Labels := by
      have hz : ∀ j, raw40013step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40013step1 = (fun i j => raw40013step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40013step1 raw40013step0; decide +kernel
      have hl : raw40013step1Labels = raw40013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40013step0 raw40013step0Labels permutation56 hz
    mixedMoment B raw40013step1 raw40013step1Labels = mixedMoment B raw40013step2 raw40013step2Labels := by
      have ha : raw40013step2 = (fun i j => raw40013step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40013step2 raw40013step1; decide +kernel
      have hl : raw40013step2Labels = raw40013step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40013step1 raw40013step1Labels permutation25 permutation6
    _ = mixedMoment B node341 node341Labels := by rfl

theorem canonical40014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40014 raw40014Labels = mixedMoment B node344 node344Labels := by
  calc
    mixedMoment B raw40014 raw40014Labels = mixedMoment B raw40014step0 raw40014step0Labels := by
      have hz : ∀ j, raw40014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40014step0 = (fun i j => raw40014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40014step0 raw40014; decide +kernel
      have hl : raw40014step0Labels = raw40014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40014 raw40014Labels permutation346 hz
    mixedMoment B raw40014step0 raw40014step0Labels = mixedMoment B raw40014step1 raw40014step1Labels := by
      have hz : ∀ j, raw40014step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40014step1 = (fun i j => raw40014step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40014step1 raw40014step0; decide +kernel
      have hl : raw40014step1Labels = raw40014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40014step0 raw40014step0Labels permutation56 hz
    mixedMoment B raw40014step1 raw40014step1Labels = mixedMoment B raw40014step2 raw40014step2Labels := by
      have ha : raw40014step2 = (fun i j => raw40014step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40014step2 raw40014step1; decide +kernel
      have hl : raw40014step2Labels = raw40014step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40014step1 raw40014step1Labels permutation8 permutation7
    mixedMoment B raw40014step2 raw40014step2Labels = mixedMoment B raw40014step3 raw40014step3Labels := by
      have ha : raw40014step3 = -raw40014step2 := by apply Matrix.ext; change ∀ i j, raw40014step3 i j = -(raw40014step2 i j); unfold raw40014step3 raw40014step2; decide +kernel
      have hl : raw40014step3Labels = raw40014step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node344 node344Labels := by rfl

theorem canonical40015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40015 raw40015Labels = mixedMoment B node72 node72Labels := by
  calc
    mixedMoment B raw40015 raw40015Labels = mixedMoment B raw40015step0 raw40015step0Labels := by
      have hz : ∀ j, raw40015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40015step0 = (fun i j => raw40015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40015step0 raw40015; decide +kernel
      have hl : raw40015step0Labels = raw40015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40015 raw40015Labels permutation346 hz
    mixedMoment B raw40015step0 raw40015step0Labels = mixedMoment B raw40015step1 raw40015step1Labels := by
      have hz : ∀ j, raw40015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40015step1 = (fun i j => raw40015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40015step1 raw40015step0; decide +kernel
      have hl : raw40015step1Labels = raw40015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40015step0 raw40015step0Labels permutation56 hz
    mixedMoment B raw40015step1 raw40015step1Labels = mixedMoment B raw40015step2 raw40015step2Labels := by
      have ha : raw40015step2 = (fun i j => raw40015step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40015step2 raw40015step1; decide +kernel
      have hl : raw40015step2Labels = raw40015step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40015step1 raw40015step1Labels permutation25 permutation6
    _ = mixedMoment B node72 node72Labels := by rfl

theorem canonical40016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40016 raw40016Labels = mixedMoment B node66 node66Labels := by
  calc
    mixedMoment B raw40016 raw40016Labels = mixedMoment B raw40016step0 raw40016step0Labels := by
      have hz : ∀ j, raw40016 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40016step0 = (fun i j => raw40016 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40016step0 raw40016; decide +kernel
      have hl : raw40016step0Labels = raw40016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40016 raw40016Labels permutation265 hz
    mixedMoment B raw40016step0 raw40016step0Labels = mixedMoment B raw40016step1 raw40016step1Labels := by
      have ha : raw40016step1 = (fun i j => raw40016step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40016step1 raw40016step0; decide +kernel
      have hl : raw40016step1Labels = raw40016step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40016step0 raw40016step0Labels permutation125 permutation6
    _ = mixedMoment B node66 node66Labels := by rfl

theorem canonical40017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40017 raw40017Labels = mixedMoment B node148 node148Labels := by
  calc
    mixedMoment B raw40017 raw40017Labels = mixedMoment B raw40017step0 raw40017step0Labels := by
      have hz : ∀ j, raw40017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40017step0 = (fun i j => raw40017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40017step0 raw40017; decide +kernel
      have hl : raw40017step0Labels = raw40017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40017 raw40017Labels permutation434 hz
    mixedMoment B raw40017step0 raw40017step0Labels = mixedMoment B raw40017step1 raw40017step1Labels := by
      have hz : ∀ j, raw40017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40017step1 = (fun i j => raw40017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40017step1 raw40017step0; decide +kernel
      have hl : raw40017step1Labels = raw40017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40017step0 raw40017step0Labels permutation80 hz
    mixedMoment B raw40017step1 raw40017step1Labels = mixedMoment B raw40017step2 raw40017step2Labels := by
      have ha : raw40017step2 = (fun i j => raw40017step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40017step2 raw40017step1; decide +kernel
      have hl : raw40017step2Labels = raw40017step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40017step1 raw40017step1Labels permutation11 permutation6
    mixedMoment B raw40017step2 raw40017step2Labels = mixedMoment B raw40017step3 raw40017step3Labels := by
      have ha : raw40017step3 = -raw40017step2 := by apply Matrix.ext; change ∀ i j, raw40017step3 i j = -(raw40017step2 i j); unfold raw40017step3 raw40017step2; decide +kernel
      have hl : raw40017step3Labels = raw40017step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node148 node148Labels := by rfl

theorem canonical40018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40018 raw40018Labels = mixedMoment B node145 node145Labels := by
  calc
    mixedMoment B raw40018 raw40018Labels = mixedMoment B raw40018step0 raw40018step0Labels := by
      have hz : ∀ j, raw40018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40018step0 = (fun i j => raw40018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40018step0 raw40018; decide +kernel
      have hl : raw40018step0Labels = raw40018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40018 raw40018Labels permutation434 hz
    mixedMoment B raw40018step0 raw40018step0Labels = mixedMoment B raw40018step1 raw40018step1Labels := by
      have ha : raw40018step1 = (fun i j => raw40018step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40018step1 raw40018step0; decide +kernel
      have hl : raw40018step1Labels = raw40018step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40018step0 raw40018step0Labels permutation46 permutation6
    mixedMoment B raw40018step1 raw40018step1Labels = mixedMoment B raw40018step2 raw40018step2Labels := by
      have ha : raw40018step2 = -raw40018step1 := by apply Matrix.ext; change ∀ i j, raw40018step2 i j = -(raw40018step1 i j); unfold raw40018step2 raw40018step1; decide +kernel
      have hl : raw40018step2Labels = raw40018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node145 node145Labels := by rfl

theorem canonical40019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40019 raw40019Labels = mixedMoment B node147 node147Labels := by
  calc
    mixedMoment B raw40019 raw40019Labels = mixedMoment B raw40019step0 raw40019step0Labels := by
      have hz : ∀ j, raw40019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40019step0 = (fun i j => raw40019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40019step0 raw40019; decide +kernel
      have hl : raw40019step0Labels = raw40019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40019 raw40019Labels permutation434 hz
    mixedMoment B raw40019step0 raw40019step0Labels = mixedMoment B raw40019step1 raw40019step1Labels := by
      have hz : ∀ j, raw40019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40019step1 = (fun i j => raw40019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40019step1 raw40019step0; decide +kernel
      have hl : raw40019step1Labels = raw40019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40019step0 raw40019step0Labels permutation80 hz
    mixedMoment B raw40019step1 raw40019step1Labels = mixedMoment B raw40019step2 raw40019step2Labels := by
      have ha : raw40019step2 = (fun i j => raw40019step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40019step2 raw40019step1; decide +kernel
      have hl : raw40019step2Labels = raw40019step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40019step1 raw40019step1Labels permutation10 permutation6
    mixedMoment B raw40019step2 raw40019step2Labels = mixedMoment B raw40019step3 raw40019step3Labels := by
      have ha : raw40019step3 = -raw40019step2 := by apply Matrix.ext; change ∀ i j, raw40019step3 i j = -(raw40019step2 i j); unfold raw40019step3 raw40019step2; decide +kernel
      have hl : raw40019step3Labels = raw40019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node147 node147Labels := by rfl

theorem canonical40020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40020 raw40020Labels = mixedMoment B node139 node139Labels := by
  calc
    mixedMoment B raw40020 raw40020Labels = mixedMoment B raw40020step0 raw40020step0Labels := by
      have hz : ∀ j, raw40020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40020step0 = (fun i j => raw40020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40020step0 raw40020; decide +kernel
      have hl : raw40020step0Labels = raw40020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40020 raw40020Labels permutation434 hz
    mixedMoment B raw40020step0 raw40020step0Labels = mixedMoment B raw40020step1 raw40020step1Labels := by
      have ha : raw40020step1 = (fun i j => raw40020step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40020step1 raw40020step0; decide +kernel
      have hl : raw40020step1Labels = raw40020step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40020step0 raw40020step0Labels permutation45 permutation6
    mixedMoment B raw40020step1 raw40020step1Labels = mixedMoment B raw40020step2 raw40020step2Labels := by
      have ha : raw40020step2 = -raw40020step1 := by apply Matrix.ext; change ∀ i j, raw40020step2 i j = -(raw40020step1 i j); unfold raw40020step2 raw40020step1; decide +kernel
      have hl : raw40020step2Labels = raw40020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node139 node139Labels := by rfl

theorem canonical40021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40021 raw40021Labels = mixedMoment B node140 node140Labels := by
  calc
    mixedMoment B raw40021 raw40021Labels = mixedMoment B raw40021step0 raw40021step0Labels := by
      have hz : ∀ j, raw40021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40021step0 = (fun i j => raw40021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40021step0 raw40021; decide +kernel
      have hl : raw40021step0Labels = raw40021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40021 raw40021Labels permutation434 hz
    mixedMoment B raw40021step0 raw40021step0Labels = mixedMoment B raw40021step1 raw40021step1Labels := by
      have hz : ∀ j, raw40021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40021step1 = (fun i j => raw40021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40021step1 raw40021step0; decide +kernel
      have hl : raw40021step1Labels = raw40021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40021step0 raw40021step0Labels permutation80 hz
    mixedMoment B raw40021step1 raw40021step1Labels = mixedMoment B raw40021step2 raw40021step2Labels := by
      have ha : raw40021step2 = (fun i j => raw40021step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40021step2 raw40021step1; decide +kernel
      have hl : raw40021step2Labels = raw40021step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40021step1 raw40021step1Labels permutation29 permutation6
    _ = mixedMoment B node140 node140Labels := by rfl

theorem canonical40022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40022 raw40022Labels = mixedMoment B node117 node117Labels := by
  calc
    mixedMoment B raw40022 raw40022Labels = mixedMoment B raw40022step0 raw40022step0Labels := by
      have hz : ∀ j, raw40022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40022step0 = (fun i j => raw40022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40022step0 raw40022; decide +kernel
      have hl : raw40022step0Labels = raw40022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40022 raw40022Labels permutation434 hz
    mixedMoment B raw40022step0 raw40022step0Labels = mixedMoment B raw40022step1 raw40022step1Labels := by
      have ha : raw40022step1 = (fun i j => raw40022step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40022step1 raw40022step0; decide +kernel
      have hl : raw40022step1Labels = raw40022step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40022step0 raw40022step0Labels permutation35 permutation7
    mixedMoment B raw40022step1 raw40022step1Labels = mixedMoment B raw40022step2 raw40022step2Labels := by
      have ha : raw40022step2 = -raw40022step1 := by apply Matrix.ext; change ∀ i j, raw40022step2 i j = -(raw40022step1 i j); unfold raw40022step2 raw40022step1; decide +kernel
      have hl : raw40022step2Labels = raw40022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node117 node117Labels := by rfl

theorem canonical40023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40023 raw40023Labels = mixedMoment B node114 node114Labels := by
  calc
    mixedMoment B raw40023 raw40023Labels = mixedMoment B raw40023step0 raw40023step0Labels := by
      have ha : raw40023step0 = (fun i j => raw40023 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40023step0 raw40023; decide +kernel
      have hl : raw40023step0Labels = raw40023Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40023 raw40023Labels permutation166 permutation7
    mixedMoment B raw40023step0 raw40023step0Labels = mixedMoment B raw40023step1 raw40023step1Labels := by
      have ha : raw40023step1 = -raw40023step0 := by apply Matrix.ext; change ∀ i j, raw40023step1 i j = -(raw40023step0 i j); unfold raw40023step1 raw40023step0; decide +kernel
      have hl : raw40023step1Labels = raw40023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node114 node114Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment544 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 544) =
      Integer.Sparse.eval keyMomentRow544 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 544).leftCharge (GramAssembly.key 544).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 224) := by
    have ha : gramCharges (GramAssembly.key 544).leftCharge (GramAssembly.key 544).rightCharge = raw39992 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39992Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39992 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 544).leftCharge (GramAssembly.key 544).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow544, Integer.Sparse.eval]

theorem keyMoment545 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 545) =
      Integer.Sparse.eval keyMomentRow545 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 545).leftCharge (GramAssembly.key 545).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 211) := by
    have ha : gramCharges (GramAssembly.key 545).leftCharge (GramAssembly.key 545).rightCharge = raw39993 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39993Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39993 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 545).leftCharge (GramAssembly.key 545).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow545, Integer.Sparse.eval]

theorem keyMoment546 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 546) =
      Integer.Sparse.eval keyMomentRow546 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 546).leftCharge (GramAssembly.key 546).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 207) := by
    have ha : gramCharges (GramAssembly.key 546).leftCharge (GramAssembly.key 546).rightCharge = raw39994 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39994Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39994 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 546).leftCharge (GramAssembly.key 546).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow546, Integer.Sparse.eval]

theorem keyMoment547 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 547) =
      Integer.Sparse.eval keyMomentRow547 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 547).leftCharge (GramAssembly.key 547).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 412) := by
    have ha : gramCharges (GramAssembly.key 547).leftCharge (GramAssembly.key 547).rightCharge = raw39995 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39995Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39995 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 547).leftCharge (GramAssembly.key 547).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow547, Integer.Sparse.eval]

theorem keyMoment548 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 548) =
      Integer.Sparse.eval keyMomentRow548 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 548).leftCharge (GramAssembly.key 548).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 286) := by
    have ha : gramCharges (GramAssembly.key 548).leftCharge (GramAssembly.key 548).rightCharge = raw39996 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39996Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39996 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 548).leftCharge (GramAssembly.key 548).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow548, Integer.Sparse.eval]

theorem keyMoment549 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 549) =
      Integer.Sparse.eval keyMomentRow549 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 549).leftCharge (GramAssembly.key 549).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 353) := by
    have ha : gramCharges (GramAssembly.key 549).leftCharge (GramAssembly.key 549).rightCharge = raw39997 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39997Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39997 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 549).leftCharge (GramAssembly.key 549).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow549, Integer.Sparse.eval]

theorem keyMoment550 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 550) =
      Integer.Sparse.eval keyMomentRow550 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 550).leftCharge (GramAssembly.key 550).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 290) := by
    have ha : gramCharges (GramAssembly.key 550).leftCharge (GramAssembly.key 550).rightCharge = raw39998 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39998Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39998 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 550).leftCharge (GramAssembly.key 550).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow550, Integer.Sparse.eval]

theorem keyMoment551 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 551) =
      Integer.Sparse.eval keyMomentRow551 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 551).leftCharge (GramAssembly.key 551).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 355) := by
    have ha : gramCharges (GramAssembly.key 551).leftCharge (GramAssembly.key 551).rightCharge = raw39999 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39999Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39999 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 551).leftCharge (GramAssembly.key 551).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow551, Integer.Sparse.eval]

theorem keyMoment552 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 552) =
      Integer.Sparse.eval keyMomentRow552 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 552).leftCharge (GramAssembly.key 552).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 552).leftCharge (GramAssembly.key 552).rightCharge = raw40000 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40000Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40000 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 552).leftCharge (GramAssembly.key 552).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow552, Integer.Sparse.eval]

theorem keyMoment553 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 553) =
      Integer.Sparse.eval keyMomentRow553 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 553).leftCharge (GramAssembly.key 553).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 553).leftCharge (GramAssembly.key 553).rightCharge = raw40001 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40001Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40001 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 553).leftCharge (GramAssembly.key 553).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow553, Integer.Sparse.eval]

theorem keyMoment554 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 554) =
      Integer.Sparse.eval keyMomentRow554 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 554).leftCharge (GramAssembly.key 554).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 351) := by
    have ha : gramCharges (GramAssembly.key 554).leftCharge (GramAssembly.key 554).rightCharge = raw40002 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40002Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40002 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 554).leftCharge (GramAssembly.key 554).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow554, Integer.Sparse.eval]

theorem keyMoment555 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 555) =
      Integer.Sparse.eval keyMomentRow555 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 555).leftCharge (GramAssembly.key 555).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 352) := by
    have ha : gramCharges (GramAssembly.key 555).leftCharge (GramAssembly.key 555).rightCharge = raw40003 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40003Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40003 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 555).leftCharge (GramAssembly.key 555).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow555, Integer.Sparse.eval]

theorem keyMoment556 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 556) =
      Integer.Sparse.eval keyMomentRow556 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 556).leftCharge (GramAssembly.key 556).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 334) := by
    have ha : gramCharges (GramAssembly.key 556).leftCharge (GramAssembly.key 556).rightCharge = raw40004 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40004Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40004 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 556).leftCharge (GramAssembly.key 556).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow556, Integer.Sparse.eval]

theorem keyMoment557 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 557) =
      Integer.Sparse.eval keyMomentRow557 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 557).leftCharge (GramAssembly.key 557).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 283) := by
    have ha : gramCharges (GramAssembly.key 557).leftCharge (GramAssembly.key 557).rightCharge = raw40005 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40005Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40005 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 557).leftCharge (GramAssembly.key 557).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow557, Integer.Sparse.eval]

theorem keyMoment558 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 558) =
      Integer.Sparse.eval keyMomentRow558 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 558).leftCharge (GramAssembly.key 558).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 133) := by
    have ha : gramCharges (GramAssembly.key 558).leftCharge (GramAssembly.key 558).rightCharge = raw40006 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40006Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40006 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 558).leftCharge (GramAssembly.key 558).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow558, Integer.Sparse.eval]

theorem keyMoment559 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 559) =
      Integer.Sparse.eval keyMomentRow559 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 559).leftCharge (GramAssembly.key 559).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 336) := by
    have ha : gramCharges (GramAssembly.key 559).leftCharge (GramAssembly.key 559).rightCharge = raw40007 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40007Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40007 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 559).leftCharge (GramAssembly.key 559).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow559, Integer.Sparse.eval]

theorem keyMoment560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 560) =
      Integer.Sparse.eval keyMomentRow560 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 560).leftCharge (GramAssembly.key 560).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 287) := by
    have ha : gramCharges (GramAssembly.key 560).leftCharge (GramAssembly.key 560).rightCharge = raw40008 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40008Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40008 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 560).leftCharge (GramAssembly.key 560).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow560, Integer.Sparse.eval]

theorem keyMoment561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 561) =
      Integer.Sparse.eval keyMomentRow561 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 561).leftCharge (GramAssembly.key 561).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 40) := by
    have ha : gramCharges (GramAssembly.key 561).leftCharge (GramAssembly.key 561).rightCharge = raw40009 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40009Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40009 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 561).leftCharge (GramAssembly.key 561).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow561, Integer.Sparse.eval]

theorem keyMoment562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 562) =
      Integer.Sparse.eval keyMomentRow562 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 562).leftCharge (GramAssembly.key 562).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 112) := by
    have ha : gramCharges (GramAssembly.key 562).leftCharge (GramAssembly.key 562).rightCharge = raw40010 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40010Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40010 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 562).leftCharge (GramAssembly.key 562).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow562, Integer.Sparse.eval]

theorem keyMoment563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 563) =
      Integer.Sparse.eval keyMomentRow563 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 563).leftCharge (GramAssembly.key 563).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 407) := by
    have ha : gramCharges (GramAssembly.key 563).leftCharge (GramAssembly.key 563).rightCharge = raw40011 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40011Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40011 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 563).leftCharge (GramAssembly.key 563).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow563, Integer.Sparse.eval]

theorem keyMoment564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 564) =
      Integer.Sparse.eval keyMomentRow564 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 564).leftCharge (GramAssembly.key 564).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 96) := by
    have ha : gramCharges (GramAssembly.key 564).leftCharge (GramAssembly.key 564).rightCharge = raw40012 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40012Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40012 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 564).leftCharge (GramAssembly.key 564).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow564, Integer.Sparse.eval]

theorem keyMoment565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 565) =
      Integer.Sparse.eval keyMomentRow565 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 565).leftCharge (GramAssembly.key 565).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 341) := by
    have ha : gramCharges (GramAssembly.key 565).leftCharge (GramAssembly.key 565).rightCharge = raw40013 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40013Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40013 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 565).leftCharge (GramAssembly.key 565).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow565, Integer.Sparse.eval]

theorem keyMoment566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 566) =
      Integer.Sparse.eval keyMomentRow566 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 566).leftCharge (GramAssembly.key 566).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 344) := by
    have ha : gramCharges (GramAssembly.key 566).leftCharge (GramAssembly.key 566).rightCharge = raw40014 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40014Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40014 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 566).leftCharge (GramAssembly.key 566).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow566, Integer.Sparse.eval]

theorem keyMoment567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 567) =
      Integer.Sparse.eval keyMomentRow567 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 567).leftCharge (GramAssembly.key 567).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 72) := by
    have ha : gramCharges (GramAssembly.key 567).leftCharge (GramAssembly.key 567).rightCharge = raw40015 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40015Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40015 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 567).leftCharge (GramAssembly.key 567).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow567, Integer.Sparse.eval]

theorem keyMoment568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 568) =
      Integer.Sparse.eval keyMomentRow568 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 568).leftCharge (GramAssembly.key 568).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 66) := by
    have ha : gramCharges (GramAssembly.key 568).leftCharge (GramAssembly.key 568).rightCharge = raw40016 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40016Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40016 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 568).leftCharge (GramAssembly.key 568).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow568, Integer.Sparse.eval]

theorem keyMoment569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 569) =
      Integer.Sparse.eval keyMomentRow569 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 569).leftCharge (GramAssembly.key 569).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 148) := by
    have ha : gramCharges (GramAssembly.key 569).leftCharge (GramAssembly.key 569).rightCharge = raw40017 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40017Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40017 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 569).leftCharge (GramAssembly.key 569).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow569, Integer.Sparse.eval]

theorem keyMoment570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 570) =
      Integer.Sparse.eval keyMomentRow570 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 570).leftCharge (GramAssembly.key 570).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 145) := by
    have ha : gramCharges (GramAssembly.key 570).leftCharge (GramAssembly.key 570).rightCharge = raw40018 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40018Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40018 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 570).leftCharge (GramAssembly.key 570).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow570, Integer.Sparse.eval]

theorem keyMoment571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 571) =
      Integer.Sparse.eval keyMomentRow571 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 571).leftCharge (GramAssembly.key 571).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 147) := by
    have ha : gramCharges (GramAssembly.key 571).leftCharge (GramAssembly.key 571).rightCharge = raw40019 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40019Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40019 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 571).leftCharge (GramAssembly.key 571).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow571, Integer.Sparse.eval]

theorem keyMoment572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 572) =
      Integer.Sparse.eval keyMomentRow572 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 572).leftCharge (GramAssembly.key 572).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 139) := by
    have ha : gramCharges (GramAssembly.key 572).leftCharge (GramAssembly.key 572).rightCharge = raw40020 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40020Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40020 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 572).leftCharge (GramAssembly.key 572).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow572, Integer.Sparse.eval]

theorem keyMoment573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 573) =
      Integer.Sparse.eval keyMomentRow573 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 573).leftCharge (GramAssembly.key 573).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 140) := by
    have ha : gramCharges (GramAssembly.key 573).leftCharge (GramAssembly.key 573).rightCharge = raw40021 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40021Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40021 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 573).leftCharge (GramAssembly.key 573).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow573, Integer.Sparse.eval]

theorem keyMoment574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 574) =
      Integer.Sparse.eval keyMomentRow574 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 574).leftCharge (GramAssembly.key 574).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 117) := by
    have ha : gramCharges (GramAssembly.key 574).leftCharge (GramAssembly.key 574).rightCharge = raw40022 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40022Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40022 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 574).leftCharge (GramAssembly.key 574).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow574, Integer.Sparse.eval]

theorem keyMoment575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 575) =
      Integer.Sparse.eval keyMomentRow575 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 575).leftCharge (GramAssembly.key 575).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 114) := by
    have ha : gramCharges (GramAssembly.key 575).leftCharge (GramAssembly.key 575).rightCharge = raw40023 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40023Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40023 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 575).leftCharge (GramAssembly.key 575).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow575, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt544 : keyMomentRows (544 : Fin 2886) =
    keyMomentRow544 := by decide +kernel

theorem keyMomentRowsAt545 : keyMomentRows (545 : Fin 2886) =
    keyMomentRow545 := by decide +kernel

theorem keyMomentRowsAt546 : keyMomentRows (546 : Fin 2886) =
    keyMomentRow546 := by decide +kernel

theorem keyMomentRowsAt547 : keyMomentRows (547 : Fin 2886) =
    keyMomentRow547 := by decide +kernel

theorem keyMomentRowsAt548 : keyMomentRows (548 : Fin 2886) =
    keyMomentRow548 := by decide +kernel

theorem keyMomentRowsAt549 : keyMomentRows (549 : Fin 2886) =
    keyMomentRow549 := by decide +kernel

theorem keyMomentRowsAt550 : keyMomentRows (550 : Fin 2886) =
    keyMomentRow550 := by decide +kernel

theorem keyMomentRowsAt551 : keyMomentRows (551 : Fin 2886) =
    keyMomentRow551 := by decide +kernel

theorem keyMomentRowsAt552 : keyMomentRows (552 : Fin 2886) =
    keyMomentRow552 := by decide +kernel

theorem keyMomentRowsAt553 : keyMomentRows (553 : Fin 2886) =
    keyMomentRow553 := by decide +kernel

theorem keyMomentRowsAt554 : keyMomentRows (554 : Fin 2886) =
    keyMomentRow554 := by decide +kernel

theorem keyMomentRowsAt555 : keyMomentRows (555 : Fin 2886) =
    keyMomentRow555 := by decide +kernel

theorem keyMomentRowsAt556 : keyMomentRows (556 : Fin 2886) =
    keyMomentRow556 := by decide +kernel

theorem keyMomentRowsAt557 : keyMomentRows (557 : Fin 2886) =
    keyMomentRow557 := by decide +kernel

theorem keyMomentRowsAt558 : keyMomentRows (558 : Fin 2886) =
    keyMomentRow558 := by decide +kernel

theorem keyMomentRowsAt559 : keyMomentRows (559 : Fin 2886) =
    keyMomentRow559 := by decide +kernel

theorem keyMomentRowsAt560 : keyMomentRows (560 : Fin 2886) =
    keyMomentRow560 := by decide +kernel

theorem keyMomentRowsAt561 : keyMomentRows (561 : Fin 2886) =
    keyMomentRow561 := by decide +kernel

theorem keyMomentRowsAt562 : keyMomentRows (562 : Fin 2886) =
    keyMomentRow562 := by decide +kernel

theorem keyMomentRowsAt563 : keyMomentRows (563 : Fin 2886) =
    keyMomentRow563 := by decide +kernel

theorem keyMomentRowsAt564 : keyMomentRows (564 : Fin 2886) =
    keyMomentRow564 := by decide +kernel

theorem keyMomentRowsAt565 : keyMomentRows (565 : Fin 2886) =
    keyMomentRow565 := by decide +kernel

theorem keyMomentRowsAt566 : keyMomentRows (566 : Fin 2886) =
    keyMomentRow566 := by decide +kernel

theorem keyMomentRowsAt567 : keyMomentRows (567 : Fin 2886) =
    keyMomentRow567 := by decide +kernel

theorem keyMomentRowsAt568 : keyMomentRows (568 : Fin 2886) =
    keyMomentRow568 := by decide +kernel

theorem keyMomentRowsAt569 : keyMomentRows (569 : Fin 2886) =
    keyMomentRow569 := by decide +kernel

theorem keyMomentRowsAt570 : keyMomentRows (570 : Fin 2886) =
    keyMomentRow570 := by decide +kernel

theorem keyMomentRowsAt571 : keyMomentRows (571 : Fin 2886) =
    keyMomentRow571 := by decide +kernel

theorem keyMomentRowsAt572 : keyMomentRows (572 : Fin 2886) =
    keyMomentRow572 := by decide +kernel

theorem keyMomentRowsAt573 : keyMomentRows (573 : Fin 2886) =
    keyMomentRow573 := by decide +kernel

theorem keyMomentRowsAt574 : keyMomentRows (574 : Fin 2886) =
    keyMomentRow574 := by decide +kernel

theorem keyMomentRowsAt575 : keyMomentRows (575 : Fin 2886) =
    keyMomentRow575 := by decide +kernel

theorem keyMomentChunkSound17_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 17) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 544 ∨ k.val = 545 ∨ k.val = 546 ∨ k.val = 547 ∨ k.val = 548 ∨ k.val = 549 ∨ k.val = 550 ∨ k.val = 551 ∨ k.val = 552 ∨ k.val = 553 ∨ k.val = 554 ∨ k.val = 555 ∨ k.val = 556 ∨ k.val = 557 ∨ k.val = 558 ∨ k.val = 559 ∨ k.val = 560 ∨ k.val = 561 ∨ k.val = 562 ∨ k.val = 563 ∨ k.val = 564 ∨ k.val = 565 ∨ k.val = 566 ∨ k.val = 567 ∨ k.val = 568 ∨ k.val = 569 ∨ k.val = 570 ∨ k.val = 571 ∨ k.val = 572 ∨ k.val = 573 ∨ k.val = 574 ∨ k.val = 575 := by omega
  rcases heq with h544 | h545 | h546 | h547 | h548 | h549 | h550 | h551 | h552 | h553 | h554 | h555 | h556 | h557 | h558 | h559 | h560 | h561 | h562 | h563 | h564 | h565 | h566 | h567 | h568 | h569 | h570 | h571 | h572 | h573 | h574 | h575
  · have he : k = (544 : Fin 2886) := Fin.ext h544
    subst k
    rw [keyMomentRowsAt544]
    exact keyMoment544 B hB
  · have he : k = (545 : Fin 2886) := Fin.ext h545
    subst k
    rw [keyMomentRowsAt545]
    exact keyMoment545 B hB
  · have he : k = (546 : Fin 2886) := Fin.ext h546
    subst k
    rw [keyMomentRowsAt546]
    exact keyMoment546 B hB
  · have he : k = (547 : Fin 2886) := Fin.ext h547
    subst k
    rw [keyMomentRowsAt547]
    exact keyMoment547 B hB
  · have he : k = (548 : Fin 2886) := Fin.ext h548
    subst k
    rw [keyMomentRowsAt548]
    exact keyMoment548 B hB
  · have he : k = (549 : Fin 2886) := Fin.ext h549
    subst k
    rw [keyMomentRowsAt549]
    exact keyMoment549 B hB
  · have he : k = (550 : Fin 2886) := Fin.ext h550
    subst k
    rw [keyMomentRowsAt550]
    exact keyMoment550 B hB
  · have he : k = (551 : Fin 2886) := Fin.ext h551
    subst k
    rw [keyMomentRowsAt551]
    exact keyMoment551 B hB
  · have he : k = (552 : Fin 2886) := Fin.ext h552
    subst k
    rw [keyMomentRowsAt552]
    exact keyMoment552 B hB
  · have he : k = (553 : Fin 2886) := Fin.ext h553
    subst k
    rw [keyMomentRowsAt553]
    exact keyMoment553 B hB
  · have he : k = (554 : Fin 2886) := Fin.ext h554
    subst k
    rw [keyMomentRowsAt554]
    exact keyMoment554 B hB
  · have he : k = (555 : Fin 2886) := Fin.ext h555
    subst k
    rw [keyMomentRowsAt555]
    exact keyMoment555 B hB
  · have he : k = (556 : Fin 2886) := Fin.ext h556
    subst k
    rw [keyMomentRowsAt556]
    exact keyMoment556 B hB
  · have he : k = (557 : Fin 2886) := Fin.ext h557
    subst k
    rw [keyMomentRowsAt557]
    exact keyMoment557 B hB
  · have he : k = (558 : Fin 2886) := Fin.ext h558
    subst k
    rw [keyMomentRowsAt558]
    exact keyMoment558 B hB
  · have he : k = (559 : Fin 2886) := Fin.ext h559
    subst k
    rw [keyMomentRowsAt559]
    exact keyMoment559 B hB
  · have he : k = (560 : Fin 2886) := Fin.ext h560
    subst k
    rw [keyMomentRowsAt560]
    exact keyMoment560 B hB
  · have he : k = (561 : Fin 2886) := Fin.ext h561
    subst k
    rw [keyMomentRowsAt561]
    exact keyMoment561 B hB
  · have he : k = (562 : Fin 2886) := Fin.ext h562
    subst k
    rw [keyMomentRowsAt562]
    exact keyMoment562 B hB
  · have he : k = (563 : Fin 2886) := Fin.ext h563
    subst k
    rw [keyMomentRowsAt563]
    exact keyMoment563 B hB
  · have he : k = (564 : Fin 2886) := Fin.ext h564
    subst k
    rw [keyMomentRowsAt564]
    exact keyMoment564 B hB
  · have he : k = (565 : Fin 2886) := Fin.ext h565
    subst k
    rw [keyMomentRowsAt565]
    exact keyMoment565 B hB
  · have he : k = (566 : Fin 2886) := Fin.ext h566
    subst k
    rw [keyMomentRowsAt566]
    exact keyMoment566 B hB
  · have he : k = (567 : Fin 2886) := Fin.ext h567
    subst k
    rw [keyMomentRowsAt567]
    exact keyMoment567 B hB
  · have he : k = (568 : Fin 2886) := Fin.ext h568
    subst k
    rw [keyMomentRowsAt568]
    exact keyMoment568 B hB
  · have he : k = (569 : Fin 2886) := Fin.ext h569
    subst k
    rw [keyMomentRowsAt569]
    exact keyMoment569 B hB
  · have he : k = (570 : Fin 2886) := Fin.ext h570
    subst k
    rw [keyMomentRowsAt570]
    exact keyMoment570 B hB
  · have he : k = (571 : Fin 2886) := Fin.ext h571
    subst k
    rw [keyMomentRowsAt571]
    exact keyMoment571 B hB
  · have he : k = (572 : Fin 2886) := Fin.ext h572
    subst k
    rw [keyMomentRowsAt572]
    exact keyMoment572 B hB
  · have he : k = (573 : Fin 2886) := Fin.ext h573
    subst k
    rw [keyMomentRowsAt573]
    exact keyMoment573 B hB
  · have he : k = (574 : Fin 2886) := Fin.ext h574
    subst k
    rw [keyMomentRowsAt574]
    exact keyMoment574 B hB
  · have he : k = (575 : Fin 2886) := Fin.ext h575
    subst k
    rw [keyMomentRowsAt575]
    exact keyMoment575 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound17_e_oai
