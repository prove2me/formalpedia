-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:07:08.088004+00:00
-- url     : https://prove2.me/submissions/61181e8b-9b4a-4ab8-acf3-ed29f6ea954e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical310
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39738 raw39738Labels = mixedMoment B node330 node330Labels := by
  calc
    mixedMoment B raw39738 raw39738Labels = mixedMoment B raw39738step0 raw39738step0Labels := by
      have ha : raw39738step0 = (fun i j => raw39738 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39738step0 raw39738; decide +kernel
      have hl : raw39738step0Labels = raw39738Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39738 raw39738Labels permutation484 permutation6
    _ = mixedMoment B node330 node330Labels := by rfl

theorem canonical39739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39739 raw39739Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw39739 raw39739Labels = mixedMoment B raw39739step0 raw39739step0Labels := by
      have ha : raw39739step0 = (fun i j => raw39739 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39739step0 raw39739; decide +kernel
      have hl : raw39739step0Labels = raw39739Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39739 raw39739Labels permutation499 permutation6
    _ = mixedMoment B node394 node394Labels := by rfl

theorem canonical39740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39740 raw39740Labels = mixedMoment B node491 node491Labels := by
  calc
    mixedMoment B raw39740 raw39740Labels = mixedMoment B raw39740step0 raw39740step0Labels := by
      have hz : ∀ j, raw39740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39740step0 = (fun i j => raw39740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39740step0 raw39740; decide +kernel
      have hl : raw39740step0Labels = raw39740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39740 raw39740Labels permutation434 hz
    mixedMoment B raw39740step0 raw39740step0Labels = mixedMoment B raw39740step1 raw39740step1Labels := by
      have ha : raw39740step1 = (fun i j => raw39740step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39740step1 raw39740step0; decide +kernel
      have hl : raw39740step1Labels = raw39740step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39740step0 raw39740step0Labels permutation151 permutation3
    mixedMoment B raw39740step1 raw39740step1Labels = mixedMoment B raw39740step2 raw39740step2Labels := by
      have ha : raw39740step2 = -raw39740step1 := by apply Matrix.ext; change ∀ i j, raw39740step2 i j = -(raw39740step1 i j); unfold raw39740step2 raw39740step1; decide +kernel
      have hl : raw39740step2Labels = raw39740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node491 node491Labels := by rfl

theorem canonical39741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39741 raw39741Labels = mixedMoment B node447 node447Labels := by
  calc
    mixedMoment B raw39741 raw39741Labels = mixedMoment B raw39741step0 raw39741step0Labels := by
      have hz : ∀ j, raw39741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39741step0 = (fun i j => raw39741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39741step0 raw39741; decide +kernel
      have hl : raw39741step0Labels = raw39741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39741 raw39741Labels permutation434 hz
    mixedMoment B raw39741step0 raw39741step0Labels = mixedMoment B raw39741step1 raw39741step1Labels := by
      have ha : raw39741step1 = (fun i j => raw39741step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39741step1 raw39741step0; decide +kernel
      have hl : raw39741step1Labels = raw39741step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39741step0 raw39741step0Labels permutation99 permutation6
    _ = mixedMoment B node447 node447Labels := by rfl

theorem canonical39742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39742 raw39742Labels = mixedMoment B node470 node470Labels := by
  calc
    mixedMoment B raw39742 raw39742Labels = mixedMoment B raw39742step0 raw39742step0Labels := by
      have ha : raw39742step0 = (fun i j => raw39742 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39742step0 raw39742; decide +kernel
      have hl : raw39742step0Labels = raw39742Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39742 raw39742Labels permutation390 permutation6
    _ = mixedMoment B node470 node470Labels := by rfl

theorem canonical39743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39743 raw39743Labels = mixedMoment B node484 node484Labels := by
  calc
    mixedMoment B raw39743 raw39743Labels = mixedMoment B raw39743step0 raw39743step0Labels := by
      have ha : raw39743step0 = (fun i j => raw39743 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39743step0 raw39743; decide +kernel
      have hl : raw39743step0Labels = raw39743Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39743 raw39743Labels permutation393 permutation6
    _ = mixedMoment B node484 node484Labels := by rfl

theorem canonical39744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39744 raw39744Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw39744 raw39744Labels = mixedMoment B raw39744step0 raw39744step0Labels := by
      have hz : ∀ j, raw39744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39744step0 = (fun i j => raw39744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39744step0 raw39744; decide +kernel
      have hl : raw39744step0Labels = raw39744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39744 raw39744Labels permutation434 hz
    mixedMoment B raw39744step0 raw39744step0Labels = mixedMoment B raw39744step1 raw39744step1Labels := by
      have ha : raw39744step1 = (fun i j => raw39744step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39744step1 raw39744step0; decide +kernel
      have hl : raw39744step1Labels = raw39744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39744step0 raw39744step0Labels permutation151 permutation2
    mixedMoment B raw39744step1 raw39744step1Labels = mixedMoment B raw39744step2 raw39744step2Labels := by
      have ha : raw39744step2 = -raw39744step1 := by apply Matrix.ext; change ∀ i j, raw39744step2 i j = -(raw39744step1 i j); unfold raw39744step2 raw39744step1; decide +kernel
      have hl : raw39744step2Labels = raw39744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

theorem canonical39745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39745 raw39745Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39745 raw39745Labels = mixedMoment B raw39745step0 raw39745step0Labels := by
      have hz : ∀ j, raw39745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39745step0 = (fun i j => raw39745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39745step0 raw39745; decide +kernel
      have hl : raw39745step0Labels = raw39745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39745 raw39745Labels permutation434 hz
    mixedMoment B raw39745step0 raw39745step0Labels = mixedMoment B raw39745step1 raw39745step1Labels := by
      have hz : ∀ j, raw39745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39745step1 = (fun i j => raw39745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39745step1 raw39745step0; decide +kernel
      have hl : raw39745step1Labels = raw39745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39745step0 raw39745step0Labels permutation80 hz
    mixedMoment B raw39745step1 raw39745step1Labels = mixedMoment B raw39745step2 raw39745step2Labels := by
      have ha : raw39745step2 = (fun i j => raw39745step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39745step2 raw39745step1; decide +kernel
      have hl : raw39745step2Labels = raw39745step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39745step1 raw39745step1Labels permutation24 permutation6
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39746 raw39746Labels = mixedMoment B node390 node390Labels := by
  calc
    mixedMoment B raw39746 raw39746Labels = mixedMoment B raw39746step0 raw39746step0Labels := by
      have hz : ∀ j, raw39746 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39746step0 = (fun i j => raw39746 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39746step0 raw39746; decide +kernel
      have hl : raw39746step0Labels = raw39746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39746 raw39746Labels permutation434 hz
    mixedMoment B raw39746step0 raw39746step0Labels = mixedMoment B raw39746step1 raw39746step1Labels := by
      have hz : ∀ j, raw39746step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39746step1 = (fun i j => raw39746step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39746step1 raw39746step0; decide +kernel
      have hl : raw39746step1Labels = raw39746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39746step0 raw39746step0Labels permutation80 hz
    mixedMoment B raw39746step1 raw39746step1Labels = mixedMoment B raw39746step2 raw39746step2Labels := by
      have ha : raw39746step2 = (fun i j => raw39746step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39746step2 raw39746step1; decide +kernel
      have hl : raw39746step2Labels = raw39746step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39746step1 raw39746step1Labels permutation30 permutation7
    _ = mixedMoment B node390 node390Labels := by rfl

theorem canonical39747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39747 raw39747Labels = mixedMoment B node153 node153Labels := by
  calc
    mixedMoment B raw39747 raw39747Labels = mixedMoment B raw39747step0 raw39747step0Labels := by
      have hz : ∀ j, raw39747 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39747step0 = (fun i j => raw39747 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39747step0 raw39747; decide +kernel
      have hl : raw39747step0Labels = raw39747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39747 raw39747Labels permutation434 hz
    mixedMoment B raw39747step0 raw39747step0Labels = mixedMoment B raw39747step1 raw39747step1Labels := by
      have hz : ∀ j, raw39747step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39747step1 = (fun i j => raw39747step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39747step1 raw39747step0; decide +kernel
      have hl : raw39747step1Labels = raw39747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39747step0 raw39747step0Labels permutation80 hz
    mixedMoment B raw39747step1 raw39747step1Labels = mixedMoment B raw39747step2 raw39747step2Labels := by
      have ha : raw39747step2 = (fun i j => raw39747step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39747step2 raw39747step1; decide +kernel
      have hl : raw39747step2Labels = raw39747step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39747step1 raw39747step1Labels permutation27 permutation6
    _ = mixedMoment B node153 node153Labels := by rfl

theorem canonical39748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39748 raw39748Labels = mixedMoment B node333 node333Labels := by
  calc
    mixedMoment B raw39748 raw39748Labels = mixedMoment B raw39748step0 raw39748step0Labels := by
      have hz : ∀ j, raw39748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39748step0 = (fun i j => raw39748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39748step0 raw39748; decide +kernel
      have hl : raw39748step0Labels = raw39748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39748 raw39748Labels permutation346 hz
    mixedMoment B raw39748step0 raw39748step0Labels = mixedMoment B raw39748step1 raw39748step1Labels := by
      have ha : raw39748step1 = (fun i j => raw39748step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39748step1 raw39748step0; decide +kernel
      have hl : raw39748step1Labels = raw39748step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39748step0 raw39748step0Labels permutation93 permutation6
    _ = mixedMoment B node333 node333Labels := by rfl

theorem canonical39749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39749 raw39749Labels = mixedMoment B node395 node395Labels := by
  calc
    mixedMoment B raw39749 raw39749Labels = mixedMoment B raw39749step0 raw39749step0Labels := by
      have hz : ∀ j, raw39749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39749step0 = (fun i j => raw39749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39749step0 raw39749; decide +kernel
      have hl : raw39749step0Labels = raw39749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39749 raw39749Labels permutation346 hz
    mixedMoment B raw39749step0 raw39749step0Labels = mixedMoment B raw39749step1 raw39749step1Labels := by
      have ha : raw39749step1 = (fun i j => raw39749step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39749step1 raw39749step0; decide +kernel
      have hl : raw39749step1Labels = raw39749step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39749step0 raw39749step0Labels permutation96 permutation6
    _ = mixedMoment B node395 node395Labels := by rfl

theorem canonical39750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39750 raw39750Labels = mixedMoment B node346 node346Labels := by
  calc
    mixedMoment B raw39750 raw39750Labels = mixedMoment B raw39750step0 raw39750step0Labels := by
      have hz : ∀ j, raw39750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39750step0 = (fun i j => raw39750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39750step0 raw39750; decide +kernel
      have hl : raw39750step0Labels = raw39750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39750 raw39750Labels permutation434 hz
    mixedMoment B raw39750step0 raw39750step0Labels = mixedMoment B raw39750step1 raw39750step1Labels := by
      have ha : raw39750step1 = (fun i j => raw39750step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39750step1 raw39750step0; decide +kernel
      have hl : raw39750step1Labels = raw39750step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39750step0 raw39750step0Labels permutation59 permutation6
    mixedMoment B raw39750step1 raw39750step1Labels = mixedMoment B raw39750step2 raw39750step2Labels := by
      have ha : raw39750step2 = -raw39750step1 := by apply Matrix.ext; change ∀ i j, raw39750step2 i j = -(raw39750step1 i j); unfold raw39750step2 raw39750step1; decide +kernel
      have hl : raw39750step2Labels = raw39750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node346 node346Labels := by rfl

theorem canonical39751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39751 raw39751Labels = mixedMoment B node147 node147Labels := by
  calc
    mixedMoment B raw39751 raw39751Labels = mixedMoment B raw39751step0 raw39751step0Labels := by
      have hz : ∀ j, raw39751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39751step0 = (fun i j => raw39751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39751step0 raw39751; decide +kernel
      have hl : raw39751step0Labels = raw39751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39751 raw39751Labels permutation434 hz
    mixedMoment B raw39751step0 raw39751step0Labels = mixedMoment B raw39751step1 raw39751step1Labels := by
      have hz : ∀ j, raw39751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39751step1 = (fun i j => raw39751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39751step1 raw39751step0; decide +kernel
      have hl : raw39751step1Labels = raw39751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39751step0 raw39751step0Labels permutation80 hz
    mixedMoment B raw39751step1 raw39751step1Labels = mixedMoment B raw39751step2 raw39751step2Labels := by
      have ha : raw39751step2 = (fun i j => raw39751step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39751step2 raw39751step1; decide +kernel
      have hl : raw39751step2Labels = raw39751step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39751step1 raw39751step1Labels permutation30 permutation7
    _ = mixedMoment B node147 node147Labels := by rfl

theorem canonical39752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39752 raw39752Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39752 raw39752Labels = mixedMoment B raw39752step0 raw39752step0Labels := by
      have hz : ∀ j, raw39752 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39752step0 = (fun i j => raw39752 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39752step0 raw39752; decide +kernel
      have hl : raw39752step0Labels = raw39752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39752 raw39752Labels permutation520 hz
    mixedMoment B raw39752step0 raw39752step0Labels = mixedMoment B raw39752step1 raw39752step1Labels := by
      have hz : ∀ j, raw39752step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39752step1 = (fun i j => raw39752step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39752step1 raw39752step0; decide +kernel
      have hl : raw39752step1Labels = raw39752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39752step0 raw39752step0Labels permutation104 hz
    mixedMoment B raw39752step1 raw39752step1Labels = mixedMoment B raw39752step2 raw39752step2Labels := by
      have hz : ∀ j, raw39752step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39752step2 = (fun i j => raw39752step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39752step2 raw39752step1; decide +kernel
      have hl : raw39752step2Labels = raw39752step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39752step1 raw39752step1Labels permutation20 hz
    mixedMoment B raw39752step2 raw39752step2Labels = mixedMoment B raw39752step3 raw39752step3Labels := by
      have ha : raw39752step3 = (fun i j => raw39752step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39752step3 raw39752step2; decide +kernel
      have hl : raw39752step3Labels = raw39752step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39752step2 raw39752step2Labels permutation6 permutation5
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical39753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39753 raw39753Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39753 raw39753Labels = mixedMoment B raw39753step0 raw39753step0Labels := by
      have hz : ∀ j, raw39753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39753step0 = (fun i j => raw39753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39753step0 raw39753; decide +kernel
      have hl : raw39753step0Labels = raw39753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39753 raw39753Labels permutation434 hz
    mixedMoment B raw39753step0 raw39753step0Labels = mixedMoment B raw39753step1 raw39753step1Labels := by
      have hz : ∀ j, raw39753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39753step1 = (fun i j => raw39753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39753step1 raw39753step0; decide +kernel
      have hl : raw39753step1Labels = raw39753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39753step0 raw39753step0Labels permutation80 hz
    mixedMoment B raw39753step1 raw39753step1Labels = mixedMoment B raw39753step2 raw39753step2Labels := by
      have ha : raw39753step2 = (fun i j => raw39753step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39753step2 raw39753step1; decide +kernel
      have hl : raw39753step2Labels = raw39753step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39753step1 raw39753step1Labels permutation30 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical39754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39754 raw39754Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39754 raw39754Labels = mixedMoment B raw39754step0 raw39754step0Labels := by
      have hz : ∀ j, raw39754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39754step0 = (fun i j => raw39754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39754step0 raw39754; decide +kernel
      have hl : raw39754step0Labels = raw39754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39754 raw39754Labels permutation434 hz
    mixedMoment B raw39754step0 raw39754step0Labels = mixedMoment B raw39754step1 raw39754step1Labels := by
      have hz : ∀ j, raw39754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39754step1 = (fun i j => raw39754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39754step1 raw39754step0; decide +kernel
      have hl : raw39754step1Labels = raw39754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39754step0 raw39754step0Labels permutation80 hz
    mixedMoment B raw39754step1 raw39754step1Labels = mixedMoment B raw39754step2 raw39754step2Labels := by
      have ha : raw39754step2 = (fun i j => raw39754step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39754step2 raw39754step1; decide +kernel
      have hl : raw39754step2Labels = raw39754step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39754step1 raw39754step1Labels permutation30 permutation4
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical39755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39755 raw39755Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw39755 raw39755Labels = mixedMoment B raw39755step0 raw39755step0Labels := by
      have hz : ∀ j, raw39755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39755step0 = (fun i j => raw39755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39755step0 raw39755; decide +kernel
      have hl : raw39755step0Labels = raw39755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39755 raw39755Labels permutation434 hz
    mixedMoment B raw39755step0 raw39755step0Labels = mixedMoment B raw39755step1 raw39755step1Labels := by
      have hz : ∀ j, raw39755step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39755step1 = (fun i j => raw39755step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39755step1 raw39755step0; decide +kernel
      have hl : raw39755step1Labels = raw39755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39755step0 raw39755step0Labels permutation80 hz
    mixedMoment B raw39755step1 raw39755step1Labels = mixedMoment B raw39755step2 raw39755step2Labels := by
      have ha : raw39755step2 = (fun i j => raw39755step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39755step2 raw39755step1; decide +kernel
      have hl : raw39755step2Labels = raw39755step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39755step1 raw39755step1Labels permutation14 permutation4
    mixedMoment B raw39755step2 raw39755step2Labels = mixedMoment B raw39755step3 raw39755step3Labels := by
      have ha : raw39755step3 = -raw39755step2 := by apply Matrix.ext; change ∀ i j, raw39755step3 i j = -(raw39755step2 i j); unfold raw39755step3 raw39755step2; decide +kernel
      have hl : raw39755step3Labels = raw39755step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node503 node503Labels := by rfl

theorem canonical39756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39756 raw39756Labels = mixedMoment B node446 node446Labels := by
  calc
    mixedMoment B raw39756 raw39756Labels = mixedMoment B raw39756step0 raw39756step0Labels := by
      have hz : ∀ j, raw39756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39756step0 = (fun i j => raw39756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39756step0 raw39756; decide +kernel
      have hl : raw39756step0Labels = raw39756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39756 raw39756Labels permutation346 hz
    mixedMoment B raw39756step0 raw39756step0Labels = mixedMoment B raw39756step1 raw39756step1Labels := by
      have ha : raw39756step1 = (fun i j => raw39756step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39756step1 raw39756step0; decide +kernel
      have hl : raw39756step1Labels = raw39756step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39756step0 raw39756step0Labels permutation74 permutation6
    _ = mixedMoment B node446 node446Labels := by rfl

theorem canonical39757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39757 raw39757Labels = mixedMoment B node493 node493Labels := by
  calc
    mixedMoment B raw39757 raw39757Labels = mixedMoment B raw39757step0 raw39757step0Labels := by
      have hz : ∀ j, raw39757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39757step0 = (fun i j => raw39757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39757step0 raw39757; decide +kernel
      have hl : raw39757step0Labels = raw39757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39757 raw39757Labels permutation346 hz
    mixedMoment B raw39757step0 raw39757step0Labels = mixedMoment B raw39757step1 raw39757step1Labels := by
      have ha : raw39757step1 = (fun i j => raw39757step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39757step1 raw39757step0; decide +kernel
      have hl : raw39757step1Labels = raw39757step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39757step0 raw39757step0Labels permutation68 permutation6
    _ = mixedMoment B node493 node493Labels := by rfl

theorem canonical39758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39758 raw39758Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw39758 raw39758Labels = mixedMoment B raw39758step0 raw39758step0Labels := by
      have hz : ∀ j, raw39758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39758step0 = (fun i j => raw39758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39758step0 raw39758; decide +kernel
      have hl : raw39758step0Labels = raw39758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39758 raw39758Labels permutation346 hz
    mixedMoment B raw39758step0 raw39758step0Labels = mixedMoment B raw39758step1 raw39758step1Labels := by
      have ha : raw39758step1 = (fun i j => raw39758step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39758step1 raw39758step0; decide +kernel
      have hl : raw39758step1Labels = raw39758step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39758step0 raw39758step0Labels permutation102 permutation4
    _ = mixedMoment B node487 node487Labels := by rfl

theorem canonical39759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39759 raw39759Labels = mixedMoment B node244 node244Labels := by
  calc
    mixedMoment B raw39759 raw39759Labels = mixedMoment B raw39759step0 raw39759step0Labels := by
      have hz : ∀ j, raw39759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39759step0 = (fun i j => raw39759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39759step0 raw39759; decide +kernel
      have hl : raw39759step0Labels = raw39759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39759 raw39759Labels permutation346 hz
    mixedMoment B raw39759step0 raw39759step0Labels = mixedMoment B raw39759step1 raw39759step1Labels := by
      have ha : raw39759step1 = (fun i j => raw39759step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39759step1 raw39759step0; decide +kernel
      have hl : raw39759step1Labels = raw39759step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39759step0 raw39759step0Labels permutation83 permutation6
    mixedMoment B raw39759step1 raw39759step1Labels = mixedMoment B raw39759step2 raw39759step2Labels := by
      have ha : raw39759step2 = -raw39759step1 := by apply Matrix.ext; change ∀ i j, raw39759step2 i j = -(raw39759step1 i j); unfold raw39759step2 raw39759step1; decide +kernel
      have hl : raw39759step2Labels = raw39759step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node244 node244Labels := by rfl

theorem canonical39760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39760 raw39760Labels = mixedMoment B node456 node456Labels := by
  calc
    mixedMoment B raw39760 raw39760Labels = mixedMoment B raw39760step0 raw39760step0Labels := by
      have ha : raw39760step0 = (fun i j => raw39760 (permutation468 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39760step0 raw39760; decide +kernel
      have hl : raw39760step0Labels = raw39760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39760 raw39760Labels permutation468 permutation6
    mixedMoment B raw39760step0 raw39760step0Labels = mixedMoment B raw39760step1 raw39760step1Labels := by
      have ha : raw39760step1 = -raw39760step0 := by apply Matrix.ext; change ∀ i j, raw39760step1 i j = -(raw39760step0 i j); unfold raw39760step1 raw39760step0; decide +kernel
      have hl : raw39760step1Labels = raw39760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node456 node456Labels := by rfl

theorem canonical39761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39761 raw39761Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw39761 raw39761Labels = mixedMoment B raw39761step0 raw39761step0Labels := by
      have hz : ∀ j, raw39761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39761step0 = (fun i j => raw39761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39761step0 raw39761; decide +kernel
      have hl : raw39761step0Labels = raw39761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39761 raw39761Labels permutation434 hz
    mixedMoment B raw39761step0 raw39761step0Labels = mixedMoment B raw39761step1 raw39761step1Labels := by
      have ha : raw39761step1 = (fun i j => raw39761step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39761step1 raw39761step0; decide +kernel
      have hl : raw39761step1Labels = raw39761step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39761step0 raw39761step0Labels permutation149 permutation5
    _ = mixedMoment B node494 node494Labels := by rfl

theorem canonical39762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39762 raw39762Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw39762 raw39762Labels = mixedMoment B raw39762step0 raw39762step0Labels := by
      have hz : ∀ j, raw39762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39762step0 = (fun i j => raw39762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39762step0 raw39762; decide +kernel
      have hl : raw39762step0Labels = raw39762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39762 raw39762Labels permutation434 hz
    mixedMoment B raw39762step0 raw39762step0Labels = mixedMoment B raw39762step1 raw39762step1Labels := by
      have ha : raw39762step1 = (fun i j => raw39762step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39762step1 raw39762step0; decide +kernel
      have hl : raw39762step1Labels = raw39762step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39762step0 raw39762step0Labels permutation104 permutation6
    mixedMoment B raw39762step1 raw39762step1Labels = mixedMoment B raw39762step2 raw39762step2Labels := by
      have ha : raw39762step2 = -raw39762step1 := by apply Matrix.ext; change ∀ i j, raw39762step2 i j = -(raw39762step1 i j); unfold raw39762step2 raw39762step1; decide +kernel
      have hl : raw39762step2Labels = raw39762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node248 node248Labels := by rfl

theorem canonical39763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39763 raw39763Labels = mixedMoment B node459 node459Labels := by
  calc
    mixedMoment B raw39763 raw39763Labels = mixedMoment B raw39763step0 raw39763step0Labels := by
      have ha : raw39763step0 = (fun i j => raw39763 (permutation553 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39763step0 raw39763; decide +kernel
      have hl : raw39763step0Labels = raw39763Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39763 raw39763Labels permutation553 permutation6
    mixedMoment B raw39763step0 raw39763step0Labels = mixedMoment B raw39763step1 raw39763step1Labels := by
      have ha : raw39763step1 = -raw39763step0 := by apply Matrix.ext; change ∀ i j, raw39763step1 i j = -(raw39763step0 i j); unfold raw39763step1 raw39763step0; decide +kernel
      have hl : raw39763step1Labels = raw39763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node459 node459Labels := by rfl

theorem canonical39764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39764 raw39764Labels = mixedMoment B node5507 node5507Labels := by
  calc
    mixedMoment B raw39764 raw39764Labels = mixedMoment B raw39764step0 raw39764step0Labels := by
      have hz : ∀ j, raw39764 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39764step0 = (fun i j => raw39764 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39764step0 raw39764; decide +kernel
      have hl : raw39764step0Labels = raw39764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39764 raw39764Labels permutation520 hz
    mixedMoment B raw39764step0 raw39764step0Labels = mixedMoment B raw39764step1 raw39764step1Labels := by
      have hz : ∀ j, raw39764step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39764step1 = (fun i j => raw39764step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39764step1 raw39764step0; decide +kernel
      have hl : raw39764step1Labels = raw39764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39764step0 raw39764step0Labels permutation104 hz
    mixedMoment B raw39764step1 raw39764step1Labels = mixedMoment B raw39764step2 raw39764step2Labels := by
      have hz : ∀ j, raw39764step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39764step2 = (fun i j => raw39764step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39764step2 raw39764step1; decide +kernel
      have hl : raw39764step2Labels = raw39764step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39764step1 raw39764step1Labels permutation20 hz
    mixedMoment B raw39764step2 raw39764step2Labels = mixedMoment B raw39764step3 raw39764step3Labels := by
      have ha : raw39764step3 = (fun i j => raw39764step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39764step3 raw39764step2; decide +kernel
      have hl : raw39764step3Labels = raw39764step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39764step2 raw39764step2Labels permutation7 permutation3
    mixedMoment B raw39764step3 raw39764step3Labels = mixedMoment B raw39764step4 raw39764step4Labels := by
      have ha : raw39764step4 = -raw39764step3 := by apply Matrix.ext; change ∀ i j, raw39764step4 i j = -(raw39764step3 i j); unfold raw39764step4 raw39764step3; decide +kernel
      have hl : raw39764step4Labels = raw39764step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5507 node5507Labels := by rfl

theorem canonical39765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39765 raw39765Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw39765 raw39765Labels = mixedMoment B raw39765step0 raw39765step0Labels := by
      have hz : ∀ j, raw39765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39765step0 = (fun i j => raw39765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39765step0 raw39765; decide +kernel
      have hl : raw39765step0Labels = raw39765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39765 raw39765Labels permutation434 hz
    mixedMoment B raw39765step0 raw39765step0Labels = mixedMoment B raw39765step1 raw39765step1Labels := by
      have hz : ∀ j, raw39765step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39765step1 = (fun i j => raw39765step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39765step1 raw39765step0; decide +kernel
      have hl : raw39765step1Labels = raw39765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39765step0 raw39765step0Labels permutation80 hz
    mixedMoment B raw39765step1 raw39765step1Labels = mixedMoment B raw39765step2 raw39765step2Labels := by
      have ha : raw39765step2 = (fun i j => raw39765step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39765step2 raw39765step1; decide +kernel
      have hl : raw39765step2Labels = raw39765step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39765step1 raw39765step1Labels permutation28 permutation7
    _ = mixedMoment B node496 node496Labels := by rfl

theorem canonical39766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39766 raw39766Labels = mixedMoment B node249 node249Labels := by
  calc
    mixedMoment B raw39766 raw39766Labels = mixedMoment B raw39766step0 raw39766step0Labels := by
      have hz : ∀ j, raw39766 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39766step0 = (fun i j => raw39766 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39766step0 raw39766; decide +kernel
      have hl : raw39766step0Labels = raw39766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39766 raw39766Labels permutation434 hz
    mixedMoment B raw39766step0 raw39766step0Labels = mixedMoment B raw39766step1 raw39766step1Labels := by
      have hz : ∀ j, raw39766step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39766step1 = (fun i j => raw39766step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39766step1 raw39766step0; decide +kernel
      have hl : raw39766step1Labels = raw39766step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39766step0 raw39766step0Labels permutation80 hz
    mixedMoment B raw39766step1 raw39766step1Labels = mixedMoment B raw39766step2 raw39766step2Labels := by
      have ha : raw39766step2 = (fun i j => raw39766step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39766step2 raw39766step1; decide +kernel
      have hl : raw39766step2Labels = raw39766step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39766step1 raw39766step1Labels permutation20 permutation6
    mixedMoment B raw39766step2 raw39766step2Labels = mixedMoment B raw39766step3 raw39766step3Labels := by
      have ha : raw39766step3 = -raw39766step2 := by apply Matrix.ext; change ∀ i j, raw39766step3 i j = -(raw39766step2 i j); unfold raw39766step3 raw39766step2; decide +kernel
      have hl : raw39766step3Labels = raw39766step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node249 node249Labels := by rfl

theorem canonical39767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39767 raw39767Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw39767 raw39767Labels = mixedMoment B raw39767step0 raw39767step0Labels := by
      have hz : ∀ j, raw39767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39767step0 = (fun i j => raw39767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39767step0 raw39767; decide +kernel
      have hl : raw39767step0Labels = raw39767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39767 raw39767Labels permutation346 hz
    mixedMoment B raw39767step0 raw39767step0Labels = mixedMoment B raw39767step1 raw39767step1Labels := by
      have ha : raw39767step1 = (fun i j => raw39767step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39767step1 raw39767step0; decide +kernel
      have hl : raw39767step1Labels = raw39767step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39767step0 raw39767step0Labels permutation137 permutation7
    _ = mixedMoment B node494 node494Labels := by rfl

theorem canonical39768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39768 raw39768Labels = mixedMoment B node337 node337Labels := by
  calc
    mixedMoment B raw39768 raw39768Labels = mixedMoment B raw39768step0 raw39768step0Labels := by
      have hz : ∀ j, raw39768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39768step0 = (fun i j => raw39768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39768step0 raw39768; decide +kernel
      have hl : raw39768step0Labels = raw39768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39768 raw39768Labels permutation346 hz
    mixedMoment B raw39768step0 raw39768step0Labels = mixedMoment B raw39768step1 raw39768step1Labels := by
      have ha : raw39768step1 = (fun i j => raw39768step0 (permutation136 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39768step1 raw39768step0; decide +kernel
      have hl : raw39768step1Labels = raw39768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39768step0 raw39768step0Labels permutation136 permutation7
    _ = mixedMoment B node337 node337Labels := by rfl

theorem canonical39769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39769 raw39769Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39769 raw39769Labels = mixedMoment B raw39769step0 raw39769step0Labels := by
      have hz : ∀ j, raw39769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39769step0 = (fun i j => raw39769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39769step0 raw39769; decide +kernel
      have hl : raw39769step0Labels = raw39769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39769 raw39769Labels permutation434 hz
    mixedMoment B raw39769step0 raw39769step0Labels = mixedMoment B raw39769step1 raw39769step1Labels := by
      have hz : ∀ j, raw39769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39769step1 = (fun i j => raw39769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39769step1 raw39769step0; decide +kernel
      have hl : raw39769step1Labels = raw39769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39769step0 raw39769step0Labels permutation80 hz
    mixedMoment B raw39769step1 raw39769step1Labels = mixedMoment B raw39769step2 raw39769step2Labels := by
      have hz : ∀ j, raw39769step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39769step2 = (fun i j => raw39769step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39769step2 raw39769step1; decide +kernel
      have hl : raw39769step2Labels = raw39769step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39769step1 raw39769step1Labels permutation14 hz
    mixedMoment B raw39769step2 raw39769step2Labels = mixedMoment B raw39769step3 raw39769step3Labels := by
      have ha : raw39769step3 = (fun i j => raw39769step2 (permutation6 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39769step3 raw39769step2; decide +kernel
      have hl : raw39769step3Labels = raw39769step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39769step2 raw39769step2Labels permutation6 permutation7
    _ = mixedMoment B node420 node420Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 288) =
      Integer.Sparse.eval keyMomentRow288 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 288).leftCharge (GramAssembly.key 288).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 330) := by
    have ha : gramCharges (GramAssembly.key 288).leftCharge (GramAssembly.key 288).rightCharge = raw39738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39738 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 288).leftCharge (GramAssembly.key 288).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow288, Integer.Sparse.eval]

theorem keyMoment289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 289) =
      Integer.Sparse.eval keyMomentRow289 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 289).leftCharge (GramAssembly.key 289).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 289).leftCharge (GramAssembly.key 289).rightCharge = raw39739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39739 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 289).leftCharge (GramAssembly.key 289).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow289, Integer.Sparse.eval]

theorem keyMoment290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 290) =
      Integer.Sparse.eval keyMomentRow290 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 290).leftCharge (GramAssembly.key 290).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 491) := by
    have ha : gramCharges (GramAssembly.key 290).leftCharge (GramAssembly.key 290).rightCharge = raw39740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39740 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 290).leftCharge (GramAssembly.key 290).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow290, Integer.Sparse.eval]

theorem keyMoment291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 291) =
      Integer.Sparse.eval keyMomentRow291 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 291).leftCharge (GramAssembly.key 291).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 447) := by
    have ha : gramCharges (GramAssembly.key 291).leftCharge (GramAssembly.key 291).rightCharge = raw39741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39741 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 291).leftCharge (GramAssembly.key 291).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow291, Integer.Sparse.eval]

theorem keyMoment292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 292) =
      Integer.Sparse.eval keyMomentRow292 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 292).leftCharge (GramAssembly.key 292).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 470) := by
    have ha : gramCharges (GramAssembly.key 292).leftCharge (GramAssembly.key 292).rightCharge = raw39742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39742 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 292).leftCharge (GramAssembly.key 292).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow292, Integer.Sparse.eval]

theorem keyMoment293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 293) =
      Integer.Sparse.eval keyMomentRow293 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 293).leftCharge (GramAssembly.key 293).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 484) := by
    have ha : gramCharges (GramAssembly.key 293).leftCharge (GramAssembly.key 293).rightCharge = raw39743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39743 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 293).leftCharge (GramAssembly.key 293).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow293, Integer.Sparse.eval]

theorem keyMoment294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 294) =
      Integer.Sparse.eval keyMomentRow294 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 294).leftCharge (GramAssembly.key 294).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 483) := by
    have ha : gramCharges (GramAssembly.key 294).leftCharge (GramAssembly.key 294).rightCharge = raw39744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39744 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 294).leftCharge (GramAssembly.key 294).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow294, Integer.Sparse.eval]

theorem keyMoment295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 295) =
      Integer.Sparse.eval keyMomentRow295 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 295).leftCharge (GramAssembly.key 295).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 295).leftCharge (GramAssembly.key 295).rightCharge = raw39745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39745 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 295).leftCharge (GramAssembly.key 295).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow295, Integer.Sparse.eval]

theorem keyMoment296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 296) =
      Integer.Sparse.eval keyMomentRow296 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 296).leftCharge (GramAssembly.key 296).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 390) := by
    have ha : gramCharges (GramAssembly.key 296).leftCharge (GramAssembly.key 296).rightCharge = raw39746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39746 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 296).leftCharge (GramAssembly.key 296).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow296, Integer.Sparse.eval]

theorem keyMoment297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 297) =
      Integer.Sparse.eval keyMomentRow297 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 297).leftCharge (GramAssembly.key 297).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 153) := by
    have ha : gramCharges (GramAssembly.key 297).leftCharge (GramAssembly.key 297).rightCharge = raw39747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39747 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 297).leftCharge (GramAssembly.key 297).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow297, Integer.Sparse.eval]

theorem keyMoment298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 298) =
      Integer.Sparse.eval keyMomentRow298 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 298).leftCharge (GramAssembly.key 298).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 333) := by
    have ha : gramCharges (GramAssembly.key 298).leftCharge (GramAssembly.key 298).rightCharge = raw39748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39748 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 298).leftCharge (GramAssembly.key 298).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow298, Integer.Sparse.eval]

theorem keyMoment299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 299) =
      Integer.Sparse.eval keyMomentRow299 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 299).leftCharge (GramAssembly.key 299).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 395) := by
    have ha : gramCharges (GramAssembly.key 299).leftCharge (GramAssembly.key 299).rightCharge = raw39749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39749 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 299).leftCharge (GramAssembly.key 299).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow299, Integer.Sparse.eval]

theorem keyMoment300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 300) =
      Integer.Sparse.eval keyMomentRow300 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 300).leftCharge (GramAssembly.key 300).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 346) := by
    have ha : gramCharges (GramAssembly.key 300).leftCharge (GramAssembly.key 300).rightCharge = raw39750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39750 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 300).leftCharge (GramAssembly.key 300).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow300, Integer.Sparse.eval]

theorem keyMoment301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 301) =
      Integer.Sparse.eval keyMomentRow301 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 301).leftCharge (GramAssembly.key 301).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 147) := by
    have ha : gramCharges (GramAssembly.key 301).leftCharge (GramAssembly.key 301).rightCharge = raw39751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39751 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 301).leftCharge (GramAssembly.key 301).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow301, Integer.Sparse.eval]

theorem keyMoment302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 302) =
      Integer.Sparse.eval keyMomentRow302 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 302).leftCharge (GramAssembly.key 302).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 302).leftCharge (GramAssembly.key 302).rightCharge = raw39752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39752 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 302).leftCharge (GramAssembly.key 302).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow302, Integer.Sparse.eval]

theorem keyMoment303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 303) =
      Integer.Sparse.eval keyMomentRow303 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 303).leftCharge (GramAssembly.key 303).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 303).leftCharge (GramAssembly.key 303).rightCharge = raw39753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39753 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 303).leftCharge (GramAssembly.key 303).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow303, Integer.Sparse.eval]

theorem keyMoment304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 304) =
      Integer.Sparse.eval keyMomentRow304 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 304).leftCharge (GramAssembly.key 304).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 304).leftCharge (GramAssembly.key 304).rightCharge = raw39754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39754 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 304).leftCharge (GramAssembly.key 304).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow304, Integer.Sparse.eval]

theorem keyMoment305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 305) =
      Integer.Sparse.eval keyMomentRow305 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 305).leftCharge (GramAssembly.key 305).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 503) := by
    have ha : gramCharges (GramAssembly.key 305).leftCharge (GramAssembly.key 305).rightCharge = raw39755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39755 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 305).leftCharge (GramAssembly.key 305).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow305, Integer.Sparse.eval]

theorem keyMoment306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 306) =
      Integer.Sparse.eval keyMomentRow306 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 306).leftCharge (GramAssembly.key 306).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 446) := by
    have ha : gramCharges (GramAssembly.key 306).leftCharge (GramAssembly.key 306).rightCharge = raw39756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39756 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 306).leftCharge (GramAssembly.key 306).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow306, Integer.Sparse.eval]

theorem keyMoment307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 307) =
      Integer.Sparse.eval keyMomentRow307 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 307).leftCharge (GramAssembly.key 307).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 493) := by
    have ha : gramCharges (GramAssembly.key 307).leftCharge (GramAssembly.key 307).rightCharge = raw39757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39757 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 307).leftCharge (GramAssembly.key 307).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow307, Integer.Sparse.eval]

theorem keyMoment308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 308) =
      Integer.Sparse.eval keyMomentRow308 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 308).leftCharge (GramAssembly.key 308).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 487) := by
    have ha : gramCharges (GramAssembly.key 308).leftCharge (GramAssembly.key 308).rightCharge = raw39758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39758 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 308).leftCharge (GramAssembly.key 308).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow308, Integer.Sparse.eval]

theorem keyMoment309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 309) =
      Integer.Sparse.eval keyMomentRow309 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 309).leftCharge (GramAssembly.key 309).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 244) := by
    have ha : gramCharges (GramAssembly.key 309).leftCharge (GramAssembly.key 309).rightCharge = raw39759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39759 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 309).leftCharge (GramAssembly.key 309).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow309, Integer.Sparse.eval]

theorem keyMoment310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 310) =
      Integer.Sparse.eval keyMomentRow310 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 310).leftCharge (GramAssembly.key 310).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 456) := by
    have ha : gramCharges (GramAssembly.key 310).leftCharge (GramAssembly.key 310).rightCharge = raw39760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39760 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 310).leftCharge (GramAssembly.key 310).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow310, Integer.Sparse.eval]

theorem keyMoment311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 311) =
      Integer.Sparse.eval keyMomentRow311 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 311).leftCharge (GramAssembly.key 311).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 311).leftCharge (GramAssembly.key 311).rightCharge = raw39761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39761 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 311).leftCharge (GramAssembly.key 311).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow311, Integer.Sparse.eval]

theorem keyMoment312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 312) =
      Integer.Sparse.eval keyMomentRow312 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 312).leftCharge (GramAssembly.key 312).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 248) := by
    have ha : gramCharges (GramAssembly.key 312).leftCharge (GramAssembly.key 312).rightCharge = raw39762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39762 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 312).leftCharge (GramAssembly.key 312).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow312, Integer.Sparse.eval]

theorem keyMoment313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 313) =
      Integer.Sparse.eval keyMomentRow313 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 313).leftCharge (GramAssembly.key 313).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 459) := by
    have ha : gramCharges (GramAssembly.key 313).leftCharge (GramAssembly.key 313).rightCharge = raw39763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39763 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 313).leftCharge (GramAssembly.key 313).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow313, Integer.Sparse.eval]

theorem keyMoment314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 314) =
      Integer.Sparse.eval keyMomentRow314 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 314).leftCharge (GramAssembly.key 314).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 5) := by
    have ha : gramCharges (GramAssembly.key 314).leftCharge (GramAssembly.key 314).rightCharge = raw39764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39764 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 314).leftCharge (GramAssembly.key 314).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow314, Integer.Sparse.eval]

theorem keyMoment315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 315) =
      Integer.Sparse.eval keyMomentRow315 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 315).leftCharge (GramAssembly.key 315).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 496) := by
    have ha : gramCharges (GramAssembly.key 315).leftCharge (GramAssembly.key 315).rightCharge = raw39765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39765 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 315).leftCharge (GramAssembly.key 315).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow315, Integer.Sparse.eval]

theorem keyMoment316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 316) =
      Integer.Sparse.eval keyMomentRow316 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 316).leftCharge (GramAssembly.key 316).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 249) := by
    have ha : gramCharges (GramAssembly.key 316).leftCharge (GramAssembly.key 316).rightCharge = raw39766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39766 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 316).leftCharge (GramAssembly.key 316).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow316, Integer.Sparse.eval]

theorem keyMoment317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 317) =
      Integer.Sparse.eval keyMomentRow317 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 317).leftCharge (GramAssembly.key 317).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 317).leftCharge (GramAssembly.key 317).rightCharge = raw39767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39767 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 317).leftCharge (GramAssembly.key 317).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow317, Integer.Sparse.eval]

theorem keyMoment318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 318) =
      Integer.Sparse.eval keyMomentRow318 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 318).leftCharge (GramAssembly.key 318).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 337) := by
    have ha : gramCharges (GramAssembly.key 318).leftCharge (GramAssembly.key 318).rightCharge = raw39768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39768 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 318).leftCharge (GramAssembly.key 318).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow318, Integer.Sparse.eval]

theorem keyMoment319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 319) =
      Integer.Sparse.eval keyMomentRow319 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 319).leftCharge (GramAssembly.key 319).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 319).leftCharge (GramAssembly.key 319).rightCharge = raw39769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39769 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 319).leftCharge (GramAssembly.key 319).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow319, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt288 : keyMomentRows (288 : Fin 2886) =
    keyMomentRow288 := by decide +kernel

theorem keyMomentRowsAt289 : keyMomentRows (289 : Fin 2886) =
    keyMomentRow289 := by decide +kernel

theorem keyMomentRowsAt290 : keyMomentRows (290 : Fin 2886) =
    keyMomentRow290 := by decide +kernel

theorem keyMomentRowsAt291 : keyMomentRows (291 : Fin 2886) =
    keyMomentRow291 := by decide +kernel

theorem keyMomentRowsAt292 : keyMomentRows (292 : Fin 2886) =
    keyMomentRow292 := by decide +kernel

theorem keyMomentRowsAt293 : keyMomentRows (293 : Fin 2886) =
    keyMomentRow293 := by decide +kernel

theorem keyMomentRowsAt294 : keyMomentRows (294 : Fin 2886) =
    keyMomentRow294 := by decide +kernel

theorem keyMomentRowsAt295 : keyMomentRows (295 : Fin 2886) =
    keyMomentRow295 := by decide +kernel

theorem keyMomentRowsAt296 : keyMomentRows (296 : Fin 2886) =
    keyMomentRow296 := by decide +kernel

theorem keyMomentRowsAt297 : keyMomentRows (297 : Fin 2886) =
    keyMomentRow297 := by decide +kernel

theorem keyMomentRowsAt298 : keyMomentRows (298 : Fin 2886) =
    keyMomentRow298 := by decide +kernel

theorem keyMomentRowsAt299 : keyMomentRows (299 : Fin 2886) =
    keyMomentRow299 := by decide +kernel

theorem keyMomentRowsAt300 : keyMomentRows (300 : Fin 2886) =
    keyMomentRow300 := by decide +kernel

theorem keyMomentRowsAt301 : keyMomentRows (301 : Fin 2886) =
    keyMomentRow301 := by decide +kernel

theorem keyMomentRowsAt302 : keyMomentRows (302 : Fin 2886) =
    keyMomentRow302 := by decide +kernel

theorem keyMomentRowsAt303 : keyMomentRows (303 : Fin 2886) =
    keyMomentRow303 := by decide +kernel

theorem keyMomentRowsAt304 : keyMomentRows (304 : Fin 2886) =
    keyMomentRow304 := by decide +kernel

theorem keyMomentRowsAt305 : keyMomentRows (305 : Fin 2886) =
    keyMomentRow305 := by decide +kernel

theorem keyMomentRowsAt306 : keyMomentRows (306 : Fin 2886) =
    keyMomentRow306 := by decide +kernel

theorem keyMomentRowsAt307 : keyMomentRows (307 : Fin 2886) =
    keyMomentRow307 := by decide +kernel

theorem keyMomentRowsAt308 : keyMomentRows (308 : Fin 2886) =
    keyMomentRow308 := by decide +kernel

theorem keyMomentRowsAt309 : keyMomentRows (309 : Fin 2886) =
    keyMomentRow309 := by decide +kernel

theorem keyMomentRowsAt310 : keyMomentRows (310 : Fin 2886) =
    keyMomentRow310 := by decide +kernel

theorem keyMomentRowsAt311 : keyMomentRows (311 : Fin 2886) =
    keyMomentRow311 := by decide +kernel

theorem keyMomentRowsAt312 : keyMomentRows (312 : Fin 2886) =
    keyMomentRow312 := by decide +kernel

theorem keyMomentRowsAt313 : keyMomentRows (313 : Fin 2886) =
    keyMomentRow313 := by decide +kernel

theorem keyMomentRowsAt314 : keyMomentRows (314 : Fin 2886) =
    keyMomentRow314 := by decide +kernel

theorem keyMomentRowsAt315 : keyMomentRows (315 : Fin 2886) =
    keyMomentRow315 := by decide +kernel

theorem keyMomentRowsAt316 : keyMomentRows (316 : Fin 2886) =
    keyMomentRow316 := by decide +kernel

theorem keyMomentRowsAt317 : keyMomentRows (317 : Fin 2886) =
    keyMomentRow317 := by decide +kernel

theorem keyMomentRowsAt318 : keyMomentRows (318 : Fin 2886) =
    keyMomentRow318 := by decide +kernel

theorem keyMomentRowsAt319 : keyMomentRows (319 : Fin 2886) =
    keyMomentRow319 := by decide +kernel

theorem keyMomentChunkSound9_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 9) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 288 ∨ k.val = 289 ∨ k.val = 290 ∨ k.val = 291 ∨ k.val = 292 ∨ k.val = 293 ∨ k.val = 294 ∨ k.val = 295 ∨ k.val = 296 ∨ k.val = 297 ∨ k.val = 298 ∨ k.val = 299 ∨ k.val = 300 ∨ k.val = 301 ∨ k.val = 302 ∨ k.val = 303 ∨ k.val = 304 ∨ k.val = 305 ∨ k.val = 306 ∨ k.val = 307 ∨ k.val = 308 ∨ k.val = 309 ∨ k.val = 310 ∨ k.val = 311 ∨ k.val = 312 ∨ k.val = 313 ∨ k.val = 314 ∨ k.val = 315 ∨ k.val = 316 ∨ k.val = 317 ∨ k.val = 318 ∨ k.val = 319 := by omega
  rcases heq with h288 | h289 | h290 | h291 | h292 | h293 | h294 | h295 | h296 | h297 | h298 | h299 | h300 | h301 | h302 | h303 | h304 | h305 | h306 | h307 | h308 | h309 | h310 | h311 | h312 | h313 | h314 | h315 | h316 | h317 | h318 | h319
  · have he : k = (288 : Fin 2886) := Fin.ext h288
    subst k
    rw [keyMomentRowsAt288]
    exact keyMoment288 B hB
  · have he : k = (289 : Fin 2886) := Fin.ext h289
    subst k
    rw [keyMomentRowsAt289]
    exact keyMoment289 B hB
  · have he : k = (290 : Fin 2886) := Fin.ext h290
    subst k
    rw [keyMomentRowsAt290]
    exact keyMoment290 B hB
  · have he : k = (291 : Fin 2886) := Fin.ext h291
    subst k
    rw [keyMomentRowsAt291]
    exact keyMoment291 B hB
  · have he : k = (292 : Fin 2886) := Fin.ext h292
    subst k
    rw [keyMomentRowsAt292]
    exact keyMoment292 B hB
  · have he : k = (293 : Fin 2886) := Fin.ext h293
    subst k
    rw [keyMomentRowsAt293]
    exact keyMoment293 B hB
  · have he : k = (294 : Fin 2886) := Fin.ext h294
    subst k
    rw [keyMomentRowsAt294]
    exact keyMoment294 B hB
  · have he : k = (295 : Fin 2886) := Fin.ext h295
    subst k
    rw [keyMomentRowsAt295]
    exact keyMoment295 B hB
  · have he : k = (296 : Fin 2886) := Fin.ext h296
    subst k
    rw [keyMomentRowsAt296]
    exact keyMoment296 B hB
  · have he : k = (297 : Fin 2886) := Fin.ext h297
    subst k
    rw [keyMomentRowsAt297]
    exact keyMoment297 B hB
  · have he : k = (298 : Fin 2886) := Fin.ext h298
    subst k
    rw [keyMomentRowsAt298]
    exact keyMoment298 B hB
  · have he : k = (299 : Fin 2886) := Fin.ext h299
    subst k
    rw [keyMomentRowsAt299]
    exact keyMoment299 B hB
  · have he : k = (300 : Fin 2886) := Fin.ext h300
    subst k
    rw [keyMomentRowsAt300]
    exact keyMoment300 B hB
  · have he : k = (301 : Fin 2886) := Fin.ext h301
    subst k
    rw [keyMomentRowsAt301]
    exact keyMoment301 B hB
  · have he : k = (302 : Fin 2886) := Fin.ext h302
    subst k
    rw [keyMomentRowsAt302]
    exact keyMoment302 B hB
  · have he : k = (303 : Fin 2886) := Fin.ext h303
    subst k
    rw [keyMomentRowsAt303]
    exact keyMoment303 B hB
  · have he : k = (304 : Fin 2886) := Fin.ext h304
    subst k
    rw [keyMomentRowsAt304]
    exact keyMoment304 B hB
  · have he : k = (305 : Fin 2886) := Fin.ext h305
    subst k
    rw [keyMomentRowsAt305]
    exact keyMoment305 B hB
  · have he : k = (306 : Fin 2886) := Fin.ext h306
    subst k
    rw [keyMomentRowsAt306]
    exact keyMoment306 B hB
  · have he : k = (307 : Fin 2886) := Fin.ext h307
    subst k
    rw [keyMomentRowsAt307]
    exact keyMoment307 B hB
  · have he : k = (308 : Fin 2886) := Fin.ext h308
    subst k
    rw [keyMomentRowsAt308]
    exact keyMoment308 B hB
  · have he : k = (309 : Fin 2886) := Fin.ext h309
    subst k
    rw [keyMomentRowsAt309]
    exact keyMoment309 B hB
  · have he : k = (310 : Fin 2886) := Fin.ext h310
    subst k
    rw [keyMomentRowsAt310]
    exact keyMoment310 B hB
  · have he : k = (311 : Fin 2886) := Fin.ext h311
    subst k
    rw [keyMomentRowsAt311]
    exact keyMoment311 B hB
  · have he : k = (312 : Fin 2886) := Fin.ext h312
    subst k
    rw [keyMomentRowsAt312]
    exact keyMoment312 B hB
  · have he : k = (313 : Fin 2886) := Fin.ext h313
    subst k
    rw [keyMomentRowsAt313]
    exact keyMoment313 B hB
  · have he : k = (314 : Fin 2886) := Fin.ext h314
    subst k
    rw [keyMomentRowsAt314]
    exact keyMoment314 B hB
  · have he : k = (315 : Fin 2886) := Fin.ext h315
    subst k
    rw [keyMomentRowsAt315]
    exact keyMoment315 B hB
  · have he : k = (316 : Fin 2886) := Fin.ext h316
    subst k
    rw [keyMomentRowsAt316]
    exact keyMoment316 B hB
  · have he : k = (317 : Fin 2886) := Fin.ext h317
    subst k
    rw [keyMomentRowsAt317]
    exact keyMoment317 B hB
  · have he : k = (318 : Fin 2886) := Fin.ext h318
    subst k
    rw [keyMomentRowsAt318]
    exact keyMoment318 B hB
  · have he : k = (319 : Fin 2886) := Fin.ext h319
    subst k
    rw [keyMomentRowsAt319]
    exact keyMoment319 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound9_e_oai
