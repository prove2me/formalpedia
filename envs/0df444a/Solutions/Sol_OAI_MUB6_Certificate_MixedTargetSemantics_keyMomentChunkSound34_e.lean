-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:52:36.927425+00:00
-- url     : https://prove2.me/submissions/399b6742-574f-4ad2-8da1-82902adf27cb

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical316
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40527 raw40527Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw40527 raw40527Labels = mixedMoment B raw40527step0 raw40527step0Labels := by
      have hz : ∀ j, raw40527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40527step0 = (fun i j => raw40527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40527step0 raw40527; decide +kernel
      have hl : raw40527step0Labels = raw40527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40527 raw40527Labels permutation346 hz
    mixedMoment B raw40527step0 raw40527step0Labels = mixedMoment B raw40527step1 raw40527step1Labels := by
      have hz : ∀ j, raw40527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40527step1 = (fun i j => raw40527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40527step1 raw40527step0; decide +kernel
      have hl : raw40527step1Labels = raw40527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40527step0 raw40527step0Labels permutation56 hz
    mixedMoment B raw40527step1 raw40527step1Labels = mixedMoment B raw40527step2 raw40527step2Labels := by
      have ha : raw40527step2 = (fun i j => raw40527step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40527step2 raw40527step1; decide +kernel
      have hl : raw40527step2Labels = raw40527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40527step1 raw40527step1Labels permutation13 permutation6
    mixedMoment B raw40527step2 raw40527step2Labels = mixedMoment B raw40527step3 raw40527step3Labels := by
      have ha : raw40527step3 = -raw40527step2 := by apply Matrix.ext; change ∀ i j, raw40527step3 i j = -(raw40527step2 i j); unfold raw40527step3 raw40527step2; decide +kernel
      have hl : raw40527step3Labels = raw40527step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1324 node1324Labels := by rfl

theorem canonical40528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40528 raw40528Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw40528 raw40528Labels = mixedMoment B raw40528step0 raw40528step0Labels := by
      have hz : ∀ j, raw40528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40528step0 = (fun i j => raw40528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40528step0 raw40528; decide +kernel
      have hl : raw40528step0Labels = raw40528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40528 raw40528Labels permutation265 hz
    mixedMoment B raw40528step0 raw40528step0Labels = mixedMoment B raw40528step1 raw40528step1Labels := by
      have ha : raw40528step1 = (fun i j => raw40528step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40528step1 raw40528step0; decide +kernel
      have hl : raw40528step1Labels = raw40528step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40528step0 raw40528step0Labels permutation97 permutation6
    _ = mixedMoment B node911 node911Labels := by rfl

theorem canonical40529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40529 raw40529Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw40529 raw40529Labels = mixedMoment B raw40529step0 raw40529step0Labels := by
      have hz : ∀ j, raw40529 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40529step0 = (fun i j => raw40529 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40529step0 raw40529; decide +kernel
      have hl : raw40529step0Labels = raw40529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40529 raw40529Labels permutation265 hz
    mixedMoment B raw40529step0 raw40529step0Labels = mixedMoment B raw40529step1 raw40529step1Labels := by
      have ha : raw40529step1 = (fun i j => raw40529step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40529step1 raw40529step0; decide +kernel
      have hl : raw40529step1Labels = raw40529step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40529step0 raw40529step0Labels permutation37 permutation6
    mixedMoment B raw40529step1 raw40529step1Labels = mixedMoment B raw40529step2 raw40529step2Labels := by
      have ha : raw40529step2 = -raw40529step1 := by apply Matrix.ext; change ∀ i j, raw40529step2 i j = -(raw40529step1 i j); unfold raw40529step2 raw40529step1; decide +kernel
      have hl : raw40529step2Labels = raw40529step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1333 node1333Labels := by rfl

theorem canonical40530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40530 raw40530Labels = mixedMoment B node654 node654Labels := by
  calc
    mixedMoment B raw40530 raw40530Labels = mixedMoment B raw40530step0 raw40530step0Labels := by
      have hz : ∀ j, raw40530 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40530step0 = (fun i j => raw40530 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40530step0 raw40530; decide +kernel
      have hl : raw40530step0Labels = raw40530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40530 raw40530Labels permutation520 hz
    mixedMoment B raw40530step0 raw40530step0Labels = mixedMoment B raw40530step1 raw40530step1Labels := by
      have hz : ∀ j, raw40530step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40530step1 = (fun i j => raw40530step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40530step1 raw40530step0; decide +kernel
      have hl : raw40530step1Labels = raw40530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40530step0 raw40530step0Labels permutation104 hz
    mixedMoment B raw40530step1 raw40530step1Labels = mixedMoment B raw40530step2 raw40530step2Labels := by
      have hz : ∀ j, raw40530step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40530step2 = (fun i j => raw40530step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40530step2 raw40530step1; decide +kernel
      have hl : raw40530step2Labels = raw40530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40530step1 raw40530step1Labels permutation20 hz
    mixedMoment B raw40530step2 raw40530step2Labels = mixedMoment B raw40530step3 raw40530step3Labels := by
      have ha : raw40530step3 = (fun i j => raw40530step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40530step3 raw40530step2; decide +kernel
      have hl : raw40530step3Labels = raw40530step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40530step2 raw40530step2Labels permutation3 permutation6
    mixedMoment B raw40530step3 raw40530step3Labels = mixedMoment B raw40530step4 raw40530step4Labels := by
      have ha : raw40530step4 = -raw40530step3 := by apply Matrix.ext; change ∀ i j, raw40530step4 i j = -(raw40530step3 i j); unfold raw40530step4 raw40530step3; decide +kernel
      have hl : raw40530step4Labels = raw40530step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node654 node654Labels := by rfl

theorem canonical40531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40531 raw40531Labels = mixedMoment B node639 node639Labels := by
  calc
    mixedMoment B raw40531 raw40531Labels = mixedMoment B raw40531step0 raw40531step0Labels := by
      have hz : ∀ j, raw40531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40531step0 = (fun i j => raw40531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40531step0 raw40531; decide +kernel
      have hl : raw40531step0Labels = raw40531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40531 raw40531Labels permutation434 hz
    mixedMoment B raw40531step0 raw40531step0Labels = mixedMoment B raw40531step1 raw40531step1Labels := by
      have hz : ∀ j, raw40531step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40531step1 = (fun i j => raw40531step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40531step1 raw40531step0; decide +kernel
      have hl : raw40531step1Labels = raw40531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40531step0 raw40531step0Labels permutation80 hz
    mixedMoment B raw40531step1 raw40531step1Labels = mixedMoment B raw40531step2 raw40531step2Labels := by
      have ha : raw40531step2 = (fun i j => raw40531step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40531step2 raw40531step1; decide +kernel
      have hl : raw40531step2Labels = raw40531step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40531step1 raw40531step1Labels permutation13 permutation6
    mixedMoment B raw40531step2 raw40531step2Labels = mixedMoment B raw40531step3 raw40531step3Labels := by
      have ha : raw40531step3 = -raw40531step2 := by apply Matrix.ext; change ∀ i j, raw40531step3 i j = -(raw40531step2 i j); unfold raw40531step3 raw40531step2; decide +kernel
      have hl : raw40531step3Labels = raw40531step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node639 node639Labels := by rfl

theorem canonical40532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40532 raw40532Labels = mixedMoment B node634 node634Labels := by
  calc
    mixedMoment B raw40532 raw40532Labels = mixedMoment B raw40532step0 raw40532step0Labels := by
      have hz : ∀ j, raw40532 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40532step0 = (fun i j => raw40532 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40532step0 raw40532; decide +kernel
      have hl : raw40532step0Labels = raw40532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40532 raw40532Labels permutation434 hz
    mixedMoment B raw40532step0 raw40532step0Labels = mixedMoment B raw40532step1 raw40532step1Labels := by
      have hz : ∀ j, raw40532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40532step1 = (fun i j => raw40532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40532step1 raw40532step0; decide +kernel
      have hl : raw40532step1Labels = raw40532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40532step0 raw40532step0Labels permutation80 hz
    mixedMoment B raw40532step1 raw40532step1Labels = mixedMoment B raw40532step2 raw40532step2Labels := by
      have ha : raw40532step2 = (fun i j => raw40532step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40532step2 raw40532step1; decide +kernel
      have hl : raw40532step2Labels = raw40532step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40532step1 raw40532step1Labels permutation11 permutation6
    mixedMoment B raw40532step2 raw40532step2Labels = mixedMoment B raw40532step3 raw40532step3Labels := by
      have ha : raw40532step3 = -raw40532step2 := by apply Matrix.ext; change ∀ i j, raw40532step3 i j = -(raw40532step2 i j); unfold raw40532step3 raw40532step2; decide +kernel
      have hl : raw40532step3Labels = raw40532step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node634 node634Labels := by rfl

theorem canonical40533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40533 raw40533Labels = mixedMoment B node624 node624Labels := by
  calc
    mixedMoment B raw40533 raw40533Labels = mixedMoment B raw40533step0 raw40533step0Labels := by
      have hz : ∀ j, raw40533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40533step0 = (fun i j => raw40533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40533step0 raw40533; decide +kernel
      have hl : raw40533step0Labels = raw40533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40533 raw40533Labels permutation346 hz
    mixedMoment B raw40533step0 raw40533step0Labels = mixedMoment B raw40533step1 raw40533step1Labels := by
      have ha : raw40533step1 = (fun i j => raw40533step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40533step1 raw40533step0; decide +kernel
      have hl : raw40533step1Labels = raw40533step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40533step0 raw40533step0Labels permutation53 permutation6
    mixedMoment B raw40533step1 raw40533step1Labels = mixedMoment B raw40533step2 raw40533step2Labels := by
      have ha : raw40533step2 = -raw40533step1 := by apply Matrix.ext; change ∀ i j, raw40533step2 i j = -(raw40533step1 i j); unfold raw40533step2 raw40533step1; decide +kernel
      have hl : raw40533step2Labels = raw40533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node624 node624Labels := by rfl

theorem canonical40534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40534 raw40534Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw40534 raw40534Labels = mixedMoment B raw40534step0 raw40534step0Labels := by
      have hz : ∀ j, raw40534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40534step0 = (fun i j => raw40534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40534step0 raw40534; decide +kernel
      have hl : raw40534step0Labels = raw40534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40534 raw40534Labels permutation520 hz
    mixedMoment B raw40534step0 raw40534step0Labels = mixedMoment B raw40534step1 raw40534step1Labels := by
      have hz : ∀ j, raw40534step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40534step1 = (fun i j => raw40534step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40534step1 raw40534step0; decide +kernel
      have hl : raw40534step1Labels = raw40534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40534step0 raw40534step0Labels permutation104 hz
    mixedMoment B raw40534step1 raw40534step1Labels = mixedMoment B raw40534step2 raw40534step2Labels := by
      have ha : raw40534step2 = (fun i j => raw40534step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40534step2 raw40534step1; decide +kernel
      have hl : raw40534step2Labels = raw40534step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40534step1 raw40534step1Labels permutation11 permutation6
    mixedMoment B raw40534step2 raw40534step2Labels = mixedMoment B raw40534step3 raw40534step3Labels := by
      have ha : raw40534step3 = -raw40534step2 := by apply Matrix.ext; change ∀ i j, raw40534step3 i j = -(raw40534step2 i j); unfold raw40534step3 raw40534step2; decide +kernel
      have hl : raw40534step3Labels = raw40534step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node653 node653Labels := by rfl

theorem canonical40535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40535 raw40535Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw40535 raw40535Labels = mixedMoment B raw40535step0 raw40535step0Labels := by
      have hz : ∀ j, raw40535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40535step0 = (fun i j => raw40535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40535step0 raw40535; decide +kernel
      have hl : raw40535step0Labels = raw40535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40535 raw40535Labels permutation434 hz
    mixedMoment B raw40535step0 raw40535step0Labels = mixedMoment B raw40535step1 raw40535step1Labels := by
      have ha : raw40535step1 = (fun i j => raw40535step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40535step1 raw40535step0; decide +kernel
      have hl : raw40535step1Labels = raw40535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40535step0 raw40535step0Labels permutation55 permutation6
    mixedMoment B raw40535step1 raw40535step1Labels = mixedMoment B raw40535step2 raw40535step2Labels := by
      have ha : raw40535step2 = -raw40535step1 := by apply Matrix.ext; change ∀ i j, raw40535step2 i j = -(raw40535step1 i j); unfold raw40535step2 raw40535step1; decide +kernel
      have hl : raw40535step2Labels = raw40535step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node638 node638Labels := by rfl

theorem canonical40536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40536 raw40536Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw40536 raw40536Labels = mixedMoment B raw40536step0 raw40536step0Labels := by
      have hz : ∀ j, raw40536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40536step0 = (fun i j => raw40536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40536step0 raw40536; decide +kernel
      have hl : raw40536step0Labels = raw40536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40536 raw40536Labels permutation434 hz
    mixedMoment B raw40536step0 raw40536step0Labels = mixedMoment B raw40536step1 raw40536step1Labels := by
      have ha : raw40536step1 = (fun i j => raw40536step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40536step1 raw40536step0; decide +kernel
      have hl : raw40536step1Labels = raw40536step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40536step0 raw40536step0Labels permutation47 permutation6
    mixedMoment B raw40536step1 raw40536step1Labels = mixedMoment B raw40536step2 raw40536step2Labels := by
      have ha : raw40536step2 = -raw40536step1 := by apply Matrix.ext; change ∀ i j, raw40536step2 i j = -(raw40536step1 i j); unfold raw40536step2 raw40536step1; decide +kernel
      have hl : raw40536step2Labels = raw40536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node631 node631Labels := by rfl

theorem canonical40537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40537 raw40537Labels = mixedMoment B node623 node623Labels := by
  calc
    mixedMoment B raw40537 raw40537Labels = mixedMoment B raw40537step0 raw40537step0Labels := by
      have ha : raw40537step0 = (fun i j => raw40537 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40537step0 raw40537; decide +kernel
      have hl : raw40537step0Labels = raw40537Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40537 raw40537Labels permutation259 permutation6
    mixedMoment B raw40537step0 raw40537step0Labels = mixedMoment B raw40537step1 raw40537step1Labels := by
      have ha : raw40537step1 = -raw40537step0 := by apply Matrix.ext; change ∀ i j, raw40537step1 i j = -(raw40537step0 i j); unfold raw40537step1 raw40537step0; decide +kernel
      have hl : raw40537step1Labels = raw40537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node623 node623Labels := by rfl

theorem canonical40538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40538 raw40538Labels = mixedMoment B node642 node642Labels := by
  calc
    mixedMoment B raw40538 raw40538Labels = mixedMoment B raw40538step0 raw40538step0Labels := by
      have hz : ∀ j, raw40538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40538step0 = (fun i j => raw40538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40538step0 raw40538; decide +kernel
      have hl : raw40538step0Labels = raw40538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40538 raw40538Labels permutation434 hz
    mixedMoment B raw40538step0 raw40538step0Labels = mixedMoment B raw40538step1 raw40538step1Labels := by
      have hz : ∀ j, raw40538step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40538step1 = (fun i j => raw40538step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40538step1 raw40538step0; decide +kernel
      have hl : raw40538step1Labels = raw40538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40538step0 raw40538step0Labels permutation80 hz
    mixedMoment B raw40538step1 raw40538step1Labels = mixedMoment B raw40538step2 raw40538step2Labels := by
      have ha : raw40538step2 = (fun i j => raw40538step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40538step2 raw40538step1; decide +kernel
      have hl : raw40538step2Labels = raw40538step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40538step1 raw40538step1Labels permutation13 permutation6
    mixedMoment B raw40538step2 raw40538step2Labels = mixedMoment B raw40538step3 raw40538step3Labels := by
      have ha : raw40538step3 = -raw40538step2 := by apply Matrix.ext; change ∀ i j, raw40538step3 i j = -(raw40538step2 i j); unfold raw40538step3 raw40538step2; decide +kernel
      have hl : raw40538step3Labels = raw40538step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node642 node642Labels := by rfl

theorem canonical40539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40539 raw40539Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw40539 raw40539Labels = mixedMoment B raw40539step0 raw40539step0Labels := by
      have hz : ∀ j, raw40539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40539step0 = (fun i j => raw40539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40539step0 raw40539; decide +kernel
      have hl : raw40539step0Labels = raw40539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40539 raw40539Labels permutation434 hz
    mixedMoment B raw40539step0 raw40539step0Labels = mixedMoment B raw40539step1 raw40539step1Labels := by
      have hz : ∀ j, raw40539step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40539step1 = (fun i j => raw40539step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40539step1 raw40539step0; decide +kernel
      have hl : raw40539step1Labels = raw40539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40539step0 raw40539step0Labels permutation80 hz
    mixedMoment B raw40539step1 raw40539step1Labels = mixedMoment B raw40539step2 raw40539step2Labels := by
      have ha : raw40539step2 = (fun i j => raw40539step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40539step2 raw40539step1; decide +kernel
      have hl : raw40539step2Labels = raw40539step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40539step1 raw40539step1Labels permutation10 permutation6
    mixedMoment B raw40539step2 raw40539step2Labels = mixedMoment B raw40539step3 raw40539step3Labels := by
      have ha : raw40539step3 = -raw40539step2 := by apply Matrix.ext; change ∀ i j, raw40539step3 i j = -(raw40539step2 i j); unfold raw40539step3 raw40539step2; decide +kernel
      have hl : raw40539step3Labels = raw40539step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node636 node636Labels := by rfl

theorem canonical40540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40540 raw40540Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw40540 raw40540Labels = mixedMoment B raw40540step0 raw40540step0Labels := by
      have hz : ∀ j, raw40540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40540step0 = (fun i j => raw40540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40540step0 raw40540; decide +kernel
      have hl : raw40540step0Labels = raw40540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40540 raw40540Labels permutation346 hz
    mixedMoment B raw40540step0 raw40540step0Labels = mixedMoment B raw40540step1 raw40540step1Labels := by
      have ha : raw40540step1 = (fun i j => raw40540step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40540step1 raw40540step0; decide +kernel
      have hl : raw40540step1Labels = raw40540step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40540step0 raw40540step0Labels permutation55 permutation6
    mixedMoment B raw40540step1 raw40540step1Labels = mixedMoment B raw40540step2 raw40540step2Labels := by
      have ha : raw40540step2 = -raw40540step1 := by apply Matrix.ext; change ∀ i j, raw40540step2 i j = -(raw40540step1 i j); unfold raw40540step2 raw40540step1; decide +kernel
      have hl : raw40540step2Labels = raw40540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node627 node627Labels := by rfl

theorem canonical40541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40541 raw40541Labels = mixedMoment B node637 node637Labels := by
  calc
    mixedMoment B raw40541 raw40541Labels = mixedMoment B raw40541step0 raw40541step0Labels := by
      have ha : raw40541step0 = (fun i j => raw40541 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40541step0 raw40541; decide +kernel
      have hl : raw40541step0Labels = raw40541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40541 raw40541Labels permutation260 permutation6
    mixedMoment B raw40541step0 raw40541step0Labels = mixedMoment B raw40541step1 raw40541step1Labels := by
      have ha : raw40541step1 = -raw40541step0 := by apply Matrix.ext; change ∀ i j, raw40541step1 i j = -(raw40541step0 i j); unfold raw40541step1 raw40541step0; decide +kernel
      have hl : raw40541step1Labels = raw40541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node637 node637Labels := by rfl

theorem canonical40542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40542 raw40542Labels = mixedMoment B node629 node629Labels := by
  calc
    mixedMoment B raw40542 raw40542Labels = mixedMoment B raw40542step0 raw40542step0Labels := by
      have ha : raw40542step0 = (fun i j => raw40542 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40542step0 raw40542; decide +kernel
      have hl : raw40542step0Labels = raw40542Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40542 raw40542Labels permutation224 permutation6
    mixedMoment B raw40542step0 raw40542step0Labels = mixedMoment B raw40542step1 raw40542step1Labels := by
      have ha : raw40542step1 = -raw40542step0 := by apply Matrix.ext; change ∀ i j, raw40542step1 i j = -(raw40542step0 i j); unfold raw40542step1 raw40542step0; decide +kernel
      have hl : raw40542step1Labels = raw40542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node629 node629Labels := by rfl

theorem canonical40543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40543 raw40543Labels = mixedMoment B node640 node640Labels := by
  calc
    mixedMoment B raw40543 raw40543Labels = mixedMoment B raw40543step0 raw40543step0Labels := by
      have hz : ∀ j, raw40543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40543step0 = (fun i j => raw40543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40543step0 raw40543; decide +kernel
      have hl : raw40543step0Labels = raw40543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40543 raw40543Labels permutation434 hz
    mixedMoment B raw40543step0 raw40543step0Labels = mixedMoment B raw40543step1 raw40543step1Labels := by
      have ha : raw40543step1 = (fun i j => raw40543step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40543step1 raw40543step0; decide +kernel
      have hl : raw40543step1Labels = raw40543step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40543step0 raw40543step0Labels permutation50 permutation6
    mixedMoment B raw40543step1 raw40543step1Labels = mixedMoment B raw40543step2 raw40543step2Labels := by
      have ha : raw40543step2 = -raw40543step1 := by apply Matrix.ext; change ∀ i j, raw40543step2 i j = -(raw40543step1 i j); unfold raw40543step2 raw40543step1; decide +kernel
      have hl : raw40543step2Labels = raw40543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node640 node640Labels := by rfl

theorem canonical40544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40544 raw40544Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw40544 raw40544Labels = mixedMoment B raw40544step0 raw40544step0Labels := by
      have hz : ∀ j, raw40544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40544step0 = (fun i j => raw40544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40544step0 raw40544; decide +kernel
      have hl : raw40544step0Labels = raw40544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40544 raw40544Labels permutation434 hz
    mixedMoment B raw40544step0 raw40544step0Labels = mixedMoment B raw40544step1 raw40544step1Labels := by
      have ha : raw40544step1 = (fun i j => raw40544step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40544step1 raw40544step0; decide +kernel
      have hl : raw40544step1Labels = raw40544step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40544step0 raw40544step0Labels permutation44 permutation6
    mixedMoment B raw40544step1 raw40544step1Labels = mixedMoment B raw40544step2 raw40544step2Labels := by
      have ha : raw40544step2 = -raw40544step1 := by apply Matrix.ext; change ∀ i j, raw40544step2 i j = -(raw40544step1 i j); unfold raw40544step2 raw40544step1; decide +kernel
      have hl : raw40544step2Labels = raw40544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node630 node630Labels := by rfl

theorem canonical40545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40545 raw40545Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw40545 raw40545Labels = mixedMoment B raw40545step0 raw40545step0Labels := by
      have hz : ∀ j, raw40545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40545step0 = (fun i j => raw40545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40545step0 raw40545; decide +kernel
      have hl : raw40545step0Labels = raw40545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40545 raw40545Labels permutation434 hz
    mixedMoment B raw40545step0 raw40545step0Labels = mixedMoment B raw40545step1 raw40545step1Labels := by
      have hz : ∀ j, raw40545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40545step1 = (fun i j => raw40545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40545step1 raw40545step0; decide +kernel
      have hl : raw40545step1Labels = raw40545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40545step0 raw40545step0Labels permutation80 hz
    mixedMoment B raw40545step1 raw40545step1Labels = mixedMoment B raw40545step2 raw40545step2Labels := by
      have ha : raw40545step2 = (fun i j => raw40545step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40545step2 raw40545step1; decide +kernel
      have hl : raw40545step2Labels = raw40545step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40545step1 raw40545step1Labels permutation12 permutation6
    mixedMoment B raw40545step2 raw40545step2Labels = mixedMoment B raw40545step3 raw40545step3Labels := by
      have ha : raw40545step3 = -raw40545step2 := by apply Matrix.ext; change ∀ i j, raw40545step3 i j = -(raw40545step2 i j); unfold raw40545step3 raw40545step2; decide +kernel
      have hl : raw40545step3Labels = raw40545step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node641 node641Labels := by rfl

theorem canonical40546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40546 raw40546Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw40546 raw40546Labels = mixedMoment B raw40546step0 raw40546step0Labels := by
      have hz : ∀ j, raw40546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40546step0 = (fun i j => raw40546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40546step0 raw40546; decide +kernel
      have hl : raw40546step0Labels = raw40546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40546 raw40546Labels permutation434 hz
    mixedMoment B raw40546step0 raw40546step0Labels = mixedMoment B raw40546step1 raw40546step1Labels := by
      have hz : ∀ j, raw40546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40546step1 = (fun i j => raw40546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40546step1 raw40546step0; decide +kernel
      have hl : raw40546step1Labels = raw40546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40546step0 raw40546step0Labels permutation80 hz
    mixedMoment B raw40546step1 raw40546step1Labels = mixedMoment B raw40546step2 raw40546step2Labels := by
      have ha : raw40546step2 = (fun i j => raw40546step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40546step2 raw40546step1; decide +kernel
      have hl : raw40546step2Labels = raw40546step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40546step1 raw40546step1Labels permutation10 permutation6
    mixedMoment B raw40546step2 raw40546step2Labels = mixedMoment B raw40546step3 raw40546step3Labels := by
      have ha : raw40546step3 = -raw40546step2 := by apply Matrix.ext; change ∀ i j, raw40546step3 i j = -(raw40546step2 i j); unfold raw40546step3 raw40546step2; decide +kernel
      have hl : raw40546step3Labels = raw40546step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

theorem canonical40547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40547 raw40547Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw40547 raw40547Labels = mixedMoment B raw40547step0 raw40547step0Labels := by
      have hz : ∀ j, raw40547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40547step0 = (fun i j => raw40547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40547step0 raw40547; decide +kernel
      have hl : raw40547step0Labels = raw40547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40547 raw40547Labels permutation346 hz
    mixedMoment B raw40547step0 raw40547step0Labels = mixedMoment B raw40547step1 raw40547step1Labels := by
      have ha : raw40547step1 = (fun i j => raw40547step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40547step1 raw40547step0; decide +kernel
      have hl : raw40547step1Labels = raw40547step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40547step0 raw40547step0Labels permutation54 permutation6
    mixedMoment B raw40547step1 raw40547step1Labels = mixedMoment B raw40547step2 raw40547step2Labels := by
      have ha : raw40547step2 = -raw40547step1 := by apply Matrix.ext; change ∀ i j, raw40547step2 i j = -(raw40547step1 i j); unfold raw40547step2 raw40547step1; decide +kernel
      have hl : raw40547step2Labels = raw40547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node626 node626Labels := by rfl

theorem canonical40548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40548 raw40548Labels = mixedMoment B node643 node643Labels := by
  calc
    mixedMoment B raw40548 raw40548Labels = mixedMoment B raw40548step0 raw40548step0Labels := by
      have hz : ∀ j, raw40548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40548step0 = (fun i j => raw40548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40548step0 raw40548; decide +kernel
      have hl : raw40548step0Labels = raw40548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40548 raw40548Labels permutation434 hz
    mixedMoment B raw40548step0 raw40548step0Labels = mixedMoment B raw40548step1 raw40548step1Labels := by
      have hz : ∀ j, raw40548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40548step1 = (fun i j => raw40548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40548step1 raw40548step0; decide +kernel
      have hl : raw40548step1Labels = raw40548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40548step0 raw40548step0Labels permutation80 hz
    mixedMoment B raw40548step1 raw40548step1Labels = mixedMoment B raw40548step2 raw40548step2Labels := by
      have hz : ∀ j, raw40548step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40548step2 = (fun i j => raw40548step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40548step2 raw40548step1; decide +kernel
      have hl : raw40548step2Labels = raw40548step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40548step1 raw40548step1Labels permutation14 hz
    mixedMoment B raw40548step2 raw40548step2Labels = mixedMoment B raw40548step3 raw40548step3Labels := by
      have ha : raw40548step3 = (fun i j => raw40548step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40548step3 raw40548step2; decide +kernel
      have hl : raw40548step3Labels = raw40548step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40548step2 raw40548step2Labels permutation3 permutation6
    mixedMoment B raw40548step3 raw40548step3Labels = mixedMoment B raw40548step4 raw40548step4Labels := by
      have ha : raw40548step4 = -raw40548step3 := by apply Matrix.ext; change ∀ i j, raw40548step4 i j = -(raw40548step3 i j); unfold raw40548step4 raw40548step3; decide +kernel
      have hl : raw40548step4Labels = raw40548step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node643 node643Labels := by rfl

theorem canonical40549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40549 raw40549Labels = mixedMoment B node591 node591Labels := by
  calc
    mixedMoment B raw40549 raw40549Labels = mixedMoment B raw40549step0 raw40549step0Labels := by
      have hz : ∀ j, raw40549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40549step0 = (fun i j => raw40549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40549step0 raw40549; decide +kernel
      have hl : raw40549step0Labels = raw40549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40549 raw40549Labels permutation434 hz
    mixedMoment B raw40549step0 raw40549step0Labels = mixedMoment B raw40549step1 raw40549step1Labels := by
      have hz : ∀ j, raw40549step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40549step1 = (fun i j => raw40549step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40549step1 raw40549step0; decide +kernel
      have hl : raw40549step1Labels = raw40549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40549step0 raw40549step0Labels permutation80 hz
    mixedMoment B raw40549step1 raw40549step1Labels = mixedMoment B raw40549step2 raw40549step2Labels := by
      have hz : ∀ j, raw40549step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40549step2 = (fun i j => raw40549step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40549step2 raw40549step1; decide +kernel
      have hl : raw40549step2Labels = raw40549step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40549step1 raw40549step1Labels permutation14 hz
    mixedMoment B raw40549step2 raw40549step2Labels = mixedMoment B raw40549step3 raw40549step3Labels := by
      have ha : raw40549step3 = (fun i j => raw40549step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40549step3 raw40549step2; decide +kernel
      have hl : raw40549step3Labels = raw40549step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40549step2 raw40549step2Labels permutation7 permutation6
    _ = mixedMoment B node591 node591Labels := by rfl

theorem canonical40550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40550 raw40550Labels = mixedMoment B node628 node628Labels := by
  calc
    mixedMoment B raw40550 raw40550Labels = mixedMoment B raw40550step0 raw40550step0Labels := by
      have hz : ∀ j, raw40550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40550step0 = (fun i j => raw40550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40550step0 raw40550; decide +kernel
      have hl : raw40550step0Labels = raw40550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40550 raw40550Labels permutation346 hz
    mixedMoment B raw40550step0 raw40550step0Labels = mixedMoment B raw40550step1 raw40550step1Labels := by
      have hz : ∀ j, raw40550step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40550step1 = (fun i j => raw40550step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40550step1 raw40550step0; decide +kernel
      have hl : raw40550step1Labels = raw40550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40550step0 raw40550step0Labels permutation56 hz
    mixedMoment B raw40550step1 raw40550step1Labels = mixedMoment B raw40550step2 raw40550step2Labels := by
      have ha : raw40550step2 = (fun i j => raw40550step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40550step2 raw40550step1; decide +kernel
      have hl : raw40550step2Labels = raw40550step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40550step1 raw40550step1Labels permutation13 permutation6
    mixedMoment B raw40550step2 raw40550step2Labels = mixedMoment B raw40550step3 raw40550step3Labels := by
      have ha : raw40550step3 = -raw40550step2 := by apply Matrix.ext; change ∀ i j, raw40550step3 i j = -(raw40550step2 i j); unfold raw40550step3 raw40550step2; decide +kernel
      have hl : raw40550step3Labels = raw40550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node628 node628Labels := by rfl

theorem canonical40551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40551 raw40551Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw40551 raw40551Labels = mixedMoment B raw40551step0 raw40551step0Labels := by
      have hz : ∀ j, raw40551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40551step0 = (fun i j => raw40551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40551step0 raw40551; decide +kernel
      have hl : raw40551step0Labels = raw40551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40551 raw40551Labels permutation346 hz
    mixedMoment B raw40551step0 raw40551step0Labels = mixedMoment B raw40551step1 raw40551step1Labels := by
      have hz : ∀ j, raw40551step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40551step1 = (fun i j => raw40551step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40551step1 raw40551step0; decide +kernel
      have hl : raw40551step1Labels = raw40551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40551step0 raw40551step0Labels permutation56 hz
    mixedMoment B raw40551step1 raw40551step1Labels = mixedMoment B raw40551step2 raw40551step2Labels := by
      have ha : raw40551step2 = (fun i j => raw40551step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40551step2 raw40551step1; decide +kernel
      have hl : raw40551step2Labels = raw40551step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40551step1 raw40551step1Labels permutation13 permutation6
    mixedMoment B raw40551step2 raw40551step2Labels = mixedMoment B raw40551step3 raw40551step3Labels := by
      have ha : raw40551step3 = -raw40551step2 := by apply Matrix.ext; change ∀ i j, raw40551step3 i j = -(raw40551step2 i j); unfold raw40551step3 raw40551step2; decide +kernel
      have hl : raw40551step3Labels = raw40551step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node635 node635Labels := by rfl

theorem canonical40552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40552 raw40552Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw40552 raw40552Labels = mixedMoment B raw40552step0 raw40552step0Labels := by
      have hz : ∀ j, raw40552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40552step0 = (fun i j => raw40552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40552step0 raw40552; decide +kernel
      have hl : raw40552step0Labels = raw40552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40552 raw40552Labels permutation434 hz
    mixedMoment B raw40552step0 raw40552step0Labels = mixedMoment B raw40552step1 raw40552step1Labels := by
      have hz : ∀ j, raw40552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40552step1 = (fun i j => raw40552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40552step1 raw40552step0; decide +kernel
      have hl : raw40552step1Labels = raw40552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40552step0 raw40552step0Labels permutation80 hz
    mixedMoment B raw40552step1 raw40552step1Labels = mixedMoment B raw40552step2 raw40552step2Labels := by
      have ha : raw40552step2 = (fun i j => raw40552step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40552step2 raw40552step1; decide +kernel
      have hl : raw40552step2Labels = raw40552step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40552step1 raw40552step1Labels permutation31 permutation3
    mixedMoment B raw40552step2 raw40552step2Labels = mixedMoment B raw40552step3 raw40552step3Labels := by
      have ha : raw40552step3 = -raw40552step2 := by apply Matrix.ext; change ∀ i j, raw40552step3 i j = -(raw40552step2 i j); unfold raw40552step3 raw40552step2; decide +kernel
      have hl : raw40552step3Labels = raw40552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2740 node2740Labels := by rfl

theorem canonical40553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40553 raw40553Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw40553 raw40553Labels = mixedMoment B raw40553step0 raw40553step0Labels := by
      have hz : ∀ j, raw40553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40553step0 = (fun i j => raw40553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40553step0 raw40553; decide +kernel
      have hl : raw40553step0Labels = raw40553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40553 raw40553Labels permutation434 hz
    mixedMoment B raw40553step0 raw40553step0Labels = mixedMoment B raw40553step1 raw40553step1Labels := by
      have hz : ∀ j, raw40553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40553step1 = (fun i j => raw40553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40553step1 raw40553step0; decide +kernel
      have hl : raw40553step1Labels = raw40553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40553step0 raw40553step0Labels permutation80 hz
    mixedMoment B raw40553step1 raw40553step1Labels = mixedMoment B raw40553step2 raw40553step2Labels := by
      have ha : raw40553step2 = (fun i j => raw40553step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40553step2 raw40553step1; decide +kernel
      have hl : raw40553step2Labels = raw40553step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40553step1 raw40553step1Labels permutation31 permutation3
    mixedMoment B raw40553step2 raw40553step2Labels = mixedMoment B raw40553step3 raw40553step3Labels := by
      have ha : raw40553step3 = -raw40553step2 := by apply Matrix.ext; change ∀ i j, raw40553step3 i j = -(raw40553step2 i j); unfold raw40553step3 raw40553step2; decide +kernel
      have hl : raw40553step3Labels = raw40553step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical40554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40554 raw40554Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw40554 raw40554Labels = mixedMoment B raw40554step0 raw40554step0Labels := by
      have hz : ∀ j, raw40554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40554step0 = (fun i j => raw40554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40554step0 raw40554; decide +kernel
      have hl : raw40554step0Labels = raw40554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40554 raw40554Labels permutation434 hz
    mixedMoment B raw40554step0 raw40554step0Labels = mixedMoment B raw40554step1 raw40554step1Labels := by
      have hz : ∀ j, raw40554step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40554step1 = (fun i j => raw40554step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40554step1 raw40554step0; decide +kernel
      have hl : raw40554step1Labels = raw40554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40554step0 raw40554step0Labels permutation80 hz
    mixedMoment B raw40554step1 raw40554step1Labels = mixedMoment B raw40554step2 raw40554step2Labels := by
      have ha : raw40554step2 = (fun i j => raw40554step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40554step2 raw40554step1; decide +kernel
      have hl : raw40554step2Labels = raw40554step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40554step1 raw40554step1Labels permutation8 permutation3
    _ = mixedMoment B node3547 node3547Labels := by rfl

theorem canonical40555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40555 raw40555Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw40555 raw40555Labels = mixedMoment B raw40555step0 raw40555step0Labels := by
      have hz : ∀ j, raw40555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40555step0 = (fun i j => raw40555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40555step0 raw40555; decide +kernel
      have hl : raw40555step0Labels = raw40555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40555 raw40555Labels permutation434 hz
    mixedMoment B raw40555step0 raw40555step0Labels = mixedMoment B raw40555step1 raw40555step1Labels := by
      have hz : ∀ j, raw40555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40555step1 = (fun i j => raw40555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40555step1 raw40555step0; decide +kernel
      have hl : raw40555step1Labels = raw40555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40555step0 raw40555step0Labels permutation80 hz
    mixedMoment B raw40555step1 raw40555step1Labels = mixedMoment B raw40555step2 raw40555step2Labels := by
      have ha : raw40555step2 = (fun i j => raw40555step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40555step2 raw40555step1; decide +kernel
      have hl : raw40555step2Labels = raw40555step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40555step1 raw40555step1Labels permutation8 permutation3
    _ = mixedMoment B node3548 node3548Labels := by rfl

theorem canonical40556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40556 raw40556Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw40556 raw40556Labels = mixedMoment B raw40556step0 raw40556step0Labels := by
      have hz : ∀ j, raw40556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40556step0 = (fun i j => raw40556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40556step0 raw40556; decide +kernel
      have hl : raw40556step0Labels = raw40556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40556 raw40556Labels permutation434 hz
    mixedMoment B raw40556step0 raw40556step0Labels = mixedMoment B raw40556step1 raw40556step1Labels := by
      have hz : ∀ j, raw40556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40556step1 = (fun i j => raw40556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40556step1 raw40556step0; decide +kernel
      have hl : raw40556step1Labels = raw40556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40556step0 raw40556step0Labels permutation80 hz
    mixedMoment B raw40556step1 raw40556step1Labels = mixedMoment B raw40556step2 raw40556step2Labels := by
      have ha : raw40556step2 = (fun i j => raw40556step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40556step2 raw40556step1; decide +kernel
      have hl : raw40556step2Labels = raw40556step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40556step1 raw40556step1Labels permutation8 permutation3
    _ = mixedMoment B node3549 node3549Labels := by rfl

theorem canonical40557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40557 raw40557Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw40557 raw40557Labels = mixedMoment B raw40557step0 raw40557step0Labels := by
      have hz : ∀ j, raw40557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40557step0 = (fun i j => raw40557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40557step0 raw40557; decide +kernel
      have hl : raw40557step0Labels = raw40557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40557 raw40557Labels permutation346 hz
    mixedMoment B raw40557step0 raw40557step0Labels = mixedMoment B raw40557step1 raw40557step1Labels := by
      have ha : raw40557step1 = (fun i j => raw40557step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40557step1 raw40557step0; decide +kernel
      have hl : raw40557step1Labels = raw40557step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40557step0 raw40557step0Labels permutation145 permutation3
    mixedMoment B raw40557step1 raw40557step1Labels = mixedMoment B raw40557step2 raw40557step2Labels := by
      have ha : raw40557step2 = -raw40557step1 := by apply Matrix.ext; change ∀ i j, raw40557step2 i j = -(raw40557step1 i j); unfold raw40557step2 raw40557step1; decide +kernel
      have hl : raw40557step2Labels = raw40557step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3075 node3075Labels := by rfl

theorem canonical40558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40558 raw40558Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw40558 raw40558Labels = mixedMoment B raw40558step0 raw40558step0Labels := by
      have hz : ∀ j, raw40558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40558step0 = (fun i j => raw40558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40558step0 raw40558; decide +kernel
      have hl : raw40558step0Labels = raw40558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40558 raw40558Labels permutation346 hz
    mixedMoment B raw40558step0 raw40558step0Labels = mixedMoment B raw40558step1 raw40558step1Labels := by
      have ha : raw40558step1 = (fun i j => raw40558step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40558step1 raw40558step0; decide +kernel
      have hl : raw40558step1Labels = raw40558step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40558step0 raw40558step0Labels permutation32 permutation3
    _ = mixedMoment B node3534 node3534Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1088 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1088) =
      Integer.Sparse.eval keyMomentRow1088 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1088).leftCharge (GramAssembly.key 1088).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1324) := by
    have ha : gramCharges (GramAssembly.key 1088).leftCharge (GramAssembly.key 1088).rightCharge = raw40527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40527 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1088).leftCharge (GramAssembly.key 1088).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1088, Integer.Sparse.eval]

theorem keyMoment1089 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1089) =
      Integer.Sparse.eval keyMomentRow1089 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1089).leftCharge (GramAssembly.key 1089).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 911) := by
    have ha : gramCharges (GramAssembly.key 1089).leftCharge (GramAssembly.key 1089).rightCharge = raw40528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40528 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1089).leftCharge (GramAssembly.key 1089).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1089, Integer.Sparse.eval]

theorem keyMoment1090 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1090) =
      Integer.Sparse.eval keyMomentRow1090 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1090).leftCharge (GramAssembly.key 1090).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1333) := by
    have ha : gramCharges (GramAssembly.key 1090).leftCharge (GramAssembly.key 1090).rightCharge = raw40529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40529 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1090).leftCharge (GramAssembly.key 1090).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1090, Integer.Sparse.eval]

theorem keyMoment1091 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1091) =
      Integer.Sparse.eval keyMomentRow1091 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1091).leftCharge (GramAssembly.key 1091).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 654) := by
    have ha : gramCharges (GramAssembly.key 1091).leftCharge (GramAssembly.key 1091).rightCharge = raw40530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40530 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1091).leftCharge (GramAssembly.key 1091).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1091, Integer.Sparse.eval]

theorem keyMoment1092 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1092) =
      Integer.Sparse.eval keyMomentRow1092 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1092).leftCharge (GramAssembly.key 1092).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 639) := by
    have ha : gramCharges (GramAssembly.key 1092).leftCharge (GramAssembly.key 1092).rightCharge = raw40531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40531 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1092).leftCharge (GramAssembly.key 1092).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1092, Integer.Sparse.eval]

theorem keyMoment1093 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1093) =
      Integer.Sparse.eval keyMomentRow1093 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1093).leftCharge (GramAssembly.key 1093).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 634) := by
    have ha : gramCharges (GramAssembly.key 1093).leftCharge (GramAssembly.key 1093).rightCharge = raw40532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40532 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1093).leftCharge (GramAssembly.key 1093).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1093, Integer.Sparse.eval]

theorem keyMoment1094 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1094) =
      Integer.Sparse.eval keyMomentRow1094 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1094).leftCharge (GramAssembly.key 1094).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 624) := by
    have ha : gramCharges (GramAssembly.key 1094).leftCharge (GramAssembly.key 1094).rightCharge = raw40533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40533 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1094).leftCharge (GramAssembly.key 1094).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1094, Integer.Sparse.eval]

theorem keyMoment1095 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1095) =
      Integer.Sparse.eval keyMomentRow1095 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1095).leftCharge (GramAssembly.key 1095).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 653) := by
    have ha : gramCharges (GramAssembly.key 1095).leftCharge (GramAssembly.key 1095).rightCharge = raw40534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40534 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1095).leftCharge (GramAssembly.key 1095).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1095, Integer.Sparse.eval]

theorem keyMoment1096 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1096) =
      Integer.Sparse.eval keyMomentRow1096 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1096).leftCharge (GramAssembly.key 1096).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 638) := by
    have ha : gramCharges (GramAssembly.key 1096).leftCharge (GramAssembly.key 1096).rightCharge = raw40535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40535 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1096).leftCharge (GramAssembly.key 1096).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1096, Integer.Sparse.eval]

theorem keyMoment1097 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1097) =
      Integer.Sparse.eval keyMomentRow1097 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1097).leftCharge (GramAssembly.key 1097).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 631) := by
    have ha : gramCharges (GramAssembly.key 1097).leftCharge (GramAssembly.key 1097).rightCharge = raw40536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40536 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1097).leftCharge (GramAssembly.key 1097).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1097, Integer.Sparse.eval]

theorem keyMoment1098 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1098) =
      Integer.Sparse.eval keyMomentRow1098 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1098).leftCharge (GramAssembly.key 1098).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 623) := by
    have ha : gramCharges (GramAssembly.key 1098).leftCharge (GramAssembly.key 1098).rightCharge = raw40537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40537 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1098).leftCharge (GramAssembly.key 1098).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1098, Integer.Sparse.eval]

theorem keyMoment1099 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1099) =
      Integer.Sparse.eval keyMomentRow1099 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1099).leftCharge (GramAssembly.key 1099).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 642) := by
    have ha : gramCharges (GramAssembly.key 1099).leftCharge (GramAssembly.key 1099).rightCharge = raw40538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40538 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1099).leftCharge (GramAssembly.key 1099).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1099, Integer.Sparse.eval]

theorem keyMoment1100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1100) =
      Integer.Sparse.eval keyMomentRow1100 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1100).leftCharge (GramAssembly.key 1100).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 636) := by
    have ha : gramCharges (GramAssembly.key 1100).leftCharge (GramAssembly.key 1100).rightCharge = raw40539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40539 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1100).leftCharge (GramAssembly.key 1100).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1100, Integer.Sparse.eval]

theorem keyMoment1101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1101) =
      Integer.Sparse.eval keyMomentRow1101 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1101).leftCharge (GramAssembly.key 1101).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 627) := by
    have ha : gramCharges (GramAssembly.key 1101).leftCharge (GramAssembly.key 1101).rightCharge = raw40540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40540 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1101).leftCharge (GramAssembly.key 1101).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1101, Integer.Sparse.eval]

theorem keyMoment1102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1102) =
      Integer.Sparse.eval keyMomentRow1102 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1102).leftCharge (GramAssembly.key 1102).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 637) := by
    have ha : gramCharges (GramAssembly.key 1102).leftCharge (GramAssembly.key 1102).rightCharge = raw40541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40541 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1102).leftCharge (GramAssembly.key 1102).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1102, Integer.Sparse.eval]

theorem keyMoment1103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1103) =
      Integer.Sparse.eval keyMomentRow1103 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1103).leftCharge (GramAssembly.key 1103).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 629) := by
    have ha : gramCharges (GramAssembly.key 1103).leftCharge (GramAssembly.key 1103).rightCharge = raw40542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40542 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1103).leftCharge (GramAssembly.key 1103).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1103, Integer.Sparse.eval]

theorem keyMoment1104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1104) =
      Integer.Sparse.eval keyMomentRow1104 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1104).leftCharge (GramAssembly.key 1104).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 640) := by
    have ha : gramCharges (GramAssembly.key 1104).leftCharge (GramAssembly.key 1104).rightCharge = raw40543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40543 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1104).leftCharge (GramAssembly.key 1104).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1104, Integer.Sparse.eval]

theorem keyMoment1105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1105) =
      Integer.Sparse.eval keyMomentRow1105 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1105).leftCharge (GramAssembly.key 1105).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 630) := by
    have ha : gramCharges (GramAssembly.key 1105).leftCharge (GramAssembly.key 1105).rightCharge = raw40544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40544 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1105).leftCharge (GramAssembly.key 1105).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1105, Integer.Sparse.eval]

theorem keyMoment1106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1106) =
      Integer.Sparse.eval keyMomentRow1106 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1106).leftCharge (GramAssembly.key 1106).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 641) := by
    have ha : gramCharges (GramAssembly.key 1106).leftCharge (GramAssembly.key 1106).rightCharge = raw40545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40545 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1106).leftCharge (GramAssembly.key 1106).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1106, Integer.Sparse.eval]

theorem keyMoment1107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1107) =
      Integer.Sparse.eval keyMomentRow1107 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1107).leftCharge (GramAssembly.key 1107).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 633) := by
    have ha : gramCharges (GramAssembly.key 1107).leftCharge (GramAssembly.key 1107).rightCharge = raw40546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40546 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1107).leftCharge (GramAssembly.key 1107).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1107, Integer.Sparse.eval]

theorem keyMoment1108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1108) =
      Integer.Sparse.eval keyMomentRow1108 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1108).leftCharge (GramAssembly.key 1108).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 626) := by
    have ha : gramCharges (GramAssembly.key 1108).leftCharge (GramAssembly.key 1108).rightCharge = raw40547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40547 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1108).leftCharge (GramAssembly.key 1108).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1108, Integer.Sparse.eval]

theorem keyMoment1109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1109) =
      Integer.Sparse.eval keyMomentRow1109 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1109).leftCharge (GramAssembly.key 1109).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 643) := by
    have ha : gramCharges (GramAssembly.key 1109).leftCharge (GramAssembly.key 1109).rightCharge = raw40548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40548 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1109).leftCharge (GramAssembly.key 1109).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1109, Integer.Sparse.eval]

theorem keyMoment1110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1110) =
      Integer.Sparse.eval keyMomentRow1110 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1110).leftCharge (GramAssembly.key 1110).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 591) := by
    have ha : gramCharges (GramAssembly.key 1110).leftCharge (GramAssembly.key 1110).rightCharge = raw40549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40549 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1110).leftCharge (GramAssembly.key 1110).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1110, Integer.Sparse.eval]

theorem keyMoment1111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1111) =
      Integer.Sparse.eval keyMomentRow1111 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1111).leftCharge (GramAssembly.key 1111).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 628) := by
    have ha : gramCharges (GramAssembly.key 1111).leftCharge (GramAssembly.key 1111).rightCharge = raw40550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40550 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1111).leftCharge (GramAssembly.key 1111).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1111, Integer.Sparse.eval]

theorem keyMoment1112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1112) =
      Integer.Sparse.eval keyMomentRow1112 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1112).leftCharge (GramAssembly.key 1112).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 635) := by
    have ha : gramCharges (GramAssembly.key 1112).leftCharge (GramAssembly.key 1112).rightCharge = raw40551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40551 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1112).leftCharge (GramAssembly.key 1112).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1112, Integer.Sparse.eval]

theorem keyMoment1113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1113) =
      Integer.Sparse.eval keyMomentRow1113 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1113).leftCharge (GramAssembly.key 1113).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2740) := by
    have ha : gramCharges (GramAssembly.key 1113).leftCharge (GramAssembly.key 1113).rightCharge = raw40552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40552 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1113).leftCharge (GramAssembly.key 1113).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1113, Integer.Sparse.eval]

theorem keyMoment1114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1114) =
      Integer.Sparse.eval keyMomentRow1114 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1114).leftCharge (GramAssembly.key 1114).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 1114).leftCharge (GramAssembly.key 1114).rightCharge = raw40553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40553 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1114).leftCharge (GramAssembly.key 1114).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1114, Integer.Sparse.eval]

theorem keyMoment1115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1115) =
      Integer.Sparse.eval keyMomentRow1115 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1115).leftCharge (GramAssembly.key 1115).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3547) := by
    have ha : gramCharges (GramAssembly.key 1115).leftCharge (GramAssembly.key 1115).rightCharge = raw40554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40554 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1115).leftCharge (GramAssembly.key 1115).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1115, Integer.Sparse.eval]

theorem keyMoment1116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1116) =
      Integer.Sparse.eval keyMomentRow1116 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1116).leftCharge (GramAssembly.key 1116).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3548) := by
    have ha : gramCharges (GramAssembly.key 1116).leftCharge (GramAssembly.key 1116).rightCharge = raw40555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40555 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1116).leftCharge (GramAssembly.key 1116).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1116, Integer.Sparse.eval]

theorem keyMoment1117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1117) =
      Integer.Sparse.eval keyMomentRow1117 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1117).leftCharge (GramAssembly.key 1117).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3549) := by
    have ha : gramCharges (GramAssembly.key 1117).leftCharge (GramAssembly.key 1117).rightCharge = raw40556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40556 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1117).leftCharge (GramAssembly.key 1117).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1117, Integer.Sparse.eval]

theorem keyMoment1118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1118) =
      Integer.Sparse.eval keyMomentRow1118 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1118).leftCharge (GramAssembly.key 1118).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3075) := by
    have ha : gramCharges (GramAssembly.key 1118).leftCharge (GramAssembly.key 1118).rightCharge = raw40557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40557 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1118).leftCharge (GramAssembly.key 1118).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1118, Integer.Sparse.eval]

theorem keyMoment1119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1119) =
      Integer.Sparse.eval keyMomentRow1119 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1119).leftCharge (GramAssembly.key 1119).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3534) := by
    have ha : gramCharges (GramAssembly.key 1119).leftCharge (GramAssembly.key 1119).rightCharge = raw40558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40558 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1119).leftCharge (GramAssembly.key 1119).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1119, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1088 : keyMomentRows (1088 : Fin 2886) =
    keyMomentRow1088 := by decide +kernel

theorem keyMomentRowsAt1089 : keyMomentRows (1089 : Fin 2886) =
    keyMomentRow1089 := by decide +kernel

theorem keyMomentRowsAt1090 : keyMomentRows (1090 : Fin 2886) =
    keyMomentRow1090 := by decide +kernel

theorem keyMomentRowsAt1091 : keyMomentRows (1091 : Fin 2886) =
    keyMomentRow1091 := by decide +kernel

theorem keyMomentRowsAt1092 : keyMomentRows (1092 : Fin 2886) =
    keyMomentRow1092 := by decide +kernel

theorem keyMomentRowsAt1093 : keyMomentRows (1093 : Fin 2886) =
    keyMomentRow1093 := by decide +kernel

theorem keyMomentRowsAt1094 : keyMomentRows (1094 : Fin 2886) =
    keyMomentRow1094 := by decide +kernel

theorem keyMomentRowsAt1095 : keyMomentRows (1095 : Fin 2886) =
    keyMomentRow1095 := by decide +kernel

theorem keyMomentRowsAt1096 : keyMomentRows (1096 : Fin 2886) =
    keyMomentRow1096 := by decide +kernel

theorem keyMomentRowsAt1097 : keyMomentRows (1097 : Fin 2886) =
    keyMomentRow1097 := by decide +kernel

theorem keyMomentRowsAt1098 : keyMomentRows (1098 : Fin 2886) =
    keyMomentRow1098 := by decide +kernel

theorem keyMomentRowsAt1099 : keyMomentRows (1099 : Fin 2886) =
    keyMomentRow1099 := by decide +kernel

theorem keyMomentRowsAt1100 : keyMomentRows (1100 : Fin 2886) =
    keyMomentRow1100 := by decide +kernel

theorem keyMomentRowsAt1101 : keyMomentRows (1101 : Fin 2886) =
    keyMomentRow1101 := by decide +kernel

theorem keyMomentRowsAt1102 : keyMomentRows (1102 : Fin 2886) =
    keyMomentRow1102 := by decide +kernel

theorem keyMomentRowsAt1103 : keyMomentRows (1103 : Fin 2886) =
    keyMomentRow1103 := by decide +kernel

theorem keyMomentRowsAt1104 : keyMomentRows (1104 : Fin 2886) =
    keyMomentRow1104 := by decide +kernel

theorem keyMomentRowsAt1105 : keyMomentRows (1105 : Fin 2886) =
    keyMomentRow1105 := by decide +kernel

theorem keyMomentRowsAt1106 : keyMomentRows (1106 : Fin 2886) =
    keyMomentRow1106 := by decide +kernel

theorem keyMomentRowsAt1107 : keyMomentRows (1107 : Fin 2886) =
    keyMomentRow1107 := by decide +kernel

theorem keyMomentRowsAt1108 : keyMomentRows (1108 : Fin 2886) =
    keyMomentRow1108 := by decide +kernel

theorem keyMomentRowsAt1109 : keyMomentRows (1109 : Fin 2886) =
    keyMomentRow1109 := by decide +kernel

theorem keyMomentRowsAt1110 : keyMomentRows (1110 : Fin 2886) =
    keyMomentRow1110 := by decide +kernel

theorem keyMomentRowsAt1111 : keyMomentRows (1111 : Fin 2886) =
    keyMomentRow1111 := by decide +kernel

theorem keyMomentRowsAt1112 : keyMomentRows (1112 : Fin 2886) =
    keyMomentRow1112 := by decide +kernel

theorem keyMomentRowsAt1113 : keyMomentRows (1113 : Fin 2886) =
    keyMomentRow1113 := by decide +kernel

theorem keyMomentRowsAt1114 : keyMomentRows (1114 : Fin 2886) =
    keyMomentRow1114 := by decide +kernel

theorem keyMomentRowsAt1115 : keyMomentRows (1115 : Fin 2886) =
    keyMomentRow1115 := by decide +kernel

theorem keyMomentRowsAt1116 : keyMomentRows (1116 : Fin 2886) =
    keyMomentRow1116 := by decide +kernel

theorem keyMomentRowsAt1117 : keyMomentRows (1117 : Fin 2886) =
    keyMomentRow1117 := by decide +kernel

theorem keyMomentRowsAt1118 : keyMomentRows (1118 : Fin 2886) =
    keyMomentRow1118 := by decide +kernel

theorem keyMomentRowsAt1119 : keyMomentRows (1119 : Fin 2886) =
    keyMomentRow1119 := by decide +kernel

theorem keyMomentChunkSound34_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 34) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1088 ∨ k.val = 1089 ∨ k.val = 1090 ∨ k.val = 1091 ∨ k.val = 1092 ∨ k.val = 1093 ∨ k.val = 1094 ∨ k.val = 1095 ∨ k.val = 1096 ∨ k.val = 1097 ∨ k.val = 1098 ∨ k.val = 1099 ∨ k.val = 1100 ∨ k.val = 1101 ∨ k.val = 1102 ∨ k.val = 1103 ∨ k.val = 1104 ∨ k.val = 1105 ∨ k.val = 1106 ∨ k.val = 1107 ∨ k.val = 1108 ∨ k.val = 1109 ∨ k.val = 1110 ∨ k.val = 1111 ∨ k.val = 1112 ∨ k.val = 1113 ∨ k.val = 1114 ∨ k.val = 1115 ∨ k.val = 1116 ∨ k.val = 1117 ∨ k.val = 1118 ∨ k.val = 1119 := by omega
  rcases heq with h1088 | h1089 | h1090 | h1091 | h1092 | h1093 | h1094 | h1095 | h1096 | h1097 | h1098 | h1099 | h1100 | h1101 | h1102 | h1103 | h1104 | h1105 | h1106 | h1107 | h1108 | h1109 | h1110 | h1111 | h1112 | h1113 | h1114 | h1115 | h1116 | h1117 | h1118 | h1119
  · have he : k = (1088 : Fin 2886) := Fin.ext h1088
    subst k
    rw [keyMomentRowsAt1088]
    exact keyMoment1088 B hB
  · have he : k = (1089 : Fin 2886) := Fin.ext h1089
    subst k
    rw [keyMomentRowsAt1089]
    exact keyMoment1089 B hB
  · have he : k = (1090 : Fin 2886) := Fin.ext h1090
    subst k
    rw [keyMomentRowsAt1090]
    exact keyMoment1090 B hB
  · have he : k = (1091 : Fin 2886) := Fin.ext h1091
    subst k
    rw [keyMomentRowsAt1091]
    exact keyMoment1091 B hB
  · have he : k = (1092 : Fin 2886) := Fin.ext h1092
    subst k
    rw [keyMomentRowsAt1092]
    exact keyMoment1092 B hB
  · have he : k = (1093 : Fin 2886) := Fin.ext h1093
    subst k
    rw [keyMomentRowsAt1093]
    exact keyMoment1093 B hB
  · have he : k = (1094 : Fin 2886) := Fin.ext h1094
    subst k
    rw [keyMomentRowsAt1094]
    exact keyMoment1094 B hB
  · have he : k = (1095 : Fin 2886) := Fin.ext h1095
    subst k
    rw [keyMomentRowsAt1095]
    exact keyMoment1095 B hB
  · have he : k = (1096 : Fin 2886) := Fin.ext h1096
    subst k
    rw [keyMomentRowsAt1096]
    exact keyMoment1096 B hB
  · have he : k = (1097 : Fin 2886) := Fin.ext h1097
    subst k
    rw [keyMomentRowsAt1097]
    exact keyMoment1097 B hB
  · have he : k = (1098 : Fin 2886) := Fin.ext h1098
    subst k
    rw [keyMomentRowsAt1098]
    exact keyMoment1098 B hB
  · have he : k = (1099 : Fin 2886) := Fin.ext h1099
    subst k
    rw [keyMomentRowsAt1099]
    exact keyMoment1099 B hB
  · have he : k = (1100 : Fin 2886) := Fin.ext h1100
    subst k
    rw [keyMomentRowsAt1100]
    exact keyMoment1100 B hB
  · have he : k = (1101 : Fin 2886) := Fin.ext h1101
    subst k
    rw [keyMomentRowsAt1101]
    exact keyMoment1101 B hB
  · have he : k = (1102 : Fin 2886) := Fin.ext h1102
    subst k
    rw [keyMomentRowsAt1102]
    exact keyMoment1102 B hB
  · have he : k = (1103 : Fin 2886) := Fin.ext h1103
    subst k
    rw [keyMomentRowsAt1103]
    exact keyMoment1103 B hB
  · have he : k = (1104 : Fin 2886) := Fin.ext h1104
    subst k
    rw [keyMomentRowsAt1104]
    exact keyMoment1104 B hB
  · have he : k = (1105 : Fin 2886) := Fin.ext h1105
    subst k
    rw [keyMomentRowsAt1105]
    exact keyMoment1105 B hB
  · have he : k = (1106 : Fin 2886) := Fin.ext h1106
    subst k
    rw [keyMomentRowsAt1106]
    exact keyMoment1106 B hB
  · have he : k = (1107 : Fin 2886) := Fin.ext h1107
    subst k
    rw [keyMomentRowsAt1107]
    exact keyMoment1107 B hB
  · have he : k = (1108 : Fin 2886) := Fin.ext h1108
    subst k
    rw [keyMomentRowsAt1108]
    exact keyMoment1108 B hB
  · have he : k = (1109 : Fin 2886) := Fin.ext h1109
    subst k
    rw [keyMomentRowsAt1109]
    exact keyMoment1109 B hB
  · have he : k = (1110 : Fin 2886) := Fin.ext h1110
    subst k
    rw [keyMomentRowsAt1110]
    exact keyMoment1110 B hB
  · have he : k = (1111 : Fin 2886) := Fin.ext h1111
    subst k
    rw [keyMomentRowsAt1111]
    exact keyMoment1111 B hB
  · have he : k = (1112 : Fin 2886) := Fin.ext h1112
    subst k
    rw [keyMomentRowsAt1112]
    exact keyMoment1112 B hB
  · have he : k = (1113 : Fin 2886) := Fin.ext h1113
    subst k
    rw [keyMomentRowsAt1113]
    exact keyMoment1113 B hB
  · have he : k = (1114 : Fin 2886) := Fin.ext h1114
    subst k
    rw [keyMomentRowsAt1114]
    exact keyMoment1114 B hB
  · have he : k = (1115 : Fin 2886) := Fin.ext h1115
    subst k
    rw [keyMomentRowsAt1115]
    exact keyMoment1115 B hB
  · have he : k = (1116 : Fin 2886) := Fin.ext h1116
    subst k
    rw [keyMomentRowsAt1116]
    exact keyMoment1116 B hB
  · have he : k = (1117 : Fin 2886) := Fin.ext h1117
    subst k
    rw [keyMomentRowsAt1117]
    exact keyMoment1117 B hB
  · have he : k = (1118 : Fin 2886) := Fin.ext h1118
    subst k
    rw [keyMomentRowsAt1118]
    exact keyMoment1118 B hB
  · have he : k = (1119 : Fin 2886) := Fin.ext h1119
    subst k
    rw [keyMomentRowsAt1119]
    exact keyMoment1119 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound34_e_oai
