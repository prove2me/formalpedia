-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:32.115215+00:00
-- url     : https://prove2.me/submissions/580b0637-0510-44a3-9f3e-b3b6aa9b21bc

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E111
import Definitions.Def_OAIQ106E115
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40432 raw40432Labels = mixedMoment B node3189 node3189Labels := by
  calc
    mixedMoment B raw40432 raw40432Labels = mixedMoment B raw40432step0 raw40432step0Labels := by
      have ha : raw40432step0 = (fun i j => raw40432 (permutation187 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40432step0 raw40432; decide +kernel
      have hl : raw40432step0Labels = raw40432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40432 raw40432Labels permutation187 permutation6
    mixedMoment B raw40432step0 raw40432step0Labels = mixedMoment B raw40432step1 raw40432step1Labels := by
      have ha : raw40432step1 = -raw40432step0 := by apply Matrix.ext; change ∀ i j, raw40432step1 i j = -(raw40432step0 i j); unfold raw40432step1 raw40432step0; decide +kernel
      have hl : raw40432step1Labels = raw40432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3189 node3189Labels := by rfl

theorem canonical40433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40433 raw40433Labels = mixedMoment B node2800 node2800Labels := by
  calc
    mixedMoment B raw40433 raw40433Labels = mixedMoment B raw40433step0 raw40433step0Labels := by
      have ha : raw40433step0 = (fun i j => raw40433 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40433step0 raw40433; decide +kernel
      have hl : raw40433step0Labels = raw40433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40433 raw40433Labels permutation620 permutation6
    _ = mixedMoment B node2800 node2800Labels := by rfl

theorem canonical40434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40434 raw40434Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw40434 raw40434Labels = mixedMoment B raw40434step0 raw40434step0Labels := by
      have ha : raw40434step0 = (fun i j => raw40434 (permutation256 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40434step0 raw40434; decide +kernel
      have hl : raw40434step0Labels = raw40434Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40434 raw40434Labels permutation256 permutation6
    mixedMoment B raw40434step0 raw40434step0Labels = mixedMoment B raw40434step1 raw40434step1Labels := by
      have ha : raw40434step1 = -raw40434step0 := by apply Matrix.ext; change ∀ i j, raw40434step1 i j = -(raw40434step0 i j); unfold raw40434step1 raw40434step0; decide +kernel
      have hl : raw40434step1Labels = raw40434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3162 node3162Labels := by rfl

theorem canonical40435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40435 raw40435Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw40435 raw40435Labels = mixedMoment B raw40435step0 raw40435step0Labels := by
      have ha : raw40435step0 = (fun i j => raw40435 (permutation193 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40435step0 raw40435; decide +kernel
      have hl : raw40435step0Labels = raw40435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40435 raw40435Labels permutation193 permutation6
    mixedMoment B raw40435step0 raw40435step0Labels = mixedMoment B raw40435step1 raw40435step1Labels := by
      have ha : raw40435step1 = -raw40435step0 := by apply Matrix.ext; change ∀ i j, raw40435step1 i j = -(raw40435step0 i j); unfold raw40435step1 raw40435step0; decide +kernel
      have hl : raw40435step1Labels = raw40435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3199 node3199Labels := by rfl

theorem canonical40436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40436 raw40436Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw40436 raw40436Labels = mixedMoment B raw40436step0 raw40436step0Labels := by
      have ha : raw40436step0 = (fun i j => raw40436 (permutation199 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40436step0 raw40436; decide +kernel
      have hl : raw40436step0Labels = raw40436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40436 raw40436Labels permutation199 permutation6
    mixedMoment B raw40436step0 raw40436step0Labels = mixedMoment B raw40436step1 raw40436step1Labels := by
      have ha : raw40436step1 = -raw40436step0 := by apply Matrix.ext; change ∀ i j, raw40436step1 i j = -(raw40436step0 i j); unfold raw40436step1 raw40436step0; decide +kernel
      have hl : raw40436step1Labels = raw40436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3133 node3133Labels := by rfl

theorem canonical40437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40437 raw40437Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw40437 raw40437Labels = mixedMoment B raw40437step0 raw40437step0Labels := by
      have ha : raw40437step0 = (fun i j => raw40437 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40437step0 raw40437; decide +kernel
      have hl : raw40437step0Labels = raw40437Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40437 raw40437Labels permutation674 permutation3
    mixedMoment B raw40437step0 raw40437step0Labels = mixedMoment B raw40437step1 raw40437step1Labels := by
      have ha : raw40437step1 = -raw40437step0 := by apply Matrix.ext; change ∀ i j, raw40437step1 i j = -(raw40437step0 i j); unfold raw40437step1 raw40437step0; decide +kernel
      have hl : raw40437step1Labels = raw40437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2707 node2707Labels := by rfl

theorem canonical40438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40438 raw40438Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw40438 raw40438Labels = mixedMoment B raw40438step0 raw40438step0Labels := by
      have ha : raw40438step0 = (fun i j => raw40438 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40438step0 raw40438; decide +kernel
      have hl : raw40438step0Labels = raw40438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40438 raw40438Labels permutation260 permutation6
    mixedMoment B raw40438step0 raw40438step0Labels = mixedMoment B raw40438step1 raw40438step1Labels := by
      have ha : raw40438step1 = -raw40438step0 := by apply Matrix.ext; change ∀ i j, raw40438step1 i j = -(raw40438step0 i j); unfold raw40438step1 raw40438step0; decide +kernel
      have hl : raw40438step1Labels = raw40438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3155 node3155Labels := by rfl

theorem canonical40439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40439 raw40439Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw40439 raw40439Labels = mixedMoment B raw40439step0 raw40439step0Labels := by
      have ha : raw40439step0 = (fun i j => raw40439 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40439step0 raw40439; decide +kernel
      have hl : raw40439step0Labels = raw40439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40439 raw40439Labels permutation260 permutation6
    mixedMoment B raw40439step0 raw40439step0Labels = mixedMoment B raw40439step1 raw40439step1Labels := by
      have ha : raw40439step1 = -raw40439step0 := by apply Matrix.ext; change ∀ i j, raw40439step1 i j = -(raw40439step0 i j); unfold raw40439step1 raw40439step0; decide +kernel
      have hl : raw40439step1Labels = raw40439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical40440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40440 raw40440Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw40440 raw40440Labels = mixedMoment B raw40440step0 raw40440step0Labels := by
      have ha : raw40440step0 = (fun i j => raw40440 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40440step0 raw40440; decide +kernel
      have hl : raw40440step0Labels = raw40440Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40440 raw40440Labels permutation240 permutation6
    mixedMoment B raw40440step0 raw40440step0Labels = mixedMoment B raw40440step1 raw40440step1Labels := by
      have ha : raw40440step1 = -raw40440step0 := by apply Matrix.ext; change ∀ i j, raw40440step1 i j = -(raw40440step0 i j); unfold raw40440step1 raw40440step0; decide +kernel
      have hl : raw40440step1Labels = raw40440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3179 node3179Labels := by rfl

theorem canonical40441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40441 raw40441Labels = mixedMoment B node3130 node3130Labels := by
  calc
    mixedMoment B raw40441 raw40441Labels = mixedMoment B raw40441step0 raw40441step0Labels := by
      have ha : raw40441step0 = (fun i j => raw40441 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40441step0 raw40441; decide +kernel
      have hl : raw40441step0Labels = raw40441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40441 raw40441Labels permutation224 permutation6
    mixedMoment B raw40441step0 raw40441step0Labels = mixedMoment B raw40441step1 raw40441step1Labels := by
      have ha : raw40441step1 = -raw40441step0 := by apply Matrix.ext; change ∀ i j, raw40441step1 i j = -(raw40441step0 i j); unfold raw40441step1 raw40441step0; decide +kernel
      have hl : raw40441step1Labels = raw40441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3130 node3130Labels := by rfl

theorem canonical40442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40442 raw40442Labels = mixedMoment B node3158 node3158Labels := by
  calc
    mixedMoment B raw40442 raw40442Labels = mixedMoment B raw40442step0 raw40442step0Labels := by
      have hz : ∀ j, raw40442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40442step0 = (fun i j => raw40442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40442step0 raw40442; decide +kernel
      have hl : raw40442step0Labels = raw40442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40442 raw40442Labels permutation434 hz
    mixedMoment B raw40442step0 raw40442step0Labels = mixedMoment B raw40442step1 raw40442step1Labels := by
      have ha : raw40442step1 = (fun i j => raw40442step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40442step1 raw40442step0; decide +kernel
      have hl : raw40442step1Labels = raw40442step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40442step0 raw40442step0Labels permutation50 permutation6
    mixedMoment B raw40442step1 raw40442step1Labels = mixedMoment B raw40442step2 raw40442step2Labels := by
      have ha : raw40442step2 = -raw40442step1 := by apply Matrix.ext; change ∀ i j, raw40442step2 i j = -(raw40442step1 i j); unfold raw40442step2 raw40442step1; decide +kernel
      have hl : raw40442step2Labels = raw40442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3158 node3158Labels := by rfl

theorem canonical40443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40443 raw40443Labels = mixedMoment B node2899 node2899Labels := by
  calc
    mixedMoment B raw40443 raw40443Labels = mixedMoment B raw40443step0 raw40443step0Labels := by
      have hz : ∀ j, raw40443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40443step0 = (fun i j => raw40443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40443step0 raw40443; decide +kernel
      have hl : raw40443step0Labels = raw40443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40443 raw40443Labels permutation434 hz
    mixedMoment B raw40443step0 raw40443step0Labels = mixedMoment B raw40443step1 raw40443step1Labels := by
      have ha : raw40443step1 = (fun i j => raw40443step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40443step1 raw40443step0; decide +kernel
      have hl : raw40443step1Labels = raw40443step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40443step0 raw40443step0Labels permutation137 permutation6
    _ = mixedMoment B node2899 node2899Labels := by rfl

theorem canonical40444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40444 raw40444Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw40444 raw40444Labels = mixedMoment B raw40444step0 raw40444step0Labels := by
      have ha : raw40444step0 = (fun i j => raw40444 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40444step0 raw40444; decide +kernel
      have hl : raw40444step0Labels = raw40444Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40444 raw40444Labels permutation218 permutation6
    mixedMoment B raw40444step0 raw40444step0Labels = mixedMoment B raw40444step1 raw40444step1Labels := by
      have ha : raw40444step1 = -raw40444step0 := by apply Matrix.ext; change ∀ i j, raw40444step1 i j = -(raw40444step0 i j); unfold raw40444step1 raw40444step0; decide +kernel
      have hl : raw40444step1Labels = raw40444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

theorem canonical40445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40445 raw40445Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw40445 raw40445Labels = mixedMoment B raw40445step0 raw40445step0Labels := by
      have ha : raw40445step0 = (fun i j => raw40445 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40445step0 raw40445; decide +kernel
      have hl : raw40445step0Labels = raw40445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40445 raw40445Labels permutation609 permutation6
    _ = mixedMoment B node2895 node2895Labels := by rfl

theorem canonical40446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40446 raw40446Labels = mixedMoment B node3137 node3137Labels := by
  calc
    mixedMoment B raw40446 raw40446Labels = mixedMoment B raw40446step0 raw40446step0Labels := by
      have ha : raw40446step0 = (fun i j => raw40446 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40446step0 raw40446; decide +kernel
      have hl : raw40446step0Labels = raw40446Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40446 raw40446Labels permutation218 permutation6
    mixedMoment B raw40446step0 raw40446step0Labels = mixedMoment B raw40446step1 raw40446step1Labels := by
      have ha : raw40446step1 = -raw40446step0 := by apply Matrix.ext; change ∀ i j, raw40446step1 i j = -(raw40446step0 i j); unfold raw40446step1 raw40446step0; decide +kernel
      have hl : raw40446step1Labels = raw40446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3137 node3137Labels := by rfl

theorem canonical40447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40447 raw40447Labels = mixedMoment B node2890 node2890Labels := by
  calc
    mixedMoment B raw40447 raw40447Labels = mixedMoment B raw40447step0 raw40447step0Labels := by
      have ha : raw40447step0 = (fun i j => raw40447 (permutation611 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40447step0 raw40447; decide +kernel
      have hl : raw40447step0Labels = raw40447Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40447 raw40447Labels permutation611 permutation6
    _ = mixedMoment B node2890 node2890Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical40448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40448 raw40448Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw40448 raw40448Labels = mixedMoment B raw40448step0 raw40448step0Labels := by
      have ha : raw40448step0 = (fun i j => raw40448 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40448step0 raw40448; decide +kernel
      have hl : raw40448step0Labels = raw40448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40448 raw40448Labels permutation260 permutation6
    mixedMoment B raw40448step0 raw40448step0Labels = mixedMoment B raw40448step1 raw40448step1Labels := by
      have ha : raw40448step1 = -raw40448step0 := by apply Matrix.ext; change ∀ i j, raw40448step1 i j = -(raw40448step0 i j); unfold raw40448step1 raw40448step0; decide +kernel
      have hl : raw40448step1Labels = raw40448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3128 node3128Labels := by rfl

theorem canonical40449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40449 raw40449Labels = mixedMoment B node3172 node3172Labels := by
  calc
    mixedMoment B raw40449 raw40449Labels = mixedMoment B raw40449step0 raw40449step0Labels := by
      have ha : raw40449step0 = (fun i j => raw40449 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40449step0 raw40449; decide +kernel
      have hl : raw40449step0Labels = raw40449Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40449 raw40449Labels permutation260 permutation6
    mixedMoment B raw40449step0 raw40449step0Labels = mixedMoment B raw40449step1 raw40449step1Labels := by
      have ha : raw40449step1 = -raw40449step0 := by apply Matrix.ext; change ∀ i j, raw40449step1 i j = -(raw40449step0 i j); unfold raw40449step1 raw40449step0; decide +kernel
      have hl : raw40449step1Labels = raw40449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3172 node3172Labels := by rfl

theorem canonical40450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40450 raw40450Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw40450 raw40450Labels = mixedMoment B raw40450step0 raw40450step0Labels := by
      have hz : ∀ j, raw40450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40450step0 = (fun i j => raw40450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40450step0 raw40450; decide +kernel
      have hl : raw40450step0Labels = raw40450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40450 raw40450Labels permutation434 hz
    mixedMoment B raw40450step0 raw40450step0Labels = mixedMoment B raw40450step1 raw40450step1Labels := by
      have hz : ∀ j, raw40450step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40450step1 = (fun i j => raw40450step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40450step1 raw40450step0; decide +kernel
      have hl : raw40450step1Labels = raw40450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40450step0 raw40450step0Labels permutation80 hz
    mixedMoment B raw40450step1 raw40450step1Labels = mixedMoment B raw40450step2 raw40450step2Labels := by
      have ha : raw40450step2 = (fun i j => raw40450step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40450step2 raw40450step1; decide +kernel
      have hl : raw40450step2Labels = raw40450step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40450step1 raw40450step1Labels permutation23 permutation6
    _ = mixedMoment B node2520 node2520Labels := by rfl

theorem canonical40451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40451 raw40451Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw40451 raw40451Labels = mixedMoment B raw40451step0 raw40451step0Labels := by
      have hz : ∀ j, raw40451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40451step0 = (fun i j => raw40451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40451step0 raw40451; decide +kernel
      have hl : raw40451step0Labels = raw40451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40451 raw40451Labels permutation434 hz
    mixedMoment B raw40451step0 raw40451step0Labels = mixedMoment B raw40451step1 raw40451step1Labels := by
      have hz : ∀ j, raw40451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40451step1 = (fun i j => raw40451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40451step1 raw40451step0; decide +kernel
      have hl : raw40451step1Labels = raw40451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40451step0 raw40451step0Labels permutation80 hz
    mixedMoment B raw40451step1 raw40451step1Labels = mixedMoment B raw40451step2 raw40451step2Labels := by
      have ha : raw40451step2 = (fun i j => raw40451step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40451step2 raw40451step1; decide +kernel
      have hl : raw40451step2Labels = raw40451step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40451step1 raw40451step1Labels permutation29 permutation6
    _ = mixedMoment B node1146 node1146Labels := by rfl

theorem canonical40452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40452 raw40452Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw40452 raw40452Labels = mixedMoment B raw40452step0 raw40452step0Labels := by
      have hz : ∀ j, raw40452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40452step0 = (fun i j => raw40452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40452step0 raw40452; decide +kernel
      have hl : raw40452step0Labels = raw40452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40452 raw40452Labels permutation346 hz
    mixedMoment B raw40452step0 raw40452step0Labels = mixedMoment B raw40452step1 raw40452step1Labels := by
      have ha : raw40452step1 = (fun i j => raw40452step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40452step1 raw40452step0; decide +kernel
      have hl : raw40452step1Labels = raw40452step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40452step0 raw40452step0Labels permutation115 permutation6
    _ = mixedMoment B node2497 node2497Labels := by rfl

theorem canonical40453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40453 raw40453Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw40453 raw40453Labels = mixedMoment B raw40453step0 raw40453step0Labels := by
      have hz : ∀ j, raw40453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40453step0 = (fun i j => raw40453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40453step0 raw40453; decide +kernel
      have hl : raw40453step0Labels = raw40453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40453 raw40453Labels permutation346 hz
    mixedMoment B raw40453step0 raw40453step0Labels = mixedMoment B raw40453step1 raw40453step1Labels := by
      have ha : raw40453step1 = (fun i j => raw40453step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40453step1 raw40453step0; decide +kernel
      have hl : raw40453step1Labels = raw40453step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40453step0 raw40453step0Labels permutation137 permutation6
    _ = mixedMoment B node1137 node1137Labels := by rfl

theorem canonical40454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40454 raw40454Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw40454 raw40454Labels = mixedMoment B raw40454step0 raw40454step0Labels := by
      have hz : ∀ j, raw40454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40454step0 = (fun i j => raw40454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40454step0 raw40454; decide +kernel
      have hl : raw40454step0Labels = raw40454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40454 raw40454Labels permutation346 hz
    mixedMoment B raw40454step0 raw40454step0Labels = mixedMoment B raw40454step1 raw40454step1Labels := by
      have ha : raw40454step1 = (fun i j => raw40454step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40454step1 raw40454step0; decide +kernel
      have hl : raw40454step1Labels = raw40454step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40454step0 raw40454step0Labels permutation115 permutation6
    _ = mixedMoment B node2443 node2443Labels := by rfl

theorem canonical40455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40455 raw40455Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw40455 raw40455Labels = mixedMoment B raw40455step0 raw40455step0Labels := by
      have hz : ∀ j, raw40455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40455step0 = (fun i j => raw40455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40455step0 raw40455; decide +kernel
      have hl : raw40455step0Labels = raw40455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40455 raw40455Labels permutation346 hz
    mixedMoment B raw40455step0 raw40455step0Labels = mixedMoment B raw40455step1 raw40455step1Labels := by
      have ha : raw40455step1 = (fun i j => raw40455step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40455step1 raw40455step0; decide +kernel
      have hl : raw40455step1Labels = raw40455step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40455step0 raw40455step0Labels permutation139 permutation6
    _ = mixedMoment B node1121 node1121Labels := by rfl

theorem canonical40456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40456 raw40456Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw40456 raw40456Labels = mixedMoment B raw40456step0 raw40456step0Labels := by
      have hz : ∀ j, raw40456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40456step0 = (fun i j => raw40456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40456step0 raw40456; decide +kernel
      have hl : raw40456step0Labels = raw40456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40456 raw40456Labels permutation346 hz
    mixedMoment B raw40456step0 raw40456step0Labels = mixedMoment B raw40456step1 raw40456step1Labels := by
      have ha : raw40456step1 = (fun i j => raw40456step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40456step1 raw40456step0; decide +kernel
      have hl : raw40456step1Labels = raw40456step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40456step0 raw40456step0Labels permutation89 permutation6
    _ = mixedMoment B node2435 node2435Labels := by rfl

theorem canonical40457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40457 raw40457Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw40457 raw40457Labels = mixedMoment B raw40457step0 raw40457step0Labels := by
      have hz : ∀ j, raw40457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40457step0 = (fun i j => raw40457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40457step0 raw40457; decide +kernel
      have hl : raw40457step0Labels = raw40457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40457 raw40457Labels permutation346 hz
    mixedMoment B raw40457step0 raw40457step0Labels = mixedMoment B raw40457step1 raw40457step1Labels := by
      have ha : raw40457step1 = (fun i j => raw40457step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40457step1 raw40457step0; decide +kernel
      have hl : raw40457step1Labels = raw40457step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40457step0 raw40457step0Labels permutation89 permutation6
    _ = mixedMoment B node2486 node2486Labels := by rfl

theorem canonical40458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40458 raw40458Labels = mixedMoment B node3132 node3132Labels := by
  calc
    mixedMoment B raw40458 raw40458Labels = mixedMoment B raw40458step0 raw40458step0Labels := by
      have hz : ∀ j, raw40458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40458step0 = (fun i j => raw40458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40458step0 raw40458; decide +kernel
      have hl : raw40458step0Labels = raw40458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40458 raw40458Labels permutation346 hz
    mixedMoment B raw40458step0 raw40458step0Labels = mixedMoment B raw40458step1 raw40458step1Labels := by
      have ha : raw40458step1 = (fun i j => raw40458step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40458step1 raw40458step0; decide +kernel
      have hl : raw40458step1Labels = raw40458step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40458step0 raw40458step0Labels permutation50 permutation6
    mixedMoment B raw40458step1 raw40458step1Labels = mixedMoment B raw40458step2 raw40458step2Labels := by
      have ha : raw40458step2 = -raw40458step1 := by apply Matrix.ext; change ∀ i j, raw40458step2 i j = -(raw40458step1 i j); unfold raw40458step2 raw40458step1; decide +kernel
      have hl : raw40458step2Labels = raw40458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3132 node3132Labels := by rfl

theorem canonical40459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40459 raw40459Labels = mixedMoment B node2440 node2440Labels := by
  calc
    mixedMoment B raw40459 raw40459Labels = mixedMoment B raw40459step0 raw40459step0Labels := by
      have ha : raw40459step0 = (fun i j => raw40459 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40459step0 raw40459; decide +kernel
      have hl : raw40459step0Labels = raw40459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40459 raw40459Labels permutation540 permutation6
    _ = mixedMoment B node2440 node2440Labels := by rfl

theorem canonical40460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40460 raw40460Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw40460 raw40460Labels = mixedMoment B raw40460step0 raw40460step0Labels := by
      have ha : raw40460step0 = (fun i j => raw40460 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40460step0 raw40460; decide +kernel
      have hl : raw40460step0Labels = raw40460Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40460 raw40460Labels permutation620 permutation6
    _ = mixedMoment B node1116 node1116Labels := by rfl

theorem canonical40461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40461 raw40461Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw40461 raw40461Labels = mixedMoment B raw40461step0 raw40461step0Labels := by
      have ha : raw40461step0 = (fun i j => raw40461 (permutation462 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40461step0 raw40461; decide +kernel
      have hl : raw40461step0Labels = raw40461Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40461 raw40461Labels permutation462 permutation6
    _ = mixedMoment B node2430 node2430Labels := by rfl

theorem canonical40462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40462 raw40462Labels = mixedMoment B node2471 node2471Labels := by
  calc
    mixedMoment B raw40462 raw40462Labels = mixedMoment B raw40462step0 raw40462step0Labels := by
      have ha : raw40462step0 = (fun i j => raw40462 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40462step0 raw40462; decide +kernel
      have hl : raw40462step0Labels = raw40462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40462 raw40462Labels permutation463 permutation6
    _ = mixedMoment B node2471 node2471Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5486 raw5486Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw5486 raw5486Labels = mixedMoment B raw5486step0 raw5486step0Labels := by
      have hz : ∀ j, raw5486 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5486step0 = (fun i j => raw5486 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5486step0 raw5486; decide +kernel
      have hl : raw5486step0Labels = raw5486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5486 raw5486Labels permutation520 hz
    mixedMoment B raw5486step0 raw5486step0Labels = mixedMoment B raw5486step1 raw5486step1Labels := by
      have ha : raw5486step1 = (fun i j => raw5486step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5486step1 raw5486step0; decide +kernel
      have hl : raw5486step1Labels = raw5486step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5486step0 raw5486step0Labels permutation137 permutation3
    mixedMoment B raw5486step1 raw5486step1Labels = mixedMoment B raw5486step2 raw5486step2Labels := by
      have ha : raw5486step2 = -raw5486step1 := by apply Matrix.ext; change ∀ i j, raw5486step2 i j = -(raw5486step1 i j); unfold raw5486step2 raw5486step1; decide +kernel
      have hl : raw5486step2Labels = raw5486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2235 node2235Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment992 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 992) =
      Integer.Sparse.eval keyMomentRow992 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 992).leftCharge (GramAssembly.key 992).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3189) := by
    have ha : gramCharges (GramAssembly.key 992).leftCharge (GramAssembly.key 992).rightCharge = raw40432 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40432Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40432 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 992).leftCharge (GramAssembly.key 992).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow992, Integer.Sparse.eval]

theorem keyMoment993 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 993) =
      Integer.Sparse.eval keyMomentRow993 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 993).leftCharge (GramAssembly.key 993).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2800) := by
    have ha : gramCharges (GramAssembly.key 993).leftCharge (GramAssembly.key 993).rightCharge = raw40433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40433 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 993).leftCharge (GramAssembly.key 993).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow993, Integer.Sparse.eval]

theorem keyMoment994 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 994) =
      Integer.Sparse.eval keyMomentRow994 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 994).leftCharge (GramAssembly.key 994).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3162) := by
    have ha : gramCharges (GramAssembly.key 994).leftCharge (GramAssembly.key 994).rightCharge = raw40434 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40434Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40434 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 994).leftCharge (GramAssembly.key 994).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow994, Integer.Sparse.eval]

theorem keyMoment995 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 995) =
      Integer.Sparse.eval keyMomentRow995 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 995).leftCharge (GramAssembly.key 995).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3199) := by
    have ha : gramCharges (GramAssembly.key 995).leftCharge (GramAssembly.key 995).rightCharge = raw40435 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40435Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40435 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 995).leftCharge (GramAssembly.key 995).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow995, Integer.Sparse.eval]

theorem keyMoment996 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 996) =
      Integer.Sparse.eval keyMomentRow996 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 996).leftCharge (GramAssembly.key 996).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3133) := by
    have ha : gramCharges (GramAssembly.key 996).leftCharge (GramAssembly.key 996).rightCharge = raw40436 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40436Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40436 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 996).leftCharge (GramAssembly.key 996).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow996, Integer.Sparse.eval]

theorem keyMoment997 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 997) =
      Integer.Sparse.eval keyMomentRow997 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 997).leftCharge (GramAssembly.key 997).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 997).leftCharge (GramAssembly.key 997).rightCharge = raw5486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5486 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 997).leftCharge (GramAssembly.key 997).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow997, Integer.Sparse.eval]

theorem keyMoment998 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 998) =
      Integer.Sparse.eval keyMomentRow998 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 998).leftCharge (GramAssembly.key 998).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2707) := by
    have ha : gramCharges (GramAssembly.key 998).leftCharge (GramAssembly.key 998).rightCharge = raw40437 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40437Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40437 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 998).leftCharge (GramAssembly.key 998).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow998, Integer.Sparse.eval]

theorem keyMoment999 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 999) =
      Integer.Sparse.eval keyMomentRow999 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 999).leftCharge (GramAssembly.key 999).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3155) := by
    have ha : gramCharges (GramAssembly.key 999).leftCharge (GramAssembly.key 999).rightCharge = raw40438 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40438Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40438 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 999).leftCharge (GramAssembly.key 999).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow999, Integer.Sparse.eval]

theorem keyMoment1000 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1000) =
      Integer.Sparse.eval keyMomentRow1000 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1000).leftCharge (GramAssembly.key 1000).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 1000).leftCharge (GramAssembly.key 1000).rightCharge = raw40439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40439 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1000).leftCharge (GramAssembly.key 1000).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1000, Integer.Sparse.eval]

theorem keyMoment1001 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1001) =
      Integer.Sparse.eval keyMomentRow1001 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1001).leftCharge (GramAssembly.key 1001).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3179) := by
    have ha : gramCharges (GramAssembly.key 1001).leftCharge (GramAssembly.key 1001).rightCharge = raw40440 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40440Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40440 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1001).leftCharge (GramAssembly.key 1001).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1001, Integer.Sparse.eval]

theorem keyMoment1002 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1002) =
      Integer.Sparse.eval keyMomentRow1002 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1002).leftCharge (GramAssembly.key 1002).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3130) := by
    have ha : gramCharges (GramAssembly.key 1002).leftCharge (GramAssembly.key 1002).rightCharge = raw40441 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40441Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40441 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1002).leftCharge (GramAssembly.key 1002).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1002, Integer.Sparse.eval]

theorem keyMoment1003 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1003) =
      Integer.Sparse.eval keyMomentRow1003 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1003).leftCharge (GramAssembly.key 1003).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3158) := by
    have ha : gramCharges (GramAssembly.key 1003).leftCharge (GramAssembly.key 1003).rightCharge = raw40442 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40442Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40442 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1003).leftCharge (GramAssembly.key 1003).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1003, Integer.Sparse.eval]

theorem keyMoment1004 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1004) =
      Integer.Sparse.eval keyMomentRow1004 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1004).leftCharge (GramAssembly.key 1004).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2899) := by
    have ha : gramCharges (GramAssembly.key 1004).leftCharge (GramAssembly.key 1004).rightCharge = raw40443 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40443Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40443 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1004).leftCharge (GramAssembly.key 1004).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1004, Integer.Sparse.eval]

theorem keyMoment1005 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1005) =
      Integer.Sparse.eval keyMomentRow1005 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1005).leftCharge (GramAssembly.key 1005).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3197) := by
    have ha : gramCharges (GramAssembly.key 1005).leftCharge (GramAssembly.key 1005).rightCharge = raw40444 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40444Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40444 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1005).leftCharge (GramAssembly.key 1005).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1005, Integer.Sparse.eval]

theorem keyMoment1006 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1006) =
      Integer.Sparse.eval keyMomentRow1006 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1006).leftCharge (GramAssembly.key 1006).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2895) := by
    have ha : gramCharges (GramAssembly.key 1006).leftCharge (GramAssembly.key 1006).rightCharge = raw40445 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40445Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40445 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1006).leftCharge (GramAssembly.key 1006).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1006, Integer.Sparse.eval]

theorem keyMoment1007 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1007) =
      Integer.Sparse.eval keyMomentRow1007 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1007).leftCharge (GramAssembly.key 1007).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3137) := by
    have ha : gramCharges (GramAssembly.key 1007).leftCharge (GramAssembly.key 1007).rightCharge = raw40446 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40446Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40446 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1007).leftCharge (GramAssembly.key 1007).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1007, Integer.Sparse.eval]

theorem keyMoment1008 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1008) =
      Integer.Sparse.eval keyMomentRow1008 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1008).leftCharge (GramAssembly.key 1008).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2890) := by
    have ha : gramCharges (GramAssembly.key 1008).leftCharge (GramAssembly.key 1008).rightCharge = raw40447 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40447Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40447 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1008).leftCharge (GramAssembly.key 1008).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1008, Integer.Sparse.eval]

theorem keyMoment1009 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1009) =
      Integer.Sparse.eval keyMomentRow1009 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1009).leftCharge (GramAssembly.key 1009).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3128) := by
    have ha : gramCharges (GramAssembly.key 1009).leftCharge (GramAssembly.key 1009).rightCharge = raw40448 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40448Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40448 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1009).leftCharge (GramAssembly.key 1009).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1009, Integer.Sparse.eval]

theorem keyMoment1010 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1010) =
      Integer.Sparse.eval keyMomentRow1010 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1010).leftCharge (GramAssembly.key 1010).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3172) := by
    have ha : gramCharges (GramAssembly.key 1010).leftCharge (GramAssembly.key 1010).rightCharge = raw40449 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40449Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40449 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1010).leftCharge (GramAssembly.key 1010).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1010, Integer.Sparse.eval]

theorem keyMoment1011 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1011) =
      Integer.Sparse.eval keyMomentRow1011 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1011).leftCharge (GramAssembly.key 1011).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2520) := by
    have ha : gramCharges (GramAssembly.key 1011).leftCharge (GramAssembly.key 1011).rightCharge = raw40450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40450 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1011).leftCharge (GramAssembly.key 1011).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1011, Integer.Sparse.eval]

theorem keyMoment1012 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1012) =
      Integer.Sparse.eval keyMomentRow1012 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1012).leftCharge (GramAssembly.key 1012).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1146) := by
    have ha : gramCharges (GramAssembly.key 1012).leftCharge (GramAssembly.key 1012).rightCharge = raw40451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40451 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1012).leftCharge (GramAssembly.key 1012).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1012, Integer.Sparse.eval]

theorem keyMoment1013 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1013) =
      Integer.Sparse.eval keyMomentRow1013 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1013).leftCharge (GramAssembly.key 1013).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2497) := by
    have ha : gramCharges (GramAssembly.key 1013).leftCharge (GramAssembly.key 1013).rightCharge = raw40452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40452 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1013).leftCharge (GramAssembly.key 1013).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1013, Integer.Sparse.eval]

theorem keyMoment1014 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1014) =
      Integer.Sparse.eval keyMomentRow1014 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1014).leftCharge (GramAssembly.key 1014).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1137) := by
    have ha : gramCharges (GramAssembly.key 1014).leftCharge (GramAssembly.key 1014).rightCharge = raw40453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40453 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1014).leftCharge (GramAssembly.key 1014).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1014, Integer.Sparse.eval]

theorem keyMoment1015 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1015) =
      Integer.Sparse.eval keyMomentRow1015 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1015).leftCharge (GramAssembly.key 1015).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2443) := by
    have ha : gramCharges (GramAssembly.key 1015).leftCharge (GramAssembly.key 1015).rightCharge = raw40454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40454 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1015).leftCharge (GramAssembly.key 1015).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1015, Integer.Sparse.eval]

theorem keyMoment1016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1016) =
      Integer.Sparse.eval keyMomentRow1016 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1016).leftCharge (GramAssembly.key 1016).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1121) := by
    have ha : gramCharges (GramAssembly.key 1016).leftCharge (GramAssembly.key 1016).rightCharge = raw40455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40455 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1016).leftCharge (GramAssembly.key 1016).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1016, Integer.Sparse.eval]

theorem keyMoment1017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1017) =
      Integer.Sparse.eval keyMomentRow1017 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1017).leftCharge (GramAssembly.key 1017).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2435) := by
    have ha : gramCharges (GramAssembly.key 1017).leftCharge (GramAssembly.key 1017).rightCharge = raw40456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40456 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1017).leftCharge (GramAssembly.key 1017).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1017, Integer.Sparse.eval]

theorem keyMoment1018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1018) =
      Integer.Sparse.eval keyMomentRow1018 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1018).leftCharge (GramAssembly.key 1018).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2486) := by
    have ha : gramCharges (GramAssembly.key 1018).leftCharge (GramAssembly.key 1018).rightCharge = raw40457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40457 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1018).leftCharge (GramAssembly.key 1018).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1018, Integer.Sparse.eval]

theorem keyMoment1019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1019) =
      Integer.Sparse.eval keyMomentRow1019 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1019).leftCharge (GramAssembly.key 1019).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3132) := by
    have ha : gramCharges (GramAssembly.key 1019).leftCharge (GramAssembly.key 1019).rightCharge = raw40458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40458 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1019).leftCharge (GramAssembly.key 1019).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1019, Integer.Sparse.eval]

theorem keyMoment1020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1020) =
      Integer.Sparse.eval keyMomentRow1020 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1020).leftCharge (GramAssembly.key 1020).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2440) := by
    have ha : gramCharges (GramAssembly.key 1020).leftCharge (GramAssembly.key 1020).rightCharge = raw40459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40459 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1020).leftCharge (GramAssembly.key 1020).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1020, Integer.Sparse.eval]

theorem keyMoment1021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1021) =
      Integer.Sparse.eval keyMomentRow1021 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1021).leftCharge (GramAssembly.key 1021).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1116) := by
    have ha : gramCharges (GramAssembly.key 1021).leftCharge (GramAssembly.key 1021).rightCharge = raw40460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1021).leftCharge (GramAssembly.key 1021).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1021, Integer.Sparse.eval]

theorem keyMoment1022 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1022) =
      Integer.Sparse.eval keyMomentRow1022 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1022).leftCharge (GramAssembly.key 1022).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2430) := by
    have ha : gramCharges (GramAssembly.key 1022).leftCharge (GramAssembly.key 1022).rightCharge = raw40461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40461 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1022).leftCharge (GramAssembly.key 1022).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1022, Integer.Sparse.eval]

theorem keyMoment1023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1023) =
      Integer.Sparse.eval keyMomentRow1023 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1023).leftCharge (GramAssembly.key 1023).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2471) := by
    have ha : gramCharges (GramAssembly.key 1023).leftCharge (GramAssembly.key 1023).rightCharge = raw40462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40462 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1023).leftCharge (GramAssembly.key 1023).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1023, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt992 : keyMomentRows (992 : Fin 2886) =
    keyMomentRow992 := by decide +kernel

theorem keyMomentRowsAt993 : keyMomentRows (993 : Fin 2886) =
    keyMomentRow993 := by decide +kernel

theorem keyMomentRowsAt994 : keyMomentRows (994 : Fin 2886) =
    keyMomentRow994 := by decide +kernel

theorem keyMomentRowsAt995 : keyMomentRows (995 : Fin 2886) =
    keyMomentRow995 := by decide +kernel

theorem keyMomentRowsAt996 : keyMomentRows (996 : Fin 2886) =
    keyMomentRow996 := by decide +kernel

theorem keyMomentRowsAt997 : keyMomentRows (997 : Fin 2886) =
    keyMomentRow997 := by decide +kernel

theorem keyMomentRowsAt998 : keyMomentRows (998 : Fin 2886) =
    keyMomentRow998 := by decide +kernel

theorem keyMomentRowsAt999 : keyMomentRows (999 : Fin 2886) =
    keyMomentRow999 := by decide +kernel

theorem keyMomentRowsAt1000 : keyMomentRows (1000 : Fin 2886) =
    keyMomentRow1000 := by decide +kernel

theorem keyMomentRowsAt1001 : keyMomentRows (1001 : Fin 2886) =
    keyMomentRow1001 := by decide +kernel

theorem keyMomentRowsAt1002 : keyMomentRows (1002 : Fin 2886) =
    keyMomentRow1002 := by decide +kernel

theorem keyMomentRowsAt1003 : keyMomentRows (1003 : Fin 2886) =
    keyMomentRow1003 := by decide +kernel

theorem keyMomentRowsAt1004 : keyMomentRows (1004 : Fin 2886) =
    keyMomentRow1004 := by decide +kernel

theorem keyMomentRowsAt1005 : keyMomentRows (1005 : Fin 2886) =
    keyMomentRow1005 := by decide +kernel

theorem keyMomentRowsAt1006 : keyMomentRows (1006 : Fin 2886) =
    keyMomentRow1006 := by decide +kernel

theorem keyMomentRowsAt1007 : keyMomentRows (1007 : Fin 2886) =
    keyMomentRow1007 := by decide +kernel

theorem keyMomentRowsAt1008 : keyMomentRows (1008 : Fin 2886) =
    keyMomentRow1008 := by decide +kernel

theorem keyMomentRowsAt1009 : keyMomentRows (1009 : Fin 2886) =
    keyMomentRow1009 := by decide +kernel

theorem keyMomentRowsAt1010 : keyMomentRows (1010 : Fin 2886) =
    keyMomentRow1010 := by decide +kernel

theorem keyMomentRowsAt1011 : keyMomentRows (1011 : Fin 2886) =
    keyMomentRow1011 := by decide +kernel

theorem keyMomentRowsAt1012 : keyMomentRows (1012 : Fin 2886) =
    keyMomentRow1012 := by decide +kernel

theorem keyMomentRowsAt1013 : keyMomentRows (1013 : Fin 2886) =
    keyMomentRow1013 := by decide +kernel

theorem keyMomentRowsAt1014 : keyMomentRows (1014 : Fin 2886) =
    keyMomentRow1014 := by decide +kernel

theorem keyMomentRowsAt1015 : keyMomentRows (1015 : Fin 2886) =
    keyMomentRow1015 := by decide +kernel

theorem keyMomentRowsAt1016 : keyMomentRows (1016 : Fin 2886) =
    keyMomentRow1016 := by decide +kernel

theorem keyMomentRowsAt1017 : keyMomentRows (1017 : Fin 2886) =
    keyMomentRow1017 := by decide +kernel

theorem keyMomentRowsAt1018 : keyMomentRows (1018 : Fin 2886) =
    keyMomentRow1018 := by decide +kernel

theorem keyMomentRowsAt1019 : keyMomentRows (1019 : Fin 2886) =
    keyMomentRow1019 := by decide +kernel

theorem keyMomentRowsAt1020 : keyMomentRows (1020 : Fin 2886) =
    keyMomentRow1020 := by decide +kernel

theorem keyMomentRowsAt1021 : keyMomentRows (1021 : Fin 2886) =
    keyMomentRow1021 := by decide +kernel

theorem keyMomentRowsAt1022 : keyMomentRows (1022 : Fin 2886) =
    keyMomentRow1022 := by decide +kernel

theorem keyMomentRowsAt1023 : keyMomentRows (1023 : Fin 2886) =
    keyMomentRow1023 := by decide +kernel

theorem keyMomentChunkSound31_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 31) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 992 ∨ k.val = 993 ∨ k.val = 994 ∨ k.val = 995 ∨ k.val = 996 ∨ k.val = 997 ∨ k.val = 998 ∨ k.val = 999 ∨ k.val = 1000 ∨ k.val = 1001 ∨ k.val = 1002 ∨ k.val = 1003 ∨ k.val = 1004 ∨ k.val = 1005 ∨ k.val = 1006 ∨ k.val = 1007 ∨ k.val = 1008 ∨ k.val = 1009 ∨ k.val = 1010 ∨ k.val = 1011 ∨ k.val = 1012 ∨ k.val = 1013 ∨ k.val = 1014 ∨ k.val = 1015 ∨ k.val = 1016 ∨ k.val = 1017 ∨ k.val = 1018 ∨ k.val = 1019 ∨ k.val = 1020 ∨ k.val = 1021 ∨ k.val = 1022 ∨ k.val = 1023 := by omega
  rcases heq with h992 | h993 | h994 | h995 | h996 | h997 | h998 | h999 | h1000 | h1001 | h1002 | h1003 | h1004 | h1005 | h1006 | h1007 | h1008 | h1009 | h1010 | h1011 | h1012 | h1013 | h1014 | h1015 | h1016 | h1017 | h1018 | h1019 | h1020 | h1021 | h1022 | h1023
  · have he : k = (992 : Fin 2886) := Fin.ext h992
    subst k
    rw [keyMomentRowsAt992]
    exact keyMoment992 B hB
  · have he : k = (993 : Fin 2886) := Fin.ext h993
    subst k
    rw [keyMomentRowsAt993]
    exact keyMoment993 B hB
  · have he : k = (994 : Fin 2886) := Fin.ext h994
    subst k
    rw [keyMomentRowsAt994]
    exact keyMoment994 B hB
  · have he : k = (995 : Fin 2886) := Fin.ext h995
    subst k
    rw [keyMomentRowsAt995]
    exact keyMoment995 B hB
  · have he : k = (996 : Fin 2886) := Fin.ext h996
    subst k
    rw [keyMomentRowsAt996]
    exact keyMoment996 B hB
  · have he : k = (997 : Fin 2886) := Fin.ext h997
    subst k
    rw [keyMomentRowsAt997]
    exact keyMoment997 B hB
  · have he : k = (998 : Fin 2886) := Fin.ext h998
    subst k
    rw [keyMomentRowsAt998]
    exact keyMoment998 B hB
  · have he : k = (999 : Fin 2886) := Fin.ext h999
    subst k
    rw [keyMomentRowsAt999]
    exact keyMoment999 B hB
  · have he : k = (1000 : Fin 2886) := Fin.ext h1000
    subst k
    rw [keyMomentRowsAt1000]
    exact keyMoment1000 B hB
  · have he : k = (1001 : Fin 2886) := Fin.ext h1001
    subst k
    rw [keyMomentRowsAt1001]
    exact keyMoment1001 B hB
  · have he : k = (1002 : Fin 2886) := Fin.ext h1002
    subst k
    rw [keyMomentRowsAt1002]
    exact keyMoment1002 B hB
  · have he : k = (1003 : Fin 2886) := Fin.ext h1003
    subst k
    rw [keyMomentRowsAt1003]
    exact keyMoment1003 B hB
  · have he : k = (1004 : Fin 2886) := Fin.ext h1004
    subst k
    rw [keyMomentRowsAt1004]
    exact keyMoment1004 B hB
  · have he : k = (1005 : Fin 2886) := Fin.ext h1005
    subst k
    rw [keyMomentRowsAt1005]
    exact keyMoment1005 B hB
  · have he : k = (1006 : Fin 2886) := Fin.ext h1006
    subst k
    rw [keyMomentRowsAt1006]
    exact keyMoment1006 B hB
  · have he : k = (1007 : Fin 2886) := Fin.ext h1007
    subst k
    rw [keyMomentRowsAt1007]
    exact keyMoment1007 B hB
  · have he : k = (1008 : Fin 2886) := Fin.ext h1008
    subst k
    rw [keyMomentRowsAt1008]
    exact keyMoment1008 B hB
  · have he : k = (1009 : Fin 2886) := Fin.ext h1009
    subst k
    rw [keyMomentRowsAt1009]
    exact keyMoment1009 B hB
  · have he : k = (1010 : Fin 2886) := Fin.ext h1010
    subst k
    rw [keyMomentRowsAt1010]
    exact keyMoment1010 B hB
  · have he : k = (1011 : Fin 2886) := Fin.ext h1011
    subst k
    rw [keyMomentRowsAt1011]
    exact keyMoment1011 B hB
  · have he : k = (1012 : Fin 2886) := Fin.ext h1012
    subst k
    rw [keyMomentRowsAt1012]
    exact keyMoment1012 B hB
  · have he : k = (1013 : Fin 2886) := Fin.ext h1013
    subst k
    rw [keyMomentRowsAt1013]
    exact keyMoment1013 B hB
  · have he : k = (1014 : Fin 2886) := Fin.ext h1014
    subst k
    rw [keyMomentRowsAt1014]
    exact keyMoment1014 B hB
  · have he : k = (1015 : Fin 2886) := Fin.ext h1015
    subst k
    rw [keyMomentRowsAt1015]
    exact keyMoment1015 B hB
  · have he : k = (1016 : Fin 2886) := Fin.ext h1016
    subst k
    rw [keyMomentRowsAt1016]
    exact keyMoment1016 B hB
  · have he : k = (1017 : Fin 2886) := Fin.ext h1017
    subst k
    rw [keyMomentRowsAt1017]
    exact keyMoment1017 B hB
  · have he : k = (1018 : Fin 2886) := Fin.ext h1018
    subst k
    rw [keyMomentRowsAt1018]
    exact keyMoment1018 B hB
  · have he : k = (1019 : Fin 2886) := Fin.ext h1019
    subst k
    rw [keyMomentRowsAt1019]
    exact keyMoment1019 B hB
  · have he : k = (1020 : Fin 2886) := Fin.ext h1020
    subst k
    rw [keyMomentRowsAt1020]
    exact keyMoment1020 B hB
  · have he : k = (1021 : Fin 2886) := Fin.ext h1021
    subst k
    rw [keyMomentRowsAt1021]
    exact keyMoment1021 B hB
  · have he : k = (1022 : Fin 2886) := Fin.ext h1022
    subst k
    rw [keyMomentRowsAt1022]
    exact keyMoment1022 B hB
  · have he : k = (1023 : Fin 2886) := Fin.ext h1023
    subst k
    rw [keyMomentRowsAt1023]
    exact keyMoment1023 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound31_e_oai
