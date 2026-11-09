-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:46:51.145786+00:00
-- url     : https://prove2.me/submissions/831fecfa-5b42-4563-b156-eec451af0318

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

theorem canonical39928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39928 raw39928Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39928 raw39928Labels = mixedMoment B raw39928step0 raw39928step0Labels := by
      have hz : ∀ j, raw39928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39928step0 = (fun i j => raw39928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39928step0 raw39928; decide +kernel
      have hl : raw39928step0Labels = raw39928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39928 raw39928Labels permutation434 hz
    mixedMoment B raw39928step0 raw39928step0Labels = mixedMoment B raw39928step1 raw39928step1Labels := by
      have hz : ∀ j, raw39928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39928step1 = (fun i j => raw39928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39928step1 raw39928step0; decide +kernel
      have hl : raw39928step1Labels = raw39928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39928step0 raw39928step0Labels permutation80 hz
    mixedMoment B raw39928step1 raw39928step1Labels = mixedMoment B raw39928step2 raw39928step2Labels := by
      have hz : ∀ j, raw39928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39928step2 = (fun i j => raw39928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39928step2 raw39928step1; decide +kernel
      have hl : raw39928step2Labels = raw39928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39928step1 raw39928step1Labels permutation14 hz
    mixedMoment B raw39928step2 raw39928step2Labels = mixedMoment B raw39928step3 raw39928step3Labels := by
      have ha : raw39928step3 = (fun i j => raw39928step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39928step3 raw39928step2; decide +kernel
      have hl : raw39928step3Labels = raw39928step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39928step2 raw39928step2Labels permutation5 permutation6
    _ = mixedMoment B node420 node420Labels := by rfl

theorem canonical39929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39929 raw39929Labels = mixedMoment B node33 node33Labels := by
  calc
    mixedMoment B raw39929 raw39929Labels = mixedMoment B raw39929step0 raw39929step0Labels := by
      have hz : ∀ j, raw39929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39929step0 = (fun i j => raw39929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39929step0 raw39929; decide +kernel
      have hl : raw39929step0Labels = raw39929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39929 raw39929Labels permutation346 hz
    mixedMoment B raw39929step0 raw39929step0Labels = mixedMoment B raw39929step1 raw39929step1Labels := by
      have hz : ∀ j, raw39929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39929step1 = (fun i j => raw39929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39929step1 raw39929step0; decide +kernel
      have hl : raw39929step1Labels = raw39929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39929step0 raw39929step0Labels permutation56 hz
    mixedMoment B raw39929step1 raw39929step1Labels = mixedMoment B raw39929step2 raw39929step2Labels := by
      have ha : raw39929step2 = (fun i j => raw39929step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39929step2 raw39929step1; decide +kernel
      have hl : raw39929step2Labels = raw39929step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39929step1 raw39929step1Labels permutation28 permutation6
    _ = mixedMoment B node33 node33Labels := by rfl

theorem canonical39930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39930 raw39930Labels = mixedMoment B node111 node111Labels := by
  calc
    mixedMoment B raw39930 raw39930Labels = mixedMoment B raw39930step0 raw39930step0Labels := by
      have hz : ∀ j, raw39930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39930step0 = (fun i j => raw39930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39930step0 raw39930; decide +kernel
      have hl : raw39930step0Labels = raw39930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39930 raw39930Labels permutation346 hz
    mixedMoment B raw39930step0 raw39930step0Labels = mixedMoment B raw39930step1 raw39930step1Labels := by
      have hz : ∀ j, raw39930step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39930step1 = (fun i j => raw39930step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39930step1 raw39930step0; decide +kernel
      have hl : raw39930step1Labels = raw39930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39930step0 raw39930step0Labels permutation56 hz
    mixedMoment B raw39930step1 raw39930step1Labels = mixedMoment B raw39930step2 raw39930step2Labels := by
      have ha : raw39930step2 = (fun i j => raw39930step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39930step2 raw39930step1; decide +kernel
      have hl : raw39930step2Labels = raw39930step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39930step1 raw39930step1Labels permutation23 permutation6
    _ = mixedMoment B node111 node111Labels := by rfl

theorem canonical39931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39931 raw39931Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39931 raw39931Labels = mixedMoment B raw39931step0 raw39931step0Labels := by
      have hz : ∀ j, raw39931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39931step0 = (fun i j => raw39931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39931step0 raw39931; decide +kernel
      have hl : raw39931step0Labels = raw39931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39931 raw39931Labels permutation346 hz
    mixedMoment B raw39931step0 raw39931step0Labels = mixedMoment B raw39931step1 raw39931step1Labels := by
      have hz : ∀ j, raw39931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39931step1 = (fun i j => raw39931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39931step1 raw39931step0; decide +kernel
      have hl : raw39931step1Labels = raw39931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39931step0 raw39931step0Labels permutation56 hz
    mixedMoment B raw39931step1 raw39931step1Labels = mixedMoment B raw39931step2 raw39931step2Labels := by
      have ha : raw39931step2 = (fun i j => raw39931step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39931step2 raw39931step1; decide +kernel
      have hl : raw39931step2Labels = raw39931step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39931step1 raw39931step1Labels permutation25 permutation6
    _ = mixedMoment B node405 node405Labels := by rfl

theorem canonical39932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39932 raw39932Labels = mixedMoment B node98 node98Labels := by
  calc
    mixedMoment B raw39932 raw39932Labels = mixedMoment B raw39932step0 raw39932step0Labels := by
      have hz : ∀ j, raw39932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39932step0 = (fun i j => raw39932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39932step0 raw39932; decide +kernel
      have hl : raw39932step0Labels = raw39932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39932 raw39932Labels permutation346 hz
    mixedMoment B raw39932step0 raw39932step0Labels = mixedMoment B raw39932step1 raw39932step1Labels := by
      have hz : ∀ j, raw39932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39932step1 = (fun i j => raw39932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39932step1 raw39932step0; decide +kernel
      have hl : raw39932step1Labels = raw39932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39932step0 raw39932step0Labels permutation56 hz
    mixedMoment B raw39932step1 raw39932step1Labels = mixedMoment B raw39932step2 raw39932step2Labels := by
      have ha : raw39932step2 = (fun i j => raw39932step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39932step2 raw39932step1; decide +kernel
      have hl : raw39932step2Labels = raw39932step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39932step1 raw39932step1Labels permutation24 permutation6
    _ = mixedMoment B node98 node98Labels := by rfl

theorem canonical39933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39933 raw39933Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw39933 raw39933Labels = mixedMoment B raw39933step0 raw39933step0Labels := by
      have hz : ∀ j, raw39933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39933step0 = (fun i j => raw39933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39933step0 raw39933; decide +kernel
      have hl : raw39933step0Labels = raw39933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39933 raw39933Labels permutation346 hz
    mixedMoment B raw39933step0 raw39933step0Labels = mixedMoment B raw39933step1 raw39933step1Labels := by
      have hz : ∀ j, raw39933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39933step1 = (fun i j => raw39933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39933step1 raw39933step0; decide +kernel
      have hl : raw39933step1Labels = raw39933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39933step0 raw39933step0Labels permutation56 hz
    mixedMoment B raw39933step1 raw39933step1Labels = mixedMoment B raw39933step2 raw39933step2Labels := by
      have ha : raw39933step2 = (fun i j => raw39933step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39933step2 raw39933step1; decide +kernel
      have hl : raw39933step2Labels = raw39933step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39933step1 raw39933step1Labels permutation24 permutation6
    _ = mixedMoment B node343 node343Labels := by rfl

theorem canonical39934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39934 raw39934Labels = mixedMoment B node452 node452Labels := by
  calc
    mixedMoment B raw39934 raw39934Labels = mixedMoment B raw39934step0 raw39934step0Labels := by
      have hz : ∀ j, raw39934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39934step0 = (fun i j => raw39934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39934step0 raw39934; decide +kernel
      have hl : raw39934step0Labels = raw39934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39934 raw39934Labels permutation346 hz
    mixedMoment B raw39934step0 raw39934step0Labels = mixedMoment B raw39934step1 raw39934step1Labels := by
      have hz : ∀ j, raw39934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39934step1 = (fun i j => raw39934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39934step1 raw39934step0; decide +kernel
      have hl : raw39934step1Labels = raw39934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39934step0 raw39934step0Labels permutation56 hz
    mixedMoment B raw39934step1 raw39934step1Labels = mixedMoment B raw39934step2 raw39934step2Labels := by
      have ha : raw39934step2 = (fun i j => raw39934step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39934step2 raw39934step1; decide +kernel
      have hl : raw39934step2Labels = raw39934step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39934step1 raw39934step1Labels permutation14 permutation6
    mixedMoment B raw39934step2 raw39934step2Labels = mixedMoment B raw39934step3 raw39934step3Labels := by
      have ha : raw39934step3 = -raw39934step2 := by apply Matrix.ext; change ∀ i j, raw39934step3 i j = -(raw39934step2 i j); unfold raw39934step3 raw39934step2; decide +kernel
      have hl : raw39934step3Labels = raw39934step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node452 node452Labels := by rfl

theorem canonical39935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39935 raw39935Labels = mixedMoment B node71 node71Labels := by
  calc
    mixedMoment B raw39935 raw39935Labels = mixedMoment B raw39935step0 raw39935step0Labels := by
      have hz : ∀ j, raw39935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39935step0 = (fun i j => raw39935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39935step0 raw39935; decide +kernel
      have hl : raw39935step0Labels = raw39935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39935 raw39935Labels permutation346 hz
    mixedMoment B raw39935step0 raw39935step0Labels = mixedMoment B raw39935step1 raw39935step1Labels := by
      have hz : ∀ j, raw39935step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39935step1 = (fun i j => raw39935step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39935step1 raw39935step0; decide +kernel
      have hl : raw39935step1Labels = raw39935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39935step0 raw39935step0Labels permutation56 hz
    mixedMoment B raw39935step1 raw39935step1Labels = mixedMoment B raw39935step2 raw39935step2Labels := by
      have ha : raw39935step2 = (fun i j => raw39935step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39935step2 raw39935step1; decide +kernel
      have hl : raw39935step2Labels = raw39935step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39935step1 raw39935step1Labels permutation24 permutation6
    _ = mixedMoment B node71 node71Labels := by rfl

end MUB6.Certificate.MixedSemantics

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

theorem canonical39936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39936 raw39936Labels = mixedMoment B node186 node186Labels := by
  calc
    mixedMoment B raw39936 raw39936Labels = mixedMoment B raw39936step0 raw39936step0Labels := by
      have hz : ∀ j, raw39936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39936step0 = (fun i j => raw39936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39936step0 raw39936; decide +kernel
      have hl : raw39936step0Labels = raw39936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39936 raw39936Labels permutation346 hz
    mixedMoment B raw39936step0 raw39936step0Labels = mixedMoment B raw39936step1 raw39936step1Labels := by
      have hz : ∀ j, raw39936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39936step1 = (fun i j => raw39936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39936step1 raw39936step0; decide +kernel
      have hl : raw39936step1Labels = raw39936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39936step0 raw39936step0Labels permutation56 hz
    mixedMoment B raw39936step1 raw39936step1Labels = mixedMoment B raw39936step2 raw39936step2Labels := by
      have ha : raw39936step2 = (fun i j => raw39936step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39936step2 raw39936step1; decide +kernel
      have hl : raw39936step2Labels = raw39936step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39936step1 raw39936step1Labels permutation15 permutation6
    mixedMoment B raw39936step2 raw39936step2Labels = mixedMoment B raw39936step3 raw39936step3Labels := by
      have ha : raw39936step3 = -raw39936step2 := by apply Matrix.ext; change ∀ i j, raw39936step3 i j = -(raw39936step2 i j); unfold raw39936step3 raw39936step2; decide +kernel
      have hl : raw39936step3Labels = raw39936step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node186 node186Labels := by rfl

theorem canonical39937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39937 raw39937Labels = mixedMoment B node95 node95Labels := by
  calc
    mixedMoment B raw39937 raw39937Labels = mixedMoment B raw39937step0 raw39937step0Labels := by
      have hz : ∀ j, raw39937 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39937step0 = (fun i j => raw39937 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39937step0 raw39937; decide +kernel
      have hl : raw39937step0Labels = raw39937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39937 raw39937Labels permutation265 hz
    mixedMoment B raw39937step0 raw39937step0Labels = mixedMoment B raw39937step1 raw39937step1Labels := by
      have ha : raw39937step1 = (fun i j => raw39937step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39937step1 raw39937step0; decide +kernel
      have hl : raw39937step1Labels = raw39937step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39937step0 raw39937step0Labels permutation125 permutation6
    _ = mixedMoment B node95 node95Labels := by rfl

theorem canonical39938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39938 raw39938Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw39938 raw39938Labels = mixedMoment B raw39938step0 raw39938step0Labels := by
      have hz : ∀ j, raw39938 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39938step0 = (fun i j => raw39938 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39938step0 raw39938; decide +kernel
      have hl : raw39938step0Labels = raw39938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39938 raw39938Labels permutation265 hz
    mixedMoment B raw39938step0 raw39938step0Labels = mixedMoment B raw39938step1 raw39938step1Labels := by
      have ha : raw39938step1 = (fun i j => raw39938step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39938step1 raw39938step0; decide +kernel
      have hl : raw39938step1Labels = raw39938step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39938step0 raw39938step0Labels permutation125 permutation6
    _ = mixedMoment B node339 node339Labels := by rfl

theorem canonical39939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39939 raw39939Labels = mixedMoment B node68 node68Labels := by
  calc
    mixedMoment B raw39939 raw39939Labels = mixedMoment B raw39939step0 raw39939step0Labels := by
      have hz : ∀ j, raw39939 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39939step0 = (fun i j => raw39939 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39939step0 raw39939; decide +kernel
      have hl : raw39939step0Labels = raw39939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39939 raw39939Labels permutation265 hz
    mixedMoment B raw39939step0 raw39939step0Labels = mixedMoment B raw39939step1 raw39939step1Labels := by
      have ha : raw39939step1 = (fun i j => raw39939step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39939step1 raw39939step0; decide +kernel
      have hl : raw39939step1Labels = raw39939step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39939step0 raw39939step0Labels permutation124 permutation6
    _ = mixedMoment B node68 node68Labels := by rfl

theorem canonical39940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39940 raw39940Labels = mixedMoment B node275 node275Labels := by
  calc
    mixedMoment B raw39940 raw39940Labels = mixedMoment B raw39940step0 raw39940step0Labels := by
      have hz : ∀ j, raw39940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39940step0 = (fun i j => raw39940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39940step0 raw39940; decide +kernel
      have hl : raw39940step0Labels = raw39940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39940 raw39940Labels permutation265 hz
    mixedMoment B raw39940step0 raw39940step0Labels = mixedMoment B raw39940step1 raw39940step1Labels := by
      have ha : raw39940step1 = (fun i j => raw39940step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39940step1 raw39940step0; decide +kernel
      have hl : raw39940step1Labels = raw39940step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39940step0 raw39940step0Labels permutation124 permutation6
    _ = mixedMoment B node275 node275Labels := by rfl

theorem canonical39941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39941 raw39941Labels = mixedMoment B node65 node65Labels := by
  calc
    mixedMoment B raw39941 raw39941Labels = mixedMoment B raw39941step0 raw39941step0Labels := by
      have ha : raw39941step0 = (fun i j => raw39941 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39941step0 raw39941; decide +kernel
      have hl : raw39941step0Labels = raw39941Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39941 raw39941Labels permutation577 permutation6
    _ = mixedMoment B node65 node65Labels := by rfl

theorem canonical39942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39942 raw39942Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39942 raw39942Labels = mixedMoment B raw39942step0 raw39942step0Labels := by
      have hz : ∀ j, raw39942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39942step0 = (fun i j => raw39942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39942step0 raw39942; decide +kernel
      have hl : raw39942step0Labels = raw39942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39942 raw39942Labels permutation434 hz
    mixedMoment B raw39942step0 raw39942step0Labels = mixedMoment B raw39942step1 raw39942step1Labels := by
      have hz : ∀ j, raw39942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39942step1 = (fun i j => raw39942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39942step1 raw39942step0; decide +kernel
      have hl : raw39942step1Labels = raw39942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39942step0 raw39942step0Labels permutation80 hz
    mixedMoment B raw39942step1 raw39942step1Labels = mixedMoment B raw39942step2 raw39942step2Labels := by
      have ha : raw39942step2 = (fun i j => raw39942step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39942step2 raw39942step1; decide +kernel
      have hl : raw39942step2Labels = raw39942step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39942step1 raw39942step1Labels permutation11 permutation7
    mixedMoment B raw39942step2 raw39942step2Labels = mixedMoment B raw39942step3 raw39942step3Labels := by
      have ha : raw39942step3 = -raw39942step2 := by apply Matrix.ext; change ∀ i j, raw39942step3 i j = -(raw39942step2 i j); unfold raw39942step3 raw39942step2; decide +kernel
      have hl : raw39942step3Labels = raw39942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node406 node406Labels := by rfl

theorem canonical39943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39943 raw39943Labels = mixedMoment B node354 node354Labels := by
  calc
    mixedMoment B raw39943 raw39943Labels = mixedMoment B raw39943step0 raw39943step0Labels := by
      have hz : ∀ j, raw39943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39943step0 = (fun i j => raw39943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39943step0 raw39943; decide +kernel
      have hl : raw39943step0Labels = raw39943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39943 raw39943Labels permutation434 hz
    mixedMoment B raw39943step0 raw39943step0Labels = mixedMoment B raw39943step1 raw39943step1Labels := by
      have hz : ∀ j, raw39943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39943step1 = (fun i j => raw39943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39943step1 raw39943step0; decide +kernel
      have hl : raw39943step1Labels = raw39943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39943step0 raw39943step0Labels permutation80 hz
    mixedMoment B raw39943step1 raw39943step1Labels = mixedMoment B raw39943step2 raw39943step2Labels := by
      have ha : raw39943step2 = (fun i j => raw39943step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39943step2 raw39943step1; decide +kernel
      have hl : raw39943step2Labels = raw39943step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39943step1 raw39943step1Labels permutation10 permutation7
    mixedMoment B raw39943step2 raw39943step2Labels = mixedMoment B raw39943step3 raw39943step3Labels := by
      have ha : raw39943step3 = -raw39943step2 := by apply Matrix.ext; change ∀ i j, raw39943step3 i j = -(raw39943step2 i j); unfold raw39943step3 raw39943step2; decide +kernel
      have hl : raw39943step3Labels = raw39943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node354 node354Labels := by rfl

theorem canonical39944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39944 raw39944Labels = mixedMoment B node328 node328Labels := by
  calc
    mixedMoment B raw39944 raw39944Labels = mixedMoment B raw39944step0 raw39944step0Labels := by
      have hz : ∀ j, raw39944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39944step0 = (fun i j => raw39944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39944step0 raw39944; decide +kernel
      have hl : raw39944step0Labels = raw39944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39944 raw39944Labels permutation346 hz
    mixedMoment B raw39944step0 raw39944step0Labels = mixedMoment B raw39944step1 raw39944step1Labels := by
      have ha : raw39944step1 = (fun i j => raw39944step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39944step1 raw39944step0; decide +kernel
      have hl : raw39944step1Labels = raw39944step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39944step0 raw39944step0Labels permutation40 permutation7
    mixedMoment B raw39944step1 raw39944step1Labels = mixedMoment B raw39944step2 raw39944step2Labels := by
      have ha : raw39944step2 = -raw39944step1 := by apply Matrix.ext; change ∀ i j, raw39944step2 i j = -(raw39944step1 i j); unfold raw39944step2 raw39944step1; decide +kernel
      have hl : raw39944step2Labels = raw39944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node328 node328Labels := by rfl

theorem canonical39945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39945 raw39945Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39945 raw39945Labels = mixedMoment B raw39945step0 raw39945step0Labels := by
      have hz : ∀ j, raw39945 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39945step0 = (fun i j => raw39945 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39945step0 raw39945; decide +kernel
      have hl : raw39945step0Labels = raw39945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39945 raw39945Labels permutation434 hz
    mixedMoment B raw39945step0 raw39945step0Labels = mixedMoment B raw39945step1 raw39945step1Labels := by
      have ha : raw39945step1 = (fun i j => raw39945step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39945step1 raw39945step0; decide +kernel
      have hl : raw39945step1Labels = raw39945step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39945step0 raw39945step0Labels permutation50 permutation7
    mixedMoment B raw39945step1 raw39945step1Labels = mixedMoment B raw39945step2 raw39945step2Labels := by
      have ha : raw39945step2 = -raw39945step1 := by apply Matrix.ext; change ∀ i j, raw39945step2 i j = -(raw39945step1 i j); unfold raw39945step2 raw39945step1; decide +kernel
      have hl : raw39945step2Labels = raw39945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39946 raw39946Labels = mixedMoment B node348 node348Labels := by
  calc
    mixedMoment B raw39946 raw39946Labels = mixedMoment B raw39946step0 raw39946step0Labels := by
      have hz : ∀ j, raw39946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39946step0 = (fun i j => raw39946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39946step0 raw39946; decide +kernel
      have hl : raw39946step0Labels = raw39946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39946 raw39946Labels permutation434 hz
    mixedMoment B raw39946step0 raw39946step0Labels = mixedMoment B raw39946step1 raw39946step1Labels := by
      have ha : raw39946step1 = (fun i j => raw39946step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39946step1 raw39946step0; decide +kernel
      have hl : raw39946step1Labels = raw39946step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39946step0 raw39946step0Labels permutation44 permutation7
    mixedMoment B raw39946step1 raw39946step1Labels = mixedMoment B raw39946step2 raw39946step2Labels := by
      have ha : raw39946step2 = -raw39946step1 := by apply Matrix.ext; change ∀ i j, raw39946step2 i j = -(raw39946step1 i j); unfold raw39946step2 raw39946step1; decide +kernel
      have hl : raw39946step2Labels = raw39946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node348 node348Labels := by rfl

theorem canonical39947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39947 raw39947Labels = mixedMoment B node347 node347Labels := by
  calc
    mixedMoment B raw39947 raw39947Labels = mixedMoment B raw39947step0 raw39947step0Labels := by
      have ha : raw39947step0 = (fun i j => raw39947 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39947step0 raw39947; decide +kernel
      have hl : raw39947step0Labels = raw39947Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39947 raw39947Labels permutation246 permutation7
    mixedMoment B raw39947step0 raw39947step0Labels = mixedMoment B raw39947step1 raw39947step1Labels := by
      have ha : raw39947step1 = -raw39947step0 := by apply Matrix.ext; change ∀ i j, raw39947step1 i j = -(raw39947step0 i j); unfold raw39947step1 raw39947step0; decide +kernel
      have hl : raw39947step1Labels = raw39947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node347 node347Labels := by rfl

theorem canonical39948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39948 raw39948Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw39948 raw39948Labels = mixedMoment B raw39948step0 raw39948step0Labels := by
      have ha : raw39948step0 = (fun i j => raw39948 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39948step0 raw39948; decide +kernel
      have hl : raw39948step0Labels = raw39948Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39948 raw39948Labels permutation240 permutation7
    mixedMoment B raw39948step0 raw39948step0Labels = mixedMoment B raw39948step1 raw39948step1Labels := by
      have ha : raw39948step1 = -raw39948step0 := by apply Matrix.ext; change ∀ i j, raw39948step1 i j = -(raw39948step0 i j); unfold raw39948step1 raw39948step0; decide +kernel
      have hl : raw39948step1Labels = raw39948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node394 node394Labels := by rfl

theorem canonical39949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39949 raw39949Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39949 raw39949Labels = mixedMoment B raw39949step0 raw39949step0Labels := by
      have hz : ∀ j, raw39949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39949step0 = (fun i j => raw39949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39949step0 raw39949; decide +kernel
      have hl : raw39949step0Labels = raw39949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39949 raw39949Labels permutation434 hz
    mixedMoment B raw39949step0 raw39949step0Labels = mixedMoment B raw39949step1 raw39949step1Labels := by
      have hz : ∀ j, raw39949step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39949step1 = (fun i j => raw39949step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39949step1 raw39949step0; decide +kernel
      have hl : raw39949step1Labels = raw39949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39949step0 raw39949step0Labels permutation80 hz
    mixedMoment B raw39949step1 raw39949step1Labels = mixedMoment B raw39949step2 raw39949step2Labels := by
      have ha : raw39949step2 = (fun i j => raw39949step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39949step2 raw39949step1; decide +kernel
      have hl : raw39949step2Labels = raw39949step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39949step1 raw39949step1Labels permutation12 permutation7
    mixedMoment B raw39949step2 raw39949step2Labels = mixedMoment B raw39949step3 raw39949step3Labels := by
      have ha : raw39949step3 = -raw39949step2 := by apply Matrix.ext; change ∀ i j, raw39949step3 i j = -(raw39949step2 i j); unfold raw39949step3 raw39949step2; decide +kernel
      have hl : raw39949step3Labels = raw39949step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39950 raw39950Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39950 raw39950Labels = mixedMoment B raw39950step0 raw39950step0Labels := by
      have hz : ∀ j, raw39950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39950step0 = (fun i j => raw39950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39950step0 raw39950; decide +kernel
      have hl : raw39950step0Labels = raw39950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39950 raw39950Labels permutation434 hz
    mixedMoment B raw39950step0 raw39950step0Labels = mixedMoment B raw39950step1 raw39950step1Labels := by
      have hz : ∀ j, raw39950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39950step1 = (fun i j => raw39950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39950step1 raw39950step0; decide +kernel
      have hl : raw39950step1Labels = raw39950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39950step0 raw39950step0Labels permutation80 hz
    mixedMoment B raw39950step1 raw39950step1Labels = mixedMoment B raw39950step2 raw39950step2Labels := by
      have ha : raw39950step2 = (fun i j => raw39950step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39950step2 raw39950step1; decide +kernel
      have hl : raw39950step2Labels = raw39950step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39950step1 raw39950step1Labels permutation10 permutation7
    mixedMoment B raw39950step2 raw39950step2Labels = mixedMoment B raw39950step3 raw39950step3Labels := by
      have ha : raw39950step3 = -raw39950step2 := by apply Matrix.ext; change ∀ i j, raw39950step3 i j = -(raw39950step2 i j); unfold raw39950step3 raw39950step2; decide +kernel
      have hl : raw39950step3Labels = raw39950step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical39951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39951 raw39951Labels = mixedMoment B node350 node350Labels := by
  calc
    mixedMoment B raw39951 raw39951Labels = mixedMoment B raw39951step0 raw39951step0Labels := by
      have hz : ∀ j, raw39951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39951step0 = (fun i j => raw39951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39951step0 raw39951; decide +kernel
      have hl : raw39951step0Labels = raw39951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39951 raw39951Labels permutation434 hz
    mixedMoment B raw39951step0 raw39951step0Labels = mixedMoment B raw39951step1 raw39951step1Labels := by
      have hz : ∀ j, raw39951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39951step1 = (fun i j => raw39951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39951step1 raw39951step0; decide +kernel
      have hl : raw39951step1Labels = raw39951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39951step0 raw39951step0Labels permutation80 hz
    mixedMoment B raw39951step1 raw39951step1Labels = mixedMoment B raw39951step2 raw39951step2Labels := by
      have ha : raw39951step2 = (fun i j => raw39951step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39951step2 raw39951step1; decide +kernel
      have hl : raw39951step2Labels = raw39951step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39951step1 raw39951step1Labels permutation29 permutation7
    _ = mixedMoment B node350 node350Labels := by rfl

theorem canonical39952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39952 raw39952Labels = mixedMoment B node349 node349Labels := by
  calc
    mixedMoment B raw39952 raw39952Labels = mixedMoment B raw39952step0 raw39952step0Labels := by
      have hz : ∀ j, raw39952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39952step0 = (fun i j => raw39952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39952step0 raw39952; decide +kernel
      have hl : raw39952step0Labels = raw39952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39952 raw39952Labels permutation346 hz
    mixedMoment B raw39952step0 raw39952step0Labels = mixedMoment B raw39952step1 raw39952step1Labels := by
      have ha : raw39952step1 = (fun i j => raw39952step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39952step1 raw39952step0; decide +kernel
      have hl : raw39952step1Labels = raw39952step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39952step0 raw39952step0Labels permutation51 permutation7
    mixedMoment B raw39952step1 raw39952step1Labels = mixedMoment B raw39952step2 raw39952step2Labels := by
      have ha : raw39952step2 = -raw39952step1 := by apply Matrix.ext; change ∀ i j, raw39952step2 i j = -(raw39952step1 i j); unfold raw39952step2 raw39952step1; decide +kernel
      have hl : raw39952step2Labels = raw39952step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node349 node349Labels := by rfl

theorem canonical39953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39953 raw39953Labels = mixedMoment B node395 node395Labels := by
  calc
    mixedMoment B raw39953 raw39953Labels = mixedMoment B raw39953step0 raw39953step0Labels := by
      have hz : ∀ j, raw39953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39953step0 = (fun i j => raw39953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39953step0 raw39953; decide +kernel
      have hl : raw39953step0Labels = raw39953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39953 raw39953Labels permutation346 hz
    mixedMoment B raw39953step0 raw39953step0Labels = mixedMoment B raw39953step1 raw39953step1Labels := by
      have ha : raw39953step1 = (fun i j => raw39953step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39953step1 raw39953step0; decide +kernel
      have hl : raw39953step1Labels = raw39953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39953step0 raw39953step0Labels permutation48 permutation7
    mixedMoment B raw39953step1 raw39953step1Labels = mixedMoment B raw39953step2 raw39953step2Labels := by
      have ha : raw39953step2 = -raw39953step1 := by apply Matrix.ext; change ∀ i j, raw39953step2 i j = -(raw39953step1 i j); unfold raw39953step2 raw39953step1; decide +kernel
      have hl : raw39953step2Labels = raw39953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node395 node395Labels := by rfl

theorem canonical39954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39954 raw39954Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39954 raw39954Labels = mixedMoment B raw39954step0 raw39954step0Labels := by
      have hz : ∀ j, raw39954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39954step0 = (fun i j => raw39954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39954step0 raw39954; decide +kernel
      have hl : raw39954step0Labels = raw39954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39954 raw39954Labels permutation434 hz
    mixedMoment B raw39954step0 raw39954step0Labels = mixedMoment B raw39954step1 raw39954step1Labels := by
      have ha : raw39954step1 = (fun i j => raw39954step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39954step1 raw39954step0; decide +kernel
      have hl : raw39954step1Labels = raw39954step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39954step0 raw39954step0Labels permutation37 permutation7
    mixedMoment B raw39954step1 raw39954step1Labels = mixedMoment B raw39954step2 raw39954step2Labels := by
      have ha : raw39954step2 = -raw39954step1 := by apply Matrix.ext; change ∀ i j, raw39954step2 i j = -(raw39954step1 i j); unfold raw39954step2 raw39954step1; decide +kernel
      have hl : raw39954step2Labels = raw39954step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39955 raw39955Labels = mixedMoment B node346 node346Labels := by
  calc
    mixedMoment B raw39955 raw39955Labels = mixedMoment B raw39955step0 raw39955step0Labels := by
      have hz : ∀ j, raw39955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39955step0 = (fun i j => raw39955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39955step0 raw39955; decide +kernel
      have hl : raw39955step0Labels = raw39955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39955 raw39955Labels permutation434 hz
    mixedMoment B raw39955step0 raw39955step0Labels = mixedMoment B raw39955step1 raw39955step1Labels := by
      have ha : raw39955step1 = (fun i j => raw39955step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39955step1 raw39955step0; decide +kernel
      have hl : raw39955step1Labels = raw39955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39955step0 raw39955step0Labels permutation44 permutation7
    mixedMoment B raw39955step1 raw39955step1Labels = mixedMoment B raw39955step2 raw39955step2Labels := by
      have ha : raw39955step2 = -raw39955step1 := by apply Matrix.ext; change ∀ i j, raw39955step2 i j = -(raw39955step1 i j); unfold raw39955step2 raw39955step1; decide +kernel
      have hl : raw39955step2Labels = raw39955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node346 node346Labels := by rfl

theorem canonical39956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39956 raw39956Labels = mixedMoment B node345 node345Labels := by
  calc
    mixedMoment B raw39956 raw39956Labels = mixedMoment B raw39956step0 raw39956step0Labels := by
      have ha : raw39956step0 = (fun i j => raw39956 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39956step0 raw39956; decide +kernel
      have hl : raw39956step0Labels = raw39956Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39956 raw39956Labels permutation249 permutation7
    mixedMoment B raw39956step0 raw39956step0Labels = mixedMoment B raw39956step1 raw39956step1Labels := by
      have ha : raw39956step1 = -raw39956step0 := by apply Matrix.ext; change ∀ i j, raw39956step1 i j = -(raw39956step0 i j); unfold raw39956step1 raw39956step0; decide +kernel
      have hl : raw39956step1Labels = raw39956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node345 node345Labels := by rfl

theorem canonical39957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39957 raw39957Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw39957 raw39957Labels = mixedMoment B raw39957step0 raw39957step0Labels := by
      have ha : raw39957step0 = (fun i j => raw39957 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39957step0 raw39957; decide +kernel
      have hl : raw39957step0Labels = raw39957Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39957 raw39957Labels permutation169 permutation7
    mixedMoment B raw39957step0 raw39957step0Labels = mixedMoment B raw39957step1 raw39957step1Labels := by
      have ha : raw39957step1 = -raw39957step0 := by apply Matrix.ext; change ∀ i j, raw39957step1 i j = -(raw39957step0 i j); unfold raw39957step1 raw39957step0; decide +kernel
      have hl : raw39957step1Labels = raw39957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node373 node373Labels := by rfl

theorem canonical39958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39958 raw39958Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39958 raw39958Labels = mixedMoment B raw39958step0 raw39958step0Labels := by
      have hz : ∀ j, raw39958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39958step0 = (fun i j => raw39958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39958step0 raw39958; decide +kernel
      have hl : raw39958step0Labels = raw39958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39958 raw39958Labels permutation434 hz
    mixedMoment B raw39958step0 raw39958step0Labels = mixedMoment B raw39958step1 raw39958step1Labels := by
      have ha : raw39958step1 = (fun i j => raw39958step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39958step1 raw39958step0; decide +kernel
      have hl : raw39958step1Labels = raw39958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39958step0 raw39958step0Labels permutation34 permutation7
    mixedMoment B raw39958step1 raw39958step1Labels = mixedMoment B raw39958step2 raw39958step2Labels := by
      have ha : raw39958step2 = -raw39958step1 := by apply Matrix.ext; change ∀ i j, raw39958step2 i j = -(raw39958step1 i j); unfold raw39958step2 raw39958step1; decide +kernel
      have hl : raw39958step2Labels = raw39958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical39959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39959 raw39959Labels = mixedMoment B node385 node385Labels := by
  calc
    mixedMoment B raw39959 raw39959Labels = mixedMoment B raw39959step0 raw39959step0Labels := by
      have hz : ∀ j, raw39959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39959step0 = (fun i j => raw39959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39959step0 raw39959; decide +kernel
      have hl : raw39959step0Labels = raw39959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39959 raw39959Labels permutation434 hz
    mixedMoment B raw39959step0 raw39959step0Labels = mixedMoment B raw39959step1 raw39959step1Labels := by
      have hz : ∀ j, raw39959step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39959step1 = (fun i j => raw39959step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39959step1 raw39959step0; decide +kernel
      have hl : raw39959step1Labels = raw39959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39959step0 raw39959step0Labels permutation80 hz
    mixedMoment B raw39959step1 raw39959step1Labels = mixedMoment B raw39959step2 raw39959step2Labels := by
      have ha : raw39959step2 = (fun i j => raw39959step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39959step2 raw39959step1; decide +kernel
      have hl : raw39959step2Labels = raw39959step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39959step1 raw39959step1Labels permutation23 permutation6
    _ = mixedMoment B node385 node385Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment480 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 480) =
      Integer.Sparse.eval keyMomentRow480 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 480).leftCharge (GramAssembly.key 480).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 420) := by
    have ha : gramCharges (GramAssembly.key 480).leftCharge (GramAssembly.key 480).rightCharge = raw39928 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39928Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39928 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 480).leftCharge (GramAssembly.key 480).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow480, Integer.Sparse.eval]

theorem keyMoment481 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 481) =
      Integer.Sparse.eval keyMomentRow481 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 481).leftCharge (GramAssembly.key 481).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 33) := by
    have ha : gramCharges (GramAssembly.key 481).leftCharge (GramAssembly.key 481).rightCharge = raw39929 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39929Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39929 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 481).leftCharge (GramAssembly.key 481).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow481, Integer.Sparse.eval]

theorem keyMoment482 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 482) =
      Integer.Sparse.eval keyMomentRow482 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 482).leftCharge (GramAssembly.key 482).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 111) := by
    have ha : gramCharges (GramAssembly.key 482).leftCharge (GramAssembly.key 482).rightCharge = raw39930 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39930Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39930 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 482).leftCharge (GramAssembly.key 482).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow482, Integer.Sparse.eval]

theorem keyMoment483 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 483) =
      Integer.Sparse.eval keyMomentRow483 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 483).leftCharge (GramAssembly.key 483).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 405) := by
    have ha : gramCharges (GramAssembly.key 483).leftCharge (GramAssembly.key 483).rightCharge = raw39931 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39931Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39931 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 483).leftCharge (GramAssembly.key 483).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow483, Integer.Sparse.eval]

theorem keyMoment484 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 484) =
      Integer.Sparse.eval keyMomentRow484 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 484).leftCharge (GramAssembly.key 484).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 98) := by
    have ha : gramCharges (GramAssembly.key 484).leftCharge (GramAssembly.key 484).rightCharge = raw39932 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39932Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39932 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 484).leftCharge (GramAssembly.key 484).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow484, Integer.Sparse.eval]

theorem keyMoment485 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 485) =
      Integer.Sparse.eval keyMomentRow485 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 485).leftCharge (GramAssembly.key 485).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 343) := by
    have ha : gramCharges (GramAssembly.key 485).leftCharge (GramAssembly.key 485).rightCharge = raw39933 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39933Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39933 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 485).leftCharge (GramAssembly.key 485).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow485, Integer.Sparse.eval]

theorem keyMoment486 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 486) =
      Integer.Sparse.eval keyMomentRow486 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 486).leftCharge (GramAssembly.key 486).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 452) := by
    have ha : gramCharges (GramAssembly.key 486).leftCharge (GramAssembly.key 486).rightCharge = raw39934 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39934Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39934 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 486).leftCharge (GramAssembly.key 486).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow486, Integer.Sparse.eval]

theorem keyMoment487 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 487) =
      Integer.Sparse.eval keyMomentRow487 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 487).leftCharge (GramAssembly.key 487).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 71) := by
    have ha : gramCharges (GramAssembly.key 487).leftCharge (GramAssembly.key 487).rightCharge = raw39935 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39935Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39935 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 487).leftCharge (GramAssembly.key 487).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow487, Integer.Sparse.eval]

theorem keyMoment488 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 488) =
      Integer.Sparse.eval keyMomentRow488 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 488).leftCharge (GramAssembly.key 488).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 186) := by
    have ha : gramCharges (GramAssembly.key 488).leftCharge (GramAssembly.key 488).rightCharge = raw39936 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39936Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39936 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 488).leftCharge (GramAssembly.key 488).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow488, Integer.Sparse.eval]

theorem keyMoment489 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 489) =
      Integer.Sparse.eval keyMomentRow489 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 489).leftCharge (GramAssembly.key 489).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 95) := by
    have ha : gramCharges (GramAssembly.key 489).leftCharge (GramAssembly.key 489).rightCharge = raw39937 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39937Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39937 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 489).leftCharge (GramAssembly.key 489).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow489, Integer.Sparse.eval]

theorem keyMoment490 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 490) =
      Integer.Sparse.eval keyMomentRow490 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 490).leftCharge (GramAssembly.key 490).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 490).leftCharge (GramAssembly.key 490).rightCharge = raw39938 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39938Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39938 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 490).leftCharge (GramAssembly.key 490).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow490, Integer.Sparse.eval]

theorem keyMoment491 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 491) =
      Integer.Sparse.eval keyMomentRow491 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 491).leftCharge (GramAssembly.key 491).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 68) := by
    have ha : gramCharges (GramAssembly.key 491).leftCharge (GramAssembly.key 491).rightCharge = raw39939 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39939Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39939 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 491).leftCharge (GramAssembly.key 491).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow491, Integer.Sparse.eval]

theorem keyMoment492 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 492) =
      Integer.Sparse.eval keyMomentRow492 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 492).leftCharge (GramAssembly.key 492).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 275) := by
    have ha : gramCharges (GramAssembly.key 492).leftCharge (GramAssembly.key 492).rightCharge = raw39940 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39940Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39940 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 492).leftCharge (GramAssembly.key 492).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow492, Integer.Sparse.eval]

theorem keyMoment493 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 493) =
      Integer.Sparse.eval keyMomentRow493 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 493).leftCharge (GramAssembly.key 493).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 65) := by
    have ha : gramCharges (GramAssembly.key 493).leftCharge (GramAssembly.key 493).rightCharge = raw39941 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39941Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39941 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 493).leftCharge (GramAssembly.key 493).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow493, Integer.Sparse.eval]

theorem keyMoment494 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 494) =
      Integer.Sparse.eval keyMomentRow494 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 494).leftCharge (GramAssembly.key 494).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 406) := by
    have ha : gramCharges (GramAssembly.key 494).leftCharge (GramAssembly.key 494).rightCharge = raw39942 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39942Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39942 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 494).leftCharge (GramAssembly.key 494).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow494, Integer.Sparse.eval]

theorem keyMoment495 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 495) =
      Integer.Sparse.eval keyMomentRow495 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 495).leftCharge (GramAssembly.key 495).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 354) := by
    have ha : gramCharges (GramAssembly.key 495).leftCharge (GramAssembly.key 495).rightCharge = raw39943 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39943Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39943 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 495).leftCharge (GramAssembly.key 495).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow495, Integer.Sparse.eval]

theorem keyMoment496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 496) =
      Integer.Sparse.eval keyMomentRow496 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 496).leftCharge (GramAssembly.key 496).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 328) := by
    have ha : gramCharges (GramAssembly.key 496).leftCharge (GramAssembly.key 496).rightCharge = raw39944 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39944Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39944 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 496).leftCharge (GramAssembly.key 496).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow496, Integer.Sparse.eval]

theorem keyMoment497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 497) =
      Integer.Sparse.eval keyMomentRow497 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 497).leftCharge (GramAssembly.key 497).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 497).leftCharge (GramAssembly.key 497).rightCharge = raw39945 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39945Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39945 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 497).leftCharge (GramAssembly.key 497).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow497, Integer.Sparse.eval]

theorem keyMoment498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 498) =
      Integer.Sparse.eval keyMomentRow498 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 498).leftCharge (GramAssembly.key 498).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 348) := by
    have ha : gramCharges (GramAssembly.key 498).leftCharge (GramAssembly.key 498).rightCharge = raw39946 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39946Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39946 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 498).leftCharge (GramAssembly.key 498).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow498, Integer.Sparse.eval]

theorem keyMoment499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 499) =
      Integer.Sparse.eval keyMomentRow499 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 499).leftCharge (GramAssembly.key 499).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 347) := by
    have ha : gramCharges (GramAssembly.key 499).leftCharge (GramAssembly.key 499).rightCharge = raw39947 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39947Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39947 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 499).leftCharge (GramAssembly.key 499).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow499, Integer.Sparse.eval]

theorem keyMoment500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 500) =
      Integer.Sparse.eval keyMomentRow500 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 500).leftCharge (GramAssembly.key 500).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 394) := by
    have ha : gramCharges (GramAssembly.key 500).leftCharge (GramAssembly.key 500).rightCharge = raw39948 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39948Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39948 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 500).leftCharge (GramAssembly.key 500).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow500, Integer.Sparse.eval]

theorem keyMoment501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 501) =
      Integer.Sparse.eval keyMomentRow501 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 501).leftCharge (GramAssembly.key 501).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 501).leftCharge (GramAssembly.key 501).rightCharge = raw39949 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39949Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39949 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 501).leftCharge (GramAssembly.key 501).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow501, Integer.Sparse.eval]

theorem keyMoment502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 502) =
      Integer.Sparse.eval keyMomentRow502 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 502).leftCharge (GramAssembly.key 502).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 502).leftCharge (GramAssembly.key 502).rightCharge = raw39950 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39950Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39950 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 502).leftCharge (GramAssembly.key 502).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow502, Integer.Sparse.eval]

theorem keyMoment503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 503) =
      Integer.Sparse.eval keyMomentRow503 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 503).leftCharge (GramAssembly.key 503).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 350) := by
    have ha : gramCharges (GramAssembly.key 503).leftCharge (GramAssembly.key 503).rightCharge = raw39951 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39951Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39951 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 503).leftCharge (GramAssembly.key 503).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow503, Integer.Sparse.eval]

theorem keyMoment504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 504) =
      Integer.Sparse.eval keyMomentRow504 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 504).leftCharge (GramAssembly.key 504).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 349) := by
    have ha : gramCharges (GramAssembly.key 504).leftCharge (GramAssembly.key 504).rightCharge = raw39952 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39952Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39952 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 504).leftCharge (GramAssembly.key 504).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow504, Integer.Sparse.eval]

theorem keyMoment505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 505) =
      Integer.Sparse.eval keyMomentRow505 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 505).leftCharge (GramAssembly.key 505).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 395) := by
    have ha : gramCharges (GramAssembly.key 505).leftCharge (GramAssembly.key 505).rightCharge = raw39953 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39953Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39953 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 505).leftCharge (GramAssembly.key 505).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow505, Integer.Sparse.eval]

theorem keyMoment506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 506) =
      Integer.Sparse.eval keyMomentRow506 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 506).leftCharge (GramAssembly.key 506).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 506).leftCharge (GramAssembly.key 506).rightCharge = raw39954 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39954Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39954 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 506).leftCharge (GramAssembly.key 506).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow506, Integer.Sparse.eval]

theorem keyMoment507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 507) =
      Integer.Sparse.eval keyMomentRow507 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 507).leftCharge (GramAssembly.key 507).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 346) := by
    have ha : gramCharges (GramAssembly.key 507).leftCharge (GramAssembly.key 507).rightCharge = raw39955 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39955Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39955 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 507).leftCharge (GramAssembly.key 507).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow507, Integer.Sparse.eval]

theorem keyMoment508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 508) =
      Integer.Sparse.eval keyMomentRow508 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 508).leftCharge (GramAssembly.key 508).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 345) := by
    have ha : gramCharges (GramAssembly.key 508).leftCharge (GramAssembly.key 508).rightCharge = raw39956 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39956Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39956 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 508).leftCharge (GramAssembly.key 508).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow508, Integer.Sparse.eval]

theorem keyMoment509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 509) =
      Integer.Sparse.eval keyMomentRow509 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 509).leftCharge (GramAssembly.key 509).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 509).leftCharge (GramAssembly.key 509).rightCharge = raw39957 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39957Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39957 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 509).leftCharge (GramAssembly.key 509).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow509, Integer.Sparse.eval]

theorem keyMoment510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 510) =
      Integer.Sparse.eval keyMomentRow510 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 510).leftCharge (GramAssembly.key 510).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 510).leftCharge (GramAssembly.key 510).rightCharge = raw39958 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39958Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39958 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 510).leftCharge (GramAssembly.key 510).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow510, Integer.Sparse.eval]

theorem keyMoment511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 511) =
      Integer.Sparse.eval keyMomentRow511 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 511).leftCharge (GramAssembly.key 511).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 385) := by
    have ha : gramCharges (GramAssembly.key 511).leftCharge (GramAssembly.key 511).rightCharge = raw39959 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39959Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39959 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 511).leftCharge (GramAssembly.key 511).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow511, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt480 : keyMomentRows (480 : Fin 2886) =
    keyMomentRow480 := by decide +kernel

theorem keyMomentRowsAt481 : keyMomentRows (481 : Fin 2886) =
    keyMomentRow481 := by decide +kernel

theorem keyMomentRowsAt482 : keyMomentRows (482 : Fin 2886) =
    keyMomentRow482 := by decide +kernel

theorem keyMomentRowsAt483 : keyMomentRows (483 : Fin 2886) =
    keyMomentRow483 := by decide +kernel

theorem keyMomentRowsAt484 : keyMomentRows (484 : Fin 2886) =
    keyMomentRow484 := by decide +kernel

theorem keyMomentRowsAt485 : keyMomentRows (485 : Fin 2886) =
    keyMomentRow485 := by decide +kernel

theorem keyMomentRowsAt486 : keyMomentRows (486 : Fin 2886) =
    keyMomentRow486 := by decide +kernel

theorem keyMomentRowsAt487 : keyMomentRows (487 : Fin 2886) =
    keyMomentRow487 := by decide +kernel

theorem keyMomentRowsAt488 : keyMomentRows (488 : Fin 2886) =
    keyMomentRow488 := by decide +kernel

theorem keyMomentRowsAt489 : keyMomentRows (489 : Fin 2886) =
    keyMomentRow489 := by decide +kernel

theorem keyMomentRowsAt490 : keyMomentRows (490 : Fin 2886) =
    keyMomentRow490 := by decide +kernel

theorem keyMomentRowsAt491 : keyMomentRows (491 : Fin 2886) =
    keyMomentRow491 := by decide +kernel

theorem keyMomentRowsAt492 : keyMomentRows (492 : Fin 2886) =
    keyMomentRow492 := by decide +kernel

theorem keyMomentRowsAt493 : keyMomentRows (493 : Fin 2886) =
    keyMomentRow493 := by decide +kernel

theorem keyMomentRowsAt494 : keyMomentRows (494 : Fin 2886) =
    keyMomentRow494 := by decide +kernel

theorem keyMomentRowsAt495 : keyMomentRows (495 : Fin 2886) =
    keyMomentRow495 := by decide +kernel

theorem keyMomentRowsAt496 : keyMomentRows (496 : Fin 2886) =
    keyMomentRow496 := by decide +kernel

theorem keyMomentRowsAt497 : keyMomentRows (497 : Fin 2886) =
    keyMomentRow497 := by decide +kernel

theorem keyMomentRowsAt498 : keyMomentRows (498 : Fin 2886) =
    keyMomentRow498 := by decide +kernel

theorem keyMomentRowsAt499 : keyMomentRows (499 : Fin 2886) =
    keyMomentRow499 := by decide +kernel

theorem keyMomentRowsAt500 : keyMomentRows (500 : Fin 2886) =
    keyMomentRow500 := by decide +kernel

theorem keyMomentRowsAt501 : keyMomentRows (501 : Fin 2886) =
    keyMomentRow501 := by decide +kernel

theorem keyMomentRowsAt502 : keyMomentRows (502 : Fin 2886) =
    keyMomentRow502 := by decide +kernel

theorem keyMomentRowsAt503 : keyMomentRows (503 : Fin 2886) =
    keyMomentRow503 := by decide +kernel

theorem keyMomentRowsAt504 : keyMomentRows (504 : Fin 2886) =
    keyMomentRow504 := by decide +kernel

theorem keyMomentRowsAt505 : keyMomentRows (505 : Fin 2886) =
    keyMomentRow505 := by decide +kernel

theorem keyMomentRowsAt506 : keyMomentRows (506 : Fin 2886) =
    keyMomentRow506 := by decide +kernel

theorem keyMomentRowsAt507 : keyMomentRows (507 : Fin 2886) =
    keyMomentRow507 := by decide +kernel

theorem keyMomentRowsAt508 : keyMomentRows (508 : Fin 2886) =
    keyMomentRow508 := by decide +kernel

theorem keyMomentRowsAt509 : keyMomentRows (509 : Fin 2886) =
    keyMomentRow509 := by decide +kernel

theorem keyMomentRowsAt510 : keyMomentRows (510 : Fin 2886) =
    keyMomentRow510 := by decide +kernel

theorem keyMomentRowsAt511 : keyMomentRows (511 : Fin 2886) =
    keyMomentRow511 := by decide +kernel

theorem keyMomentChunkSound15_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 15) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 480 ∨ k.val = 481 ∨ k.val = 482 ∨ k.val = 483 ∨ k.val = 484 ∨ k.val = 485 ∨ k.val = 486 ∨ k.val = 487 ∨ k.val = 488 ∨ k.val = 489 ∨ k.val = 490 ∨ k.val = 491 ∨ k.val = 492 ∨ k.val = 493 ∨ k.val = 494 ∨ k.val = 495 ∨ k.val = 496 ∨ k.val = 497 ∨ k.val = 498 ∨ k.val = 499 ∨ k.val = 500 ∨ k.val = 501 ∨ k.val = 502 ∨ k.val = 503 ∨ k.val = 504 ∨ k.val = 505 ∨ k.val = 506 ∨ k.val = 507 ∨ k.val = 508 ∨ k.val = 509 ∨ k.val = 510 ∨ k.val = 511 := by omega
  rcases heq with h480 | h481 | h482 | h483 | h484 | h485 | h486 | h487 | h488 | h489 | h490 | h491 | h492 | h493 | h494 | h495 | h496 | h497 | h498 | h499 | h500 | h501 | h502 | h503 | h504 | h505 | h506 | h507 | h508 | h509 | h510 | h511
  · have he : k = (480 : Fin 2886) := Fin.ext h480
    subst k
    rw [keyMomentRowsAt480]
    exact keyMoment480 B hB
  · have he : k = (481 : Fin 2886) := Fin.ext h481
    subst k
    rw [keyMomentRowsAt481]
    exact keyMoment481 B hB
  · have he : k = (482 : Fin 2886) := Fin.ext h482
    subst k
    rw [keyMomentRowsAt482]
    exact keyMoment482 B hB
  · have he : k = (483 : Fin 2886) := Fin.ext h483
    subst k
    rw [keyMomentRowsAt483]
    exact keyMoment483 B hB
  · have he : k = (484 : Fin 2886) := Fin.ext h484
    subst k
    rw [keyMomentRowsAt484]
    exact keyMoment484 B hB
  · have he : k = (485 : Fin 2886) := Fin.ext h485
    subst k
    rw [keyMomentRowsAt485]
    exact keyMoment485 B hB
  · have he : k = (486 : Fin 2886) := Fin.ext h486
    subst k
    rw [keyMomentRowsAt486]
    exact keyMoment486 B hB
  · have he : k = (487 : Fin 2886) := Fin.ext h487
    subst k
    rw [keyMomentRowsAt487]
    exact keyMoment487 B hB
  · have he : k = (488 : Fin 2886) := Fin.ext h488
    subst k
    rw [keyMomentRowsAt488]
    exact keyMoment488 B hB
  · have he : k = (489 : Fin 2886) := Fin.ext h489
    subst k
    rw [keyMomentRowsAt489]
    exact keyMoment489 B hB
  · have he : k = (490 : Fin 2886) := Fin.ext h490
    subst k
    rw [keyMomentRowsAt490]
    exact keyMoment490 B hB
  · have he : k = (491 : Fin 2886) := Fin.ext h491
    subst k
    rw [keyMomentRowsAt491]
    exact keyMoment491 B hB
  · have he : k = (492 : Fin 2886) := Fin.ext h492
    subst k
    rw [keyMomentRowsAt492]
    exact keyMoment492 B hB
  · have he : k = (493 : Fin 2886) := Fin.ext h493
    subst k
    rw [keyMomentRowsAt493]
    exact keyMoment493 B hB
  · have he : k = (494 : Fin 2886) := Fin.ext h494
    subst k
    rw [keyMomentRowsAt494]
    exact keyMoment494 B hB
  · have he : k = (495 : Fin 2886) := Fin.ext h495
    subst k
    rw [keyMomentRowsAt495]
    exact keyMoment495 B hB
  · have he : k = (496 : Fin 2886) := Fin.ext h496
    subst k
    rw [keyMomentRowsAt496]
    exact keyMoment496 B hB
  · have he : k = (497 : Fin 2886) := Fin.ext h497
    subst k
    rw [keyMomentRowsAt497]
    exact keyMoment497 B hB
  · have he : k = (498 : Fin 2886) := Fin.ext h498
    subst k
    rw [keyMomentRowsAt498]
    exact keyMoment498 B hB
  · have he : k = (499 : Fin 2886) := Fin.ext h499
    subst k
    rw [keyMomentRowsAt499]
    exact keyMoment499 B hB
  · have he : k = (500 : Fin 2886) := Fin.ext h500
    subst k
    rw [keyMomentRowsAt500]
    exact keyMoment500 B hB
  · have he : k = (501 : Fin 2886) := Fin.ext h501
    subst k
    rw [keyMomentRowsAt501]
    exact keyMoment501 B hB
  · have he : k = (502 : Fin 2886) := Fin.ext h502
    subst k
    rw [keyMomentRowsAt502]
    exact keyMoment502 B hB
  · have he : k = (503 : Fin 2886) := Fin.ext h503
    subst k
    rw [keyMomentRowsAt503]
    exact keyMoment503 B hB
  · have he : k = (504 : Fin 2886) := Fin.ext h504
    subst k
    rw [keyMomentRowsAt504]
    exact keyMoment504 B hB
  · have he : k = (505 : Fin 2886) := Fin.ext h505
    subst k
    rw [keyMomentRowsAt505]
    exact keyMoment505 B hB
  · have he : k = (506 : Fin 2886) := Fin.ext h506
    subst k
    rw [keyMomentRowsAt506]
    exact keyMoment506 B hB
  · have he : k = (507 : Fin 2886) := Fin.ext h507
    subst k
    rw [keyMomentRowsAt507]
    exact keyMoment507 B hB
  · have he : k = (508 : Fin 2886) := Fin.ext h508
    subst k
    rw [keyMomentRowsAt508]
    exact keyMoment508 B hB
  · have he : k = (509 : Fin 2886) := Fin.ext h509
    subst k
    rw [keyMomentRowsAt509]
    exact keyMoment509 B hB
  · have he : k = (510 : Fin 2886) := Fin.ext h510
    subst k
    rw [keyMomentRowsAt510]
    exact keyMoment510 B hB
  · have he : k = (511 : Fin 2886) := Fin.ext h511
    subst k
    rw [keyMomentRowsAt511]
    exact keyMoment511 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound15_e_oai
