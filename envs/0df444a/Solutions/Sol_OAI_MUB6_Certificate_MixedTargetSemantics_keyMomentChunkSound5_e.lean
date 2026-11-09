-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:57:34.855351+00:00
-- url     : https://prove2.me/submissions/5ef34cac-d2c4-4bed-8a68-8fe796021e32

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39610 raw39610Labels = mixedMoment B node104 node104Labels := by
  calc
    mixedMoment B raw39610 raw39610Labels = mixedMoment B raw39610step0 raw39610step0Labels := by
      have hz : ∀ j, raw39610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39610step0 = (fun i j => raw39610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39610step0 raw39610; decide +kernel
      have hl : raw39610step0Labels = raw39610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39610 raw39610Labels permutation434 hz
    mixedMoment B raw39610step0 raw39610step0Labels = mixedMoment B raw39610step1 raw39610step1Labels := by
      have hz : ∀ j, raw39610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39610step1 = (fun i j => raw39610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39610step1 raw39610step0; decide +kernel
      have hl : raw39610step1Labels = raw39610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39610step0 raw39610step0Labels permutation80 hz
    mixedMoment B raw39610step1 raw39610step1Labels = mixedMoment B raw39610step2 raw39610step2Labels := by
      have hz : ∀ j, raw39610step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39610step2 = (fun i j => raw39610step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39610step2 raw39610step1; decide +kernel
      have hl : raw39610step2Labels = raw39610step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39610step1 raw39610step1Labels permutation14 hz
    mixedMoment B raw39610step2 raw39610step2Labels = mixedMoment B raw39610step3 raw39610step3Labels := by
      have ha : raw39610step3 = (fun i j => raw39610step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39610step3 raw39610step2; decide +kernel
      have hl : raw39610step3Labels = raw39610step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39610step2 raw39610step2Labels permutation5 permutation6
    _ = mixedMoment B node104 node104Labels := by rfl

theorem canonical39611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39611 raw39611Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw39611 raw39611Labels = mixedMoment B raw39611step0 raw39611step0Labels := by
      have hz : ∀ j, raw39611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39611step0 = (fun i j => raw39611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39611step0 raw39611; decide +kernel
      have hl : raw39611step0Labels = raw39611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39611 raw39611Labels permutation434 hz
    mixedMoment B raw39611step0 raw39611step0Labels = mixedMoment B raw39611step1 raw39611step1Labels := by
      have hz : ∀ j, raw39611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39611step1 = (fun i j => raw39611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39611step1 raw39611step0; decide +kernel
      have hl : raw39611step1Labels = raw39611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39611step0 raw39611step0Labels permutation80 hz
    mixedMoment B raw39611step1 raw39611step1Labels = mixedMoment B raw39611step2 raw39611step2Labels := by
      have hz : ∀ j, raw39611step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39611step2 = (fun i j => raw39611step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39611step2 raw39611step1; decide +kernel
      have hl : raw39611step2Labels = raw39611step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39611step1 raw39611step1Labels permutation14 hz
    mixedMoment B raw39611step2 raw39611step2Labels = mixedMoment B raw39611step3 raw39611step3Labels := by
      have ha : raw39611step3 = (fun i j => raw39611step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39611step3 raw39611step2; decide +kernel
      have hl : raw39611step3Labels = raw39611step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39611step2 raw39611step2Labels permutation2 permutation7
    mixedMoment B raw39611step3 raw39611step3Labels = mixedMoment B raw39611step4 raw39611step4Labels := by
      have ha : raw39611step4 = -raw39611step3 := by apply Matrix.ext; change ∀ i j, raw39611step4 i j = -(raw39611step3 i j); unfold raw39611step4 raw39611step3; decide +kernel
      have hl : raw39611step4Labels = raw39611step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node100 node100Labels := by rfl

theorem canonical39612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39612 raw39612Labels = mixedMoment B node37 node37Labels := by
  calc
    mixedMoment B raw39612 raw39612Labels = mixedMoment B raw39612step0 raw39612step0Labels := by
      have hz : ∀ j, raw39612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39612step0 = (fun i j => raw39612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39612step0 raw39612; decide +kernel
      have hl : raw39612step0Labels = raw39612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39612 raw39612Labels permutation434 hz
    mixedMoment B raw39612step0 raw39612step0Labels = mixedMoment B raw39612step1 raw39612step1Labels := by
      have hz : ∀ j, raw39612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39612step1 = (fun i j => raw39612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39612step1 raw39612step0; decide +kernel
      have hl : raw39612step1Labels = raw39612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39612step0 raw39612step0Labels permutation80 hz
    mixedMoment B raw39612step1 raw39612step1Labels = mixedMoment B raw39612step2 raw39612step2Labels := by
      have hz : ∀ j, raw39612step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39612step2 = (fun i j => raw39612step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39612step2 raw39612step1; decide +kernel
      have hl : raw39612step2Labels = raw39612step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39612step1 raw39612step1Labels permutation14 hz
    mixedMoment B raw39612step2 raw39612step2Labels = mixedMoment B raw39612step3 raw39612step3Labels := by
      have ha : raw39612step3 = (fun i j => raw39612step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39612step3 raw39612step2; decide +kernel
      have hl : raw39612step3Labels = raw39612step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39612step2 raw39612step2Labels permutation7 permutation6
    _ = mixedMoment B node37 node37Labels := by rfl

theorem canonical39613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39613 raw39613Labels = mixedMoment B node16 node16Labels := by
  calc
    mixedMoment B raw39613 raw39613Labels = mixedMoment B raw39613step0 raw39613step0Labels := by
      have hz : ∀ j, raw39613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39613step0 = (fun i j => raw39613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39613step0 raw39613; decide +kernel
      have hl : raw39613step0Labels = raw39613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39613 raw39613Labels permutation346 hz
    mixedMoment B raw39613step0 raw39613step0Labels = mixedMoment B raw39613step1 raw39613step1Labels := by
      have hz : ∀ j, raw39613step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39613step1 = (fun i j => raw39613step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39613step1 raw39613step0; decide +kernel
      have hl : raw39613step1Labels = raw39613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39613step0 raw39613step0Labels permutation56 hz
    mixedMoment B raw39613step1 raw39613step1Labels = mixedMoment B raw39613step2 raw39613step2Labels := by
      have ha : raw39613step2 = (fun i j => raw39613step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39613step2 raw39613step1; decide +kernel
      have hl : raw39613step2Labels = raw39613step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39613step1 raw39613step1Labels permutation31 permutation6
    _ = mixedMoment B node16 node16Labels := by rfl

theorem canonical39614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39614 raw39614Labels = mixedMoment B node88 node88Labels := by
  calc
    mixedMoment B raw39614 raw39614Labels = mixedMoment B raw39614step0 raw39614step0Labels := by
      have hz : ∀ j, raw39614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39614step0 = (fun i j => raw39614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39614step0 raw39614; decide +kernel
      have hl : raw39614step0Labels = raw39614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39614 raw39614Labels permutation346 hz
    mixedMoment B raw39614step0 raw39614step0Labels = mixedMoment B raw39614step1 raw39614step1Labels := by
      have hz : ∀ j, raw39614step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39614step1 = (fun i j => raw39614step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39614step1 raw39614step0; decide +kernel
      have hl : raw39614step1Labels = raw39614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39614step0 raw39614step0Labels permutation56 hz
    mixedMoment B raw39614step1 raw39614step1Labels = mixedMoment B raw39614step2 raw39614step2Labels := by
      have ha : raw39614step2 = (fun i j => raw39614step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39614step2 raw39614step1; decide +kernel
      have hl : raw39614step2Labels = raw39614step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39614step1 raw39614step1Labels permutation17 permutation6
    _ = mixedMoment B node88 node88Labels := by rfl

theorem canonical39615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39615 raw39615Labels = mixedMoment B node99 node99Labels := by
  calc
    mixedMoment B raw39615 raw39615Labels = mixedMoment B raw39615step0 raw39615step0Labels := by
      have hz : ∀ j, raw39615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39615step0 = (fun i j => raw39615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39615step0 raw39615; decide +kernel
      have hl : raw39615step0Labels = raw39615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39615 raw39615Labels permutation346 hz
    mixedMoment B raw39615step0 raw39615step0Labels = mixedMoment B raw39615step1 raw39615step1Labels := by
      have hz : ∀ j, raw39615step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39615step1 = (fun i j => raw39615step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39615step1 raw39615step0; decide +kernel
      have hl : raw39615step1Labels = raw39615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39615step0 raw39615step0Labels permutation56 hz
    mixedMoment B raw39615step1 raw39615step1Labels = mixedMoment B raw39615step2 raw39615step2Labels := by
      have ha : raw39615step2 = (fun i j => raw39615step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39615step2 raw39615step1; decide +kernel
      have hl : raw39615step2Labels = raw39615step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39615step1 raw39615step1Labels permutation12 permutation7
    mixedMoment B raw39615step2 raw39615step2Labels = mixedMoment B raw39615step3 raw39615step3Labels := by
      have ha : raw39615step3 = -raw39615step2 := by apply Matrix.ext; change ∀ i j, raw39615step3 i j = -(raw39615step2 i j); unfold raw39615step3 raw39615step2; decide +kernel
      have hl : raw39615step3Labels = raw39615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node99 node99Labels := by rfl

theorem canonical39616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39616 raw39616Labels = mixedMoment B node59 node59Labels := by
  calc
    mixedMoment B raw39616 raw39616Labels = mixedMoment B raw39616step0 raw39616step0Labels := by
      have hz : ∀ j, raw39616 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39616step0 = (fun i j => raw39616 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39616step0 raw39616; decide +kernel
      have hl : raw39616step0Labels = raw39616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39616 raw39616Labels permutation265 hz
    mixedMoment B raw39616step0 raw39616step0Labels = mixedMoment B raw39616step1 raw39616step1Labels := by
      have ha : raw39616step1 = (fun i j => raw39616step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39616step1 raw39616step0; decide +kernel
      have hl : raw39616step1Labels = raw39616step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39616step0 raw39616step0Labels permutation97 permutation6
    _ = mixedMoment B node59 node59Labels := by rfl

theorem canonical39617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39617 raw39617Labels = mixedMoment B node19 node19Labels := by
  calc
    mixedMoment B raw39617 raw39617Labels = mixedMoment B raw39617step0 raw39617step0Labels := by
      have hz : ∀ j, raw39617 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39617step0 = (fun i j => raw39617 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39617step0 raw39617; decide +kernel
      have hl : raw39617step0Labels = raw39617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39617 raw39617Labels permutation434 hz
    mixedMoment B raw39617step0 raw39617step0Labels = mixedMoment B raw39617step1 raw39617step1Labels := by
      have hz : ∀ j, raw39617step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39617step1 = (fun i j => raw39617step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39617step1 raw39617step0; decide +kernel
      have hl : raw39617step1Labels = raw39617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39617step0 raw39617step0Labels permutation80 hz
    mixedMoment B raw39617step1 raw39617step1Labels = mixedMoment B raw39617step2 raw39617step2Labels := by
      have ha : raw39617step2 = (fun i j => raw39617step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39617step2 raw39617step1; decide +kernel
      have hl : raw39617step2Labels = raw39617step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39617step1 raw39617step1Labels permutation11 permutation7
    mixedMoment B raw39617step2 raw39617step2Labels = mixedMoment B raw39617step3 raw39617step3Labels := by
      have ha : raw39617step3 = -raw39617step2 := by apply Matrix.ext; change ∀ i j, raw39617step3 i j = -(raw39617step2 i j); unfold raw39617step3 raw39617step2; decide +kernel
      have hl : raw39617step3Labels = raw39617step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node19 node19Labels := by rfl

theorem canonical39618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39618 raw39618Labels = mixedMoment B node14 node14Labels := by
  calc
    mixedMoment B raw39618 raw39618Labels = mixedMoment B raw39618step0 raw39618step0Labels := by
      have hz : ∀ j, raw39618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39618step0 = (fun i j => raw39618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39618step0 raw39618; decide +kernel
      have hl : raw39618step0Labels = raw39618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39618 raw39618Labels permutation346 hz
    mixedMoment B raw39618step0 raw39618step0Labels = mixedMoment B raw39618step1 raw39618step1Labels := by
      have ha : raw39618step1 = (fun i j => raw39618step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39618step1 raw39618step0; decide +kernel
      have hl : raw39618step1Labels = raw39618step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39618step0 raw39618step0Labels permutation53 permutation7
    mixedMoment B raw39618step1 raw39618step1Labels = mixedMoment B raw39618step2 raw39618step2Labels := by
      have ha : raw39618step2 = -raw39618step1 := by apply Matrix.ext; change ∀ i j, raw39618step2 i j = -(raw39618step1 i j); unfold raw39618step2 raw39618step1; decide +kernel
      have hl : raw39618step2Labels = raw39618step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node14 node14Labels := by rfl

theorem canonical39619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39619 raw39619Labels = mixedMoment B node12 node12Labels := by
  calc
    mixedMoment B raw39619 raw39619Labels = mixedMoment B raw39619step0 raw39619step0Labels := by
      have hz : ∀ j, raw39619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39619step0 = (fun i j => raw39619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39619step0 raw39619; decide +kernel
      have hl : raw39619step0Labels = raw39619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39619 raw39619Labels permutation434 hz
    mixedMoment B raw39619step0 raw39619step0Labels = mixedMoment B raw39619step1 raw39619step1Labels := by
      have ha : raw39619step1 = (fun i j => raw39619step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39619step1 raw39619step0; decide +kernel
      have hl : raw39619step1Labels = raw39619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39619step0 raw39619step0Labels permutation46 permutation7
    mixedMoment B raw39619step1 raw39619step1Labels = mixedMoment B raw39619step2 raw39619step2Labels := by
      have ha : raw39619step2 = -raw39619step1 := by apply Matrix.ext; change ∀ i j, raw39619step2 i j = -(raw39619step1 i j); unfold raw39619step2 raw39619step1; decide +kernel
      have hl : raw39619step2Labels = raw39619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node12 node12Labels := by rfl

theorem canonical39620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39620 raw39620Labels = mixedMoment B node17 node17Labels := by
  calc
    mixedMoment B raw39620 raw39620Labels = mixedMoment B raw39620step0 raw39620step0Labels := by
      have hz : ∀ j, raw39620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39620step0 = (fun i j => raw39620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39620step0 raw39620; decide +kernel
      have hl : raw39620step0Labels = raw39620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39620 raw39620Labels permutation434 hz
    mixedMoment B raw39620step0 raw39620step0Labels = mixedMoment B raw39620step1 raw39620step1Labels := by
      have hz : ∀ j, raw39620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39620step1 = (fun i j => raw39620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39620step1 raw39620step0; decide +kernel
      have hl : raw39620step1Labels = raw39620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39620step0 raw39620step0Labels permutation80 hz
    mixedMoment B raw39620step1 raw39620step1Labels = mixedMoment B raw39620step2 raw39620step2Labels := by
      have ha : raw39620step2 = (fun i j => raw39620step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39620step2 raw39620step1; decide +kernel
      have hl : raw39620step2Labels = raw39620step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39620step1 raw39620step1Labels permutation10 permutation7
    mixedMoment B raw39620step2 raw39620step2Labels = mixedMoment B raw39620step3 raw39620step3Labels := by
      have ha : raw39620step3 = -raw39620step2 := by apply Matrix.ext; change ∀ i j, raw39620step3 i j = -(raw39620step2 i j); unfold raw39620step3 raw39620step2; decide +kernel
      have hl : raw39620step3Labels = raw39620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node17 node17Labels := by rfl

theorem canonical39621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39621 raw39621Labels = mixedMoment B node15 node15Labels := by
  calc
    mixedMoment B raw39621 raw39621Labels = mixedMoment B raw39621step0 raw39621step0Labels := by
      have hz : ∀ j, raw39621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39621step0 = (fun i j => raw39621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39621step0 raw39621; decide +kernel
      have hl : raw39621step0Labels = raw39621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39621 raw39621Labels permutation346 hz
    mixedMoment B raw39621step0 raw39621step0Labels = mixedMoment B raw39621step1 raw39621step1Labels := by
      have ha : raw39621step1 = (fun i j => raw39621step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39621step1 raw39621step0; decide +kernel
      have hl : raw39621step1Labels = raw39621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39621step0 raw39621step0Labels permutation54 permutation7
    mixedMoment B raw39621step1 raw39621step1Labels = mixedMoment B raw39621step2 raw39621step2Labels := by
      have ha : raw39621step2 = -raw39621step1 := by apply Matrix.ext; change ∀ i j, raw39621step2 i j = -(raw39621step1 i j); unfold raw39621step2 raw39621step1; decide +kernel
      have hl : raw39621step2Labels = raw39621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node15 node15Labels := by rfl

theorem canonical39622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39622 raw39622Labels = mixedMoment B node8 node8Labels := by
  calc
    mixedMoment B raw39622 raw39622Labels = mixedMoment B raw39622step0 raw39622step0Labels := by
      have ha : raw39622step0 = (fun i j => raw39622 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39622step0 raw39622; decide +kernel
      have hl : raw39622step0Labels = raw39622Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39622 raw39622Labels permutation224 permutation7
    mixedMoment B raw39622step0 raw39622step0Labels = mixedMoment B raw39622step1 raw39622step1Labels := by
      have ha : raw39622step1 = -raw39622step0 := by apply Matrix.ext; change ∀ i j, raw39622step1 i j = -(raw39622step0 i j); unfold raw39622step1 raw39622step0; decide +kernel
      have hl : raw39622step1Labels = raw39622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node8 node8Labels := by rfl

theorem canonical39623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39623 raw39623Labels = mixedMoment B node9 node9Labels := by
  calc
    mixedMoment B raw39623 raw39623Labels = mixedMoment B raw39623step0 raw39623step0Labels := by
      have hz : ∀ j, raw39623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39623step0 = (fun i j => raw39623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39623step0 raw39623; decide +kernel
      have hl : raw39623step0Labels = raw39623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39623 raw39623Labels permutation434 hz
    mixedMoment B raw39623step0 raw39623step0Labels = mixedMoment B raw39623step1 raw39623step1Labels := by
      have ha : raw39623step1 = (fun i j => raw39623step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39623step1 raw39623step0; decide +kernel
      have hl : raw39623step1Labels = raw39623step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39623step0 raw39623step0Labels permutation44 permutation7
    mixedMoment B raw39623step1 raw39623step1Labels = mixedMoment B raw39623step2 raw39623step2Labels := by
      have ha : raw39623step2 = -raw39623step1 := by apply Matrix.ext; change ∀ i j, raw39623step2 i j = -(raw39623step1 i j); unfold raw39623step2 raw39623step1; decide +kernel
      have hl : raw39623step2Labels = raw39623step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node9 node9Labels := by rfl

theorem canonical39624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39624 raw39624Labels = mixedMoment B node13 node13Labels := by
  calc
    mixedMoment B raw39624 raw39624Labels = mixedMoment B raw39624step0 raw39624step0Labels := by
      have hz : ∀ j, raw39624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39624step0 = (fun i j => raw39624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39624step0 raw39624; decide +kernel
      have hl : raw39624step0Labels = raw39624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39624 raw39624Labels permutation434 hz
    mixedMoment B raw39624step0 raw39624step0Labels = mixedMoment B raw39624step1 raw39624step1Labels := by
      have hz : ∀ j, raw39624step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39624step1 = (fun i j => raw39624step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39624step1 raw39624step0; decide +kernel
      have hl : raw39624step1Labels = raw39624step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39624step0 raw39624step0Labels permutation80 hz
    mixedMoment B raw39624step1 raw39624step1Labels = mixedMoment B raw39624step2 raw39624step2Labels := by
      have ha : raw39624step2 = (fun i j => raw39624step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39624step2 raw39624step1; decide +kernel
      have hl : raw39624step2Labels = raw39624step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39624step1 raw39624step1Labels permutation10 permutation7
    mixedMoment B raw39624step2 raw39624step2Labels = mixedMoment B raw39624step3 raw39624step3Labels := by
      have ha : raw39624step3 = -raw39624step2 := by apply Matrix.ext; change ∀ i j, raw39624step3 i j = -(raw39624step2 i j); unfold raw39624step3 raw39624step2; decide +kernel
      have hl : raw39624step3Labels = raw39624step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node13 node13Labels := by rfl

theorem canonical39625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39625 raw39625Labels = mixedMoment B node11 node11Labels := by
  calc
    mixedMoment B raw39625 raw39625Labels = mixedMoment B raw39625step0 raw39625step0Labels := by
      have hz : ∀ j, raw39625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39625step0 = (fun i j => raw39625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39625step0 raw39625; decide +kernel
      have hl : raw39625step0Labels = raw39625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39625 raw39625Labels permutation346 hz
    mixedMoment B raw39625step0 raw39625step0Labels = mixedMoment B raw39625step1 raw39625step1Labels := by
      have ha : raw39625step1 = (fun i j => raw39625step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39625step1 raw39625step0; decide +kernel
      have hl : raw39625step1Labels = raw39625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39625step0 raw39625step0Labels permutation51 permutation7
    mixedMoment B raw39625step1 raw39625step1Labels = mixedMoment B raw39625step2 raw39625step2Labels := by
      have ha : raw39625step2 = -raw39625step1 := by apply Matrix.ext; change ∀ i j, raw39625step2 i j = -(raw39625step1 i j); unfold raw39625step2 raw39625step1; decide +kernel
      have hl : raw39625step2Labels = raw39625step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node11 node11Labels := by rfl

theorem canonical39626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39626 raw39626Labels = mixedMoment B node20 node20Labels := by
  calc
    mixedMoment B raw39626 raw39626Labels = mixedMoment B raw39626step0 raw39626step0Labels := by
      have hz : ∀ j, raw39626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39626step0 = (fun i j => raw39626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39626step0 raw39626; decide +kernel
      have hl : raw39626step0Labels = raw39626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39626 raw39626Labels permutation434 hz
    mixedMoment B raw39626step0 raw39626step0Labels = mixedMoment B raw39626step1 raw39626step1Labels := by
      have hz : ∀ j, raw39626step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39626step1 = (fun i j => raw39626step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39626step1 raw39626step0; decide +kernel
      have hl : raw39626step1Labels = raw39626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39626step0 raw39626step0Labels permutation80 hz
    mixedMoment B raw39626step1 raw39626step1Labels = mixedMoment B raw39626step2 raw39626step2Labels := by
      have hz : ∀ j, raw39626step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39626step2 = (fun i j => raw39626step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39626step2 raw39626step1; decide +kernel
      have hl : raw39626step2Labels = raw39626step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39626step1 raw39626step1Labels permutation14 hz
    mixedMoment B raw39626step2 raw39626step2Labels = mixedMoment B raw39626step3 raw39626step3Labels := by
      have ha : raw39626step3 = (fun i j => raw39626step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39626step3 raw39626step2; decide +kernel
      have hl : raw39626step3Labels = raw39626step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39626step2 raw39626step2Labels permutation7 permutation6
    _ = mixedMoment B node20 node20Labels := by rfl

theorem canonical39627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39627 raw39627Labels = mixedMoment B node16 node16Labels := by
  calc
    mixedMoment B raw39627 raw39627Labels = mixedMoment B raw39627step0 raw39627step0Labels := by
      have hz : ∀ j, raw39627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39627step0 = (fun i j => raw39627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39627step0 raw39627; decide +kernel
      have hl : raw39627step0Labels = raw39627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39627 raw39627Labels permutation346 hz
    mixedMoment B raw39627step0 raw39627step0Labels = mixedMoment B raw39627step1 raw39627step1Labels := by
      have hz : ∀ j, raw39627step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39627step1 = (fun i j => raw39627step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39627step1 raw39627step0; decide +kernel
      have hl : raw39627step1Labels = raw39627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39627step0 raw39627step0Labels permutation56 hz
    mixedMoment B raw39627step1 raw39627step1Labels = mixedMoment B raw39627step2 raw39627step2Labels := by
      have ha : raw39627step2 = (fun i j => raw39627step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39627step2 raw39627step1; decide +kernel
      have hl : raw39627step2Labels = raw39627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39627step1 raw39627step1Labels permutation13 permutation7
    mixedMoment B raw39627step2 raw39627step2Labels = mixedMoment B raw39627step3 raw39627step3Labels := by
      have ha : raw39627step3 = -raw39627step2 := by apply Matrix.ext; change ∀ i j, raw39627step3 i j = -(raw39627step2 i j); unfold raw39627step3 raw39627step2; decide +kernel
      have hl : raw39627step3Labels = raw39627step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node16 node16Labels := by rfl

theorem canonical39628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39628 raw39628Labels = mixedMoment B node18 node18Labels := by
  calc
    mixedMoment B raw39628 raw39628Labels = mixedMoment B raw39628step0 raw39628step0Labels := by
      have hz : ∀ j, raw39628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39628step0 = (fun i j => raw39628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39628step0 raw39628; decide +kernel
      have hl : raw39628step0Labels = raw39628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39628 raw39628Labels permutation346 hz
    mixedMoment B raw39628step0 raw39628step0Labels = mixedMoment B raw39628step1 raw39628step1Labels := by
      have hz : ∀ j, raw39628step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39628step1 = (fun i j => raw39628step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39628step1 raw39628step0; decide +kernel
      have hl : raw39628step1Labels = raw39628step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39628step0 raw39628step0Labels permutation56 hz
    mixedMoment B raw39628step1 raw39628step1Labels = mixedMoment B raw39628step2 raw39628step2Labels := by
      have ha : raw39628step2 = (fun i j => raw39628step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39628step2 raw39628step1; decide +kernel
      have hl : raw39628step2Labels = raw39628step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39628step1 raw39628step1Labels permutation13 permutation7
    mixedMoment B raw39628step2 raw39628step2Labels = mixedMoment B raw39628step3 raw39628step3Labels := by
      have ha : raw39628step3 = -raw39628step2 := by apply Matrix.ext; change ∀ i j, raw39628step3 i j = -(raw39628step2 i j); unfold raw39628step3 raw39628step2; decide +kernel
      have hl : raw39628step3Labels = raw39628step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node18 node18Labels := by rfl

theorem canonical39629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39629 raw39629Labels = mixedMoment B node5502 node5502Labels := by
  calc
    mixedMoment B raw39629 raw39629Labels = mixedMoment B raw39629step0 raw39629step0Labels := by
      have hz : ∀ j, raw39629 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39629step0 = (fun i j => raw39629 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39629step0 raw39629; decide +kernel
      have hl : raw39629step0Labels = raw39629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39629 raw39629Labels permutation520 hz
    mixedMoment B raw39629step0 raw39629step0Labels = mixedMoment B raw39629step1 raw39629step1Labels := by
      have hz : ∀ j, raw39629step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39629step1 = (fun i j => raw39629step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39629step1 raw39629step0; decide +kernel
      have hl : raw39629step1Labels = raw39629step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39629step0 raw39629step0Labels permutation104 hz
    mixedMoment B raw39629step1 raw39629step1Labels = mixedMoment B raw39629step2 raw39629step2Labels := by
      have hz : ∀ j, raw39629step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39629step2 = (fun i j => raw39629step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39629step2 raw39629step1; decide +kernel
      have hl : raw39629step2Labels = raw39629step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39629step1 raw39629step1Labels permutation20 hz
    mixedMoment B raw39629step2 raw39629step2Labels = mixedMoment B raw39629step3 raw39629step3Labels := by
      have ha : raw39629step3 = (fun i j => raw39629step2 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39629step3 raw39629step2; decide +kernel
      have hl : raw39629step3Labels = raw39629step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39629step2 raw39629step2Labels permutation7 permutation5
    _ = mixedMoment B node5502 node5502Labels := by rfl

theorem canonical39630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39630 raw39630Labels = mixedMoment B node389 node389Labels := by
  calc
    mixedMoment B raw39630 raw39630Labels = mixedMoment B raw39630step0 raw39630step0Labels := by
      have hz : ∀ j, raw39630 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39630step0 = (fun i j => raw39630 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39630step0 raw39630; decide +kernel
      have hl : raw39630step0Labels = raw39630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39630 raw39630Labels permutation434 hz
    mixedMoment B raw39630step0 raw39630step0Labels = mixedMoment B raw39630step1 raw39630step1Labels := by
      have hz : ∀ j, raw39630step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39630step1 = (fun i j => raw39630step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39630step1 raw39630step0; decide +kernel
      have hl : raw39630step1Labels = raw39630step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39630step0 raw39630step0Labels permutation80 hz
    mixedMoment B raw39630step1 raw39630step1Labels = mixedMoment B raw39630step2 raw39630step2Labels := by
      have ha : raw39630step2 = (fun i j => raw39630step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39630step2 raw39630step1; decide +kernel
      have hl : raw39630step2Labels = raw39630step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39630step1 raw39630step1Labels permutation8 permutation5
    mixedMoment B raw39630step2 raw39630step2Labels = mixedMoment B raw39630step3 raw39630step3Labels := by
      have ha : raw39630step3 = -raw39630step2 := by apply Matrix.ext; change ∀ i j, raw39630step3 i j = -(raw39630step2 i j); unfold raw39630step3 raw39630step2; decide +kernel
      have hl : raw39630step3Labels = raw39630step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node389 node389Labels := by rfl

theorem canonical39631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39631 raw39631Labels = mixedMoment B node385 node385Labels := by
  calc
    mixedMoment B raw39631 raw39631Labels = mixedMoment B raw39631step0 raw39631step0Labels := by
      have hz : ∀ j, raw39631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39631step0 = (fun i j => raw39631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39631step0 raw39631; decide +kernel
      have hl : raw39631step0Labels = raw39631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39631 raw39631Labels permutation434 hz
    mixedMoment B raw39631step0 raw39631step0Labels = mixedMoment B raw39631step1 raw39631step1Labels := by
      have hz : ∀ j, raw39631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39631step1 = (fun i j => raw39631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39631step1 raw39631step0; decide +kernel
      have hl : raw39631step1Labels = raw39631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39631step0 raw39631step0Labels permutation80 hz
    mixedMoment B raw39631step1 raw39631step1Labels = mixedMoment B raw39631step2 raw39631step2Labels := by
      have ha : raw39631step2 = (fun i j => raw39631step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39631step2 raw39631step1; decide +kernel
      have hl : raw39631step2Labels = raw39631step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39631step1 raw39631step1Labels permutation23 permutation4
    _ = mixedMoment B node385 node385Labels := by rfl

theorem canonical39632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39632 raw39632Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39632 raw39632Labels = mixedMoment B raw39632step0 raw39632step0Labels := by
      have hz : ∀ j, raw39632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39632step0 = (fun i j => raw39632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39632step0 raw39632; decide +kernel
      have hl : raw39632step0Labels = raw39632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39632 raw39632Labels permutation346 hz
    mixedMoment B raw39632step0 raw39632step0Labels = mixedMoment B raw39632step1 raw39632step1Labels := by
      have ha : raw39632step1 = (fun i j => raw39632step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39632step1 raw39632step0; decide +kernel
      have hl : raw39632step1Labels = raw39632step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39632step0 raw39632step0Labels permutation34 permutation5
    mixedMoment B raw39632step1 raw39632step1Labels = mixedMoment B raw39632step2 raw39632step2Labels := by
      have ha : raw39632step2 = -raw39632step1 := by apply Matrix.ext; change ∀ i j, raw39632step2 i j = -(raw39632step1 i j); unfold raw39632step2 raw39632step1; decide +kernel
      have hl : raw39632step2Labels = raw39632step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node377 node377Labels := by rfl

theorem canonical39633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39633 raw39633Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39633 raw39633Labels = mixedMoment B raw39633step0 raw39633step0Labels := by
      have hz : ∀ j, raw39633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39633step0 = (fun i j => raw39633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39633step0 raw39633; decide +kernel
      have hl : raw39633step0Labels = raw39633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39633 raw39633Labels permutation346 hz
    mixedMoment B raw39633step0 raw39633step0Labels = mixedMoment B raw39633step1 raw39633step1Labels := by
      have ha : raw39633step1 = (fun i j => raw39633step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39633step1 raw39633step0; decide +kernel
      have hl : raw39633step1Labels = raw39633step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39633step0 raw39633step0Labels permutation32 permutation5
    mixedMoment B raw39633step1 raw39633step1Labels = mixedMoment B raw39633step2 raw39633step2Labels := by
      have ha : raw39633step2 = -raw39633step1 := by apply Matrix.ext; change ∀ i j, raw39633step2 i j = -(raw39633step1 i j); unfold raw39633step2 raw39633step1; decide +kernel
      have hl : raw39633step2Labels = raw39633step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node387 node387Labels := by rfl

theorem canonical39634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39634 raw39634Labels = mixedMoment B node383 node383Labels := by
  calc
    mixedMoment B raw39634 raw39634Labels = mixedMoment B raw39634step0 raw39634step0Labels := by
      have hz : ∀ j, raw39634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39634step0 = (fun i j => raw39634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39634step0 raw39634; decide +kernel
      have hl : raw39634step0Labels = raw39634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39634 raw39634Labels permutation346 hz
    mixedMoment B raw39634step0 raw39634step0Labels = mixedMoment B raw39634step1 raw39634step1Labels := by
      have ha : raw39634step1 = (fun i j => raw39634step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39634step1 raw39634step0; decide +kernel
      have hl : raw39634step1Labels = raw39634step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39634step0 raw39634step0Labels permutation36 permutation5
    mixedMoment B raw39634step1 raw39634step1Labels = mixedMoment B raw39634step2 raw39634step2Labels := by
      have ha : raw39634step2 = -raw39634step1 := by apply Matrix.ext; change ∀ i j, raw39634step2 i j = -(raw39634step1 i j); unfold raw39634step2 raw39634step1; decide +kernel
      have hl : raw39634step2Labels = raw39634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node383 node383Labels := by rfl

theorem canonical39635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39635 raw39635Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39635 raw39635Labels = mixedMoment B raw39635step0 raw39635step0Labels := by
      have hz : ∀ j, raw39635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39635step0 = (fun i j => raw39635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39635step0 raw39635; decide +kernel
      have hl : raw39635step0Labels = raw39635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39635 raw39635Labels permutation346 hz
    mixedMoment B raw39635step0 raw39635step0Labels = mixedMoment B raw39635step1 raw39635step1Labels := by
      have ha : raw39635step1 = (fun i j => raw39635step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39635step1 raw39635step0; decide +kernel
      have hl : raw39635step1Labels = raw39635step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39635step0 raw39635step0Labels permutation37 permutation5
    mixedMoment B raw39635step1 raw39635step1Labels = mixedMoment B raw39635step2 raw39635step2Labels := by
      have ha : raw39635step2 = -raw39635step1 := by apply Matrix.ext; change ∀ i j, raw39635step2 i j = -(raw39635step1 i j); unfold raw39635step2 raw39635step1; decide +kernel
      have hl : raw39635step2Labels = raw39635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node384 node384Labels := by rfl

theorem canonical39636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39636 raw39636Labels = mixedMoment B node382 node382Labels := by
  calc
    mixedMoment B raw39636 raw39636Labels = mixedMoment B raw39636step0 raw39636step0Labels := by
      have ha : raw39636step0 = (fun i j => raw39636 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39636step0 raw39636; decide +kernel
      have hl : raw39636step0Labels = raw39636Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39636 raw39636Labels permutation170 permutation5
    mixedMoment B raw39636step0 raw39636step0Labels = mixedMoment B raw39636step1 raw39636step1Labels := by
      have ha : raw39636step1 = -raw39636step0 := by apply Matrix.ext; change ∀ i j, raw39636step1 i j = -(raw39636step0 i j); unfold raw39636step1 raw39636step0; decide +kernel
      have hl : raw39636step1Labels = raw39636step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node382 node382Labels := by rfl

theorem canonical39637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39637 raw39637Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39637 raw39637Labels = mixedMoment B raw39637step0 raw39637step0Labels := by
      have hz : ∀ j, raw39637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39637step0 = (fun i j => raw39637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39637step0 raw39637; decide +kernel
      have hl : raw39637step0Labels = raw39637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39637 raw39637Labels permutation434 hz
    mixedMoment B raw39637step0 raw39637step0Labels = mixedMoment B raw39637step1 raw39637step1Labels := by
      have hz : ∀ j, raw39637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39637step1 = (fun i j => raw39637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39637step1 raw39637step0; decide +kernel
      have hl : raw39637step1Labels = raw39637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39637step0 raw39637step0Labels permutation80 hz
    mixedMoment B raw39637step1 raw39637step1Labels = mixedMoment B raw39637step2 raw39637step2Labels := by
      have ha : raw39637step2 = (fun i j => raw39637step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39637step2 raw39637step1; decide +kernel
      have hl : raw39637step2Labels = raw39637step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39637step1 raw39637step1Labels permutation10 permutation5
    mixedMoment B raw39637step2 raw39637step2Labels = mixedMoment B raw39637step3 raw39637step3Labels := by
      have ha : raw39637step3 = -raw39637step2 := by apply Matrix.ext; change ∀ i j, raw39637step3 i j = -(raw39637step2 i j); unfold raw39637step3 raw39637step2; decide +kernel
      have hl : raw39637step3Labels = raw39637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node402 node402Labels := by rfl

theorem canonical39638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39638 raw39638Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw39638 raw39638Labels = mixedMoment B raw39638step0 raw39638step0Labels := by
      have hz : ∀ j, raw39638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39638step0 = (fun i j => raw39638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39638step0 raw39638; decide +kernel
      have hl : raw39638step0Labels = raw39638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39638 raw39638Labels permutation434 hz
    mixedMoment B raw39638step0 raw39638step0Labels = mixedMoment B raw39638step1 raw39638step1Labels := by
      have hz : ∀ j, raw39638step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39638step1 = (fun i j => raw39638step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39638step1 raw39638step0; decide +kernel
      have hl : raw39638step1Labels = raw39638step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39638step0 raw39638step0Labels permutation80 hz
    mixedMoment B raw39638step1 raw39638step1Labels = mixedMoment B raw39638step2 raw39638step2Labels := by
      have ha : raw39638step2 = (fun i j => raw39638step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39638step2 raw39638step1; decide +kernel
      have hl : raw39638step2Labels = raw39638step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39638step1 raw39638step1Labels permutation8 permutation5
    mixedMoment B raw39638step2 raw39638step2Labels = mixedMoment B raw39638step3 raw39638step3Labels := by
      have ha : raw39638step3 = -raw39638step2 := by apply Matrix.ext; change ∀ i j, raw39638step3 i j = -(raw39638step2 i j); unfold raw39638step3 raw39638step2; decide +kernel
      have hl : raw39638step3Labels = raw39638step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node414 node414Labels := by rfl

theorem canonical39639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39639 raw39639Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39639 raw39639Labels = mixedMoment B raw39639step0 raw39639step0Labels := by
      have hz : ∀ j, raw39639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39639step0 = (fun i j => raw39639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39639step0 raw39639; decide +kernel
      have hl : raw39639step0Labels = raw39639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39639 raw39639Labels permutation434 hz
    mixedMoment B raw39639step0 raw39639step0Labels = mixedMoment B raw39639step1 raw39639step1Labels := by
      have hz : ∀ j, raw39639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39639step1 = (fun i j => raw39639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39639step1 raw39639step0; decide +kernel
      have hl : raw39639step1Labels = raw39639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39639step0 raw39639step0Labels permutation80 hz
    mixedMoment B raw39639step1 raw39639step1Labels = mixedMoment B raw39639step2 raw39639step2Labels := by
      have ha : raw39639step2 = (fun i j => raw39639step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39639step2 raw39639step1; decide +kernel
      have hl : raw39639step2Labels = raw39639step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39639step1 raw39639step1Labels permutation12 permutation5
    mixedMoment B raw39639step2 raw39639step2Labels = mixedMoment B raw39639step3 raw39639step3Labels := by
      have ha : raw39639step3 = -raw39639step2 := by apply Matrix.ext; change ∀ i j, raw39639step3 i j = -(raw39639step2 i j); unfold raw39639step3 raw39639step2; decide +kernel
      have hl : raw39639step3Labels = raw39639step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node410 node410Labels := by rfl

theorem canonical39640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39640 raw39640Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39640 raw39640Labels = mixedMoment B raw39640step0 raw39640step0Labels := by
      have hz : ∀ j, raw39640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39640step0 = (fun i j => raw39640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39640step0 raw39640; decide +kernel
      have hl : raw39640step0Labels = raw39640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39640 raw39640Labels permutation346 hz
    mixedMoment B raw39640step0 raw39640step0Labels = mixedMoment B raw39640step1 raw39640step1Labels := by
      have ha : raw39640step1 = (fun i j => raw39640step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39640step1 raw39640step0; decide +kernel
      have hl : raw39640step1Labels = raw39640step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39640step0 raw39640step0Labels permutation50 permutation5
    mixedMoment B raw39640step1 raw39640step1Labels = mixedMoment B raw39640step2 raw39640step2Labels := by
      have ha : raw39640step2 = -raw39640step1 := by apply Matrix.ext; change ∀ i j, raw39640step2 i j = -(raw39640step1 i j); unfold raw39640step2 raw39640step1; decide +kernel
      have hl : raw39640step2Labels = raw39640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node409 node409Labels := by rfl

theorem canonical39641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39641 raw39641Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39641 raw39641Labels = mixedMoment B raw39641step0 raw39641step0Labels := by
      have hz : ∀ j, raw39641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39641step0 = (fun i j => raw39641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39641step0 raw39641; decide +kernel
      have hl : raw39641step0Labels = raw39641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39641 raw39641Labels permutation434 hz
    mixedMoment B raw39641step0 raw39641step0Labels = mixedMoment B raw39641step1 raw39641step1Labels := by
      have hz : ∀ j, raw39641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39641step1 = (fun i j => raw39641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39641step1 raw39641step0; decide +kernel
      have hl : raw39641step1Labels = raw39641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39641step0 raw39641step0Labels permutation80 hz
    mixedMoment B raw39641step1 raw39641step1Labels = mixedMoment B raw39641step2 raw39641step2Labels := by
      have ha : raw39641step2 = (fun i j => raw39641step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39641step2 raw39641step1; decide +kernel
      have hl : raw39641step2Labels = raw39641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39641step1 raw39641step1Labels permutation16 permutation6
    mixedMoment B raw39641step2 raw39641step2Labels = mixedMoment B raw39641step3 raw39641step3Labels := by
      have ha : raw39641step3 = -raw39641step2 := by apply Matrix.ext; change ∀ i j, raw39641step3 i j = -(raw39641step2 i j); unfold raw39641step3 raw39641step2; decide +kernel
      have hl : raw39641step3Labels = raw39641step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node391 node391Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 160) =
      Integer.Sparse.eval keyMomentRow160 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 160).leftCharge (GramAssembly.key 160).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 104) := by
    have ha : gramCharges (GramAssembly.key 160).leftCharge (GramAssembly.key 160).rightCharge = raw39610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39610 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 160).leftCharge (GramAssembly.key 160).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow160, Integer.Sparse.eval]

theorem keyMoment161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 161) =
      Integer.Sparse.eval keyMomentRow161 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 161).leftCharge (GramAssembly.key 161).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 100) := by
    have ha : gramCharges (GramAssembly.key 161).leftCharge (GramAssembly.key 161).rightCharge = raw39611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39611 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 161).leftCharge (GramAssembly.key 161).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow161, Integer.Sparse.eval]

theorem keyMoment162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 162) =
      Integer.Sparse.eval keyMomentRow162 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 162).leftCharge (GramAssembly.key 162).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 37) := by
    have ha : gramCharges (GramAssembly.key 162).leftCharge (GramAssembly.key 162).rightCharge = raw39612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39612 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 162).leftCharge (GramAssembly.key 162).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow162, Integer.Sparse.eval]

theorem keyMoment163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 163) =
      Integer.Sparse.eval keyMomentRow163 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 163).leftCharge (GramAssembly.key 163).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 16) := by
    have ha : gramCharges (GramAssembly.key 163).leftCharge (GramAssembly.key 163).rightCharge = raw39613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39613 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 163).leftCharge (GramAssembly.key 163).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow163, Integer.Sparse.eval]

theorem keyMoment164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 164) =
      Integer.Sparse.eval keyMomentRow164 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 164).leftCharge (GramAssembly.key 164).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 88) := by
    have ha : gramCharges (GramAssembly.key 164).leftCharge (GramAssembly.key 164).rightCharge = raw39614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39614 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 164).leftCharge (GramAssembly.key 164).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow164, Integer.Sparse.eval]

theorem keyMoment165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 165) =
      Integer.Sparse.eval keyMomentRow165 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 165).leftCharge (GramAssembly.key 165).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 99) := by
    have ha : gramCharges (GramAssembly.key 165).leftCharge (GramAssembly.key 165).rightCharge = raw39615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39615 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 165).leftCharge (GramAssembly.key 165).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow165, Integer.Sparse.eval]

theorem keyMoment166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 166) =
      Integer.Sparse.eval keyMomentRow166 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 166).leftCharge (GramAssembly.key 166).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 59) := by
    have ha : gramCharges (GramAssembly.key 166).leftCharge (GramAssembly.key 166).rightCharge = raw39616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39616 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 166).leftCharge (GramAssembly.key 166).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow166, Integer.Sparse.eval]

theorem keyMoment167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 167) =
      Integer.Sparse.eval keyMomentRow167 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 167).leftCharge (GramAssembly.key 167).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 19) := by
    have ha : gramCharges (GramAssembly.key 167).leftCharge (GramAssembly.key 167).rightCharge = raw39617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39617 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 167).leftCharge (GramAssembly.key 167).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow167, Integer.Sparse.eval]

theorem keyMoment168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 168) =
      Integer.Sparse.eval keyMomentRow168 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 168).leftCharge (GramAssembly.key 168).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 14) := by
    have ha : gramCharges (GramAssembly.key 168).leftCharge (GramAssembly.key 168).rightCharge = raw39618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39618 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 168).leftCharge (GramAssembly.key 168).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow168, Integer.Sparse.eval]

theorem keyMoment169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 169) =
      Integer.Sparse.eval keyMomentRow169 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 169).leftCharge (GramAssembly.key 169).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 12) := by
    have ha : gramCharges (GramAssembly.key 169).leftCharge (GramAssembly.key 169).rightCharge = raw39619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39619 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 169).leftCharge (GramAssembly.key 169).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow169, Integer.Sparse.eval]

theorem keyMoment170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 170) =
      Integer.Sparse.eval keyMomentRow170 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 170).leftCharge (GramAssembly.key 170).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 17) := by
    have ha : gramCharges (GramAssembly.key 170).leftCharge (GramAssembly.key 170).rightCharge = raw39620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39620 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 170).leftCharge (GramAssembly.key 170).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow170, Integer.Sparse.eval]

theorem keyMoment171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 171) =
      Integer.Sparse.eval keyMomentRow171 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 171).leftCharge (GramAssembly.key 171).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 15) := by
    have ha : gramCharges (GramAssembly.key 171).leftCharge (GramAssembly.key 171).rightCharge = raw39621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39621 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 171).leftCharge (GramAssembly.key 171).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow171, Integer.Sparse.eval]

theorem keyMoment172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 172) =
      Integer.Sparse.eval keyMomentRow172 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 172).leftCharge (GramAssembly.key 172).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 8) := by
    have ha : gramCharges (GramAssembly.key 172).leftCharge (GramAssembly.key 172).rightCharge = raw39622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39622 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 172).leftCharge (GramAssembly.key 172).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow172, Integer.Sparse.eval]

theorem keyMoment173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 173) =
      Integer.Sparse.eval keyMomentRow173 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 173).leftCharge (GramAssembly.key 173).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 9) := by
    have ha : gramCharges (GramAssembly.key 173).leftCharge (GramAssembly.key 173).rightCharge = raw39623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39623 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 173).leftCharge (GramAssembly.key 173).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow173, Integer.Sparse.eval]

theorem keyMoment174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 174) =
      Integer.Sparse.eval keyMomentRow174 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 174).leftCharge (GramAssembly.key 174).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 13) := by
    have ha : gramCharges (GramAssembly.key 174).leftCharge (GramAssembly.key 174).rightCharge = raw39624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39624 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 174).leftCharge (GramAssembly.key 174).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow174, Integer.Sparse.eval]

theorem keyMoment175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 175) =
      Integer.Sparse.eval keyMomentRow175 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 175).leftCharge (GramAssembly.key 175).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 11) := by
    have ha : gramCharges (GramAssembly.key 175).leftCharge (GramAssembly.key 175).rightCharge = raw39625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39625 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 175).leftCharge (GramAssembly.key 175).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow175, Integer.Sparse.eval]

theorem keyMoment176 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 176) =
      Integer.Sparse.eval keyMomentRow176 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 176).leftCharge (GramAssembly.key 176).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 20) := by
    have ha : gramCharges (GramAssembly.key 176).leftCharge (GramAssembly.key 176).rightCharge = raw39626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39626 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 176).leftCharge (GramAssembly.key 176).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow176, Integer.Sparse.eval]

theorem keyMoment177 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 177) =
      Integer.Sparse.eval keyMomentRow177 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 177).leftCharge (GramAssembly.key 177).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 16) := by
    have ha : gramCharges (GramAssembly.key 177).leftCharge (GramAssembly.key 177).rightCharge = raw39627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39627 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 177).leftCharge (GramAssembly.key 177).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow177, Integer.Sparse.eval]

theorem keyMoment178 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 178) =
      Integer.Sparse.eval keyMomentRow178 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 178).leftCharge (GramAssembly.key 178).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 18) := by
    have ha : gramCharges (GramAssembly.key 178).leftCharge (GramAssembly.key 178).rightCharge = raw39628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39628 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 178).leftCharge (GramAssembly.key 178).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow178, Integer.Sparse.eval]

theorem keyMoment179 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 179) =
      Integer.Sparse.eval keyMomentRow179 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 179).leftCharge (GramAssembly.key 179).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 0) := by
    have ha : gramCharges (GramAssembly.key 179).leftCharge (GramAssembly.key 179).rightCharge = raw39629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39629 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 179).leftCharge (GramAssembly.key 179).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow179, Integer.Sparse.eval]

theorem keyMoment180 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 180) =
      Integer.Sparse.eval keyMomentRow180 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 180).leftCharge (GramAssembly.key 180).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 389) := by
    have ha : gramCharges (GramAssembly.key 180).leftCharge (GramAssembly.key 180).rightCharge = raw39630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39630 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 180).leftCharge (GramAssembly.key 180).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow180, Integer.Sparse.eval]

theorem keyMoment181 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 181) =
      Integer.Sparse.eval keyMomentRow181 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 181).leftCharge (GramAssembly.key 181).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 385) := by
    have ha : gramCharges (GramAssembly.key 181).leftCharge (GramAssembly.key 181).rightCharge = raw39631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39631 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 181).leftCharge (GramAssembly.key 181).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow181, Integer.Sparse.eval]

theorem keyMoment182 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 182) =
      Integer.Sparse.eval keyMomentRow182 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 182).leftCharge (GramAssembly.key 182).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 377) := by
    have ha : gramCharges (GramAssembly.key 182).leftCharge (GramAssembly.key 182).rightCharge = raw39632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39632 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 182).leftCharge (GramAssembly.key 182).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow182, Integer.Sparse.eval]

theorem keyMoment183 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 183) =
      Integer.Sparse.eval keyMomentRow183 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 183).leftCharge (GramAssembly.key 183).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 183).leftCharge (GramAssembly.key 183).rightCharge = raw39633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39633 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 183).leftCharge (GramAssembly.key 183).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow183, Integer.Sparse.eval]

theorem keyMoment184 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 184) =
      Integer.Sparse.eval keyMomentRow184 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 184).leftCharge (GramAssembly.key 184).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 383) := by
    have ha : gramCharges (GramAssembly.key 184).leftCharge (GramAssembly.key 184).rightCharge = raw39634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39634 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 184).leftCharge (GramAssembly.key 184).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow184, Integer.Sparse.eval]

theorem keyMoment185 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 185) =
      Integer.Sparse.eval keyMomentRow185 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 185).leftCharge (GramAssembly.key 185).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 384) := by
    have ha : gramCharges (GramAssembly.key 185).leftCharge (GramAssembly.key 185).rightCharge = raw39635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39635 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 185).leftCharge (GramAssembly.key 185).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow185, Integer.Sparse.eval]

theorem keyMoment186 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 186) =
      Integer.Sparse.eval keyMomentRow186 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 186).leftCharge (GramAssembly.key 186).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 382) := by
    have ha : gramCharges (GramAssembly.key 186).leftCharge (GramAssembly.key 186).rightCharge = raw39636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39636 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 186).leftCharge (GramAssembly.key 186).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow186, Integer.Sparse.eval]

theorem keyMoment187 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 187) =
      Integer.Sparse.eval keyMomentRow187 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 187).leftCharge (GramAssembly.key 187).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 402) := by
    have ha : gramCharges (GramAssembly.key 187).leftCharge (GramAssembly.key 187).rightCharge = raw39637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39637 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 187).leftCharge (GramAssembly.key 187).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow187, Integer.Sparse.eval]

theorem keyMoment188 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 188) =
      Integer.Sparse.eval keyMomentRow188 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 188).leftCharge (GramAssembly.key 188).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 414) := by
    have ha : gramCharges (GramAssembly.key 188).leftCharge (GramAssembly.key 188).rightCharge = raw39638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39638 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 188).leftCharge (GramAssembly.key 188).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow188, Integer.Sparse.eval]

theorem keyMoment189 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 189) =
      Integer.Sparse.eval keyMomentRow189 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 189).leftCharge (GramAssembly.key 189).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 410) := by
    have ha : gramCharges (GramAssembly.key 189).leftCharge (GramAssembly.key 189).rightCharge = raw39639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39639 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 189).leftCharge (GramAssembly.key 189).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow189, Integer.Sparse.eval]

theorem keyMoment190 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 190) =
      Integer.Sparse.eval keyMomentRow190 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 190).leftCharge (GramAssembly.key 190).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 409) := by
    have ha : gramCharges (GramAssembly.key 190).leftCharge (GramAssembly.key 190).rightCharge = raw39640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39640 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 190).leftCharge (GramAssembly.key 190).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow190, Integer.Sparse.eval]

theorem keyMoment191 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 191) =
      Integer.Sparse.eval keyMomentRow191 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 191).leftCharge (GramAssembly.key 191).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 391) := by
    have ha : gramCharges (GramAssembly.key 191).leftCharge (GramAssembly.key 191).rightCharge = raw39641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39641 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 191).leftCharge (GramAssembly.key 191).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow191, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt160 : keyMomentRows (160 : Fin 2886) =
    keyMomentRow160 := by decide +kernel

theorem keyMomentRowsAt161 : keyMomentRows (161 : Fin 2886) =
    keyMomentRow161 := by decide +kernel

theorem keyMomentRowsAt162 : keyMomentRows (162 : Fin 2886) =
    keyMomentRow162 := by decide +kernel

theorem keyMomentRowsAt163 : keyMomentRows (163 : Fin 2886) =
    keyMomentRow163 := by decide +kernel

theorem keyMomentRowsAt164 : keyMomentRows (164 : Fin 2886) =
    keyMomentRow164 := by decide +kernel

theorem keyMomentRowsAt165 : keyMomentRows (165 : Fin 2886) =
    keyMomentRow165 := by decide +kernel

theorem keyMomentRowsAt166 : keyMomentRows (166 : Fin 2886) =
    keyMomentRow166 := by decide +kernel

theorem keyMomentRowsAt167 : keyMomentRows (167 : Fin 2886) =
    keyMomentRow167 := by decide +kernel

theorem keyMomentRowsAt168 : keyMomentRows (168 : Fin 2886) =
    keyMomentRow168 := by decide +kernel

theorem keyMomentRowsAt169 : keyMomentRows (169 : Fin 2886) =
    keyMomentRow169 := by decide +kernel

theorem keyMomentRowsAt170 : keyMomentRows (170 : Fin 2886) =
    keyMomentRow170 := by decide +kernel

theorem keyMomentRowsAt171 : keyMomentRows (171 : Fin 2886) =
    keyMomentRow171 := by decide +kernel

theorem keyMomentRowsAt172 : keyMomentRows (172 : Fin 2886) =
    keyMomentRow172 := by decide +kernel

theorem keyMomentRowsAt173 : keyMomentRows (173 : Fin 2886) =
    keyMomentRow173 := by decide +kernel

theorem keyMomentRowsAt174 : keyMomentRows (174 : Fin 2886) =
    keyMomentRow174 := by decide +kernel

theorem keyMomentRowsAt175 : keyMomentRows (175 : Fin 2886) =
    keyMomentRow175 := by decide +kernel

theorem keyMomentRowsAt176 : keyMomentRows (176 : Fin 2886) =
    keyMomentRow176 := by decide +kernel

theorem keyMomentRowsAt177 : keyMomentRows (177 : Fin 2886) =
    keyMomentRow177 := by decide +kernel

theorem keyMomentRowsAt178 : keyMomentRows (178 : Fin 2886) =
    keyMomentRow178 := by decide +kernel

theorem keyMomentRowsAt179 : keyMomentRows (179 : Fin 2886) =
    keyMomentRow179 := by decide +kernel

theorem keyMomentRowsAt180 : keyMomentRows (180 : Fin 2886) =
    keyMomentRow180 := by decide +kernel

theorem keyMomentRowsAt181 : keyMomentRows (181 : Fin 2886) =
    keyMomentRow181 := by decide +kernel

theorem keyMomentRowsAt182 : keyMomentRows (182 : Fin 2886) =
    keyMomentRow182 := by decide +kernel

theorem keyMomentRowsAt183 : keyMomentRows (183 : Fin 2886) =
    keyMomentRow183 := by decide +kernel

theorem keyMomentRowsAt184 : keyMomentRows (184 : Fin 2886) =
    keyMomentRow184 := by decide +kernel

theorem keyMomentRowsAt185 : keyMomentRows (185 : Fin 2886) =
    keyMomentRow185 := by decide +kernel

theorem keyMomentRowsAt186 : keyMomentRows (186 : Fin 2886) =
    keyMomentRow186 := by decide +kernel

theorem keyMomentRowsAt187 : keyMomentRows (187 : Fin 2886) =
    keyMomentRow187 := by decide +kernel

theorem keyMomentRowsAt188 : keyMomentRows (188 : Fin 2886) =
    keyMomentRow188 := by decide +kernel

theorem keyMomentRowsAt189 : keyMomentRows (189 : Fin 2886) =
    keyMomentRow189 := by decide +kernel

theorem keyMomentRowsAt190 : keyMomentRows (190 : Fin 2886) =
    keyMomentRow190 := by decide +kernel

theorem keyMomentRowsAt191 : keyMomentRows (191 : Fin 2886) =
    keyMomentRow191 := by decide +kernel

theorem keyMomentChunkSound5_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 5) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 160 ∨ k.val = 161 ∨ k.val = 162 ∨ k.val = 163 ∨ k.val = 164 ∨ k.val = 165 ∨ k.val = 166 ∨ k.val = 167 ∨ k.val = 168 ∨ k.val = 169 ∨ k.val = 170 ∨ k.val = 171 ∨ k.val = 172 ∨ k.val = 173 ∨ k.val = 174 ∨ k.val = 175 ∨ k.val = 176 ∨ k.val = 177 ∨ k.val = 178 ∨ k.val = 179 ∨ k.val = 180 ∨ k.val = 181 ∨ k.val = 182 ∨ k.val = 183 ∨ k.val = 184 ∨ k.val = 185 ∨ k.val = 186 ∨ k.val = 187 ∨ k.val = 188 ∨ k.val = 189 ∨ k.val = 190 ∨ k.val = 191 := by omega
  rcases heq with h160 | h161 | h162 | h163 | h164 | h165 | h166 | h167 | h168 | h169 | h170 | h171 | h172 | h173 | h174 | h175 | h176 | h177 | h178 | h179 | h180 | h181 | h182 | h183 | h184 | h185 | h186 | h187 | h188 | h189 | h190 | h191
  · have he : k = (160 : Fin 2886) := Fin.ext h160
    subst k
    rw [keyMomentRowsAt160]
    exact keyMoment160 B hB
  · have he : k = (161 : Fin 2886) := Fin.ext h161
    subst k
    rw [keyMomentRowsAt161]
    exact keyMoment161 B hB
  · have he : k = (162 : Fin 2886) := Fin.ext h162
    subst k
    rw [keyMomentRowsAt162]
    exact keyMoment162 B hB
  · have he : k = (163 : Fin 2886) := Fin.ext h163
    subst k
    rw [keyMomentRowsAt163]
    exact keyMoment163 B hB
  · have he : k = (164 : Fin 2886) := Fin.ext h164
    subst k
    rw [keyMomentRowsAt164]
    exact keyMoment164 B hB
  · have he : k = (165 : Fin 2886) := Fin.ext h165
    subst k
    rw [keyMomentRowsAt165]
    exact keyMoment165 B hB
  · have he : k = (166 : Fin 2886) := Fin.ext h166
    subst k
    rw [keyMomentRowsAt166]
    exact keyMoment166 B hB
  · have he : k = (167 : Fin 2886) := Fin.ext h167
    subst k
    rw [keyMomentRowsAt167]
    exact keyMoment167 B hB
  · have he : k = (168 : Fin 2886) := Fin.ext h168
    subst k
    rw [keyMomentRowsAt168]
    exact keyMoment168 B hB
  · have he : k = (169 : Fin 2886) := Fin.ext h169
    subst k
    rw [keyMomentRowsAt169]
    exact keyMoment169 B hB
  · have he : k = (170 : Fin 2886) := Fin.ext h170
    subst k
    rw [keyMomentRowsAt170]
    exact keyMoment170 B hB
  · have he : k = (171 : Fin 2886) := Fin.ext h171
    subst k
    rw [keyMomentRowsAt171]
    exact keyMoment171 B hB
  · have he : k = (172 : Fin 2886) := Fin.ext h172
    subst k
    rw [keyMomentRowsAt172]
    exact keyMoment172 B hB
  · have he : k = (173 : Fin 2886) := Fin.ext h173
    subst k
    rw [keyMomentRowsAt173]
    exact keyMoment173 B hB
  · have he : k = (174 : Fin 2886) := Fin.ext h174
    subst k
    rw [keyMomentRowsAt174]
    exact keyMoment174 B hB
  · have he : k = (175 : Fin 2886) := Fin.ext h175
    subst k
    rw [keyMomentRowsAt175]
    exact keyMoment175 B hB
  · have he : k = (176 : Fin 2886) := Fin.ext h176
    subst k
    rw [keyMomentRowsAt176]
    exact keyMoment176 B hB
  · have he : k = (177 : Fin 2886) := Fin.ext h177
    subst k
    rw [keyMomentRowsAt177]
    exact keyMoment177 B hB
  · have he : k = (178 : Fin 2886) := Fin.ext h178
    subst k
    rw [keyMomentRowsAt178]
    exact keyMoment178 B hB
  · have he : k = (179 : Fin 2886) := Fin.ext h179
    subst k
    rw [keyMomentRowsAt179]
    exact keyMoment179 B hB
  · have he : k = (180 : Fin 2886) := Fin.ext h180
    subst k
    rw [keyMomentRowsAt180]
    exact keyMoment180 B hB
  · have he : k = (181 : Fin 2886) := Fin.ext h181
    subst k
    rw [keyMomentRowsAt181]
    exact keyMoment181 B hB
  · have he : k = (182 : Fin 2886) := Fin.ext h182
    subst k
    rw [keyMomentRowsAt182]
    exact keyMoment182 B hB
  · have he : k = (183 : Fin 2886) := Fin.ext h183
    subst k
    rw [keyMomentRowsAt183]
    exact keyMoment183 B hB
  · have he : k = (184 : Fin 2886) := Fin.ext h184
    subst k
    rw [keyMomentRowsAt184]
    exact keyMoment184 B hB
  · have he : k = (185 : Fin 2886) := Fin.ext h185
    subst k
    rw [keyMomentRowsAt185]
    exact keyMoment185 B hB
  · have he : k = (186 : Fin 2886) := Fin.ext h186
    subst k
    rw [keyMomentRowsAt186]
    exact keyMoment186 B hB
  · have he : k = (187 : Fin 2886) := Fin.ext h187
    subst k
    rw [keyMomentRowsAt187]
    exact keyMoment187 B hB
  · have he : k = (188 : Fin 2886) := Fin.ext h188
    subst k
    rw [keyMomentRowsAt188]
    exact keyMoment188 B hB
  · have he : k = (189 : Fin 2886) := Fin.ext h189
    subst k
    rw [keyMomentRowsAt189]
    exact keyMoment189 B hB
  · have he : k = (190 : Fin 2886) := Fin.ext h190
    subst k
    rw [keyMomentRowsAt190]
    exact keyMoment190 B hB
  · have he : k = (191 : Fin 2886) := Fin.ext h191
    subst k
    rw [keyMomentRowsAt191]
    exact keyMoment191 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound5_e_oai
