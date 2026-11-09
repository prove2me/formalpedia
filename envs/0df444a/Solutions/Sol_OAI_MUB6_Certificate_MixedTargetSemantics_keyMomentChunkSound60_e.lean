-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:44.197745+00:00
-- url     : https://prove2.me/submissions/fe560f6c-5102-4372-89e5-474f99668ff1

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

theorem canonical41333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41333 raw41333Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw41333 raw41333Labels = mixedMoment B raw41333step0 raw41333step0Labels := by
      have hz : ∀ j, raw41333 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41333step0 = (fun i j => raw41333 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41333step0 raw41333; decide +kernel
      have hl : raw41333step0Labels = raw41333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41333 raw41333Labels permutation520 hz
    mixedMoment B raw41333step0 raw41333step0Labels = mixedMoment B raw41333step1 raw41333step1Labels := by
      have ha : raw41333step1 = (fun i j => raw41333step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41333step1 raw41333step0; decide +kernel
      have hl : raw41333step1Labels = raw41333step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41333step0 raw41333step0Labels permutation151 permutation3
    mixedMoment B raw41333step1 raw41333step1Labels = mixedMoment B raw41333step2 raw41333step2Labels := by
      have ha : raw41333step2 = -raw41333step1 := by apply Matrix.ext; change ∀ i j, raw41333step2 i j = -(raw41333step1 i j); unfold raw41333step2 raw41333step1; decide +kernel
      have hl : raw41333step2Labels = raw41333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical41334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41334 raw41334Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw41334 raw41334Labels = mixedMoment B raw41334step0 raw41334step0Labels := by
      have ha : raw41334step0 = (fun i j => raw41334 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41334step0 raw41334; decide +kernel
      have hl : raw41334step0Labels = raw41334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41334 raw41334Labels permutation506 permutation6
    _ = mixedMoment B node3720 node3720Labels := by rfl

theorem canonical41335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41335 raw41335Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw41335 raw41335Labels = mixedMoment B raw41335step0 raw41335step0Labels := by
      have ha : raw41335step0 = (fun i j => raw41335 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41335step0 raw41335; decide +kernel
      have hl : raw41335step0Labels = raw41335Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41335 raw41335Labels permutation664 permutation3
    mixedMoment B raw41335step0 raw41335step0Labels = mixedMoment B raw41335step1 raw41335step1Labels := by
      have ha : raw41335step1 = -raw41335step0 := by apply Matrix.ext; change ∀ i j, raw41335step1 i j = -(raw41335step0 i j); unfold raw41335step1 raw41335step0; decide +kernel
      have hl : raw41335step1Labels = raw41335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical41336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41336 raw41336Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw41336 raw41336Labels = mixedMoment B raw41336step0 raw41336step0Labels := by
      have ha : raw41336step0 = (fun i j => raw41336 (permutation648 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41336step0 raw41336; decide +kernel
      have hl : raw41336step0Labels = raw41336Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41336 raw41336Labels permutation648 permutation6
    _ = mixedMoment B node2925 node2925Labels := by rfl

theorem canonical41337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41337 raw41337Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw41337 raw41337Labels = mixedMoment B raw41337step0 raw41337step0Labels := by
      have hz : ∀ j, raw41337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41337step0 = (fun i j => raw41337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41337step0 raw41337; decide +kernel
      have hl : raw41337step0Labels = raw41337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41337 raw41337Labels permutation434 hz
    mixedMoment B raw41337step0 raw41337step0Labels = mixedMoment B raw41337step1 raw41337step1Labels := by
      have ha : raw41337step1 = (fun i j => raw41337step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41337step1 raw41337step0; decide +kernel
      have hl : raw41337step1Labels = raw41337step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41337step0 raw41337step0Labels permutation129 permutation6
    _ = mixedMoment B node1237 node1237Labels := by rfl

theorem canonical41338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41338 raw41338Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw41338 raw41338Labels = mixedMoment B raw41338step0 raw41338step0Labels := by
      have hz : ∀ j, raw41338 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41338step0 = (fun i j => raw41338 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41338step0 raw41338; decide +kernel
      have hl : raw41338step0Labels = raw41338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41338 raw41338Labels permutation520 hz
    mixedMoment B raw41338step0 raw41338step0Labels = mixedMoment B raw41338step1 raw41338step1Labels := by
      have ha : raw41338step1 = (fun i j => raw41338step0 (permutation87 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41338step1 raw41338step0; decide +kernel
      have hl : raw41338step1Labels = raw41338step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41338step0 raw41338step0Labels permutation87 permutation6
    mixedMoment B raw41338step1 raw41338step1Labels = mixedMoment B raw41338step2 raw41338step2Labels := by
      have ha : raw41338step2 = -raw41338step1 := by apply Matrix.ext; change ∀ i j, raw41338step2 i j = -(raw41338step1 i j); unfold raw41338step2 raw41338step1; decide +kernel
      have hl : raw41338step2Labels = raw41338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2575 node2575Labels := by rfl

theorem canonical41339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41339 raw41339Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw41339 raw41339Labels = mixedMoment B raw41339step0 raw41339step0Labels := by
      have ha : raw41339step0 = (fun i j => raw41339 (permutation376 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41339step0 raw41339; decide +kernel
      have hl : raw41339step0Labels = raw41339Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41339 raw41339Labels permutation376 permutation6
    mixedMoment B raw41339step0 raw41339step0Labels = mixedMoment B raw41339step1 raw41339step1Labels := by
      have ha : raw41339step1 = -raw41339step0 := by apply Matrix.ext; change ∀ i j, raw41339step1 i j = -(raw41339step0 i j); unfold raw41339step1 raw41339step0; decide +kernel
      have hl : raw41339step1Labels = raw41339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2545 node2545Labels := by rfl

theorem canonical41340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41340 raw41340Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw41340 raw41340Labels = mixedMoment B raw41340step0 raw41340step0Labels := by
      have hz : ∀ j, raw41340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41340step0 = (fun i j => raw41340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41340step0 raw41340; decide +kernel
      have hl : raw41340step0Labels = raw41340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41340 raw41340Labels permutation434 hz
    mixedMoment B raw41340step0 raw41340step0Labels = mixedMoment B raw41340step1 raw41340step1Labels := by
      have ha : raw41340step1 = (fun i j => raw41340step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41340step1 raw41340step0; decide +kernel
      have hl : raw41340step1Labels = raw41340step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41340step0 raw41340step0Labels permutation132 permutation6
    _ = mixedMoment B node1215 node1215Labels := by rfl

theorem canonical41341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41341 raw41341Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw41341 raw41341Labels = mixedMoment B raw41341step0 raw41341step0Labels := by
      have hz : ∀ j, raw41341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41341step0 = (fun i j => raw41341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41341step0 raw41341; decide +kernel
      have hl : raw41341step0Labels = raw41341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41341 raw41341Labels permutation434 hz
    mixedMoment B raw41341step0 raw41341step0Labels = mixedMoment B raw41341step1 raw41341step1Labels := by
      have ha : raw41341step1 = (fun i j => raw41341step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41341step1 raw41341step0; decide +kernel
      have hl : raw41341step1Labels = raw41341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41341step0 raw41341step0Labels permutation151 permutation3
    mixedMoment B raw41341step1 raw41341step1Labels = mixedMoment B raw41341step2 raw41341step2Labels := by
      have ha : raw41341step2 = -raw41341step1 := by apply Matrix.ext; change ∀ i j, raw41341step2 i j = -(raw41341step1 i j); unfold raw41341step2 raw41341step1; decide +kernel
      have hl : raw41341step2Labels = raw41341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3906 node3906Labels := by rfl

theorem canonical41342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41342 raw41342Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw41342 raw41342Labels = mixedMoment B raw41342step0 raw41342step0Labels := by
      have hz : ∀ j, raw41342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41342step0 = (fun i j => raw41342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41342step0 raw41342; decide +kernel
      have hl : raw41342step0Labels = raw41342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41342 raw41342Labels permutation434 hz
    mixedMoment B raw41342step0 raw41342step0Labels = mixedMoment B raw41342step1 raw41342step1Labels := by
      have ha : raw41342step1 = (fun i j => raw41342step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41342step1 raw41342step0; decide +kernel
      have hl : raw41342step1Labels = raw41342step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41342step0 raw41342step0Labels permutation111 permutation6
    mixedMoment B raw41342step1 raw41342step1Labels = mixedMoment B raw41342step2 raw41342step2Labels := by
      have ha : raw41342step2 = -raw41342step1 := by apply Matrix.ext; change ∀ i j, raw41342step2 i j = -(raw41342step1 i j); unfold raw41342step2 raw41342step1; decide +kernel
      have hl : raw41342step2Labels = raw41342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical41343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41343 raw41343Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw41343 raw41343Labels = mixedMoment B raw41343step0 raw41343step0Labels := by
      have hz : ∀ j, raw41343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41343step0 = (fun i j => raw41343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41343step0 raw41343; decide +kernel
      have hl : raw41343step0Labels = raw41343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41343 raw41343Labels permutation434 hz
    mixedMoment B raw41343step0 raw41343step0Labels = mixedMoment B raw41343step1 raw41343step1Labels := by
      have ha : raw41343step1 = (fun i j => raw41343step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41343step1 raw41343step0; decide +kernel
      have hl : raw41343step1Labels = raw41343step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41343step0 raw41343step0Labels permutation111 permutation6
    mixedMoment B raw41343step1 raw41343step1Labels = mixedMoment B raw41343step2 raw41343step2Labels := by
      have ha : raw41343step2 = -raw41343step1 := by apply Matrix.ext; change ∀ i j, raw41343step2 i j = -(raw41343step1 i j); unfold raw41343step2 raw41343step1; decide +kernel
      have hl : raw41343step2Labels = raw41343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical323
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41344 raw41344Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw41344 raw41344Labels = mixedMoment B raw41344step0 raw41344step0Labels := by
      have hz : ∀ j, raw41344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41344step0 = (fun i j => raw41344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41344step0 raw41344; decide +kernel
      have hl : raw41344step0Labels = raw41344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41344 raw41344Labels permutation434 hz
    mixedMoment B raw41344step0 raw41344step0Labels = mixedMoment B raw41344step1 raw41344step1Labels := by
      have ha : raw41344step1 = (fun i j => raw41344step0 (permutation135 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41344step1 raw41344step0; decide +kernel
      have hl : raw41344step1Labels = raw41344step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41344step0 raw41344step0Labels permutation135 permutation6
    mixedMoment B raw41344step1 raw41344step1Labels = mixedMoment B raw41344step2 raw41344step2Labels := by
      have ha : raw41344step2 = -raw41344step1 := by apply Matrix.ext; change ∀ i j, raw41344step2 i j = -(raw41344step1 i j); unfold raw41344step2 raw41344step1; decide +kernel
      have hl : raw41344step2Labels = raw41344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

theorem canonical41345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41345 raw41345Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw41345 raw41345Labels = mixedMoment B raw41345step0 raw41345step0Labels := by
      have hz : ∀ j, raw41345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41345step0 = (fun i j => raw41345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41345step0 raw41345; decide +kernel
      have hl : raw41345step0Labels = raw41345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41345 raw41345Labels permutation434 hz
    mixedMoment B raw41345step0 raw41345step0Labels = mixedMoment B raw41345step1 raw41345step1Labels := by
      have ha : raw41345step1 = (fun i j => raw41345step0 (permutation82 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41345step1 raw41345step0; decide +kernel
      have hl : raw41345step1Labels = raw41345step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41345step0 raw41345step0Labels permutation82 permutation6
    _ = mixedMoment B node3903 node3903Labels := by rfl

theorem canonical41346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41346 raw41346Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw41346 raw41346Labels = mixedMoment B raw41346step0 raw41346step0Labels := by
      have ha : raw41346step0 = (fun i j => raw41346 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41346step0 raw41346; decide +kernel
      have hl : raw41346step0Labels = raw41346Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41346 raw41346Labels permutation414 permutation6
    _ = mixedMoment B node3875 node3875Labels := by rfl

theorem canonical41347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41347 raw41347Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw41347 raw41347Labels = mixedMoment B raw41347step0 raw41347step0Labels := by
      have ha : raw41347step0 = (fun i j => raw41347 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41347step0 raw41347; decide +kernel
      have hl : raw41347step0Labels = raw41347Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41347 raw41347Labels permutation414 permutation6
    _ = mixedMoment B node3719 node3719Labels := by rfl

theorem canonical41348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41348 raw41348Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw41348 raw41348Labels = mixedMoment B raw41348step0 raw41348step0Labels := by
      have ha : raw41348step0 = (fun i j => raw41348 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41348step0 raw41348; decide +kernel
      have hl : raw41348step0Labels = raw41348Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41348 raw41348Labels permutation399 permutation6
    _ = mixedMoment B node3843 node3843Labels := by rfl

theorem canonical41349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41349 raw41349Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw41349 raw41349Labels = mixedMoment B raw41349step0 raw41349step0Labels := by
      have ha : raw41349step0 = (fun i j => raw41349 (permutation359 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41349step0 raw41349; decide +kernel
      have hl : raw41349step0Labels = raw41349Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41349 raw41349Labels permutation359 permutation6
    _ = mixedMoment B node3901 node3901Labels := by rfl

theorem canonical41350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41350 raw41350Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw41350 raw41350Labels = mixedMoment B raw41350step0 raw41350step0Labels := by
      have ha : raw41350step0 = (fun i j => raw41350 (permutation401 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41350step0 raw41350; decide +kernel
      have hl : raw41350step0Labels = raw41350Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41350 raw41350Labels permutation401 permutation6
    _ = mixedMoment B node3837 node3837Labels := by rfl

theorem canonical41351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41351 raw41351Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw41351 raw41351Labels = mixedMoment B raw41351step0 raw41351step0Labels := by
      have hz : ∀ j, raw41351 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41351step0 = (fun i j => raw41351 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41351step0 raw41351; decide +kernel
      have hl : raw41351step0Labels = raw41351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41351 raw41351Labels permutation434 hz
    mixedMoment B raw41351step0 raw41351step0Labels = mixedMoment B raw41351step1 raw41351step1Labels := by
      have ha : raw41351step1 = (fun i j => raw41351step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41351step1 raw41351step0; decide +kernel
      have hl : raw41351step1Labels = raw41351step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41351step0 raw41351step0Labels permutation110 permutation6
    mixedMoment B raw41351step1 raw41351step1Labels = mixedMoment B raw41351step2 raw41351step2Labels := by
      have ha : raw41351step2 = -raw41351step1 := by apply Matrix.ext; change ∀ i j, raw41351step2 i j = -(raw41351step1 i j); unfold raw41351step2 raw41351step1; decide +kernel
      have hl : raw41351step2Labels = raw41351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

theorem canonical41352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41352 raw41352Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw41352 raw41352Labels = mixedMoment B raw41352step0 raw41352step0Labels := by
      have hz : ∀ j, raw41352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41352step0 = (fun i j => raw41352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41352step0 raw41352; decide +kernel
      have hl : raw41352step0Labels = raw41352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41352 raw41352Labels permutation434 hz
    mixedMoment B raw41352step0 raw41352step0Labels = mixedMoment B raw41352step1 raw41352step1Labels := by
      have ha : raw41352step1 = (fun i j => raw41352step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41352step1 raw41352step0; decide +kernel
      have hl : raw41352step1Labels = raw41352step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41352step0 raw41352step0Labels permutation134 permutation6
    mixedMoment B raw41352step1 raw41352step1Labels = mixedMoment B raw41352step2 raw41352step2Labels := by
      have ha : raw41352step2 = -raw41352step1 := by apply Matrix.ext; change ∀ i j, raw41352step2 i j = -(raw41352step1 i j); unfold raw41352step2 raw41352step1; decide +kernel
      have hl : raw41352step2Labels = raw41352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

theorem canonical41353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41353 raw41353Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw41353 raw41353Labels = mixedMoment B raw41353step0 raw41353step0Labels := by
      have ha : raw41353step0 = (fun i j => raw41353 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41353step0 raw41353; decide +kernel
      have hl : raw41353step0Labels = raw41353Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41353 raw41353Labels permutation623 permutation6
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical41354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41354 raw41354Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw41354 raw41354Labels = mixedMoment B raw41354step0 raw41354step0Labels := by
      have ha : raw41354step0 = (fun i j => raw41354 (permutation541 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41354step0 raw41354; decide +kernel
      have hl : raw41354step0Labels = raw41354Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41354 raw41354Labels permutation541 permutation6
    _ = mixedMoment B node3974 node3974Labels := by rfl

theorem canonical41355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41355 raw41355Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw41355 raw41355Labels = mixedMoment B raw41355step0 raw41355step0Labels := by
      have hz : ∀ j, raw41355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41355step0 = (fun i j => raw41355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41355step0 raw41355; decide +kernel
      have hl : raw41355step0Labels = raw41355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41355 raw41355Labels permutation346 hz
    mixedMoment B raw41355step0 raw41355step0Labels = mixedMoment B raw41355step1 raw41355step1Labels := by
      have ha : raw41355step1 = (fun i j => raw41355step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41355step1 raw41355step0; decide +kernel
      have hl : raw41355step1Labels = raw41355step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41355step0 raw41355step0Labels permutation128 permutation6
    _ = mixedMoment B node1236 node1236Labels := by rfl

theorem canonical41356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41356 raw41356Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw41356 raw41356Labels = mixedMoment B raw41356step0 raw41356step0Labels := by
      have hz : ∀ j, raw41356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41356step0 = (fun i j => raw41356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41356step0 raw41356; decide +kernel
      have hl : raw41356step0Labels = raw41356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41356 raw41356Labels permutation346 hz
    mixedMoment B raw41356step0 raw41356step0Labels = mixedMoment B raw41356step1 raw41356step1Labels := by
      have ha : raw41356step1 = (fun i j => raw41356step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41356step1 raw41356step0; decide +kernel
      have hl : raw41356step1Labels = raw41356step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41356step0 raw41356step0Labels permutation104 permutation6
    _ = mixedMoment B node2739 node2739Labels := by rfl

theorem canonical41357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41357 raw41357Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw41357 raw41357Labels = mixedMoment B raw41357step0 raw41357step0Labels := by
      have hz : ∀ j, raw41357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41357step0 = (fun i j => raw41357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41357step0 raw41357; decide +kernel
      have hl : raw41357step0Labels = raw41357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41357 raw41357Labels permutation346 hz
    mixedMoment B raw41357step0 raw41357step0Labels = mixedMoment B raw41357step1 raw41357step1Labels := by
      have ha : raw41357step1 = (fun i j => raw41357step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41357step1 raw41357step0; decide +kernel
      have hl : raw41357step1Labels = raw41357step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41357step0 raw41357step0Labels permutation108 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

theorem canonical41358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41358 raw41358Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw41358 raw41358Labels = mixedMoment B raw41358step0 raw41358step0Labels := by
      have ha : raw41358step0 = (fun i j => raw41358 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41358step0 raw41358; decide +kernel
      have hl : raw41358step0Labels = raw41358Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41358 raw41358Labels permutation590 permutation6
    _ = mixedMoment B node1235 node1235Labels := by rfl

theorem canonical41359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41359 raw41359Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw41359 raw41359Labels = mixedMoment B raw41359step0 raw41359step0Labels := by
      have ha : raw41359step0 = (fun i j => raw41359 (permutation526 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41359step0 raw41359; decide +kernel
      have hl : raw41359step0Labels = raw41359Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41359 raw41359Labels permutation526 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

theorem canonical41360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41360 raw41360Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw41360 raw41360Labels = mixedMoment B raw41360step0 raw41360step0Labels := by
      have hz : ∀ j, raw41360 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41360step0 = (fun i j => raw41360 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41360step0 raw41360; decide +kernel
      have hl : raw41360step0Labels = raw41360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41360 raw41360Labels permutation520 hz
    mixedMoment B raw41360step0 raw41360step0Labels = mixedMoment B raw41360step1 raw41360step1Labels := by
      have hz : ∀ j, raw41360step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41360step1 = (fun i j => raw41360step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41360step1 raw41360step0; decide +kernel
      have hl : raw41360step1Labels = raw41360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41360step0 raw41360step0Labels permutation104 hz
    mixedMoment B raw41360step1 raw41360step1Labels = mixedMoment B raw41360step2 raw41360step2Labels := by
      have ha : raw41360step2 = (fun i j => raw41360step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41360step2 raw41360step1; decide +kernel
      have hl : raw41360step2Labels = raw41360step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41360step1 raw41360step1Labels permutation21 permutation6
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical41361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41361 raw41361Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw41361 raw41361Labels = mixedMoment B raw41361step0 raw41361step0Labels := by
      have hz : ∀ j, raw41361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41361step0 = (fun i j => raw41361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41361step0 raw41361; decide +kernel
      have hl : raw41361step0Labels = raw41361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41361 raw41361Labels permutation434 hz
    mixedMoment B raw41361step0 raw41361step0Labels = mixedMoment B raw41361step1 raw41361step1Labels := by
      have ha : raw41361step1 = (fun i j => raw41361step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41361step1 raw41361step0; decide +kernel
      have hl : raw41361step1Labels = raw41361step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41361step0 raw41361step0Labels permutation99 permutation6
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical41362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41362 raw41362Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw41362 raw41362Labels = mixedMoment B raw41362step0 raw41362step0Labels := by
      have hz : ∀ j, raw41362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41362step0 = (fun i j => raw41362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41362step0 raw41362; decide +kernel
      have hl : raw41362step0Labels = raw41362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41362 raw41362Labels permutation434 hz
    mixedMoment B raw41362step0 raw41362step0Labels = mixedMoment B raw41362step1 raw41362step1Labels := by
      have ha : raw41362step1 = (fun i j => raw41362step0 (permutation111 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41362step1 raw41362step0; decide +kernel
      have hl : raw41362step1Labels = raw41362step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41362step0 raw41362step0Labels permutation111 permutation6
    mixedMoment B raw41362step1 raw41362step1Labels = mixedMoment B raw41362step2 raw41362step2Labels := by
      have ha : raw41362step2 = -raw41362step1 := by apply Matrix.ext; change ∀ i j, raw41362step2 i j = -(raw41362step1 i j); unfold raw41362step2 raw41362step1; decide +kernel
      have hl : raw41362step2Labels = raw41362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

theorem canonical41363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41363 raw41363Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw41363 raw41363Labels = mixedMoment B raw41363step0 raw41363step0Labels := by
      have hz : ∀ j, raw41363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41363step0 = (fun i j => raw41363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41363step0 raw41363; decide +kernel
      have hl : raw41363step0Labels = raw41363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41363 raw41363Labels permutation434 hz
    mixedMoment B raw41363step0 raw41363step0Labels = mixedMoment B raw41363step1 raw41363step1Labels := by
      have ha : raw41363step1 = (fun i j => raw41363step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41363step1 raw41363step0; decide +kernel
      have hl : raw41363step1Labels = raw41363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41363step0 raw41363step0Labels permutation93 permutation6
    _ = mixedMoment B node3845 node3845Labels := by rfl

theorem canonical41364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41364 raw41364Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw41364 raw41364Labels = mixedMoment B raw41364step0 raw41364step0Labels := by
      have hz : ∀ j, raw41364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41364step0 = (fun i j => raw41364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41364step0 raw41364; decide +kernel
      have hl : raw41364step0Labels = raw41364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41364 raw41364Labels permutation434 hz
    mixedMoment B raw41364step0 raw41364step0Labels = mixedMoment B raw41364step1 raw41364step1Labels := by
      have ha : raw41364step1 = (fun i j => raw41364step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41364step1 raw41364step0; decide +kernel
      have hl : raw41364step1Labels = raw41364step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41364step0 raw41364step0Labels permutation83 permutation6
    _ = mixedMoment B node3902 node3902Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1920 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1920) =
      Integer.Sparse.eval keyMomentRow1920 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1920).leftCharge (GramAssembly.key 1920).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 1920).leftCharge (GramAssembly.key 1920).rightCharge = raw41333 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41333Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41333 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1920).leftCharge (GramAssembly.key 1920).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1920, Integer.Sparse.eval]

theorem keyMoment1921 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1921) =
      Integer.Sparse.eval keyMomentRow1921 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1921).leftCharge (GramAssembly.key 1921).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3720) := by
    have ha : gramCharges (GramAssembly.key 1921).leftCharge (GramAssembly.key 1921).rightCharge = raw41334 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41334Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41334 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1921).leftCharge (GramAssembly.key 1921).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1921, Integer.Sparse.eval]

theorem keyMoment1922 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1922) =
      Integer.Sparse.eval keyMomentRow1922 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1922).leftCharge (GramAssembly.key 1922).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 1922).leftCharge (GramAssembly.key 1922).rightCharge = raw41335 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41335Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41335 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1922).leftCharge (GramAssembly.key 1922).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1922, Integer.Sparse.eval]

theorem keyMoment1923 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1923) =
      Integer.Sparse.eval keyMomentRow1923 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1923).leftCharge (GramAssembly.key 1923).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2925) := by
    have ha : gramCharges (GramAssembly.key 1923).leftCharge (GramAssembly.key 1923).rightCharge = raw41336 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41336Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41336 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1923).leftCharge (GramAssembly.key 1923).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1923, Integer.Sparse.eval]

theorem keyMoment1924 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1924) =
      Integer.Sparse.eval keyMomentRow1924 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1924).leftCharge (GramAssembly.key 1924).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1237) := by
    have ha : gramCharges (GramAssembly.key 1924).leftCharge (GramAssembly.key 1924).rightCharge = raw41337 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41337Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41337 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1924).leftCharge (GramAssembly.key 1924).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1924, Integer.Sparse.eval]

theorem keyMoment1925 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1925) =
      Integer.Sparse.eval keyMomentRow1925 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1925).leftCharge (GramAssembly.key 1925).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2575) := by
    have ha : gramCharges (GramAssembly.key 1925).leftCharge (GramAssembly.key 1925).rightCharge = raw41338 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41338Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41338 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1925).leftCharge (GramAssembly.key 1925).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1925, Integer.Sparse.eval]

theorem keyMoment1926 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1926) =
      Integer.Sparse.eval keyMomentRow1926 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1926).leftCharge (GramAssembly.key 1926).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2545) := by
    have ha : gramCharges (GramAssembly.key 1926).leftCharge (GramAssembly.key 1926).rightCharge = raw41339 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41339Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41339 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1926).leftCharge (GramAssembly.key 1926).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1926, Integer.Sparse.eval]

theorem keyMoment1927 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1927) =
      Integer.Sparse.eval keyMomentRow1927 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1927).leftCharge (GramAssembly.key 1927).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1215) := by
    have ha : gramCharges (GramAssembly.key 1927).leftCharge (GramAssembly.key 1927).rightCharge = raw41340 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41340Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41340 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1927).leftCharge (GramAssembly.key 1927).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1927, Integer.Sparse.eval]

theorem keyMoment1928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1928) =
      Integer.Sparse.eval keyMomentRow1928 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1928).leftCharge (GramAssembly.key 1928).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3906) := by
    have ha : gramCharges (GramAssembly.key 1928).leftCharge (GramAssembly.key 1928).rightCharge = raw41341 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41341Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41341 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1928).leftCharge (GramAssembly.key 1928).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1928, Integer.Sparse.eval]

theorem keyMoment1929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1929) =
      Integer.Sparse.eval keyMomentRow1929 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1929).leftCharge (GramAssembly.key 1929).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1929).leftCharge (GramAssembly.key 1929).rightCharge = raw41342 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41342Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41342 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1929).leftCharge (GramAssembly.key 1929).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1929, Integer.Sparse.eval]

theorem keyMoment1930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1930) =
      Integer.Sparse.eval keyMomentRow1930 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1930).leftCharge (GramAssembly.key 1930).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2028) := by
    have ha : gramCharges (GramAssembly.key 1930).leftCharge (GramAssembly.key 1930).rightCharge = raw41343 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41343Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41343 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1930).leftCharge (GramAssembly.key 1930).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1930, Integer.Sparse.eval]

theorem keyMoment1931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1931) =
      Integer.Sparse.eval keyMomentRow1931 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1931).leftCharge (GramAssembly.key 1931).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3533) := by
    have ha : gramCharges (GramAssembly.key 1931).leftCharge (GramAssembly.key 1931).rightCharge = raw41344 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41344Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41344 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1931).leftCharge (GramAssembly.key 1931).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1931, Integer.Sparse.eval]

theorem keyMoment1932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1932) =
      Integer.Sparse.eval keyMomentRow1932 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1932).leftCharge (GramAssembly.key 1932).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3903) := by
    have ha : gramCharges (GramAssembly.key 1932).leftCharge (GramAssembly.key 1932).rightCharge = raw41345 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41345Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41345 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1932).leftCharge (GramAssembly.key 1932).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1932, Integer.Sparse.eval]

theorem keyMoment1933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1933) =
      Integer.Sparse.eval keyMomentRow1933 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1933).leftCharge (GramAssembly.key 1933).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3875) := by
    have ha : gramCharges (GramAssembly.key 1933).leftCharge (GramAssembly.key 1933).rightCharge = raw41346 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41346Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41346 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1933).leftCharge (GramAssembly.key 1933).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1933, Integer.Sparse.eval]

theorem keyMoment1934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1934) =
      Integer.Sparse.eval keyMomentRow1934 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1934).leftCharge (GramAssembly.key 1934).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3719) := by
    have ha : gramCharges (GramAssembly.key 1934).leftCharge (GramAssembly.key 1934).rightCharge = raw41347 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41347Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41347 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1934).leftCharge (GramAssembly.key 1934).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1934, Integer.Sparse.eval]

theorem keyMoment1935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1935) =
      Integer.Sparse.eval keyMomentRow1935 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1935).leftCharge (GramAssembly.key 1935).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3843) := by
    have ha : gramCharges (GramAssembly.key 1935).leftCharge (GramAssembly.key 1935).rightCharge = raw41348 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41348Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41348 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1935).leftCharge (GramAssembly.key 1935).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1935, Integer.Sparse.eval]

theorem keyMoment1936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1936) =
      Integer.Sparse.eval keyMomentRow1936 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1936).leftCharge (GramAssembly.key 1936).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3901) := by
    have ha : gramCharges (GramAssembly.key 1936).leftCharge (GramAssembly.key 1936).rightCharge = raw41349 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41349Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41349 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1936).leftCharge (GramAssembly.key 1936).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1936, Integer.Sparse.eval]

theorem keyMoment1937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1937) =
      Integer.Sparse.eval keyMomentRow1937 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1937).leftCharge (GramAssembly.key 1937).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3837) := by
    have ha : gramCharges (GramAssembly.key 1937).leftCharge (GramAssembly.key 1937).rightCharge = raw41350 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41350Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41350 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1937).leftCharge (GramAssembly.key 1937).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1937, Integer.Sparse.eval]

theorem keyMoment1938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1938) =
      Integer.Sparse.eval keyMomentRow1938 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1938).leftCharge (GramAssembly.key 1938).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2025) := by
    have ha : gramCharges (GramAssembly.key 1938).leftCharge (GramAssembly.key 1938).rightCharge = raw41351 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41351Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41351 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1938).leftCharge (GramAssembly.key 1938).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1938, Integer.Sparse.eval]

theorem keyMoment1939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1939) =
      Integer.Sparse.eval keyMomentRow1939 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1939).leftCharge (GramAssembly.key 1939).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3534) := by
    have ha : gramCharges (GramAssembly.key 1939).leftCharge (GramAssembly.key 1939).rightCharge = raw41352 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41352Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41352 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1939).leftCharge (GramAssembly.key 1939).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1939, Integer.Sparse.eval]

theorem keyMoment1940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1940) =
      Integer.Sparse.eval keyMomentRow1940 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1940).leftCharge (GramAssembly.key 1940).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2924) := by
    have ha : gramCharges (GramAssembly.key 1940).leftCharge (GramAssembly.key 1940).rightCharge = raw41353 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41353Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41353 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1940).leftCharge (GramAssembly.key 1940).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1940, Integer.Sparse.eval]

theorem keyMoment1941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1941) =
      Integer.Sparse.eval keyMomentRow1941 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1941).leftCharge (GramAssembly.key 1941).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3974) := by
    have ha : gramCharges (GramAssembly.key 1941).leftCharge (GramAssembly.key 1941).rightCharge = raw41354 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41354Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41354 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1941).leftCharge (GramAssembly.key 1941).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1941, Integer.Sparse.eval]

theorem keyMoment1942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1942) =
      Integer.Sparse.eval keyMomentRow1942 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1942).leftCharge (GramAssembly.key 1942).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1236) := by
    have ha : gramCharges (GramAssembly.key 1942).leftCharge (GramAssembly.key 1942).rightCharge = raw41355 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41355Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41355 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1942).leftCharge (GramAssembly.key 1942).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1942, Integer.Sparse.eval]

theorem keyMoment1943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1943) =
      Integer.Sparse.eval keyMomentRow1943 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1943).leftCharge (GramAssembly.key 1943).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2739) := by
    have ha : gramCharges (GramAssembly.key 1943).leftCharge (GramAssembly.key 1943).rightCharge = raw41356 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41356Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41356 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1943).leftCharge (GramAssembly.key 1943).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1943, Integer.Sparse.eval]

theorem keyMoment1944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1944) =
      Integer.Sparse.eval keyMomentRow1944 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1944).leftCharge (GramAssembly.key 1944).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2722) := by
    have ha : gramCharges (GramAssembly.key 1944).leftCharge (GramAssembly.key 1944).rightCharge = raw41357 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41357Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41357 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1944).leftCharge (GramAssembly.key 1944).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1944, Integer.Sparse.eval]

theorem keyMoment1945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1945) =
      Integer.Sparse.eval keyMomentRow1945 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1945).leftCharge (GramAssembly.key 1945).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1235) := by
    have ha : gramCharges (GramAssembly.key 1945).leftCharge (GramAssembly.key 1945).rightCharge = raw41358 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41358Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41358 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1945).leftCharge (GramAssembly.key 1945).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1945, Integer.Sparse.eval]

theorem keyMoment1946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1946) =
      Integer.Sparse.eval keyMomentRow1946 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1946).leftCharge (GramAssembly.key 1946).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2721) := by
    have ha : gramCharges (GramAssembly.key 1946).leftCharge (GramAssembly.key 1946).rightCharge = raw41359 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41359Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41359 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1946).leftCharge (GramAssembly.key 1946).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1946, Integer.Sparse.eval]

theorem keyMoment1947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1947) =
      Integer.Sparse.eval keyMomentRow1947 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1947).leftCharge (GramAssembly.key 1947).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1947).leftCharge (GramAssembly.key 1947).rightCharge = raw41360 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41360Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41360 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1947).leftCharge (GramAssembly.key 1947).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1947, Integer.Sparse.eval]

theorem keyMoment1948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1948) =
      Integer.Sparse.eval keyMomentRow1948 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1948).leftCharge (GramAssembly.key 1948).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3876) := by
    have ha : gramCharges (GramAssembly.key 1948).leftCharge (GramAssembly.key 1948).rightCharge = raw41361 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41361Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41361 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1948).leftCharge (GramAssembly.key 1948).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1948, Integer.Sparse.eval]

theorem keyMoment1949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1949) =
      Integer.Sparse.eval keyMomentRow1949 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1949).leftCharge (GramAssembly.key 1949).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3693) := by
    have ha : gramCharges (GramAssembly.key 1949).leftCharge (GramAssembly.key 1949).rightCharge = raw41362 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41362Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41362 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1949).leftCharge (GramAssembly.key 1949).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1949, Integer.Sparse.eval]

theorem keyMoment1950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1950) =
      Integer.Sparse.eval keyMomentRow1950 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1950).leftCharge (GramAssembly.key 1950).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3845) := by
    have ha : gramCharges (GramAssembly.key 1950).leftCharge (GramAssembly.key 1950).rightCharge = raw41363 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41363Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41363 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1950).leftCharge (GramAssembly.key 1950).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1950, Integer.Sparse.eval]

theorem keyMoment1951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1951) =
      Integer.Sparse.eval keyMomentRow1951 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1951).leftCharge (GramAssembly.key 1951).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3902) := by
    have ha : gramCharges (GramAssembly.key 1951).leftCharge (GramAssembly.key 1951).rightCharge = raw41364 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41364Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41364 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1951).leftCharge (GramAssembly.key 1951).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1951, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1920 : keyMomentRows (1920 : Fin 2886) =
    keyMomentRow1920 := by decide +kernel

theorem keyMomentRowsAt1921 : keyMomentRows (1921 : Fin 2886) =
    keyMomentRow1921 := by decide +kernel

theorem keyMomentRowsAt1922 : keyMomentRows (1922 : Fin 2886) =
    keyMomentRow1922 := by decide +kernel

theorem keyMomentRowsAt1923 : keyMomentRows (1923 : Fin 2886) =
    keyMomentRow1923 := by decide +kernel

theorem keyMomentRowsAt1924 : keyMomentRows (1924 : Fin 2886) =
    keyMomentRow1924 := by decide +kernel

theorem keyMomentRowsAt1925 : keyMomentRows (1925 : Fin 2886) =
    keyMomentRow1925 := by decide +kernel

theorem keyMomentRowsAt1926 : keyMomentRows (1926 : Fin 2886) =
    keyMomentRow1926 := by decide +kernel

theorem keyMomentRowsAt1927 : keyMomentRows (1927 : Fin 2886) =
    keyMomentRow1927 := by decide +kernel

theorem keyMomentRowsAt1928 : keyMomentRows (1928 : Fin 2886) =
    keyMomentRow1928 := by decide +kernel

theorem keyMomentRowsAt1929 : keyMomentRows (1929 : Fin 2886) =
    keyMomentRow1929 := by decide +kernel

theorem keyMomentRowsAt1930 : keyMomentRows (1930 : Fin 2886) =
    keyMomentRow1930 := by decide +kernel

theorem keyMomentRowsAt1931 : keyMomentRows (1931 : Fin 2886) =
    keyMomentRow1931 := by decide +kernel

theorem keyMomentRowsAt1932 : keyMomentRows (1932 : Fin 2886) =
    keyMomentRow1932 := by decide +kernel

theorem keyMomentRowsAt1933 : keyMomentRows (1933 : Fin 2886) =
    keyMomentRow1933 := by decide +kernel

theorem keyMomentRowsAt1934 : keyMomentRows (1934 : Fin 2886) =
    keyMomentRow1934 := by decide +kernel

theorem keyMomentRowsAt1935 : keyMomentRows (1935 : Fin 2886) =
    keyMomentRow1935 := by decide +kernel

theorem keyMomentRowsAt1936 : keyMomentRows (1936 : Fin 2886) =
    keyMomentRow1936 := by decide +kernel

theorem keyMomentRowsAt1937 : keyMomentRows (1937 : Fin 2886) =
    keyMomentRow1937 := by decide +kernel

theorem keyMomentRowsAt1938 : keyMomentRows (1938 : Fin 2886) =
    keyMomentRow1938 := by decide +kernel

theorem keyMomentRowsAt1939 : keyMomentRows (1939 : Fin 2886) =
    keyMomentRow1939 := by decide +kernel

theorem keyMomentRowsAt1940 : keyMomentRows (1940 : Fin 2886) =
    keyMomentRow1940 := by decide +kernel

theorem keyMomentRowsAt1941 : keyMomentRows (1941 : Fin 2886) =
    keyMomentRow1941 := by decide +kernel

theorem keyMomentRowsAt1942 : keyMomentRows (1942 : Fin 2886) =
    keyMomentRow1942 := by decide +kernel

theorem keyMomentRowsAt1943 : keyMomentRows (1943 : Fin 2886) =
    keyMomentRow1943 := by decide +kernel

theorem keyMomentRowsAt1944 : keyMomentRows (1944 : Fin 2886) =
    keyMomentRow1944 := by decide +kernel

theorem keyMomentRowsAt1945 : keyMomentRows (1945 : Fin 2886) =
    keyMomentRow1945 := by decide +kernel

theorem keyMomentRowsAt1946 : keyMomentRows (1946 : Fin 2886) =
    keyMomentRow1946 := by decide +kernel

theorem keyMomentRowsAt1947 : keyMomentRows (1947 : Fin 2886) =
    keyMomentRow1947 := by decide +kernel

theorem keyMomentRowsAt1948 : keyMomentRows (1948 : Fin 2886) =
    keyMomentRow1948 := by decide +kernel

theorem keyMomentRowsAt1949 : keyMomentRows (1949 : Fin 2886) =
    keyMomentRow1949 := by decide +kernel

theorem keyMomentRowsAt1950 : keyMomentRows (1950 : Fin 2886) =
    keyMomentRow1950 := by decide +kernel

theorem keyMomentRowsAt1951 : keyMomentRows (1951 : Fin 2886) =
    keyMomentRow1951 := by decide +kernel

theorem keyMomentChunkSound60_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 60) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1920 ∨ k.val = 1921 ∨ k.val = 1922 ∨ k.val = 1923 ∨ k.val = 1924 ∨ k.val = 1925 ∨ k.val = 1926 ∨ k.val = 1927 ∨ k.val = 1928 ∨ k.val = 1929 ∨ k.val = 1930 ∨ k.val = 1931 ∨ k.val = 1932 ∨ k.val = 1933 ∨ k.val = 1934 ∨ k.val = 1935 ∨ k.val = 1936 ∨ k.val = 1937 ∨ k.val = 1938 ∨ k.val = 1939 ∨ k.val = 1940 ∨ k.val = 1941 ∨ k.val = 1942 ∨ k.val = 1943 ∨ k.val = 1944 ∨ k.val = 1945 ∨ k.val = 1946 ∨ k.val = 1947 ∨ k.val = 1948 ∨ k.val = 1949 ∨ k.val = 1950 ∨ k.val = 1951 := by omega
  rcases heq with h1920 | h1921 | h1922 | h1923 | h1924 | h1925 | h1926 | h1927 | h1928 | h1929 | h1930 | h1931 | h1932 | h1933 | h1934 | h1935 | h1936 | h1937 | h1938 | h1939 | h1940 | h1941 | h1942 | h1943 | h1944 | h1945 | h1946 | h1947 | h1948 | h1949 | h1950 | h1951
  · have he : k = (1920 : Fin 2886) := Fin.ext h1920
    subst k
    rw [keyMomentRowsAt1920]
    exact keyMoment1920 B hB
  · have he : k = (1921 : Fin 2886) := Fin.ext h1921
    subst k
    rw [keyMomentRowsAt1921]
    exact keyMoment1921 B hB
  · have he : k = (1922 : Fin 2886) := Fin.ext h1922
    subst k
    rw [keyMomentRowsAt1922]
    exact keyMoment1922 B hB
  · have he : k = (1923 : Fin 2886) := Fin.ext h1923
    subst k
    rw [keyMomentRowsAt1923]
    exact keyMoment1923 B hB
  · have he : k = (1924 : Fin 2886) := Fin.ext h1924
    subst k
    rw [keyMomentRowsAt1924]
    exact keyMoment1924 B hB
  · have he : k = (1925 : Fin 2886) := Fin.ext h1925
    subst k
    rw [keyMomentRowsAt1925]
    exact keyMoment1925 B hB
  · have he : k = (1926 : Fin 2886) := Fin.ext h1926
    subst k
    rw [keyMomentRowsAt1926]
    exact keyMoment1926 B hB
  · have he : k = (1927 : Fin 2886) := Fin.ext h1927
    subst k
    rw [keyMomentRowsAt1927]
    exact keyMoment1927 B hB
  · have he : k = (1928 : Fin 2886) := Fin.ext h1928
    subst k
    rw [keyMomentRowsAt1928]
    exact keyMoment1928 B hB
  · have he : k = (1929 : Fin 2886) := Fin.ext h1929
    subst k
    rw [keyMomentRowsAt1929]
    exact keyMoment1929 B hB
  · have he : k = (1930 : Fin 2886) := Fin.ext h1930
    subst k
    rw [keyMomentRowsAt1930]
    exact keyMoment1930 B hB
  · have he : k = (1931 : Fin 2886) := Fin.ext h1931
    subst k
    rw [keyMomentRowsAt1931]
    exact keyMoment1931 B hB
  · have he : k = (1932 : Fin 2886) := Fin.ext h1932
    subst k
    rw [keyMomentRowsAt1932]
    exact keyMoment1932 B hB
  · have he : k = (1933 : Fin 2886) := Fin.ext h1933
    subst k
    rw [keyMomentRowsAt1933]
    exact keyMoment1933 B hB
  · have he : k = (1934 : Fin 2886) := Fin.ext h1934
    subst k
    rw [keyMomentRowsAt1934]
    exact keyMoment1934 B hB
  · have he : k = (1935 : Fin 2886) := Fin.ext h1935
    subst k
    rw [keyMomentRowsAt1935]
    exact keyMoment1935 B hB
  · have he : k = (1936 : Fin 2886) := Fin.ext h1936
    subst k
    rw [keyMomentRowsAt1936]
    exact keyMoment1936 B hB
  · have he : k = (1937 : Fin 2886) := Fin.ext h1937
    subst k
    rw [keyMomentRowsAt1937]
    exact keyMoment1937 B hB
  · have he : k = (1938 : Fin 2886) := Fin.ext h1938
    subst k
    rw [keyMomentRowsAt1938]
    exact keyMoment1938 B hB
  · have he : k = (1939 : Fin 2886) := Fin.ext h1939
    subst k
    rw [keyMomentRowsAt1939]
    exact keyMoment1939 B hB
  · have he : k = (1940 : Fin 2886) := Fin.ext h1940
    subst k
    rw [keyMomentRowsAt1940]
    exact keyMoment1940 B hB
  · have he : k = (1941 : Fin 2886) := Fin.ext h1941
    subst k
    rw [keyMomentRowsAt1941]
    exact keyMoment1941 B hB
  · have he : k = (1942 : Fin 2886) := Fin.ext h1942
    subst k
    rw [keyMomentRowsAt1942]
    exact keyMoment1942 B hB
  · have he : k = (1943 : Fin 2886) := Fin.ext h1943
    subst k
    rw [keyMomentRowsAt1943]
    exact keyMoment1943 B hB
  · have he : k = (1944 : Fin 2886) := Fin.ext h1944
    subst k
    rw [keyMomentRowsAt1944]
    exact keyMoment1944 B hB
  · have he : k = (1945 : Fin 2886) := Fin.ext h1945
    subst k
    rw [keyMomentRowsAt1945]
    exact keyMoment1945 B hB
  · have he : k = (1946 : Fin 2886) := Fin.ext h1946
    subst k
    rw [keyMomentRowsAt1946]
    exact keyMoment1946 B hB
  · have he : k = (1947 : Fin 2886) := Fin.ext h1947
    subst k
    rw [keyMomentRowsAt1947]
    exact keyMoment1947 B hB
  · have he : k = (1948 : Fin 2886) := Fin.ext h1948
    subst k
    rw [keyMomentRowsAt1948]
    exact keyMoment1948 B hB
  · have he : k = (1949 : Fin 2886) := Fin.ext h1949
    subst k
    rw [keyMomentRowsAt1949]
    exact keyMoment1949 B hB
  · have he : k = (1950 : Fin 2886) := Fin.ext h1950
    subst k
    rw [keyMomentRowsAt1950]
    exact keyMoment1950 B hB
  · have he : k = (1951 : Fin 2886) := Fin.ext h1951
    subst k
    rw [keyMomentRowsAt1951]
    exact keyMoment1951 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound60_e_oai
