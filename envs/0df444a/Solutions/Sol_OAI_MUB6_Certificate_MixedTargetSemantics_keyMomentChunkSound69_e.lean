-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:48.786103+00:00
-- url     : https://prove2.me/submissions/2dc206e6-231b-406c-aa28-f11bcf0b25cb

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

theorem rename_labels {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (small : Fin n → Fin l) (e : Fin l ↪ Fin k) (h : label = e ∘ small) :
    mixedMoment B A label = mixedMoment B A small := by
  rw [h]
  exact mixedMoment_label_embedding hk B A e small

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical326
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41728 raw41728Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw41728 raw41728Labels = mixedMoment B raw41728step0 raw41728step0Labels := by
      have ha : raw41728step0 = (fun i j => raw41728 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41728step0 raw41728; decide +kernel
      have hl : raw41728step0Labels = raw41728Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41728 raw41728Labels permutation337 permutation4
    mixedMoment B raw41728step0 raw41728step0Labels = mixedMoment B raw41728step1 raw41728step1Labels := by
      have ha : raw41728step1 = -raw41728step0 := by apply Matrix.ext; change ∀ i j, raw41728step1 i j = -(raw41728step0 i j); unfold raw41728step1 raw41728step0; decide +kernel
      have hl : raw41728step1Labels = raw41728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41728step1 raw41728step1Labels = mixedMoment B raw41728step2 raw41728step2Labels := by
      have ha : raw41728step2 = raw41728step1 := by apply Matrix.ext; unfold raw41728step2 raw41728step1; decide +kernel
      have hl : raw41728step1Labels = labelEmbedding1 ∘ raw41728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41728step1 raw41728step1Labels raw41728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

theorem canonical41729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41729 raw41729Labels = mixedMoment B node4667 node4667Labels := by
  calc
    mixedMoment B raw41729 raw41729Labels = mixedMoment B raw41729step0 raw41729step0Labels := by
      have ha : raw41729step0 = (fun i j => raw41729 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41729step0 raw41729; decide +kernel
      have hl : raw41729step0Labels = raw41729Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41729 raw41729Labels permutation345 permutation6
    _ = mixedMoment B node4667 node4667Labels := by rfl

theorem canonical41730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41730 raw41730Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw41730 raw41730Labels = mixedMoment B raw41730step0 raw41730step0Labels := by
      have ha : raw41730step0 = (fun i j => raw41730 (permutation313 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41730step0 raw41730; decide +kernel
      have hl : raw41730step0Labels = raw41730Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41730 raw41730Labels permutation313 permutation4
    mixedMoment B raw41730step0 raw41730step0Labels = mixedMoment B raw41730step1 raw41730step1Labels := by
      have ha : raw41730step1 = -raw41730step0 := by apply Matrix.ext; change ∀ i j, raw41730step1 i j = -(raw41730step0 i j); unfold raw41730step1 raw41730step0; decide +kernel
      have hl : raw41730step1Labels = raw41730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41730step1 raw41730step1Labels = mixedMoment B raw41730step2 raw41730step2Labels := by
      have ha : raw41730step2 = raw41730step1 := by apply Matrix.ext; unfold raw41730step2 raw41730step1; decide +kernel
      have hl : raw41730step1Labels = labelEmbedding1 ∘ raw41730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41730step1 raw41730step1Labels raw41730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

theorem canonical41731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41731 raw41731Labels = mixedMoment B node4765 node4765Labels := by
  calc
    mixedMoment B raw41731 raw41731Labels = mixedMoment B raw41731step0 raw41731step0Labels := by
      have ha : raw41731step0 = (fun i j => raw41731 (permutation316 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41731step0 raw41731; decide +kernel
      have hl : raw41731step0Labels = raw41731Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41731 raw41731Labels permutation316 permutation6
    _ = mixedMoment B node4765 node4765Labels := by rfl

theorem canonical41732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41732 raw41732Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw41732 raw41732Labels = mixedMoment B raw41732step0 raw41732step0Labels := by
      have ha : raw41732step0 = (fun i j => raw41732 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41732step0 raw41732; decide +kernel
      have hl : raw41732step0Labels = raw41732Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41732 raw41732Labels permutation179 permutation2
    mixedMoment B raw41732step0 raw41732step0Labels = mixedMoment B raw41732step1 raw41732step1Labels := by
      have ha : raw41732step1 = raw41732step0 := by apply Matrix.ext; unfold raw41732step1 raw41732step0; decide +kernel
      have hl : raw41732step0Labels = labelEmbedding1 ∘ raw41732step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41732step0 raw41732step0Labels raw41732step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2219 node2219Labels := by rfl

theorem canonical41733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41733 raw41733Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw41733 raw41733Labels = mixedMoment B raw41733step0 raw41733step0Labels := by
      have ha : raw41733step0 = (fun i j => raw41733 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41733step0 raw41733; decide +kernel
      have hl : raw41733step0Labels = raw41733Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41733 raw41733Labels permutation317 permutation6
    _ = mixedMoment B node4793 node4793Labels := by rfl

theorem canonical41734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41734 raw41734Labels = mixedMoment B node2160 node2160Labels := by
  calc
    mixedMoment B raw41734 raw41734Labels = mixedMoment B raw41734step0 raw41734step0Labels := by
      have ha : raw41734step0 = (fun i j => raw41734 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41734step0 raw41734; decide +kernel
      have hl : raw41734step0Labels = raw41734Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41734 raw41734Labels permutation180 permutation2
    mixedMoment B raw41734step0 raw41734step0Labels = mixedMoment B raw41734step1 raw41734step1Labels := by
      have ha : raw41734step1 = raw41734step0 := by apply Matrix.ext; unfold raw41734step1 raw41734step0; decide +kernel
      have hl : raw41734step0Labels = labelEmbedding1 ∘ raw41734step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41734step0 raw41734step0Labels raw41734step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2160 node2160Labels := by rfl

theorem canonical41735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41735 raw41735Labels = mixedMoment B node4667 node4667Labels := by
  calc
    mixedMoment B raw41735 raw41735Labels = mixedMoment B raw41735step0 raw41735step0Labels := by
      have ha : raw41735step0 = (fun i j => raw41735 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41735step0 raw41735; decide +kernel
      have hl : raw41735step0Labels = raw41735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41735 raw41735Labels permutation197 permutation7
    mixedMoment B raw41735step0 raw41735step0Labels = mixedMoment B raw41735step1 raw41735step1Labels := by
      have ha : raw41735step1 = -raw41735step0 := by apply Matrix.ext; change ∀ i j, raw41735step1 i j = -(raw41735step0 i j); unfold raw41735step1 raw41735step0; decide +kernel
      have hl : raw41735step1Labels = raw41735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41735step1 raw41735step1Labels = mixedMoment B raw41735step2 raw41735step2Labels := by
      have ha : raw41735step2 = raw41735step1 := by apply Matrix.ext; unfold raw41735step2 raw41735step1; decide +kernel
      have hl : raw41735step1Labels = labelEmbedding6 ∘ raw41735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41735step1 raw41735step1Labels raw41735step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4667 node4667Labels := by rfl

theorem canonical41736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41736 raw41736Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw41736 raw41736Labels = mixedMoment B raw41736step0 raw41736step0Labels := by
      have hz : ∀ j, raw41736 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41736step0 = (fun i j => raw41736 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41736step0 raw41736; decide +kernel
      have hl : raw41736step0Labels = raw41736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41736 raw41736Labels permutation520 hz
    mixedMoment B raw41736step0 raw41736step0Labels = mixedMoment B raw41736step1 raw41736step1Labels := by
      have hz : ∀ j, raw41736step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41736step1 = (fun i j => raw41736step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41736step1 raw41736step0; decide +kernel
      have hl : raw41736step1Labels = raw41736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41736step0 raw41736step0Labels permutation104 hz
    mixedMoment B raw41736step1 raw41736step1Labels = mixedMoment B raw41736step2 raw41736step2Labels := by
      have ha : raw41736step2 = (fun i j => raw41736step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41736step2 raw41736step1; decide +kernel
      have hl : raw41736step2Labels = raw41736step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41736step1 raw41736step1Labels permutation10 permutation2
    mixedMoment B raw41736step2 raw41736step2Labels = mixedMoment B raw41736step3 raw41736step3Labels := by
      have ha : raw41736step3 = raw41736step2 := by apply Matrix.ext; unfold raw41736step3 raw41736step2; decide +kernel
      have hl : raw41736step2Labels = labelEmbedding1 ∘ raw41736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41736step2 raw41736step2Labels raw41736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

theorem canonical41737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41737 raw41737Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw41737 raw41737Labels = mixedMoment B raw41737step0 raw41737step0Labels := by
      have hz : ∀ j, raw41737 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41737step0 = (fun i j => raw41737 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41737step0 raw41737; decide +kernel
      have hl : raw41737step0Labels = raw41737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41737 raw41737Labels permutation520 hz
    mixedMoment B raw41737step0 raw41737step0Labels = mixedMoment B raw41737step1 raw41737step1Labels := by
      have hz : ∀ j, raw41737step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41737step1 = (fun i j => raw41737step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41737step1 raw41737step0; decide +kernel
      have hl : raw41737step1Labels = raw41737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41737step0 raw41737step0Labels permutation104 hz
    mixedMoment B raw41737step1 raw41737step1Labels = mixedMoment B raw41737step2 raw41737step2Labels := by
      have ha : raw41737step2 = (fun i j => raw41737step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41737step2 raw41737step1; decide +kernel
      have hl : raw41737step2Labels = raw41737step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41737step1 raw41737step1Labels permutation10 permutation2
    mixedMoment B raw41737step2 raw41737step2Labels = mixedMoment B raw41737step3 raw41737step3Labels := by
      have ha : raw41737step3 = raw41737step2 := by apply Matrix.ext; unfold raw41737step3 raw41737step2; decide +kernel
      have hl : raw41737step2Labels = labelEmbedding8 ∘ raw41737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41737step2 raw41737step2Labels raw41737step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

theorem canonical41738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41738 raw41738Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw41738 raw41738Labels = mixedMoment B raw41738step0 raw41738step0Labels := by
      have hz : ∀ j, raw41738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41738step0 = (fun i j => raw41738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41738step0 raw41738; decide +kernel
      have hl : raw41738step0Labels = raw41738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41738 raw41738Labels permutation434 hz
    mixedMoment B raw41738step0 raw41738step0Labels = mixedMoment B raw41738step1 raw41738step1Labels := by
      have ha : raw41738step1 = (fun i j => raw41738step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41738step1 raw41738step0; decide +kernel
      have hl : raw41738step1Labels = raw41738step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41738step0 raw41738step0Labels permutation38 permutation2
    mixedMoment B raw41738step1 raw41738step1Labels = mixedMoment B raw41738step2 raw41738step2Labels := by
      have ha : raw41738step2 = raw41738step1 := by apply Matrix.ext; unfold raw41738step2 raw41738step1; decide +kernel
      have hl : raw41738step1Labels = labelEmbedding1 ∘ raw41738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41738step1 raw41738step1Labels raw41738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

theorem canonical41739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41739 raw41739Labels = mixedMoment B node4880 node4880Labels := by
  calc
    mixedMoment B raw41739 raw41739Labels = mixedMoment B raw41739step0 raw41739step0Labels := by
      have hz : ∀ j, raw41739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41739step0 = (fun i j => raw41739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41739step0 raw41739; decide +kernel
      have hl : raw41739step0Labels = raw41739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41739 raw41739Labels permutation434 hz
    mixedMoment B raw41739step0 raw41739step0Labels = mixedMoment B raw41739step1 raw41739step1Labels := by
      have ha : raw41739step1 = (fun i j => raw41739step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41739step1 raw41739step0; decide +kernel
      have hl : raw41739step1Labels = raw41739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41739step0 raw41739step0Labels permutation53 permutation7
    mixedMoment B raw41739step1 raw41739step1Labels = mixedMoment B raw41739step2 raw41739step2Labels := by
      have ha : raw41739step2 = -raw41739step1 := by apply Matrix.ext; change ∀ i j, raw41739step2 i j = -(raw41739step1 i j); unfold raw41739step2 raw41739step1; decide +kernel
      have hl : raw41739step2Labels = raw41739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41739step2 raw41739step2Labels = mixedMoment B raw41739step3 raw41739step3Labels := by
      have ha : raw41739step3 = raw41739step2 := by apply Matrix.ext; unfold raw41739step3 raw41739step2; decide +kernel
      have hl : raw41739step2Labels = labelEmbedding6 ∘ raw41739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41739step2 raw41739step2Labels raw41739step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4880 node4880Labels := by rfl

theorem canonical41740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41740 raw41740Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw41740 raw41740Labels = mixedMoment B raw41740step0 raw41740step0Labels := by
      have hz : ∀ j, raw41740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41740step0 = (fun i j => raw41740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41740step0 raw41740; decide +kernel
      have hl : raw41740step0Labels = raw41740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41740 raw41740Labels permutation434 hz
    mixedMoment B raw41740step0 raw41740step0Labels = mixedMoment B raw41740step1 raw41740step1Labels := by
      have ha : raw41740step1 = (fun i j => raw41740step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41740step1 raw41740step0; decide +kernel
      have hl : raw41740step1Labels = raw41740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41740step0 raw41740step0Labels permutation38 permutation2
    mixedMoment B raw41740step1 raw41740step1Labels = mixedMoment B raw41740step2 raw41740step2Labels := by
      have ha : raw41740step2 = raw41740step1 := by apply Matrix.ext; unfold raw41740step2 raw41740step1; decide +kernel
      have hl : raw41740step1Labels = labelEmbedding1 ∘ raw41740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41740step1 raw41740step1Labels raw41740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical41741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41741 raw41741Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw41741 raw41741Labels = mixedMoment B raw41741step0 raw41741step0Labels := by
      have hz : ∀ j, raw41741 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41741step0 = (fun i j => raw41741 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41741step0 raw41741; decide +kernel
      have hl : raw41741step0Labels = raw41741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41741 raw41741Labels permutation434 hz
    mixedMoment B raw41741step0 raw41741step0Labels = mixedMoment B raw41741step1 raw41741step1Labels := by
      have ha : raw41741step1 = (fun i j => raw41741step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41741step1 raw41741step0; decide +kernel
      have hl : raw41741step1Labels = raw41741step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41741step0 raw41741step0Labels permutation38 permutation2
    mixedMoment B raw41741step1 raw41741step1Labels = mixedMoment B raw41741step2 raw41741step2Labels := by
      have ha : raw41741step2 = raw41741step1 := by apply Matrix.ext; unfold raw41741step2 raw41741step1; decide +kernel
      have hl : raw41741step1Labels = labelEmbedding8 ∘ raw41741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41741step1 raw41741step1Labels raw41741step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

theorem canonical41742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41742 raw41742Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw41742 raw41742Labels = mixedMoment B raw41742step0 raw41742step0Labels := by
      have hz : ∀ j, raw41742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41742step0 = (fun i j => raw41742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41742step0 raw41742; decide +kernel
      have hl : raw41742step0Labels = raw41742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41742 raw41742Labels permutation434 hz
    mixedMoment B raw41742step0 raw41742step0Labels = mixedMoment B raw41742step1 raw41742step1Labels := by
      have ha : raw41742step1 = (fun i j => raw41742step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41742step1 raw41742step0; decide +kernel
      have hl : raw41742step1Labels = raw41742step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41742step0 raw41742step0Labels permutation38 permutation2
    mixedMoment B raw41742step1 raw41742step1Labels = mixedMoment B raw41742step2 raw41742step2Labels := by
      have ha : raw41742step2 = raw41742step1 := by apply Matrix.ext; unfold raw41742step2 raw41742step1; decide +kernel
      have hl : raw41742step1Labels = labelEmbedding1 ∘ raw41742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41742step1 raw41742step1Labels raw41742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical41743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41743 raw41743Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw41743 raw41743Labels = mixedMoment B raw41743step0 raw41743step0Labels := by
      have hz : ∀ j, raw41743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41743step0 = (fun i j => raw41743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41743step0 raw41743; decide +kernel
      have hl : raw41743step0Labels = raw41743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41743 raw41743Labels permutation434 hz
    mixedMoment B raw41743step0 raw41743step0Labels = mixedMoment B raw41743step1 raw41743step1Labels := by
      have ha : raw41743step1 = (fun i j => raw41743step0 (permutation47 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41743step1 raw41743step0; decide +kernel
      have hl : raw41743step1Labels = raw41743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41743step0 raw41743step0Labels permutation47 permutation7
    mixedMoment B raw41743step1 raw41743step1Labels = mixedMoment B raw41743step2 raw41743step2Labels := by
      have ha : raw41743step2 = -raw41743step1 := by apply Matrix.ext; change ∀ i j, raw41743step2 i j = -(raw41743step1 i j); unfold raw41743step2 raw41743step1; decide +kernel
      have hl : raw41743step2Labels = raw41743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41743step2 raw41743step2Labels = mixedMoment B raw41743step3 raw41743step3Labels := by
      have ha : raw41743step3 = raw41743step2 := by apply Matrix.ext; unfold raw41743step3 raw41743step2; decide +kernel
      have hl : raw41743step2Labels = labelEmbedding6 ∘ raw41743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41743step2 raw41743step2Labels raw41743step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical41744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41744 raw41744Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw41744 raw41744Labels = mixedMoment B raw41744step0 raw41744step0Labels := by
      have hz : ∀ j, raw41744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41744step0 = (fun i j => raw41744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41744step0 raw41744; decide +kernel
      have hl : raw41744step0Labels = raw41744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41744 raw41744Labels permutation434 hz
    mixedMoment B raw41744step0 raw41744step0Labels = mixedMoment B raw41744step1 raw41744step1Labels := by
      have ha : raw41744step1 = (fun i j => raw41744step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41744step1 raw41744step0; decide +kernel
      have hl : raw41744step1Labels = raw41744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41744step0 raw41744step0Labels permutation38 permutation2
    mixedMoment B raw41744step1 raw41744step1Labels = mixedMoment B raw41744step2 raw41744step2Labels := by
      have ha : raw41744step2 = raw41744step1 := by apply Matrix.ext; unfold raw41744step2 raw41744step1; decide +kernel
      have hl : raw41744step1Labels = labelEmbedding1 ∘ raw41744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41744step1 raw41744step1Labels raw41744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

theorem canonical41745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41745 raw41745Labels = mixedMoment B node4700 node4700Labels := by
  calc
    mixedMoment B raw41745 raw41745Labels = mixedMoment B raw41745step0 raw41745step0Labels := by
      have hz : ∀ j, raw41745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41745step0 = (fun i j => raw41745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41745step0 raw41745; decide +kernel
      have hl : raw41745step0Labels = raw41745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41745 raw41745Labels permutation434 hz
    mixedMoment B raw41745step0 raw41745step0Labels = mixedMoment B raw41745step1 raw41745step1Labels := by
      have ha : raw41745step1 = (fun i j => raw41745step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41745step1 raw41745step0; decide +kernel
      have hl : raw41745step1Labels = raw41745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41745step0 raw41745step0Labels permutation46 permutation7
    mixedMoment B raw41745step1 raw41745step1Labels = mixedMoment B raw41745step2 raw41745step2Labels := by
      have ha : raw41745step2 = -raw41745step1 := by apply Matrix.ext; change ∀ i j, raw41745step2 i j = -(raw41745step1 i j); unfold raw41745step2 raw41745step1; decide +kernel
      have hl : raw41745step2Labels = raw41745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41745step2 raw41745step2Labels = mixedMoment B raw41745step3 raw41745step3Labels := by
      have ha : raw41745step3 = raw41745step2 := by apply Matrix.ext; unfold raw41745step3 raw41745step2; decide +kernel
      have hl : raw41745step2Labels = labelEmbedding6 ∘ raw41745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41745step2 raw41745step2Labels raw41745step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4700 node4700Labels := by rfl

theorem canonical41746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41746 raw41746Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw41746 raw41746Labels = mixedMoment B raw41746step0 raw41746step0Labels := by
      have ha : raw41746step0 = (fun i j => raw41746 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41746step0 raw41746; decide +kernel
      have hl : raw41746step0Labels = raw41746Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41746 raw41746Labels permutation206 permutation2
    mixedMoment B raw41746step0 raw41746step0Labels = mixedMoment B raw41746step1 raw41746step1Labels := by
      have ha : raw41746step1 = raw41746step0 := by apply Matrix.ext; unfold raw41746step1 raw41746step0; decide +kernel
      have hl : raw41746step0Labels = labelEmbedding1 ∘ raw41746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41746step0 raw41746step0Labels raw41746step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical41747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41747 raw41747Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw41747 raw41747Labels = mixedMoment B raw41747step0 raw41747step0Labels := by
      have ha : raw41747step0 = (fun i j => raw41747 (permutation221 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41747step0 raw41747; decide +kernel
      have hl : raw41747step0Labels = raw41747Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41747 raw41747Labels permutation221 permutation7
    mixedMoment B raw41747step0 raw41747step0Labels = mixedMoment B raw41747step1 raw41747step1Labels := by
      have ha : raw41747step1 = -raw41747step0 := by apply Matrix.ext; change ∀ i j, raw41747step1 i j = -(raw41747step0 i j); unfold raw41747step1 raw41747step0; decide +kernel
      have hl : raw41747step1Labels = raw41747step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41747step1 raw41747step1Labels = mixedMoment B raw41747step2 raw41747step2Labels := by
      have ha : raw41747step2 = raw41747step1 := by apply Matrix.ext; unfold raw41747step2 raw41747step1; decide +kernel
      have hl : raw41747step1Labels = labelEmbedding6 ∘ raw41747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41747step1 raw41747step1Labels raw41747step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

theorem canonical41748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41748 raw41748Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw41748 raw41748Labels = mixedMoment B raw41748step0 raw41748step0Labels := by
      have ha : raw41748step0 = (fun i j => raw41748 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41748step0 raw41748; decide +kernel
      have hl : raw41748step0Labels = raw41748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41748 raw41748Labels permutation206 permutation2
    mixedMoment B raw41748step0 raw41748step0Labels = mixedMoment B raw41748step1 raw41748step1Labels := by
      have ha : raw41748step1 = raw41748step0 := by apply Matrix.ext; unfold raw41748step1 raw41748step0; decide +kernel
      have hl : raw41748step0Labels = labelEmbedding1 ∘ raw41748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41748step0 raw41748step0Labels raw41748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical41749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41749 raw41749Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw41749 raw41749Labels = mixedMoment B raw41749step0 raw41749step0Labels := by
      have ha : raw41749step0 = (fun i j => raw41749 (permutation215 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41749step0 raw41749; decide +kernel
      have hl : raw41749step0Labels = raw41749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41749 raw41749Labels permutation215 permutation7
    mixedMoment B raw41749step0 raw41749step0Labels = mixedMoment B raw41749step1 raw41749step1Labels := by
      have ha : raw41749step1 = -raw41749step0 := by apply Matrix.ext; change ∀ i j, raw41749step1 i j = -(raw41749step0 i j); unfold raw41749step1 raw41749step0; decide +kernel
      have hl : raw41749step1Labels = raw41749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41749step1 raw41749step1Labels = mixedMoment B raw41749step2 raw41749step2Labels := by
      have ha : raw41749step2 = raw41749step1 := by apply Matrix.ext; unfold raw41749step2 raw41749step1; decide +kernel
      have hl : raw41749step1Labels = labelEmbedding6 ∘ raw41749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41749step1 raw41749step1Labels raw41749step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

theorem canonical41750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41750 raw41750Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw41750 raw41750Labels = mixedMoment B raw41750step0 raw41750step0Labels := by
      have ha : raw41750step0 = (fun i j => raw41750 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41750step0 raw41750; decide +kernel
      have hl : raw41750step0Labels = raw41750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41750 raw41750Labels permutation206 permutation2
    mixedMoment B raw41750step0 raw41750step0Labels = mixedMoment B raw41750step1 raw41750step1Labels := by
      have ha : raw41750step1 = raw41750step0 := by apply Matrix.ext; unfold raw41750step1 raw41750step0; decide +kernel
      have hl : raw41750step0Labels = labelEmbedding1 ∘ raw41750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41750step0 raw41750step0Labels raw41750step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

theorem canonical41751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41751 raw41751Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw41751 raw41751Labels = mixedMoment B raw41751step0 raw41751step0Labels := by
      have ha : raw41751step0 = (fun i j => raw41751 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41751step0 raw41751; decide +kernel
      have hl : raw41751step0Labels = raw41751Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41751 raw41751Labels permutation214 permutation7
    mixedMoment B raw41751step0 raw41751step0Labels = mixedMoment B raw41751step1 raw41751step1Labels := by
      have ha : raw41751step1 = -raw41751step0 := by apply Matrix.ext; change ∀ i j, raw41751step1 i j = -(raw41751step0 i j); unfold raw41751step1 raw41751step0; decide +kernel
      have hl : raw41751step1Labels = raw41751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41751step1 raw41751step1Labels = mixedMoment B raw41751step2 raw41751step2Labels := by
      have ha : raw41751step2 = raw41751step1 := by apply Matrix.ext; unfold raw41751step2 raw41751step1; decide +kernel
      have hl : raw41751step1Labels = labelEmbedding6 ∘ raw41751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41751step1 raw41751step1Labels raw41751step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4773 node4773Labels := by rfl

theorem canonical41752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41752 raw41752Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw41752 raw41752Labels = mixedMoment B raw41752step0 raw41752step0Labels := by
      have ha : raw41752step0 = (fun i j => raw41752 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41752step0 raw41752; decide +kernel
      have hl : raw41752step0Labels = raw41752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41752 raw41752Labels permutation206 permutation2
    mixedMoment B raw41752step0 raw41752step0Labels = mixedMoment B raw41752step1 raw41752step1Labels := by
      have ha : raw41752step1 = raw41752step0 := by apply Matrix.ext; unfold raw41752step1 raw41752step0; decide +kernel
      have hl : raw41752step0Labels = labelEmbedding1 ∘ raw41752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41752step0 raw41752step0Labels raw41752step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical41753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41753 raw41753Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw41753 raw41753Labels = mixedMoment B raw41753step0 raw41753step0Labels := by
      have ha : raw41753step0 = (fun i j => raw41753 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41753step0 raw41753; decide +kernel
      have hl : raw41753step0Labels = raw41753Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41753 raw41753Labels permutation214 permutation7
    mixedMoment B raw41753step0 raw41753step0Labels = mixedMoment B raw41753step1 raw41753step1Labels := by
      have ha : raw41753step1 = -raw41753step0 := by apply Matrix.ext; change ∀ i j, raw41753step1 i j = -(raw41753step0 i j); unfold raw41753step1 raw41753step0; decide +kernel
      have hl : raw41753step1Labels = raw41753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41753step1 raw41753step1Labels = mixedMoment B raw41753step2 raw41753step2Labels := by
      have ha : raw41753step2 = raw41753step1 := by apply Matrix.ext; unfold raw41753step2 raw41753step1; decide +kernel
      have hl : raw41753step1Labels = labelEmbedding6 ∘ raw41753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41753step1 raw41753step1Labels raw41753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4665 node4665Labels := by rfl

theorem canonical41754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41754 raw41754Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw41754 raw41754Labels = mixedMoment B raw41754step0 raw41754step0Labels := by
      have ha : raw41754step0 = (fun i j => raw41754 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41754step0 raw41754; decide +kernel
      have hl : raw41754step0Labels = raw41754Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41754 raw41754Labels permutation180 permutation2
    mixedMoment B raw41754step0 raw41754step0Labels = mixedMoment B raw41754step1 raw41754step1Labels := by
      have ha : raw41754step1 = raw41754step0 := by apply Matrix.ext; unfold raw41754step1 raw41754step0; decide +kernel
      have hl : raw41754step0Labels = labelEmbedding1 ∘ raw41754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41754step0 raw41754step0Labels raw41754step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

theorem canonical41755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41755 raw41755Labels = mixedMoment B node4698 node4698Labels := by
  calc
    mixedMoment B raw41755 raw41755Labels = mixedMoment B raw41755step0 raw41755step0Labels := by
      have ha : raw41755step0 = (fun i j => raw41755 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41755step0 raw41755; decide +kernel
      have hl : raw41755step0Labels = raw41755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41755 raw41755Labels permutation255 permutation7
    mixedMoment B raw41755step0 raw41755step0Labels = mixedMoment B raw41755step1 raw41755step1Labels := by
      have ha : raw41755step1 = -raw41755step0 := by apply Matrix.ext; change ∀ i j, raw41755step1 i j = -(raw41755step0 i j); unfold raw41755step1 raw41755step0; decide +kernel
      have hl : raw41755step1Labels = raw41755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41755step1 raw41755step1Labels = mixedMoment B raw41755step2 raw41755step2Labels := by
      have ha : raw41755step2 = raw41755step1 := by apply Matrix.ext; unfold raw41755step2 raw41755step1; decide +kernel
      have hl : raw41755step1Labels = labelEmbedding6 ∘ raw41755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41755step1 raw41755step1Labels raw41755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4698 node4698Labels := by rfl

theorem canonical41756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41756 raw41756Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw41756 raw41756Labels = mixedMoment B raw41756step0 raw41756step0Labels := by
      have ha : raw41756step0 = (fun i j => raw41756 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41756step0 raw41756; decide +kernel
      have hl : raw41756step0Labels = raw41756Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41756 raw41756Labels permutation181 permutation2
    mixedMoment B raw41756step0 raw41756step0Labels = mixedMoment B raw41756step1 raw41756step1Labels := by
      have ha : raw41756step1 = raw41756step0 := by apply Matrix.ext; unfold raw41756step1 raw41756step0; decide +kernel
      have hl : raw41756step0Labels = labelEmbedding1 ∘ raw41756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41756step0 raw41756step0Labels raw41756step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical41757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41757 raw41757Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw41757 raw41757Labels = mixedMoment B raw41757step0 raw41757step0Labels := by
      have ha : raw41757step0 = (fun i j => raw41757 (permutation263 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41757step0 raw41757; decide +kernel
      have hl : raw41757step0Labels = raw41757Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41757 raw41757Labels permutation263 permutation7
    mixedMoment B raw41757step0 raw41757step0Labels = mixedMoment B raw41757step1 raw41757step1Labels := by
      have ha : raw41757step1 = -raw41757step0 := by apply Matrix.ext; change ∀ i j, raw41757step1 i j = -(raw41757step0 i j); unfold raw41757step1 raw41757step0; decide +kernel
      have hl : raw41757step1Labels = raw41757step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41757step1 raw41757step1Labels = mixedMoment B raw41757step2 raw41757step2Labels := by
      have ha : raw41757step2 = raw41757step1 := by apply Matrix.ext; unfold raw41757step2 raw41757step1; decide +kernel
      have hl : raw41757step1Labels = labelEmbedding6 ∘ raw41757step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41757step1 raw41757step1Labels raw41757step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical41758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41758 raw41758Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw41758 raw41758Labels = mixedMoment B raw41758step0 raw41758step0Labels := by
      have ha : raw41758step0 = (fun i j => raw41758 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41758step0 raw41758; decide +kernel
      have hl : raw41758step0Labels = raw41758Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41758 raw41758Labels permutation176 permutation2
    mixedMoment B raw41758step0 raw41758step0Labels = mixedMoment B raw41758step1 raw41758step1Labels := by
      have ha : raw41758step1 = raw41758step0 := by apply Matrix.ext; unfold raw41758step1 raw41758step0; decide +kernel
      have hl : raw41758step0Labels = labelEmbedding1 ∘ raw41758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41758step0 raw41758step0Labels raw41758step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical41759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41759 raw41759Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw41759 raw41759Labels = mixedMoment B raw41759step0 raw41759step0Labels := by
      have ha : raw41759step0 = (fun i j => raw41759 (permutation217 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41759step0 raw41759; decide +kernel
      have hl : raw41759step0Labels = raw41759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41759 raw41759Labels permutation217 permutation7
    mixedMoment B raw41759step0 raw41759step0Labels = mixedMoment B raw41759step1 raw41759step1Labels := by
      have ha : raw41759step1 = -raw41759step0 := by apply Matrix.ext; change ∀ i j, raw41759step1 i j = -(raw41759step0 i j); unfold raw41759step1 raw41759step0; decide +kernel
      have hl : raw41759step1Labels = raw41759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41759step1 raw41759step1Labels = mixedMoment B raw41759step2 raw41759step2Labels := by
      have ha : raw41759step2 = raw41759step1 := by apply Matrix.ext; unfold raw41759step2 raw41759step1; decide +kernel
      have hl : raw41759step1Labels = labelEmbedding6 ∘ raw41759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41759step1 raw41759step1Labels raw41759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical41760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41760 raw41760Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw41760 raw41760Labels = mixedMoment B raw41760step0 raw41760step0Labels := by
      have hz : ∀ j, raw41760 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41760step0 = (fun i j => raw41760 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41760step0 raw41760; decide +kernel
      have hl : raw41760step0Labels = raw41760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41760 raw41760Labels permutation434 hz
    mixedMoment B raw41760step0 raw41760step0Labels = mixedMoment B raw41760step1 raw41760step1Labels := by
      have hz : ∀ j, raw41760step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41760step1 = (fun i j => raw41760step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41760step1 raw41760step0; decide +kernel
      have hl : raw41760step1Labels = raw41760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41760step0 raw41760step0Labels permutation80 hz
    mixedMoment B raw41760step1 raw41760step1Labels = mixedMoment B raw41760step2 raw41760step2Labels := by
      have ha : raw41760step2 = raw41760step1 := by apply Matrix.ext; unfold raw41760step2 raw41760step1; decide +kernel
      have hl : raw41760step1Labels = labelEmbedding1 ∘ raw41760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41760step1 raw41760step1Labels raw41760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2280 node2280Labels := by rfl

theorem canonical41761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41761 raw41761Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw41761 raw41761Labels = mixedMoment B raw41761step0 raw41761step0Labels := by
      have hz : ∀ j, raw41761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41761step0 = (fun i j => raw41761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41761step0 raw41761; decide +kernel
      have hl : raw41761step0Labels = raw41761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41761 raw41761Labels permutation434 hz
    mixedMoment B raw41761step0 raw41761step0Labels = mixedMoment B raw41761step1 raw41761step1Labels := by
      have hz : ∀ j, raw41761step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41761step1 = (fun i j => raw41761step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41761step1 raw41761step0; decide +kernel
      have hl : raw41761step1Labels = raw41761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41761step0 raw41761step0Labels permutation80 hz
    mixedMoment B raw41761step1 raw41761step1Labels = mixedMoment B raw41761step2 raw41761step2Labels := by
      have ha : raw41761step2 = (fun i j => raw41761step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41761step2 raw41761step1; decide +kernel
      have hl : raw41761step2Labels = raw41761step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41761step1 raw41761step1Labels permutation12 permutation7
    mixedMoment B raw41761step2 raw41761step2Labels = mixedMoment B raw41761step3 raw41761step3Labels := by
      have ha : raw41761step3 = -raw41761step2 := by apply Matrix.ext; change ∀ i j, raw41761step3 i j = -(raw41761step2 i j); unfold raw41761step3 raw41761step2; decide +kernel
      have hl : raw41761step3Labels = raw41761step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41761step3 raw41761step3Labels = mixedMoment B raw41761step4 raw41761step4Labels := by
      have ha : raw41761step4 = raw41761step3 := by apply Matrix.ext; unfold raw41761step4 raw41761step3; decide +kernel
      have hl : raw41761step3Labels = labelEmbedding6 ∘ raw41761step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41761step3 raw41761step3Labels raw41761step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

theorem canonical41762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41762 raw41762Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw41762 raw41762Labels = mixedMoment B raw41762step0 raw41762step0Labels := by
      have hz : ∀ j, raw41762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41762step0 = (fun i j => raw41762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41762step0 raw41762; decide +kernel
      have hl : raw41762step0Labels = raw41762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41762 raw41762Labels permutation434 hz
    mixedMoment B raw41762step0 raw41762step0Labels = mixedMoment B raw41762step1 raw41762step1Labels := by
      have hz : ∀ j, raw41762step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41762step1 = (fun i j => raw41762step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41762step1 raw41762step0; decide +kernel
      have hl : raw41762step1Labels = raw41762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41762step0 raw41762step0Labels permutation80 hz
    mixedMoment B raw41762step1 raw41762step1Labels = mixedMoment B raw41762step2 raw41762step2Labels := by
      have ha : raw41762step2 = raw41762step1 := by apply Matrix.ext; unfold raw41762step2 raw41762step1; decide +kernel
      have hl : raw41762step1Labels = labelEmbedding1 ∘ raw41762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41762step1 raw41762step1Labels raw41762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

theorem canonical41763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41763 raw41763Labels = mixedMoment B node4704 node4704Labels := by
  calc
    mixedMoment B raw41763 raw41763Labels = mixedMoment B raw41763step0 raw41763step0Labels := by
      have hz : ∀ j, raw41763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41763step0 = (fun i j => raw41763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41763step0 raw41763; decide +kernel
      have hl : raw41763step0Labels = raw41763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41763 raw41763Labels permutation434 hz
    mixedMoment B raw41763step0 raw41763step0Labels = mixedMoment B raw41763step1 raw41763step1Labels := by
      have hz : ∀ j, raw41763step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41763step1 = (fun i j => raw41763step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41763step1 raw41763step0; decide +kernel
      have hl : raw41763step1Labels = raw41763step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41763step0 raw41763step0Labels permutation80 hz
    mixedMoment B raw41763step1 raw41763step1Labels = mixedMoment B raw41763step2 raw41763step2Labels := by
      have ha : raw41763step2 = (fun i j => raw41763step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41763step2 raw41763step1; decide +kernel
      have hl : raw41763step2Labels = raw41763step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41763step1 raw41763step1Labels permutation10 permutation7
    mixedMoment B raw41763step2 raw41763step2Labels = mixedMoment B raw41763step3 raw41763step3Labels := by
      have ha : raw41763step3 = -raw41763step2 := by apply Matrix.ext; change ∀ i j, raw41763step3 i j = -(raw41763step2 i j); unfold raw41763step3 raw41763step2; decide +kernel
      have hl : raw41763step3Labels = raw41763step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41763step3 raw41763step3Labels = mixedMoment B raw41763step4 raw41763step4Labels := by
      have ha : raw41763step4 = raw41763step3 := by apply Matrix.ext; unfold raw41763step4 raw41763step3; decide +kernel
      have hl : raw41763step3Labels = labelEmbedding6 ∘ raw41763step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41763step3 raw41763step3Labels raw41763step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4704 node4704Labels := by rfl

theorem canonical41764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41764 raw41764Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw41764 raw41764Labels = mixedMoment B raw41764step0 raw41764step0Labels := by
      have hz : ∀ j, raw41764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41764step0 = (fun i j => raw41764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41764step0 raw41764; decide +kernel
      have hl : raw41764step0Labels = raw41764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41764 raw41764Labels permutation346 hz
    mixedMoment B raw41764step0 raw41764step0Labels = mixedMoment B raw41764step1 raw41764step1Labels := by
      have ha : raw41764step1 = (fun i j => raw41764step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41764step1 raw41764step0; decide +kernel
      have hl : raw41764step1Labels = raw41764step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41764step0 raw41764step0Labels permutation38 permutation2
    mixedMoment B raw41764step1 raw41764step1Labels = mixedMoment B raw41764step2 raw41764step2Labels := by
      have ha : raw41764step2 = raw41764step1 := by apply Matrix.ext; unfold raw41764step2 raw41764step1; decide +kernel
      have hl : raw41764step1Labels = labelEmbedding1 ∘ raw41764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41764step1 raw41764step1Labels raw41764step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical41765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41765 raw41765Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw41765 raw41765Labels = mixedMoment B raw41765step0 raw41765step0Labels := by
      have hz : ∀ j, raw41765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41765step0 = (fun i j => raw41765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41765step0 raw41765; decide +kernel
      have hl : raw41765step0Labels = raw41765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41765 raw41765Labels permutation346 hz
    mixedMoment B raw41765step0 raw41765step0Labels = mixedMoment B raw41765step1 raw41765step1Labels := by
      have ha : raw41765step1 = (fun i j => raw41765step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41765step1 raw41765step0; decide +kernel
      have hl : raw41765step1Labels = raw41765step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41765step0 raw41765step0Labels permutation42 permutation7
    mixedMoment B raw41765step1 raw41765step1Labels = mixedMoment B raw41765step2 raw41765step2Labels := by
      have ha : raw41765step2 = -raw41765step1 := by apply Matrix.ext; change ∀ i j, raw41765step2 i j = -(raw41765step1 i j); unfold raw41765step2 raw41765step1; decide +kernel
      have hl : raw41765step2Labels = raw41765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41765step2 raw41765step2Labels = mixedMoment B raw41765step3 raw41765step3Labels := by
      have ha : raw41765step3 = raw41765step2 := by apply Matrix.ext; unfold raw41765step3 raw41765step2; decide +kernel
      have hl : raw41765step2Labels = labelEmbedding6 ∘ raw41765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41765step2 raw41765step2Labels raw41765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

theorem canonical41766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41766 raw41766Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw41766 raw41766Labels = mixedMoment B raw41766step0 raw41766step0Labels := by
      have hz : ∀ j, raw41766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41766step0 = (fun i j => raw41766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41766step0 raw41766; decide +kernel
      have hl : raw41766step0Labels = raw41766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41766 raw41766Labels permutation346 hz
    mixedMoment B raw41766step0 raw41766step0Labels = mixedMoment B raw41766step1 raw41766step1Labels := by
      have ha : raw41766step1 = (fun i j => raw41766step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41766step1 raw41766step0; decide +kernel
      have hl : raw41766step1Labels = raw41766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41766step0 raw41766step0Labels permutation38 permutation2
    mixedMoment B raw41766step1 raw41766step1Labels = mixedMoment B raw41766step2 raw41766step2Labels := by
      have ha : raw41766step2 = raw41766step1 := by apply Matrix.ext; unfold raw41766step2 raw41766step1; decide +kernel
      have hl : raw41766step1Labels = labelEmbedding1 ∘ raw41766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41766step1 raw41766step1Labels raw41766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

theorem canonical41767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41767 raw41767Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw41767 raw41767Labels = mixedMoment B raw41767step0 raw41767step0Labels := by
      have hz : ∀ j, raw41767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41767step0 = (fun i j => raw41767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41767step0 raw41767; decide +kernel
      have hl : raw41767step0Labels = raw41767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41767 raw41767Labels permutation346 hz
    mixedMoment B raw41767step0 raw41767step0Labels = mixedMoment B raw41767step1 raw41767step1Labels := by
      have ha : raw41767step1 = (fun i j => raw41767step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41767step1 raw41767step0; decide +kernel
      have hl : raw41767step1Labels = raw41767step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41767step0 raw41767step0Labels permutation40 permutation7
    mixedMoment B raw41767step1 raw41767step1Labels = mixedMoment B raw41767step2 raw41767step2Labels := by
      have ha : raw41767step2 = -raw41767step1 := by apply Matrix.ext; change ∀ i j, raw41767step2 i j = -(raw41767step1 i j); unfold raw41767step2 raw41767step1; decide +kernel
      have hl : raw41767step2Labels = raw41767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41767step2 raw41767step2Labels = mixedMoment B raw41767step3 raw41767step3Labels := by
      have ha : raw41767step3 = raw41767step2 := by apply Matrix.ext; unfold raw41767step3 raw41767step2; decide +kernel
      have hl : raw41767step2Labels = labelEmbedding6 ∘ raw41767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41767step2 raw41767step2Labels raw41767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4776 node4776Labels := by rfl

theorem canonical41768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41768 raw41768Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw41768 raw41768Labels = mixedMoment B raw41768step0 raw41768step0Labels := by
      have hz : ∀ j, raw41768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41768step0 = (fun i j => raw41768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41768step0 raw41768; decide +kernel
      have hl : raw41768step0Labels = raw41768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41768 raw41768Labels permutation346 hz
    mixedMoment B raw41768step0 raw41768step0Labels = mixedMoment B raw41768step1 raw41768step1Labels := by
      have ha : raw41768step1 = (fun i j => raw41768step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41768step1 raw41768step0; decide +kernel
      have hl : raw41768step1Labels = raw41768step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41768step0 raw41768step0Labels permutation38 permutation2
    mixedMoment B raw41768step1 raw41768step1Labels = mixedMoment B raw41768step2 raw41768step2Labels := by
      have ha : raw41768step2 = raw41768step1 := by apply Matrix.ext; unfold raw41768step2 raw41768step1; decide +kernel
      have hl : raw41768step1Labels = labelEmbedding1 ∘ raw41768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41768step1 raw41768step1Labels raw41768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

theorem canonical41769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41769 raw41769Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw41769 raw41769Labels = mixedMoment B raw41769step0 raw41769step0Labels := by
      have hz : ∀ j, raw41769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41769step0 = (fun i j => raw41769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41769step0 raw41769; decide +kernel
      have hl : raw41769step0Labels = raw41769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41769 raw41769Labels permutation346 hz
    mixedMoment B raw41769step0 raw41769step0Labels = mixedMoment B raw41769step1 raw41769step1Labels := by
      have ha : raw41769step1 = (fun i j => raw41769step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41769step1 raw41769step0; decide +kernel
      have hl : raw41769step1Labels = raw41769step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41769step0 raw41769step0Labels permutation40 permutation7
    mixedMoment B raw41769step1 raw41769step1Labels = mixedMoment B raw41769step2 raw41769step2Labels := by
      have ha : raw41769step2 = -raw41769step1 := by apply Matrix.ext; change ∀ i j, raw41769step2 i j = -(raw41769step1 i j); unfold raw41769step2 raw41769step1; decide +kernel
      have hl : raw41769step2Labels = raw41769step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41769step2 raw41769step2Labels = mixedMoment B raw41769step3 raw41769step3Labels := by
      have ha : raw41769step3 = raw41769step2 := by apply Matrix.ext; unfold raw41769step3 raw41769step2; decide +kernel
      have hl : raw41769step2Labels = labelEmbedding6 ∘ raw41769step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41769step2 raw41769step2Labels raw41769step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4669 node4669Labels := by rfl

theorem canonical41770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41770 raw41770Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw41770 raw41770Labels = mixedMoment B raw41770step0 raw41770step0Labels := by
      have hz : ∀ j, raw41770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41770step0 = (fun i j => raw41770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41770step0 raw41770; decide +kernel
      have hl : raw41770step0Labels = raw41770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41770 raw41770Labels permutation346 hz
    mixedMoment B raw41770step0 raw41770step0Labels = mixedMoment B raw41770step1 raw41770step1Labels := by
      have ha : raw41770step1 = (fun i j => raw41770step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41770step1 raw41770step0; decide +kernel
      have hl : raw41770step1Labels = raw41770step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41770step0 raw41770step0Labels permutation37 permutation2
    mixedMoment B raw41770step1 raw41770step1Labels = mixedMoment B raw41770step2 raw41770step2Labels := by
      have ha : raw41770step2 = raw41770step1 := by apply Matrix.ext; unfold raw41770step2 raw41770step1; decide +kernel
      have hl : raw41770step1Labels = labelEmbedding1 ∘ raw41770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41770step1 raw41770step1Labels raw41770step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

theorem canonical41771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41771 raw41771Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw41771 raw41771Labels = mixedMoment B raw41771step0 raw41771step0Labels := by
      have hz : ∀ j, raw41771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41771step0 = (fun i j => raw41771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41771step0 raw41771; decide +kernel
      have hl : raw41771step0Labels = raw41771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41771 raw41771Labels permutation346 hz
    mixedMoment B raw41771step0 raw41771step0Labels = mixedMoment B raw41771step1 raw41771step1Labels := by
      have ha : raw41771step1 = (fun i j => raw41771step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41771step1 raw41771step0; decide +kernel
      have hl : raw41771step1Labels = raw41771step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41771step0 raw41771step0Labels permutation54 permutation7
    mixedMoment B raw41771step1 raw41771step1Labels = mixedMoment B raw41771step2 raw41771step2Labels := by
      have ha : raw41771step2 = -raw41771step1 := by apply Matrix.ext; change ∀ i j, raw41771step2 i j = -(raw41771step1 i j); unfold raw41771step2 raw41771step1; decide +kernel
      have hl : raw41771step2Labels = raw41771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41771step2 raw41771step2Labels = mixedMoment B raw41771step3 raw41771step3Labels := by
      have ha : raw41771step3 = raw41771step2 := by apply Matrix.ext; unfold raw41771step3 raw41771step2; decide +kernel
      have hl : raw41771step2Labels = labelEmbedding6 ∘ raw41771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41771step2 raw41771step2Labels raw41771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4703 node4703Labels := by rfl

theorem canonical41772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41772 raw41772Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw41772 raw41772Labels = mixedMoment B raw41772step0 raw41772step0Labels := by
      have hz : ∀ j, raw41772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41772step0 = (fun i j => raw41772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41772step0 raw41772; decide +kernel
      have hl : raw41772step0Labels = raw41772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41772 raw41772Labels permutation346 hz
    mixedMoment B raw41772step0 raw41772step0Labels = mixedMoment B raw41772step1 raw41772step1Labels := by
      have ha : raw41772step1 = (fun i j => raw41772step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41772step1 raw41772step0; decide +kernel
      have hl : raw41772step1Labels = raw41772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41772step0 raw41772step0Labels permutation37 permutation2
    mixedMoment B raw41772step1 raw41772step1Labels = mixedMoment B raw41772step2 raw41772step2Labels := by
      have ha : raw41772step2 = raw41772step1 := by apply Matrix.ext; unfold raw41772step2 raw41772step1; decide +kernel
      have hl : raw41772step1Labels = labelEmbedding1 ∘ raw41772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41772step1 raw41772step1Labels raw41772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical41773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41773 raw41773Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw41773 raw41773Labels = mixedMoment B raw41773step0 raw41773step0Labels := by
      have hz : ∀ j, raw41773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41773step0 = (fun i j => raw41773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41773step0 raw41773; decide +kernel
      have hl : raw41773step0Labels = raw41773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41773 raw41773Labels permutation346 hz
    mixedMoment B raw41773step0 raw41773step0Labels = mixedMoment B raw41773step1 raw41773step1Labels := by
      have ha : raw41773step1 = (fun i j => raw41773step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41773step1 raw41773step0; decide +kernel
      have hl : raw41773step1Labels = raw41773step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41773step0 raw41773step0Labels permutation54 permutation7
    mixedMoment B raw41773step1 raw41773step1Labels = mixedMoment B raw41773step2 raw41773step2Labels := by
      have ha : raw41773step2 = -raw41773step1 := by apply Matrix.ext; change ∀ i j, raw41773step2 i j = -(raw41773step1 i j); unfold raw41773step2 raw41773step1; decide +kernel
      have hl : raw41773step2Labels = raw41773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41773step2 raw41773step2Labels = mixedMoment B raw41773step3 raw41773step3Labels := by
      have ha : raw41773step3 = raw41773step2 := by apply Matrix.ext; unfold raw41773step3 raw41773step2; decide +kernel
      have hl : raw41773step2Labels = labelEmbedding6 ∘ raw41773step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41773step2 raw41773step2Labels raw41773step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

theorem canonical41774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41774 raw41774Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw41774 raw41774Labels = mixedMoment B raw41774step0 raw41774step0Labels := by
      have ha : raw41774step0 = (fun i j => raw41774 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41774step0 raw41774; decide +kernel
      have hl : raw41774step0Labels = raw41774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41774 raw41774Labels permutation182 permutation2
    mixedMoment B raw41774step0 raw41774step0Labels = mixedMoment B raw41774step1 raw41774step1Labels := by
      have ha : raw41774step1 = raw41774step0 := by apply Matrix.ext; unfold raw41774step1 raw41774step0; decide +kernel
      have hl : raw41774step0Labels = labelEmbedding1 ∘ raw41774step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41774step0 raw41774step0Labels raw41774step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

theorem canonical41775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41775 raw41775Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw41775 raw41775Labels = mixedMoment B raw41775step0 raw41775step0Labels := by
      have ha : raw41775step0 = (fun i j => raw41775 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41775step0 raw41775; decide +kernel
      have hl : raw41775step0Labels = raw41775Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41775 raw41775Labels permutation184 permutation7
    mixedMoment B raw41775step0 raw41775step0Labels = mixedMoment B raw41775step1 raw41775step1Labels := by
      have ha : raw41775step1 = -raw41775step0 := by apply Matrix.ext; change ∀ i j, raw41775step1 i j = -(raw41775step0 i j); unfold raw41775step1 raw41775step0; decide +kernel
      have hl : raw41775step1Labels = raw41775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41775step1 raw41775step1Labels = mixedMoment B raw41775step2 raw41775step2Labels := by
      have ha : raw41775step2 = raw41775step1 := by apply Matrix.ext; unfold raw41775step2 raw41775step1; decide +kernel
      have hl : raw41775step1Labels = labelEmbedding6 ∘ raw41775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41775step1 raw41775step1Labels raw41775step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4756 node4756Labels := by rfl

theorem canonical41776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41776 raw41776Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw41776 raw41776Labels = mixedMoment B raw41776step0 raw41776step0Labels := by
      have ha : raw41776step0 = (fun i j => raw41776 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41776step0 raw41776; decide +kernel
      have hl : raw41776step0Labels = raw41776Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41776 raw41776Labels permutation181 permutation2
    mixedMoment B raw41776step0 raw41776step0Labels = mixedMoment B raw41776step1 raw41776step1Labels := by
      have ha : raw41776step1 = raw41776step0 := by apply Matrix.ext; unfold raw41776step1 raw41776step0; decide +kernel
      have hl : raw41776step0Labels = labelEmbedding1 ∘ raw41776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41776step0 raw41776step0Labels raw41776step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

theorem canonical41777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41777 raw41777Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw41777 raw41777Labels = mixedMoment B raw41777step0 raw41777step0Labels := by
      have ha : raw41777step0 = (fun i j => raw41777 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41777step0 raw41777; decide +kernel
      have hl : raw41777step0Labels = raw41777Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41777 raw41777Labels permutation198 permutation7
    mixedMoment B raw41777step0 raw41777step0Labels = mixedMoment B raw41777step1 raw41777step1Labels := by
      have ha : raw41777step1 = -raw41777step0 := by apply Matrix.ext; change ∀ i j, raw41777step1 i j = -(raw41777step0 i j); unfold raw41777step1 raw41777step0; decide +kernel
      have hl : raw41777step1Labels = raw41777step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41777step1 raw41777step1Labels = mixedMoment B raw41777step2 raw41777step2Labels := by
      have ha : raw41777step2 = raw41777step1 := by apply Matrix.ext; unfold raw41777step2 raw41777step1; decide +kernel
      have hl : raw41777step1Labels = labelEmbedding6 ∘ raw41777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41777step1 raw41777step1Labels raw41777step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4775 node4775Labels := by rfl

theorem canonical41778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41778 raw41778Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw41778 raw41778Labels = mixedMoment B raw41778step0 raw41778step0Labels := by
      have ha : raw41778step0 = (fun i j => raw41778 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41778step0 raw41778; decide +kernel
      have hl : raw41778step0Labels = raw41778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41778 raw41778Labels permutation179 permutation2
    mixedMoment B raw41778step0 raw41778step0Labels = mixedMoment B raw41778step1 raw41778step1Labels := by
      have ha : raw41778step1 = raw41778step0 := by apply Matrix.ext; unfold raw41778step1 raw41778step0; decide +kernel
      have hl : raw41778step0Labels = labelEmbedding1 ∘ raw41778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41778step0 raw41778step0Labels raw41778step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical41779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41779 raw41779Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw41779 raw41779Labels = mixedMoment B raw41779step0 raw41779step0Labels := by
      have ha : raw41779step0 = (fun i j => raw41779 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41779step0 raw41779; decide +kernel
      have hl : raw41779step0Labels = raw41779Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41779 raw41779Labels permutation192 permutation7
    mixedMoment B raw41779step0 raw41779step0Labels = mixedMoment B raw41779step1 raw41779step1Labels := by
      have ha : raw41779step1 = -raw41779step0 := by apply Matrix.ext; change ∀ i j, raw41779step1 i j = -(raw41779step0 i j); unfold raw41779step1 raw41779step0; decide +kernel
      have hl : raw41779step1Labels = raw41779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41779step1 raw41779step1Labels = mixedMoment B raw41779step2 raw41779step2Labels := by
      have ha : raw41779step2 = raw41779step1 := by apply Matrix.ext; unfold raw41779step2 raw41779step1; decide +kernel
      have hl : raw41779step1Labels = labelEmbedding6 ∘ raw41779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41779step1 raw41779step1Labels raw41779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical41780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41780 raw41780Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw41780 raw41780Labels = mixedMoment B raw41780step0 raw41780step0Labels := by
      have ha : raw41780step0 = (fun i j => raw41780 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41780step0 raw41780; decide +kernel
      have hl : raw41780step0Labels = raw41780Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41780 raw41780Labels permutation181 permutation2
    mixedMoment B raw41780step0 raw41780step0Labels = mixedMoment B raw41780step1 raw41780step1Labels := by
      have ha : raw41780step1 = raw41780step0 := by apply Matrix.ext; unfold raw41780step1 raw41780step0; decide +kernel
      have hl : raw41780step0Labels = labelEmbedding1 ∘ raw41780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41780step0 raw41780step0Labels raw41780step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical41781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41781 raw41781Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw41781 raw41781Labels = mixedMoment B raw41781step0 raw41781step0Labels := by
      have ha : raw41781step0 = (fun i j => raw41781 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41781step0 raw41781; decide +kernel
      have hl : raw41781step0Labels = raw41781Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41781 raw41781Labels permutation198 permutation7
    mixedMoment B raw41781step0 raw41781step0Labels = mixedMoment B raw41781step1 raw41781step1Labels := by
      have ha : raw41781step1 = -raw41781step0 := by apply Matrix.ext; change ∀ i j, raw41781step1 i j = -(raw41781step0 i j); unfold raw41781step1 raw41781step0; decide +kernel
      have hl : raw41781step1Labels = raw41781step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41781step1 raw41781step1Labels = mixedMoment B raw41781step2 raw41781step2Labels := by
      have ha : raw41781step2 = raw41781step1 := by apply Matrix.ext; unfold raw41781step2 raw41781step1; decide +kernel
      have hl : raw41781step1Labels = labelEmbedding6 ∘ raw41781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41781step1 raw41781step1Labels raw41781step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4668 node4668Labels := by rfl

theorem canonical41782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41782 raw41782Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw41782 raw41782Labels = mixedMoment B raw41782step0 raw41782step0Labels := by
      have hz : ∀ j, raw41782 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41782step0 = (fun i j => raw41782 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41782step0 raw41782; decide +kernel
      have hl : raw41782step0Labels = raw41782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41782 raw41782Labels permutation520 hz
    mixedMoment B raw41782step0 raw41782step0Labels = mixedMoment B raw41782step1 raw41782step1Labels := by
      have ha : raw41782step1 = raw41782step0 := by apply Matrix.ext; unfold raw41782step1 raw41782step0; decide +kernel
      have hl : raw41782step0Labels = labelEmbedding1 ∘ raw41782step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41782step0 raw41782step0Labels raw41782step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

theorem canonical41783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41783 raw41783Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw41783 raw41783Labels = mixedMoment B raw41783step0 raw41783step0Labels := by
      have hz : ∀ j, raw41783 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41783step0 = (fun i j => raw41783 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41783step0 raw41783; decide +kernel
      have hl : raw41783step0Labels = raw41783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41783 raw41783Labels permutation520 hz
    mixedMoment B raw41783step0 raw41783step0Labels = mixedMoment B raw41783step1 raw41783step1Labels := by
      have ha : raw41783step1 = raw41783step0 := by apply Matrix.ext; unfold raw41783step1 raw41783step0; decide +kernel
      have hl : raw41783step0Labels = labelEmbedding8 ∘ raw41783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41783step0 raw41783step0Labels raw41783step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

theorem canonical41784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41784 raw41784Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw41784 raw41784Labels = mixedMoment B raw41784step0 raw41784step0Labels := by
      have ha : raw41784step0 = raw41784 := by apply Matrix.ext; unfold raw41784step0 raw41784; decide +kernel
      have hl : raw41784Labels = labelEmbedding1 ∘ raw41784step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41784 raw41784Labels raw41784step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

theorem canonical41785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41785 raw41785Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw41785 raw41785Labels = mixedMoment B raw41785step0 raw41785step0Labels := by
      have ha : raw41785step0 = (fun i j => raw41785 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41785step0 raw41785; decide +kernel
      have hl : raw41785step0Labels = raw41785Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41785 raw41785Labels permutation246 permutation7
    mixedMoment B raw41785step0 raw41785step0Labels = mixedMoment B raw41785step1 raw41785step1Labels := by
      have ha : raw41785step1 = -raw41785step0 := by apply Matrix.ext; change ∀ i j, raw41785step1 i j = -(raw41785step0 i j); unfold raw41785step1 raw41785step0; decide +kernel
      have hl : raw41785step1Labels = raw41785step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41785step1 raw41785step1Labels = mixedMoment B raw41785step2 raw41785step2Labels := by
      have ha : raw41785step2 = raw41785step1 := by apply Matrix.ext; unfold raw41785step2 raw41785step1; decide +kernel
      have hl : raw41785step1Labels = labelEmbedding6 ∘ raw41785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41785step1 raw41785step1Labels raw41785step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

theorem canonical41786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41786 raw41786Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw41786 raw41786Labels = mixedMoment B raw41786step0 raw41786step0Labels := by
      have ha : raw41786step0 = raw41786 := by apply Matrix.ext; unfold raw41786step0 raw41786; decide +kernel
      have hl : raw41786Labels = labelEmbedding1 ∘ raw41786step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41786 raw41786Labels raw41786step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2233 node2233Labels := by rfl

theorem canonical41787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41787 raw41787Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw41787 raw41787Labels = mixedMoment B raw41787step0 raw41787step0Labels := by
      have ha : raw41787step0 = raw41787 := by apply Matrix.ext; unfold raw41787step0 raw41787; decide +kernel
      have hl : raw41787Labels = labelEmbedding8 ∘ raw41787step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41787 raw41787Labels raw41787step0Labels labelEmbedding8 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical41788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41788 raw41788Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw41788 raw41788Labels = mixedMoment B raw41788step0 raw41788step0Labels := by
      have ha : raw41788step0 = raw41788 := by apply Matrix.ext; unfold raw41788step0 raw41788; decide +kernel
      have hl : raw41788Labels = labelEmbedding1 ∘ raw41788step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41788 raw41788Labels raw41788step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

theorem canonical41789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41789 raw41789Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw41789 raw41789Labels = mixedMoment B raw41789step0 raw41789step0Labels := by
      have ha : raw41789step0 = (fun i j => raw41789 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41789step0 raw41789; decide +kernel
      have hl : raw41789step0Labels = raw41789Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41789 raw41789Labels permutation224 permutation7
    mixedMoment B raw41789step0 raw41789step0Labels = mixedMoment B raw41789step1 raw41789step1Labels := by
      have ha : raw41789step1 = -raw41789step0 := by apply Matrix.ext; change ∀ i j, raw41789step1 i j = -(raw41789step0 i j); unfold raw41789step1 raw41789step0; decide +kernel
      have hl : raw41789step1Labels = raw41789step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41789step1 raw41789step1Labels = mixedMoment B raw41789step2 raw41789step2Labels := by
      have ha : raw41789step2 = raw41789step1 := by apply Matrix.ext; unfold raw41789step2 raw41789step1; decide +kernel
      have hl : raw41789step1Labels = labelEmbedding6 ∘ raw41789step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41789step1 raw41789step1Labels raw41789step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

theorem canonical41790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41790 raw41790Labels = mixedMoment B node2231 node2231Labels := by
  calc
    mixedMoment B raw41790 raw41790Labels = mixedMoment B raw41790step0 raw41790step0Labels := by
      have ha : raw41790step0 = raw41790 := by apply Matrix.ext; unfold raw41790step0 raw41790; decide +kernel
      have hl : raw41790Labels = labelEmbedding1 ∘ raw41790step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41790 raw41790Labels raw41790step0Labels labelEmbedding1 hl
    _ = mixedMoment B node2231 node2231Labels := by rfl

theorem canonical41791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41791 raw41791Labels = mixedMoment B node4695 node4695Labels := by
  calc
    mixedMoment B raw41791 raw41791Labels = mixedMoment B raw41791step0 raw41791step0Labels := by
      have ha : raw41791step0 = (fun i j => raw41791 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41791step0 raw41791; decide +kernel
      have hl : raw41791step0Labels = raw41791Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41791 raw41791Labels permutation224 permutation7
    mixedMoment B raw41791step0 raw41791step0Labels = mixedMoment B raw41791step1 raw41791step1Labels := by
      have ha : raw41791step1 = -raw41791step0 := by apply Matrix.ext; change ∀ i j, raw41791step1 i j = -(raw41791step0 i j); unfold raw41791step1 raw41791step0; decide +kernel
      have hl : raw41791step1Labels = raw41791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41791step1 raw41791step1Labels = mixedMoment B raw41791step2 raw41791step2Labels := by
      have ha : raw41791step2 = raw41791step1 := by apply Matrix.ext; unfold raw41791step2 raw41791step1; decide +kernel
      have hl : raw41791step1Labels = labelEmbedding6 ∘ raw41791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41791step1 raw41791step1Labels raw41791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4695 node4695Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2208 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2208) =
      Integer.Sparse.eval keyMomentRow2208 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2160) := by
    have ha : gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge = raw41728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41728 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4667) := by
    have ha : gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge = raw41729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41729 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2208).leftCharge (GramAssembly.key 2208).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2208, Integer.Sparse.eval]
  ring

theorem keyMoment2209 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2209) =
      Integer.Sparse.eval keyMomentRow2209 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2179) := by
    have ha : gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge = raw41730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41730 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4765) := by
    have ha : gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge = raw41731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41731 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2209).leftCharge (GramAssembly.key 2209).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2209, Integer.Sparse.eval]
  ring

theorem keyMoment2210 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2210) =
      Integer.Sparse.eval keyMomentRow2210 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2219) := by
    have ha : gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge = raw41732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41732 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4793) := by
    have ha : gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge = raw41733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41733 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2210).leftCharge (GramAssembly.key 2210).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2210, Integer.Sparse.eval]
  ring

theorem keyMoment2211 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2211) =
      Integer.Sparse.eval keyMomentRow2211 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2160) := by
    have ha : gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge = raw41734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41734 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4667) := by
    have ha : gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge = raw41735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41735 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2211).leftCharge (GramAssembly.key 2211).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2211, Integer.Sparse.eval]
  ring

theorem keyMoment2212 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2212) =
      Integer.Sparse.eval keyMomentRow2212 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge = raw41736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41736 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4892) := by
    have ha : gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge = raw41737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41737 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2212).leftCharge (GramAssembly.key 2212).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2212, Integer.Sparse.eval]
  ring

theorem keyMoment2213 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2213) =
      Integer.Sparse.eval keyMomentRow2213 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2254) := by
    have ha : gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge = raw41738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41738 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4880) := by
    have ha : gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge = raw41739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41739 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2213).leftCharge (GramAssembly.key 2213).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2213, Integer.Sparse.eval]
  ring

theorem keyMoment2214 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2214) =
      Integer.Sparse.eval keyMomentRow2214 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge = raw41740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41740 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4891) := by
    have ha : gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge = raw41741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41741 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2214).leftCharge (GramAssembly.key 2214).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2214, Integer.Sparse.eval]
  ring

theorem keyMoment2215 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2215) =
      Integer.Sparse.eval keyMomentRow2215 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2251) := by
    have ha : gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge = raw41742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41742 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4867) := by
    have ha : gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge = raw41743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41743 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2215).leftCharge (GramAssembly.key 2215).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2215, Integer.Sparse.eval]
  ring

theorem keyMoment2216 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2216) =
      Integer.Sparse.eval keyMomentRow2216 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2249) := by
    have ha : gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge = raw41744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41744 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4700) := by
    have ha : gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge = raw41745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41745 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2216).leftCharge (GramAssembly.key 2216).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2216, Integer.Sparse.eval]
  ring

theorem keyMoment2217 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2217) =
      Integer.Sparse.eval keyMomentRow2217 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2196) := by
    have ha : gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge = raw41746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41746 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4816) := by
    have ha : gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge = raw41747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41747 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2217).leftCharge (GramAssembly.key 2217).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2217, Integer.Sparse.eval]
  ring

theorem keyMoment2218 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2218) =
      Integer.Sparse.eval keyMomentRow2218 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2195) := by
    have ha : gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge = raw41748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41748 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4803) := by
    have ha : gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge = raw41749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41749 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2218).leftCharge (GramAssembly.key 2218).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2218, Integer.Sparse.eval]
  ring

theorem keyMoment2219 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2219) =
      Integer.Sparse.eval keyMomentRow2219 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2194) := by
    have ha : gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge = raw41750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41750 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4773) := by
    have ha : gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge = raw41751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41751 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2219).leftCharge (GramAssembly.key 2219).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2219, Integer.Sparse.eval]
  ring

theorem keyMoment2220 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2220) =
      Integer.Sparse.eval keyMomentRow2220 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2144) := by
    have ha : gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge = raw41752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41752 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4665) := by
    have ha : gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge = raw41753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41753 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2220).leftCharge (GramAssembly.key 2220).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2220, Integer.Sparse.eval]
  ring

theorem keyMoment2221 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2221) =
      Integer.Sparse.eval keyMomentRow2221 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2248) := by
    have ha : gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge = raw41754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41754 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4698) := by
    have ha : gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge = raw41755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41755 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2221).leftCharge (GramAssembly.key 2221).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2221, Integer.Sparse.eval]
  ring

theorem keyMoment2222 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2222) =
      Integer.Sparse.eval keyMomentRow2222 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2250) := by
    have ha : gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge = raw41756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41756 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4852) := by
    have ha : gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge = raw41757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41757 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2222).leftCharge (GramAssembly.key 2222).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2222, Integer.Sparse.eval]
  ring

theorem keyMoment2223 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2223) =
      Integer.Sparse.eval keyMomentRow2223 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge = raw41758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41758 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge = raw41759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41759 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2223).leftCharge (GramAssembly.key 2223).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2223, Integer.Sparse.eval]
  ring

theorem keyMoment2224 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2224) =
      Integer.Sparse.eval keyMomentRow2224 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2280) := by
    have ha : gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge = raw41760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41760 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4884) := by
    have ha : gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge = raw41761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41761 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2224).leftCharge (GramAssembly.key 2224).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2224, Integer.Sparse.eval]
  ring

theorem keyMoment2225 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2225) =
      Integer.Sparse.eval keyMomentRow2225 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2273) := by
    have ha : gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge = raw41762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41762 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4704) := by
    have ha : gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge = raw41763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41763 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2225).leftCharge (GramAssembly.key 2225).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2225, Integer.Sparse.eval]
  ring

theorem keyMoment2226 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2226) =
      Integer.Sparse.eval keyMomentRow2226 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2217) := by
    have ha : gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge = raw41764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41764 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4821) := by
    have ha : gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge = raw41765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41765 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2226).leftCharge (GramAssembly.key 2226).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2226, Integer.Sparse.eval]
  ring

theorem keyMoment2227 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2227) =
      Integer.Sparse.eval keyMomentRow2227 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2212) := by
    have ha : gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge = raw41766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41766 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4776) := by
    have ha : gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge = raw41767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41767 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2227).leftCharge (GramAssembly.key 2227).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2227, Integer.Sparse.eval]
  ring

theorem keyMoment2228 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2228) =
      Integer.Sparse.eval keyMomentRow2228 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2155) := by
    have ha : gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge = raw41768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41768 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4669) := by
    have ha : gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge = raw41769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41769 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2228).leftCharge (GramAssembly.key 2228).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2228, Integer.Sparse.eval]
  ring

theorem keyMoment2229 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2229) =
      Integer.Sparse.eval keyMomentRow2229 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2272) := by
    have ha : gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge = raw41770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41770 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4703) := by
    have ha : gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge = raw41771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41771 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2229).leftCharge (GramAssembly.key 2229).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2229, Integer.Sparse.eval]
  ring

theorem keyMoment2230 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2230) =
      Integer.Sparse.eval keyMomentRow2230 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2274) := by
    have ha : gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge = raw41772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41772 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4856) := by
    have ha : gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge = raw41773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41773 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2230).leftCharge (GramAssembly.key 2230).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2230, Integer.Sparse.eval]
  ring

theorem keyMoment2231 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2231) =
      Integer.Sparse.eval keyMomentRow2231 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2176) := by
    have ha : gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge = raw41774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41774 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4756) := by
    have ha : gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge = raw41775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41775 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2231).leftCharge (GramAssembly.key 2231).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2231, Integer.Sparse.eval]
  ring

theorem keyMoment2232 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2232) =
      Integer.Sparse.eval keyMomentRow2232 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2211) := by
    have ha : gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge = raw41776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41776 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4775) := by
    have ha : gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge = raw41777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41777 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2232).leftCharge (GramAssembly.key 2232).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2232, Integer.Sparse.eval]
  ring

theorem keyMoment2233 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2233) =
      Integer.Sparse.eval keyMomentRow2233 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2213) := by
    have ha : gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge = raw41778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41778 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4795) := by
    have ha : gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge = raw41779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41779 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2233).leftCharge (GramAssembly.key 2233).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2233, Integer.Sparse.eval]
  ring

theorem keyMoment2234 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2234) =
      Integer.Sparse.eval keyMomentRow2234 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2154) := by
    have ha : gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge = raw41780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41780 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4668) := by
    have ha : gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge = raw41781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41781 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2234).leftCharge (GramAssembly.key 2234).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2234, Integer.Sparse.eval]
  ring

theorem keyMoment2235 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2235) =
      Integer.Sparse.eval keyMomentRow2235 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2235) := by
    have ha : gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge = raw41782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41782 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4886) := by
    have ha : gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge = raw41783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41783 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2235).leftCharge (GramAssembly.key 2235).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2235, Integer.Sparse.eval]
  ring

theorem keyMoment2236 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2236) =
      Integer.Sparse.eval keyMomentRow2236 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2234) := by
    have ha : gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge = raw41784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41784 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4878) := by
    have ha : gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge = raw41785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41785 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2236).leftCharge (GramAssembly.key 2236).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2236, Integer.Sparse.eval]
  ring

theorem keyMoment2237 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2237) =
      Integer.Sparse.eval keyMomentRow2237 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2233) := by
    have ha : gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge = raw41786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41786 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge = raw41787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41787 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2237).leftCharge (GramAssembly.key 2237).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2237, Integer.Sparse.eval]
  ring

theorem keyMoment2238 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2238) =
      Integer.Sparse.eval keyMomentRow2238 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2232) := by
    have ha : gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge = raw41788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41788 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4863) := by
    have ha : gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge = raw41789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41789 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2238).leftCharge (GramAssembly.key 2238).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2238, Integer.Sparse.eval]
  ring

theorem keyMoment2239 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2239) =
      Integer.Sparse.eval keyMomentRow2239 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2231) := by
    have ha : gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge = raw41790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41790 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4695) := by
    have ha : gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge = raw41791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41791 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2239).leftCharge (GramAssembly.key 2239).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2239, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk69
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2208 : keyMomentRows (2208 : Fin 2886) =
    keyMomentRow2208 := by decide +kernel

theorem keyMomentRowsAt2209 : keyMomentRows (2209 : Fin 2886) =
    keyMomentRow2209 := by decide +kernel

theorem keyMomentRowsAt2210 : keyMomentRows (2210 : Fin 2886) =
    keyMomentRow2210 := by decide +kernel

theorem keyMomentRowsAt2211 : keyMomentRows (2211 : Fin 2886) =
    keyMomentRow2211 := by decide +kernel

theorem keyMomentRowsAt2212 : keyMomentRows (2212 : Fin 2886) =
    keyMomentRow2212 := by decide +kernel

theorem keyMomentRowsAt2213 : keyMomentRows (2213 : Fin 2886) =
    keyMomentRow2213 := by decide +kernel

theorem keyMomentRowsAt2214 : keyMomentRows (2214 : Fin 2886) =
    keyMomentRow2214 := by decide +kernel

theorem keyMomentRowsAt2215 : keyMomentRows (2215 : Fin 2886) =
    keyMomentRow2215 := by decide +kernel

theorem keyMomentRowsAt2216 : keyMomentRows (2216 : Fin 2886) =
    keyMomentRow2216 := by decide +kernel

theorem keyMomentRowsAt2217 : keyMomentRows (2217 : Fin 2886) =
    keyMomentRow2217 := by decide +kernel

theorem keyMomentRowsAt2218 : keyMomentRows (2218 : Fin 2886) =
    keyMomentRow2218 := by decide +kernel

theorem keyMomentRowsAt2219 : keyMomentRows (2219 : Fin 2886) =
    keyMomentRow2219 := by decide +kernel

theorem keyMomentRowsAt2220 : keyMomentRows (2220 : Fin 2886) =
    keyMomentRow2220 := by decide +kernel

theorem keyMomentRowsAt2221 : keyMomentRows (2221 : Fin 2886) =
    keyMomentRow2221 := by decide +kernel

theorem keyMomentRowsAt2222 : keyMomentRows (2222 : Fin 2886) =
    keyMomentRow2222 := by decide +kernel

theorem keyMomentRowsAt2223 : keyMomentRows (2223 : Fin 2886) =
    keyMomentRow2223 := by decide +kernel

theorem keyMomentRowsAt2224 : keyMomentRows (2224 : Fin 2886) =
    keyMomentRow2224 := by decide +kernel

theorem keyMomentRowsAt2225 : keyMomentRows (2225 : Fin 2886) =
    keyMomentRow2225 := by decide +kernel

theorem keyMomentRowsAt2226 : keyMomentRows (2226 : Fin 2886) =
    keyMomentRow2226 := by decide +kernel

theorem keyMomentRowsAt2227 : keyMomentRows (2227 : Fin 2886) =
    keyMomentRow2227 := by decide +kernel

theorem keyMomentRowsAt2228 : keyMomentRows (2228 : Fin 2886) =
    keyMomentRow2228 := by decide +kernel

theorem keyMomentRowsAt2229 : keyMomentRows (2229 : Fin 2886) =
    keyMomentRow2229 := by decide +kernel

theorem keyMomentRowsAt2230 : keyMomentRows (2230 : Fin 2886) =
    keyMomentRow2230 := by decide +kernel

theorem keyMomentRowsAt2231 : keyMomentRows (2231 : Fin 2886) =
    keyMomentRow2231 := by decide +kernel

theorem keyMomentRowsAt2232 : keyMomentRows (2232 : Fin 2886) =
    keyMomentRow2232 := by decide +kernel

theorem keyMomentRowsAt2233 : keyMomentRows (2233 : Fin 2886) =
    keyMomentRow2233 := by decide +kernel

theorem keyMomentRowsAt2234 : keyMomentRows (2234 : Fin 2886) =
    keyMomentRow2234 := by decide +kernel

theorem keyMomentRowsAt2235 : keyMomentRows (2235 : Fin 2886) =
    keyMomentRow2235 := by decide +kernel

theorem keyMomentRowsAt2236 : keyMomentRows (2236 : Fin 2886) =
    keyMomentRow2236 := by decide +kernel

theorem keyMomentRowsAt2237 : keyMomentRows (2237 : Fin 2886) =
    keyMomentRow2237 := by decide +kernel

theorem keyMomentRowsAt2238 : keyMomentRows (2238 : Fin 2886) =
    keyMomentRow2238 := by decide +kernel

theorem keyMomentRowsAt2239 : keyMomentRows (2239 : Fin 2886) =
    keyMomentRow2239 := by decide +kernel

theorem keyMomentChunkSound69_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 69) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2208 ∨ k.val = 2209 ∨ k.val = 2210 ∨ k.val = 2211 ∨ k.val = 2212 ∨ k.val = 2213 ∨ k.val = 2214 ∨ k.val = 2215 ∨ k.val = 2216 ∨ k.val = 2217 ∨ k.val = 2218 ∨ k.val = 2219 ∨ k.val = 2220 ∨ k.val = 2221 ∨ k.val = 2222 ∨ k.val = 2223 ∨ k.val = 2224 ∨ k.val = 2225 ∨ k.val = 2226 ∨ k.val = 2227 ∨ k.val = 2228 ∨ k.val = 2229 ∨ k.val = 2230 ∨ k.val = 2231 ∨ k.val = 2232 ∨ k.val = 2233 ∨ k.val = 2234 ∨ k.val = 2235 ∨ k.val = 2236 ∨ k.val = 2237 ∨ k.val = 2238 ∨ k.val = 2239 := by omega
  rcases heq with h2208 | h2209 | h2210 | h2211 | h2212 | h2213 | h2214 | h2215 | h2216 | h2217 | h2218 | h2219 | h2220 | h2221 | h2222 | h2223 | h2224 | h2225 | h2226 | h2227 | h2228 | h2229 | h2230 | h2231 | h2232 | h2233 | h2234 | h2235 | h2236 | h2237 | h2238 | h2239
  · have he : k = (2208 : Fin 2886) := Fin.ext h2208
    subst k
    rw [keyMomentRowsAt2208]
    exact keyMoment2208 B hB
  · have he : k = (2209 : Fin 2886) := Fin.ext h2209
    subst k
    rw [keyMomentRowsAt2209]
    exact keyMoment2209 B hB
  · have he : k = (2210 : Fin 2886) := Fin.ext h2210
    subst k
    rw [keyMomentRowsAt2210]
    exact keyMoment2210 B hB
  · have he : k = (2211 : Fin 2886) := Fin.ext h2211
    subst k
    rw [keyMomentRowsAt2211]
    exact keyMoment2211 B hB
  · have he : k = (2212 : Fin 2886) := Fin.ext h2212
    subst k
    rw [keyMomentRowsAt2212]
    exact keyMoment2212 B hB
  · have he : k = (2213 : Fin 2886) := Fin.ext h2213
    subst k
    rw [keyMomentRowsAt2213]
    exact keyMoment2213 B hB
  · have he : k = (2214 : Fin 2886) := Fin.ext h2214
    subst k
    rw [keyMomentRowsAt2214]
    exact keyMoment2214 B hB
  · have he : k = (2215 : Fin 2886) := Fin.ext h2215
    subst k
    rw [keyMomentRowsAt2215]
    exact keyMoment2215 B hB
  · have he : k = (2216 : Fin 2886) := Fin.ext h2216
    subst k
    rw [keyMomentRowsAt2216]
    exact keyMoment2216 B hB
  · have he : k = (2217 : Fin 2886) := Fin.ext h2217
    subst k
    rw [keyMomentRowsAt2217]
    exact keyMoment2217 B hB
  · have he : k = (2218 : Fin 2886) := Fin.ext h2218
    subst k
    rw [keyMomentRowsAt2218]
    exact keyMoment2218 B hB
  · have he : k = (2219 : Fin 2886) := Fin.ext h2219
    subst k
    rw [keyMomentRowsAt2219]
    exact keyMoment2219 B hB
  · have he : k = (2220 : Fin 2886) := Fin.ext h2220
    subst k
    rw [keyMomentRowsAt2220]
    exact keyMoment2220 B hB
  · have he : k = (2221 : Fin 2886) := Fin.ext h2221
    subst k
    rw [keyMomentRowsAt2221]
    exact keyMoment2221 B hB
  · have he : k = (2222 : Fin 2886) := Fin.ext h2222
    subst k
    rw [keyMomentRowsAt2222]
    exact keyMoment2222 B hB
  · have he : k = (2223 : Fin 2886) := Fin.ext h2223
    subst k
    rw [keyMomentRowsAt2223]
    exact keyMoment2223 B hB
  · have he : k = (2224 : Fin 2886) := Fin.ext h2224
    subst k
    rw [keyMomentRowsAt2224]
    exact keyMoment2224 B hB
  · have he : k = (2225 : Fin 2886) := Fin.ext h2225
    subst k
    rw [keyMomentRowsAt2225]
    exact keyMoment2225 B hB
  · have he : k = (2226 : Fin 2886) := Fin.ext h2226
    subst k
    rw [keyMomentRowsAt2226]
    exact keyMoment2226 B hB
  · have he : k = (2227 : Fin 2886) := Fin.ext h2227
    subst k
    rw [keyMomentRowsAt2227]
    exact keyMoment2227 B hB
  · have he : k = (2228 : Fin 2886) := Fin.ext h2228
    subst k
    rw [keyMomentRowsAt2228]
    exact keyMoment2228 B hB
  · have he : k = (2229 : Fin 2886) := Fin.ext h2229
    subst k
    rw [keyMomentRowsAt2229]
    exact keyMoment2229 B hB
  · have he : k = (2230 : Fin 2886) := Fin.ext h2230
    subst k
    rw [keyMomentRowsAt2230]
    exact keyMoment2230 B hB
  · have he : k = (2231 : Fin 2886) := Fin.ext h2231
    subst k
    rw [keyMomentRowsAt2231]
    exact keyMoment2231 B hB
  · have he : k = (2232 : Fin 2886) := Fin.ext h2232
    subst k
    rw [keyMomentRowsAt2232]
    exact keyMoment2232 B hB
  · have he : k = (2233 : Fin 2886) := Fin.ext h2233
    subst k
    rw [keyMomentRowsAt2233]
    exact keyMoment2233 B hB
  · have he : k = (2234 : Fin 2886) := Fin.ext h2234
    subst k
    rw [keyMomentRowsAt2234]
    exact keyMoment2234 B hB
  · have he : k = (2235 : Fin 2886) := Fin.ext h2235
    subst k
    rw [keyMomentRowsAt2235]
    exact keyMoment2235 B hB
  · have he : k = (2236 : Fin 2886) := Fin.ext h2236
    subst k
    rw [keyMomentRowsAt2236]
    exact keyMoment2236 B hB
  · have he : k = (2237 : Fin 2886) := Fin.ext h2237
    subst k
    rw [keyMomentRowsAt2237]
    exact keyMoment2237 B hB
  · have he : k = (2238 : Fin 2886) := Fin.ext h2238
    subst k
    rw [keyMomentRowsAt2238]
    exact keyMoment2238 B hB
  · have he : k = (2239 : Fin 2886) := Fin.ext h2239
    subst k
    rw [keyMomentRowsAt2239]
    exact keyMoment2239 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound69_e_oai
