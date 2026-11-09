-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:14:15.865179+00:00
-- url     : https://prove2.me/submissions/65214ecb-6361-4d83-af1d-2996b22d2e53

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E089
import Definitions.Def_OAIQ106E094
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical104
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical13405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13405 raw13405Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw13405 raw13405Labels = mixedMoment B raw13405step0 raw13405step0Labels := by
      have ha : raw13405step0 = (fun i j => raw13405 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13405step0 raw13405; decide +kernel
      have hl : raw13405step0Labels = raw13405Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13405 raw13405Labels permutation152 permutation3
    _ = mixedMoment B node4025 node4025Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical145
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical18571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18571 raw18571Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18571 raw18571Labels = mixedMoment B raw18571step0 raw18571step0Labels := by
      have hz : ∀ j, raw18571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18571step0 = (fun i j => raw18571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18571step0 raw18571; decide +kernel
      have hl : raw18571step0Labels = raw18571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18571 raw18571Labels permutation434 hz
    mixedMoment B raw18571step0 raw18571step0Labels = mixedMoment B raw18571step1 raw18571step1Labels := by
      have ha : raw18571step1 = (fun i j => raw18571step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18571step1 raw18571step0; decide +kernel
      have hl : raw18571step1Labels = raw18571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18571step0 raw18571step0Labels permutation151 permutation3
    mixedMoment B raw18571step1 raw18571step1Labels = mixedMoment B raw18571step2 raw18571step2Labels := by
      have ha : raw18571step2 = -raw18571step1 := by apply Matrix.ext; change ∀ i j, raw18571step2 i j = -(raw18571step1 i j); unfold raw18571step2 raw18571step1; decide +kernel
      have hl : raw18571step2Labels = raw18571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40800 raw40800Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw40800 raw40800Labels = mixedMoment B raw40800step0 raw40800step0Labels := by
      have hz : ∀ j, raw40800 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40800step0 = (fun i j => raw40800 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40800step0 raw40800; decide +kernel
      have hl : raw40800step0Labels = raw40800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40800 raw40800Labels permutation434 hz
    mixedMoment B raw40800step0 raw40800step0Labels = mixedMoment B raw40800step1 raw40800step1Labels := by
      have ha : raw40800step1 = (fun i j => raw40800step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40800step1 raw40800step0; decide +kernel
      have hl : raw40800step1Labels = raw40800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40800step0 raw40800step0Labels permutation151 permutation3
    mixedMoment B raw40800step1 raw40800step1Labels = mixedMoment B raw40800step2 raw40800step2Labels := by
      have ha : raw40800step2 = -raw40800step1 := by apply Matrix.ext; change ∀ i j, raw40800step2 i j = -(raw40800step1 i j); unfold raw40800step2 raw40800step1; decide +kernel
      have hl : raw40800step2Labels = raw40800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

theorem canonical40801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40801 raw40801Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw40801 raw40801Labels = mixedMoment B raw40801step0 raw40801step0Labels := by
      have hz : ∀ j, raw40801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40801step0 = (fun i j => raw40801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40801step0 raw40801; decide +kernel
      have hl : raw40801step0Labels = raw40801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40801 raw40801Labels permutation434 hz
    mixedMoment B raw40801step0 raw40801step0Labels = mixedMoment B raw40801step1 raw40801step1Labels := by
      have ha : raw40801step1 = (fun i j => raw40801step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40801step1 raw40801step0; decide +kernel
      have hl : raw40801step1Labels = raw40801step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40801step0 raw40801step0Labels permutation151 permutation3
    mixedMoment B raw40801step1 raw40801step1Labels = mixedMoment B raw40801step2 raw40801step2Labels := by
      have ha : raw40801step2 = -raw40801step1 := by apply Matrix.ext; change ∀ i j, raw40801step2 i j = -(raw40801step1 i j); unfold raw40801step2 raw40801step1; decide +kernel
      have hl : raw40801step2Labels = raw40801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

theorem canonical40802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40802 raw40802Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw40802 raw40802Labels = mixedMoment B raw40802step0 raw40802step0Labels := by
      have hz : ∀ j, raw40802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40802step0 = (fun i j => raw40802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40802step0 raw40802; decide +kernel
      have hl : raw40802step0Labels = raw40802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40802 raw40802Labels permutation434 hz
    mixedMoment B raw40802step0 raw40802step0Labels = mixedMoment B raw40802step1 raw40802step1Labels := by
      have ha : raw40802step1 = (fun i j => raw40802step0 (permutation106 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40802step1 raw40802step0; decide +kernel
      have hl : raw40802step1Labels = raw40802step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40802step0 raw40802step0Labels permutation106 permutation6
    mixedMoment B raw40802step1 raw40802step1Labels = mixedMoment B raw40802step2 raw40802step2Labels := by
      have ha : raw40802step2 = -raw40802step1 := by apply Matrix.ext; change ∀ i j, raw40802step2 i j = -(raw40802step1 i j); unfold raw40802step2 raw40802step1; decide +kernel
      have hl : raw40802step2Labels = raw40802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical40803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40803 raw40803Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw40803 raw40803Labels = mixedMoment B raw40803step0 raw40803step0Labels := by
      have ha : raw40803step0 = (fun i j => raw40803 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40803step0 raw40803; decide +kernel
      have hl : raw40803step0Labels = raw40803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40803 raw40803Labels permutation664 permutation3
    mixedMoment B raw40803step0 raw40803step0Labels = mixedMoment B raw40803step1 raw40803step1Labels := by
      have ha : raw40803step1 = -raw40803step0 := by apply Matrix.ext; change ∀ i j, raw40803step1 i j = -(raw40803step0 i j); unfold raw40803step1 raw40803step0; decide +kernel
      have hl : raw40803step1Labels = raw40803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

theorem canonical40804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40804 raw40804Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw40804 raw40804Labels = mixedMoment B raw40804step0 raw40804step0Labels := by
      have ha : raw40804step0 = (fun i j => raw40804 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40804step0 raw40804; decide +kernel
      have hl : raw40804step0Labels = raw40804Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40804 raw40804Labels permutation688 permutation3
    mixedMoment B raw40804step0 raw40804step0Labels = mixedMoment B raw40804step1 raw40804step1Labels := by
      have ha : raw40804step1 = -raw40804step0 := by apply Matrix.ext; change ∀ i j, raw40804step1 i j = -(raw40804step0 i j); unfold raw40804step1 raw40804step0; decide +kernel
      have hl : raw40804step1Labels = raw40804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical40805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40805 raw40805Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw40805 raw40805Labels = mixedMoment B raw40805step0 raw40805step0Labels := by
      have ha : raw40805step0 = (fun i j => raw40805 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40805step0 raw40805; decide +kernel
      have hl : raw40805step0Labels = raw40805Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40805 raw40805Labels permutation688 permutation3
    mixedMoment B raw40805step0 raw40805step0Labels = mixedMoment B raw40805step1 raw40805step1Labels := by
      have ha : raw40805step1 = -raw40805step0 := by apply Matrix.ext; change ∀ i j, raw40805step1 i j = -(raw40805step0 i j); unfold raw40805step1 raw40805step0; decide +kernel
      have hl : raw40805step1Labels = raw40805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

theorem canonical40806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40806 raw40806Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw40806 raw40806Labels = mixedMoment B raw40806step0 raw40806step0Labels := by
      have ha : raw40806step0 = (fun i j => raw40806 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40806step0 raw40806; decide +kernel
      have hl : raw40806step0Labels = raw40806Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40806 raw40806Labels permutation609 permutation6
    _ = mixedMoment B node4022 node4022Labels := by rfl

theorem canonical40807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40807 raw40807Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw40807 raw40807Labels = mixedMoment B raw40807step0 raw40807step0Labels := by
      have ha : raw40807step0 = (fun i j => raw40807 (permutation450 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40807step0 raw40807; decide +kernel
      have hl : raw40807step0Labels = raw40807Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40807 raw40807Labels permutation450 permutation6
    mixedMoment B raw40807step0 raw40807step0Labels = mixedMoment B raw40807step1 raw40807step1Labels := by
      have ha : raw40807step1 = -raw40807step0 := by apply Matrix.ext; change ∀ i j, raw40807step1 i j = -(raw40807step0 i j); unfold raw40807step1 raw40807step0; decide +kernel
      have hl : raw40807step1Labels = raw40807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

theorem canonical40808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40808 raw40808Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw40808 raw40808Labels = mixedMoment B raw40808step0 raw40808step0Labels := by
      have ha : raw40808step0 = (fun i j => raw40808 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40808step0 raw40808; decide +kernel
      have hl : raw40808step0Labels = raw40808Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40808 raw40808Labels permutation445 permutation6
    mixedMoment B raw40808step0 raw40808step0Labels = mixedMoment B raw40808step1 raw40808step1Labels := by
      have ha : raw40808step1 = -raw40808step0 := by apply Matrix.ext; change ∀ i j, raw40808step1 i j = -(raw40808step0 i j); unfold raw40808step1 raw40808step0; decide +kernel
      have hl : raw40808step1Labels = raw40808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

theorem canonical40809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40809 raw40809Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw40809 raw40809Labels = mixedMoment B raw40809step0 raw40809step0Labels := by
      have ha : raw40809step0 = (fun i j => raw40809 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40809step0 raw40809; decide +kernel
      have hl : raw40809step0Labels = raw40809Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40809 raw40809Labels permutation152 permutation3
    _ = mixedMoment B node4024 node4024Labels := by rfl

theorem canonical40810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40810 raw40810Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw40810 raw40810Labels = mixedMoment B raw40810step0 raw40810step0Labels := by
      have hz : ∀ j, raw40810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40810step0 = (fun i j => raw40810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40810step0 raw40810; decide +kernel
      have hl : raw40810step0Labels = raw40810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40810 raw40810Labels permutation434 hz
    mixedMoment B raw40810step0 raw40810step0Labels = mixedMoment B raw40810step1 raw40810step1Labels := by
      have hz : ∀ j, raw40810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40810step1 = (fun i j => raw40810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40810step1 raw40810step0; decide +kernel
      have hl : raw40810step1Labels = raw40810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40810step0 raw40810step0Labels permutation80 hz
    mixedMoment B raw40810step1 raw40810step1Labels = mixedMoment B raw40810step2 raw40810step2Labels := by
      have ha : raw40810step2 = (fun i j => raw40810step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40810step2 raw40810step1; decide +kernel
      have hl : raw40810step2Labels = raw40810step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40810step1 raw40810step1Labels permutation31 permutation3
    mixedMoment B raw40810step2 raw40810step2Labels = mixedMoment B raw40810step3 raw40810step3Labels := by
      have ha : raw40810step3 = -raw40810step2 := by apply Matrix.ext; change ∀ i j, raw40810step3 i j = -(raw40810step2 i j); unfold raw40810step3 raw40810step2; decide +kernel
      have hl : raw40810step3Labels = raw40810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical40811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40811 raw40811Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw40811 raw40811Labels = mixedMoment B raw40811step0 raw40811step0Labels := by
      have hz : ∀ j, raw40811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40811step0 = (fun i j => raw40811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40811step0 raw40811; decide +kernel
      have hl : raw40811step0Labels = raw40811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40811 raw40811Labels permutation434 hz
    mixedMoment B raw40811step0 raw40811step0Labels = mixedMoment B raw40811step1 raw40811step1Labels := by
      have hz : ∀ j, raw40811step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40811step1 = (fun i j => raw40811step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40811step1 raw40811step0; decide +kernel
      have hl : raw40811step1Labels = raw40811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40811step0 raw40811step0Labels permutation80 hz
    mixedMoment B raw40811step1 raw40811step1Labels = mixedMoment B raw40811step2 raw40811step2Labels := by
      have ha : raw40811step2 = (fun i j => raw40811step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40811step2 raw40811step1; decide +kernel
      have hl : raw40811step2Labels = raw40811step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40811step1 raw40811step1Labels permutation28 permutation6
    _ = mixedMoment B node2888 node2888Labels := by rfl

theorem canonical40812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40812 raw40812Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw40812 raw40812Labels = mixedMoment B raw40812step0 raw40812step0Labels := by
      have hz : ∀ j, raw40812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40812step0 = (fun i j => raw40812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40812step0 raw40812; decide +kernel
      have hl : raw40812step0Labels = raw40812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40812 raw40812Labels permutation346 hz
    mixedMoment B raw40812step0 raw40812step0Labels = mixedMoment B raw40812step1 raw40812step1Labels := by
      have ha : raw40812step1 = (fun i j => raw40812step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40812step1 raw40812step0; decide +kernel
      have hl : raw40812step1Labels = raw40812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40812step0 raw40812step0Labels permutation151 permutation3
    mixedMoment B raw40812step1 raw40812step1Labels = mixedMoment B raw40812step2 raw40812step2Labels := by
      have ha : raw40812step2 = -raw40812step1 := by apply Matrix.ext; change ∀ i j, raw40812step2 i j = -(raw40812step1 i j); unfold raw40812step2 raw40812step1; decide +kernel
      have hl : raw40812step2Labels = raw40812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical40813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40813 raw40813Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw40813 raw40813Labels = mixedMoment B raw40813step0 raw40813step0Labels := by
      have hz : ∀ j, raw40813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40813step0 = (fun i j => raw40813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40813step0 raw40813; decide +kernel
      have hl : raw40813step0Labels = raw40813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40813 raw40813Labels permutation346 hz
    mixedMoment B raw40813step0 raw40813step0Labels = mixedMoment B raw40813step1 raw40813step1Labels := by
      have ha : raw40813step1 = (fun i j => raw40813step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40813step1 raw40813step0; decide +kernel
      have hl : raw40813step1Labels = raw40813step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40813step0 raw40813step0Labels permutation137 permutation6
    _ = mixedMoment B node2885 node2885Labels := by rfl

theorem canonical40814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40814 raw40814Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw40814 raw40814Labels = mixedMoment B raw40814step0 raw40814step0Labels := by
      have hz : ∀ j, raw40814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40814step0 = (fun i j => raw40814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40814step0 raw40814; decide +kernel
      have hl : raw40814step0Labels = raw40814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40814 raw40814Labels permutation346 hz
    mixedMoment B raw40814step0 raw40814step0Labels = mixedMoment B raw40814step1 raw40814step1Labels := by
      have ha : raw40814step1 = (fun i j => raw40814step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40814step1 raw40814step0; decide +kernel
      have hl : raw40814step1Labels = raw40814step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40814step0 raw40814step0Labels permutation84 permutation6
    mixedMoment B raw40814step1 raw40814step1Labels = mixedMoment B raw40814step2 raw40814step2Labels := by
      have ha : raw40814step2 = -raw40814step1 := by apply Matrix.ext; change ∀ i j, raw40814step2 i j = -(raw40814step1 i j); unfold raw40814step2 raw40814step1; decide +kernel
      have hl : raw40814step2Labels = raw40814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3733 node3733Labels := by rfl

theorem canonical40815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40815 raw40815Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw40815 raw40815Labels = mixedMoment B raw40815step0 raw40815step0Labels := by
      have hz : ∀ j, raw40815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40815step0 = (fun i j => raw40815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40815step0 raw40815; decide +kernel
      have hl : raw40815step0Labels = raw40815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40815 raw40815Labels permutation346 hz
    mixedMoment B raw40815step0 raw40815step0Labels = mixedMoment B raw40815step1 raw40815step1Labels := by
      have ha : raw40815step1 = (fun i j => raw40815step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40815step1 raw40815step0; decide +kernel
      have hl : raw40815step1Labels = raw40815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40815step0 raw40815step0Labels permutation138 permutation6
    _ = mixedMoment B node2867 node2867Labels := by rfl

theorem canonical40816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40816 raw40816Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw40816 raw40816Labels = mixedMoment B raw40816step0 raw40816step0Labels := by
      have ha : raw40816step0 = (fun i j => raw40816 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40816step0 raw40816; decide +kernel
      have hl : raw40816step0Labels = raw40816Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40816 raw40816Labels permutation540 permutation6
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical40817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40817 raw40817Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw40817 raw40817Labels = mixedMoment B raw40817step0 raw40817step0Labels := by
      have ha : raw40817step0 = (fun i j => raw40817 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40817step0 raw40817; decide +kernel
      have hl : raw40817step0Labels = raw40817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40817 raw40817Labels permutation620 permutation6
    _ = mixedMoment B node2864 node2864Labels := by rfl

theorem canonical40818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40818 raw40818Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw40818 raw40818Labels = mixedMoment B raw40818step0 raw40818step0Labels := by
      have ha : raw40818step0 = (fun i j => raw40818 (permutation462 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40818step0 raw40818; decide +kernel
      have hl : raw40818step0Labels = raw40818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40818 raw40818Labels permutation462 permutation6
    _ = mixedMoment B node3946 node3946Labels := by rfl

theorem canonical40819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40819 raw40819Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw40819 raw40819Labels = mixedMoment B raw40819step0 raw40819step0Labels := by
      have ha : raw40819step0 = (fun i j => raw40819 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40819step0 raw40819; decide +kernel
      have hl : raw40819step0Labels = raw40819Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40819 raw40819Labels permutation463 permutation6
    _ = mixedMoment B node3954 node3954Labels := by rfl

theorem canonical40820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40820 raw40820Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw40820 raw40820Labels = mixedMoment B raw40820step0 raw40820step0Labels := by
      have ha : raw40820step0 = (fun i j => raw40820 (permutation365 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40820step0 raw40820; decide +kernel
      have hl : raw40820step0Labels = raw40820Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40820 raw40820Labels permutation365 permutation6
    mixedMoment B raw40820step0 raw40820step0Labels = mixedMoment B raw40820step1 raw40820step1Labels := by
      have ha : raw40820step1 = -raw40820step0 := by apply Matrix.ext; change ∀ i j, raw40820step1 i j = -(raw40820step0 i j); unfold raw40820step1 raw40820step0; decide +kernel
      have hl : raw40820step1Labels = raw40820step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3720 node3720Labels := by rfl

theorem canonical40821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40821 raw40821Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40821 raw40821Labels = mixedMoment B raw40821step0 raw40821step0Labels := by
      have hz : ∀ j, raw40821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40821step0 = (fun i j => raw40821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40821step0 raw40821; decide +kernel
      have hl : raw40821step0Labels = raw40821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40821 raw40821Labels permutation520 hz
    mixedMoment B raw40821step0 raw40821step0Labels = mixedMoment B raw40821step1 raw40821step1Labels := by
      have hz : ∀ j, raw40821step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40821step1 = (fun i j => raw40821step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40821step1 raw40821step0; decide +kernel
      have hl : raw40821step1Labels = raw40821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40821step0 raw40821step0Labels permutation104 hz
    mixedMoment B raw40821step1 raw40821step1Labels = mixedMoment B raw40821step2 raw40821step2Labels := by
      have ha : raw40821step2 = (fun i j => raw40821step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40821step2 raw40821step1; decide +kernel
      have hl : raw40821step2Labels = raw40821step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40821step1 raw40821step1Labels permutation31 permutation3
    mixedMoment B raw40821step2 raw40821step2Labels = mixedMoment B raw40821step3 raw40821step3Labels := by
      have ha : raw40821step3 = -raw40821step2 := by apply Matrix.ext; change ∀ i j, raw40821step3 i j = -(raw40821step2 i j); unfold raw40821step3 raw40821step2; decide +kernel
      have hl : raw40821step3Labels = raw40821step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

theorem canonical40822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40822 raw40822Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40822 raw40822Labels = mixedMoment B raw40822step0 raw40822step0Labels := by
      have hz : ∀ j, raw40822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40822step0 = (fun i j => raw40822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40822step0 raw40822; decide +kernel
      have hl : raw40822step0Labels = raw40822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40822 raw40822Labels permutation434 hz
    mixedMoment B raw40822step0 raw40822step0Labels = mixedMoment B raw40822step1 raw40822step1Labels := by
      have ha : raw40822step1 = (fun i j => raw40822step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40822step1 raw40822step0; decide +kernel
      have hl : raw40822step1Labels = raw40822step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40822step0 raw40822step0Labels permutation151 permutation3
    mixedMoment B raw40822step1 raw40822step1Labels = mixedMoment B raw40822step2 raw40822step2Labels := by
      have ha : raw40822step2 = -raw40822step1 := by apply Matrix.ext; change ∀ i j, raw40822step2 i j = -(raw40822step1 i j); unfold raw40822step2 raw40822step1; decide +kernel
      have hl : raw40822step2Labels = raw40822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical40823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40823 raw40823Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw40823 raw40823Labels = mixedMoment B raw40823step0 raw40823step0Labels := by
      have hz : ∀ j, raw40823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40823step0 = (fun i j => raw40823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40823step0 raw40823; decide +kernel
      have hl : raw40823step0Labels = raw40823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40823 raw40823Labels permutation434 hz
    mixedMoment B raw40823step0 raw40823step0Labels = mixedMoment B raw40823step1 raw40823step1Labels := by
      have ha : raw40823step1 = (fun i j => raw40823step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40823step1 raw40823step0; decide +kernel
      have hl : raw40823step1Labels = raw40823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40823step0 raw40823step0Labels permutation151 permutation3
    mixedMoment B raw40823step1 raw40823step1Labels = mixedMoment B raw40823step2 raw40823step2Labels := by
      have ha : raw40823step2 = -raw40823step1 := by apply Matrix.ext; change ∀ i j, raw40823step2 i j = -(raw40823step1 i j); unfold raw40823step2 raw40823step1; decide +kernel
      have hl : raw40823step2Labels = raw40823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

theorem canonical40824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40824 raw40824Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40824 raw40824Labels = mixedMoment B raw40824step0 raw40824step0Labels := by
      have hz : ∀ j, raw40824 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40824step0 = (fun i j => raw40824 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40824step0 raw40824; decide +kernel
      have hl : raw40824step0Labels = raw40824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40824 raw40824Labels permutation434 hz
    mixedMoment B raw40824step0 raw40824step0Labels = mixedMoment B raw40824step1 raw40824step1Labels := by
      have ha : raw40824step1 = (fun i j => raw40824step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40824step1 raw40824step0; decide +kernel
      have hl : raw40824step1Labels = raw40824step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40824step0 raw40824step0Labels permutation151 permutation3
    mixedMoment B raw40824step1 raw40824step1Labels = mixedMoment B raw40824step2 raw40824step2Labels := by
      have ha : raw40824step2 = -raw40824step1 := by apply Matrix.ext; change ∀ i j, raw40824step2 i j = -(raw40824step1 i j); unfold raw40824step2 raw40824step1; decide +kernel
      have hl : raw40824step2Labels = raw40824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical40825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40825 raw40825Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40825 raw40825Labels = mixedMoment B raw40825step0 raw40825step0Labels := by
      have hz : ∀ j, raw40825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40825step0 = (fun i j => raw40825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40825step0 raw40825; decide +kernel
      have hl : raw40825step0Labels = raw40825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40825 raw40825Labels permutation434 hz
    mixedMoment B raw40825step0 raw40825step0Labels = mixedMoment B raw40825step1 raw40825step1Labels := by
      have ha : raw40825step1 = (fun i j => raw40825step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40825step1 raw40825step0; decide +kernel
      have hl : raw40825step1Labels = raw40825step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40825step0 raw40825step0Labels permutation151 permutation3
    mixedMoment B raw40825step1 raw40825step1Labels = mixedMoment B raw40825step2 raw40825step2Labels := by
      have ha : raw40825step2 = -raw40825step1 := by apply Matrix.ext; change ∀ i j, raw40825step2 i j = -(raw40825step1 i j); unfold raw40825step2 raw40825step1; decide +kernel
      have hl : raw40825step2Labels = raw40825step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

theorem canonical40826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40826 raw40826Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw40826 raw40826Labels = mixedMoment B raw40826step0 raw40826step0Labels := by
      have hz : ∀ j, raw40826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40826step0 = (fun i j => raw40826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40826step0 raw40826; decide +kernel
      have hl : raw40826step0Labels = raw40826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40826 raw40826Labels permutation434 hz
    mixedMoment B raw40826step0 raw40826step0Labels = mixedMoment B raw40826step1 raw40826step1Labels := by
      have ha : raw40826step1 = (fun i j => raw40826step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40826step1 raw40826step0; decide +kernel
      have hl : raw40826step1Labels = raw40826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40826step0 raw40826step0Labels permutation101 permutation6
    _ = mixedMoment B node3877 node3877Labels := by rfl

theorem canonical40827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40827 raw40827Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw40827 raw40827Labels = mixedMoment B raw40827step0 raw40827step0Labels := by
      have hz : ∀ j, raw40827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40827step0 = (fun i j => raw40827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40827step0 raw40827; decide +kernel
      have hl : raw40827step0Labels = raw40827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40827 raw40827Labels permutation434 hz
    mixedMoment B raw40827step0 raw40827step0Labels = mixedMoment B raw40827step1 raw40827step1Labels := by
      have ha : raw40827step1 = (fun i j => raw40827step0 (permutation105 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40827step1 raw40827step0; decide +kernel
      have hl : raw40827step1Labels = raw40827step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40827step0 raw40827step0Labels permutation105 permutation6
    mixedMoment B raw40827step1 raw40827step1Labels = mixedMoment B raw40827step2 raw40827step2Labels := by
      have ha : raw40827step2 = -raw40827step1 := by apply Matrix.ext; change ∀ i j, raw40827step2 i j = -(raw40827step1 i j); unfold raw40827step2 raw40827step1; decide +kernel
      have hl : raw40827step2Labels = raw40827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3379 node3379Labels := by rfl

theorem canonical40828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40828 raw40828Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw40828 raw40828Labels = mixedMoment B raw40828step0 raw40828step0Labels := by
      have ha : raw40828step0 = (fun i j => raw40828 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40828step0 raw40828; decide +kernel
      have hl : raw40828step0Labels = raw40828Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40828 raw40828Labels permutation664 permutation3
    mixedMoment B raw40828step0 raw40828step0Labels = mixedMoment B raw40828step1 raw40828step1Labels := by
      have ha : raw40828step1 = -raw40828step0 := by apply Matrix.ext; change ∀ i j, raw40828step1 i j = -(raw40828step0 i j); unfold raw40828step1 raw40828step0; decide +kernel
      have hl : raw40828step1Labels = raw40828step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3069 node3069Labels := by rfl

theorem canonical40829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40829 raw40829Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw40829 raw40829Labels = mixedMoment B raw40829step0 raw40829step0Labels := by
      have ha : raw40829step0 = (fun i j => raw40829 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40829step0 raw40829; decide +kernel
      have hl : raw40829step0Labels = raw40829Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40829 raw40829Labels permutation688 permutation3
    mixedMoment B raw40829step0 raw40829step0Labels = mixedMoment B raw40829step1 raw40829step1Labels := by
      have ha : raw40829step1 = -raw40829step0 := by apply Matrix.ext; change ∀ i j, raw40829step1 i j = -(raw40829step0 i j); unfold raw40829step1 raw40829step0; decide +kernel
      have hl : raw40829step1Labels = raw40829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3841 node3841Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1376 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1376) =
      Integer.Sparse.eval keyMomentRow1376 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1376).leftCharge (GramAssembly.key 1376).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3535) := by
    have ha : gramCharges (GramAssembly.key 1376).leftCharge (GramAssembly.key 1376).rightCharge = raw40800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40800 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1376).leftCharge (GramAssembly.key 1376).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1376, Integer.Sparse.eval]

theorem keyMoment1377 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1377) =
      Integer.Sparse.eval keyMomentRow1377 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1377).leftCharge (GramAssembly.key 1377).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3809) := by
    have ha : gramCharges (GramAssembly.key 1377).leftCharge (GramAssembly.key 1377).rightCharge = raw18571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw18571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical18571 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1377).leftCharge (GramAssembly.key 1377).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1377, Integer.Sparse.eval]

theorem keyMoment1378 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1378) =
      Integer.Sparse.eval keyMomentRow1378 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1378).leftCharge (GramAssembly.key 1378).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3959) := by
    have ha : gramCharges (GramAssembly.key 1378).leftCharge (GramAssembly.key 1378).rightCharge = raw40801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40801 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1378).leftCharge (GramAssembly.key 1378).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1378, Integer.Sparse.eval]

theorem keyMoment1379 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1379) =
      Integer.Sparse.eval keyMomentRow1379 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1379).leftCharge (GramAssembly.key 1379).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3395) := by
    have ha : gramCharges (GramAssembly.key 1379).leftCharge (GramAssembly.key 1379).rightCharge = raw40802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40802 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1379).leftCharge (GramAssembly.key 1379).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1379, Integer.Sparse.eval]

theorem keyMoment1380 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1380) =
      Integer.Sparse.eval keyMomentRow1380 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1380).leftCharge (GramAssembly.key 1380).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3066) := by
    have ha : gramCharges (GramAssembly.key 1380).leftCharge (GramAssembly.key 1380).rightCharge = raw40803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40803 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1380).leftCharge (GramAssembly.key 1380).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1380, Integer.Sparse.eval]

theorem keyMoment1381 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1381) =
      Integer.Sparse.eval keyMomentRow1381 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1381).leftCharge (GramAssembly.key 1381).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 1381).leftCharge (GramAssembly.key 1381).rightCharge = raw40804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40804 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1381).leftCharge (GramAssembly.key 1381).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1381, Integer.Sparse.eval]

theorem keyMoment1382 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1382) =
      Integer.Sparse.eval keyMomentRow1382 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1382).leftCharge (GramAssembly.key 1382).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3972) := by
    have ha : gramCharges (GramAssembly.key 1382).leftCharge (GramAssembly.key 1382).rightCharge = raw40805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40805 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1382).leftCharge (GramAssembly.key 1382).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1382, Integer.Sparse.eval]

theorem keyMoment1383 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1383) =
      Integer.Sparse.eval keyMomentRow1383 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1383).leftCharge (GramAssembly.key 1383).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4022) := by
    have ha : gramCharges (GramAssembly.key 1383).leftCharge (GramAssembly.key 1383).rightCharge = raw40806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40806 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1383).leftCharge (GramAssembly.key 1383).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1383, Integer.Sparse.eval]

theorem keyMoment1384 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1384) =
      Integer.Sparse.eval keyMomentRow1384 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1384).leftCharge (GramAssembly.key 1384).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3730) := by
    have ha : gramCharges (GramAssembly.key 1384).leftCharge (GramAssembly.key 1384).rightCharge = raw40807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40807 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1384).leftCharge (GramAssembly.key 1384).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1384, Integer.Sparse.eval]

theorem keyMoment1385 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1385) =
      Integer.Sparse.eval keyMomentRow1385 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1385).leftCharge (GramAssembly.key 1385).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3722) := by
    have ha : gramCharges (GramAssembly.key 1385).leftCharge (GramAssembly.key 1385).rightCharge = raw40808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40808 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1385).leftCharge (GramAssembly.key 1385).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1385, Integer.Sparse.eval]

theorem keyMoment1386 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1386) =
      Integer.Sparse.eval keyMomentRow1386 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1386).leftCharge (GramAssembly.key 1386).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4024) := by
    have ha : gramCharges (GramAssembly.key 1386).leftCharge (GramAssembly.key 1386).rightCharge = raw40809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40809 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1386).leftCharge (GramAssembly.key 1386).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1386, Integer.Sparse.eval]

theorem keyMoment1387 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1387) =
      Integer.Sparse.eval keyMomentRow1387 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1387).leftCharge (GramAssembly.key 1387).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4025) := by
    have ha : gramCharges (GramAssembly.key 1387).leftCharge (GramAssembly.key 1387).rightCharge = raw13405 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw13405Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical13405 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1387).leftCharge (GramAssembly.key 1387).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1387, Integer.Sparse.eval]

theorem keyMoment1388 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1388) =
      Integer.Sparse.eval keyMomentRow1388 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1388).leftCharge (GramAssembly.key 1388).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1388).leftCharge (GramAssembly.key 1388).rightCharge = raw40810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40810 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1388).leftCharge (GramAssembly.key 1388).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1388, Integer.Sparse.eval]

theorem keyMoment1389 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1389) =
      Integer.Sparse.eval keyMomentRow1389 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1389).leftCharge (GramAssembly.key 1389).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2888) := by
    have ha : gramCharges (GramAssembly.key 1389).leftCharge (GramAssembly.key 1389).rightCharge = raw40811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40811 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1389).leftCharge (GramAssembly.key 1389).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1389, Integer.Sparse.eval]

theorem keyMoment1390 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1390) =
      Integer.Sparse.eval keyMomentRow1390 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1390).leftCharge (GramAssembly.key 1390).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1390).leftCharge (GramAssembly.key 1390).rightCharge = raw40812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40812 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1390).leftCharge (GramAssembly.key 1390).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1390, Integer.Sparse.eval]

theorem keyMoment1391 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1391) =
      Integer.Sparse.eval keyMomentRow1391 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1391).leftCharge (GramAssembly.key 1391).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2885) := by
    have ha : gramCharges (GramAssembly.key 1391).leftCharge (GramAssembly.key 1391).rightCharge = raw40813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40813 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1391).leftCharge (GramAssembly.key 1391).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1391, Integer.Sparse.eval]

theorem keyMoment1392 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1392) =
      Integer.Sparse.eval keyMomentRow1392 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1392).leftCharge (GramAssembly.key 1392).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3733) := by
    have ha : gramCharges (GramAssembly.key 1392).leftCharge (GramAssembly.key 1392).rightCharge = raw40814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40814 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1392).leftCharge (GramAssembly.key 1392).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1392, Integer.Sparse.eval]

theorem keyMoment1393 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1393) =
      Integer.Sparse.eval keyMomentRow1393 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1393).leftCharge (GramAssembly.key 1393).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2867) := by
    have ha : gramCharges (GramAssembly.key 1393).leftCharge (GramAssembly.key 1393).rightCharge = raw40815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40815 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1393).leftCharge (GramAssembly.key 1393).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1393, Integer.Sparse.eval]

theorem keyMoment1394 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1394) =
      Integer.Sparse.eval keyMomentRow1394 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1394).leftCharge (GramAssembly.key 1394).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3949) := by
    have ha : gramCharges (GramAssembly.key 1394).leftCharge (GramAssembly.key 1394).rightCharge = raw40816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40816 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1394).leftCharge (GramAssembly.key 1394).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1394, Integer.Sparse.eval]

theorem keyMoment1395 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1395) =
      Integer.Sparse.eval keyMomentRow1395 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1395).leftCharge (GramAssembly.key 1395).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2864) := by
    have ha : gramCharges (GramAssembly.key 1395).leftCharge (GramAssembly.key 1395).rightCharge = raw40817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40817 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1395).leftCharge (GramAssembly.key 1395).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1395, Integer.Sparse.eval]

theorem keyMoment1396 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1396) =
      Integer.Sparse.eval keyMomentRow1396 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1396).leftCharge (GramAssembly.key 1396).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3946) := by
    have ha : gramCharges (GramAssembly.key 1396).leftCharge (GramAssembly.key 1396).rightCharge = raw40818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40818 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1396).leftCharge (GramAssembly.key 1396).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1396, Integer.Sparse.eval]

theorem keyMoment1397 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1397) =
      Integer.Sparse.eval keyMomentRow1397 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1397).leftCharge (GramAssembly.key 1397).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3954) := by
    have ha : gramCharges (GramAssembly.key 1397).leftCharge (GramAssembly.key 1397).rightCharge = raw40819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40819 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1397).leftCharge (GramAssembly.key 1397).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1397, Integer.Sparse.eval]

theorem keyMoment1398 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1398) =
      Integer.Sparse.eval keyMomentRow1398 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1398).leftCharge (GramAssembly.key 1398).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3720) := by
    have ha : gramCharges (GramAssembly.key 1398).leftCharge (GramAssembly.key 1398).rightCharge = raw40820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40820 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1398).leftCharge (GramAssembly.key 1398).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1398, Integer.Sparse.eval]

theorem keyMoment1399 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1399) =
      Integer.Sparse.eval keyMomentRow1399 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1399).leftCharge (GramAssembly.key 1399).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2279) := by
    have ha : gramCharges (GramAssembly.key 1399).leftCharge (GramAssembly.key 1399).rightCharge = raw40821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40821 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1399).leftCharge (GramAssembly.key 1399).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1399, Integer.Sparse.eval]

theorem keyMoment1400 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1400) =
      Integer.Sparse.eval keyMomentRow1400 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1400).leftCharge (GramAssembly.key 1400).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 1400).leftCharge (GramAssembly.key 1400).rightCharge = raw40822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40822 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1400).leftCharge (GramAssembly.key 1400).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1400, Integer.Sparse.eval]

theorem keyMoment1401 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1401) =
      Integer.Sparse.eval keyMomentRow1401 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1401).leftCharge (GramAssembly.key 1401).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3045) := by
    have ha : gramCharges (GramAssembly.key 1401).leftCharge (GramAssembly.key 1401).rightCharge = raw40823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40823 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1401).leftCharge (GramAssembly.key 1401).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1401, Integer.Sparse.eval]

theorem keyMoment1402 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1402) =
      Integer.Sparse.eval keyMomentRow1402 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1402).leftCharge (GramAssembly.key 1402).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1402).leftCharge (GramAssembly.key 1402).rightCharge = raw40824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40824 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1402).leftCharge (GramAssembly.key 1402).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1402, Integer.Sparse.eval]

theorem keyMoment1403 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1403) =
      Integer.Sparse.eval keyMomentRow1403 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1403).leftCharge (GramAssembly.key 1403).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3814) := by
    have ha : gramCharges (GramAssembly.key 1403).leftCharge (GramAssembly.key 1403).rightCharge = raw40825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40825 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1403).leftCharge (GramAssembly.key 1403).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1403, Integer.Sparse.eval]

theorem keyMoment1404 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1404) =
      Integer.Sparse.eval keyMomentRow1404 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1404).leftCharge (GramAssembly.key 1404).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3877) := by
    have ha : gramCharges (GramAssembly.key 1404).leftCharge (GramAssembly.key 1404).rightCharge = raw40826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40826 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1404).leftCharge (GramAssembly.key 1404).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1404, Integer.Sparse.eval]

theorem keyMoment1405 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1405) =
      Integer.Sparse.eval keyMomentRow1405 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1405).leftCharge (GramAssembly.key 1405).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3379) := by
    have ha : gramCharges (GramAssembly.key 1405).leftCharge (GramAssembly.key 1405).rightCharge = raw40827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40827 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1405).leftCharge (GramAssembly.key 1405).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1405, Integer.Sparse.eval]

theorem keyMoment1406 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1406) =
      Integer.Sparse.eval keyMomentRow1406 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1406).leftCharge (GramAssembly.key 1406).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3069) := by
    have ha : gramCharges (GramAssembly.key 1406).leftCharge (GramAssembly.key 1406).rightCharge = raw40828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40828 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1406).leftCharge (GramAssembly.key 1406).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1406, Integer.Sparse.eval]

theorem keyMoment1407 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1407) =
      Integer.Sparse.eval keyMomentRow1407 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1407).leftCharge (GramAssembly.key 1407).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3841) := by
    have ha : gramCharges (GramAssembly.key 1407).leftCharge (GramAssembly.key 1407).rightCharge = raw40829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40829 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1407).leftCharge (GramAssembly.key 1407).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1407, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1376 : keyMomentRows (1376 : Fin 2886) =
    keyMomentRow1376 := by decide +kernel

theorem keyMomentRowsAt1377 : keyMomentRows (1377 : Fin 2886) =
    keyMomentRow1377 := by decide +kernel

theorem keyMomentRowsAt1378 : keyMomentRows (1378 : Fin 2886) =
    keyMomentRow1378 := by decide +kernel

theorem keyMomentRowsAt1379 : keyMomentRows (1379 : Fin 2886) =
    keyMomentRow1379 := by decide +kernel

theorem keyMomentRowsAt1380 : keyMomentRows (1380 : Fin 2886) =
    keyMomentRow1380 := by decide +kernel

theorem keyMomentRowsAt1381 : keyMomentRows (1381 : Fin 2886) =
    keyMomentRow1381 := by decide +kernel

theorem keyMomentRowsAt1382 : keyMomentRows (1382 : Fin 2886) =
    keyMomentRow1382 := by decide +kernel

theorem keyMomentRowsAt1383 : keyMomentRows (1383 : Fin 2886) =
    keyMomentRow1383 := by decide +kernel

theorem keyMomentRowsAt1384 : keyMomentRows (1384 : Fin 2886) =
    keyMomentRow1384 := by decide +kernel

theorem keyMomentRowsAt1385 : keyMomentRows (1385 : Fin 2886) =
    keyMomentRow1385 := by decide +kernel

theorem keyMomentRowsAt1386 : keyMomentRows (1386 : Fin 2886) =
    keyMomentRow1386 := by decide +kernel

theorem keyMomentRowsAt1387 : keyMomentRows (1387 : Fin 2886) =
    keyMomentRow1387 := by decide +kernel

theorem keyMomentRowsAt1388 : keyMomentRows (1388 : Fin 2886) =
    keyMomentRow1388 := by decide +kernel

theorem keyMomentRowsAt1389 : keyMomentRows (1389 : Fin 2886) =
    keyMomentRow1389 := by decide +kernel

theorem keyMomentRowsAt1390 : keyMomentRows (1390 : Fin 2886) =
    keyMomentRow1390 := by decide +kernel

theorem keyMomentRowsAt1391 : keyMomentRows (1391 : Fin 2886) =
    keyMomentRow1391 := by decide +kernel

theorem keyMomentRowsAt1392 : keyMomentRows (1392 : Fin 2886) =
    keyMomentRow1392 := by decide +kernel

theorem keyMomentRowsAt1393 : keyMomentRows (1393 : Fin 2886) =
    keyMomentRow1393 := by decide +kernel

theorem keyMomentRowsAt1394 : keyMomentRows (1394 : Fin 2886) =
    keyMomentRow1394 := by decide +kernel

theorem keyMomentRowsAt1395 : keyMomentRows (1395 : Fin 2886) =
    keyMomentRow1395 := by decide +kernel

theorem keyMomentRowsAt1396 : keyMomentRows (1396 : Fin 2886) =
    keyMomentRow1396 := by decide +kernel

theorem keyMomentRowsAt1397 : keyMomentRows (1397 : Fin 2886) =
    keyMomentRow1397 := by decide +kernel

theorem keyMomentRowsAt1398 : keyMomentRows (1398 : Fin 2886) =
    keyMomentRow1398 := by decide +kernel

theorem keyMomentRowsAt1399 : keyMomentRows (1399 : Fin 2886) =
    keyMomentRow1399 := by decide +kernel

theorem keyMomentRowsAt1400 : keyMomentRows (1400 : Fin 2886) =
    keyMomentRow1400 := by decide +kernel

theorem keyMomentRowsAt1401 : keyMomentRows (1401 : Fin 2886) =
    keyMomentRow1401 := by decide +kernel

theorem keyMomentRowsAt1402 : keyMomentRows (1402 : Fin 2886) =
    keyMomentRow1402 := by decide +kernel

theorem keyMomentRowsAt1403 : keyMomentRows (1403 : Fin 2886) =
    keyMomentRow1403 := by decide +kernel

theorem keyMomentRowsAt1404 : keyMomentRows (1404 : Fin 2886) =
    keyMomentRow1404 := by decide +kernel

theorem keyMomentRowsAt1405 : keyMomentRows (1405 : Fin 2886) =
    keyMomentRow1405 := by decide +kernel

theorem keyMomentRowsAt1406 : keyMomentRows (1406 : Fin 2886) =
    keyMomentRow1406 := by decide +kernel

theorem keyMomentRowsAt1407 : keyMomentRows (1407 : Fin 2886) =
    keyMomentRow1407 := by decide +kernel

theorem keyMomentChunkSound43_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 43) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1376 ∨ k.val = 1377 ∨ k.val = 1378 ∨ k.val = 1379 ∨ k.val = 1380 ∨ k.val = 1381 ∨ k.val = 1382 ∨ k.val = 1383 ∨ k.val = 1384 ∨ k.val = 1385 ∨ k.val = 1386 ∨ k.val = 1387 ∨ k.val = 1388 ∨ k.val = 1389 ∨ k.val = 1390 ∨ k.val = 1391 ∨ k.val = 1392 ∨ k.val = 1393 ∨ k.val = 1394 ∨ k.val = 1395 ∨ k.val = 1396 ∨ k.val = 1397 ∨ k.val = 1398 ∨ k.val = 1399 ∨ k.val = 1400 ∨ k.val = 1401 ∨ k.val = 1402 ∨ k.val = 1403 ∨ k.val = 1404 ∨ k.val = 1405 ∨ k.val = 1406 ∨ k.val = 1407 := by omega
  rcases heq with h1376 | h1377 | h1378 | h1379 | h1380 | h1381 | h1382 | h1383 | h1384 | h1385 | h1386 | h1387 | h1388 | h1389 | h1390 | h1391 | h1392 | h1393 | h1394 | h1395 | h1396 | h1397 | h1398 | h1399 | h1400 | h1401 | h1402 | h1403 | h1404 | h1405 | h1406 | h1407
  · have he : k = (1376 : Fin 2886) := Fin.ext h1376
    subst k
    rw [keyMomentRowsAt1376]
    exact keyMoment1376 B hB
  · have he : k = (1377 : Fin 2886) := Fin.ext h1377
    subst k
    rw [keyMomentRowsAt1377]
    exact keyMoment1377 B hB
  · have he : k = (1378 : Fin 2886) := Fin.ext h1378
    subst k
    rw [keyMomentRowsAt1378]
    exact keyMoment1378 B hB
  · have he : k = (1379 : Fin 2886) := Fin.ext h1379
    subst k
    rw [keyMomentRowsAt1379]
    exact keyMoment1379 B hB
  · have he : k = (1380 : Fin 2886) := Fin.ext h1380
    subst k
    rw [keyMomentRowsAt1380]
    exact keyMoment1380 B hB
  · have he : k = (1381 : Fin 2886) := Fin.ext h1381
    subst k
    rw [keyMomentRowsAt1381]
    exact keyMoment1381 B hB
  · have he : k = (1382 : Fin 2886) := Fin.ext h1382
    subst k
    rw [keyMomentRowsAt1382]
    exact keyMoment1382 B hB
  · have he : k = (1383 : Fin 2886) := Fin.ext h1383
    subst k
    rw [keyMomentRowsAt1383]
    exact keyMoment1383 B hB
  · have he : k = (1384 : Fin 2886) := Fin.ext h1384
    subst k
    rw [keyMomentRowsAt1384]
    exact keyMoment1384 B hB
  · have he : k = (1385 : Fin 2886) := Fin.ext h1385
    subst k
    rw [keyMomentRowsAt1385]
    exact keyMoment1385 B hB
  · have he : k = (1386 : Fin 2886) := Fin.ext h1386
    subst k
    rw [keyMomentRowsAt1386]
    exact keyMoment1386 B hB
  · have he : k = (1387 : Fin 2886) := Fin.ext h1387
    subst k
    rw [keyMomentRowsAt1387]
    exact keyMoment1387 B hB
  · have he : k = (1388 : Fin 2886) := Fin.ext h1388
    subst k
    rw [keyMomentRowsAt1388]
    exact keyMoment1388 B hB
  · have he : k = (1389 : Fin 2886) := Fin.ext h1389
    subst k
    rw [keyMomentRowsAt1389]
    exact keyMoment1389 B hB
  · have he : k = (1390 : Fin 2886) := Fin.ext h1390
    subst k
    rw [keyMomentRowsAt1390]
    exact keyMoment1390 B hB
  · have he : k = (1391 : Fin 2886) := Fin.ext h1391
    subst k
    rw [keyMomentRowsAt1391]
    exact keyMoment1391 B hB
  · have he : k = (1392 : Fin 2886) := Fin.ext h1392
    subst k
    rw [keyMomentRowsAt1392]
    exact keyMoment1392 B hB
  · have he : k = (1393 : Fin 2886) := Fin.ext h1393
    subst k
    rw [keyMomentRowsAt1393]
    exact keyMoment1393 B hB
  · have he : k = (1394 : Fin 2886) := Fin.ext h1394
    subst k
    rw [keyMomentRowsAt1394]
    exact keyMoment1394 B hB
  · have he : k = (1395 : Fin 2886) := Fin.ext h1395
    subst k
    rw [keyMomentRowsAt1395]
    exact keyMoment1395 B hB
  · have he : k = (1396 : Fin 2886) := Fin.ext h1396
    subst k
    rw [keyMomentRowsAt1396]
    exact keyMoment1396 B hB
  · have he : k = (1397 : Fin 2886) := Fin.ext h1397
    subst k
    rw [keyMomentRowsAt1397]
    exact keyMoment1397 B hB
  · have he : k = (1398 : Fin 2886) := Fin.ext h1398
    subst k
    rw [keyMomentRowsAt1398]
    exact keyMoment1398 B hB
  · have he : k = (1399 : Fin 2886) := Fin.ext h1399
    subst k
    rw [keyMomentRowsAt1399]
    exact keyMoment1399 B hB
  · have he : k = (1400 : Fin 2886) := Fin.ext h1400
    subst k
    rw [keyMomentRowsAt1400]
    exact keyMoment1400 B hB
  · have he : k = (1401 : Fin 2886) := Fin.ext h1401
    subst k
    rw [keyMomentRowsAt1401]
    exact keyMoment1401 B hB
  · have he : k = (1402 : Fin 2886) := Fin.ext h1402
    subst k
    rw [keyMomentRowsAt1402]
    exact keyMoment1402 B hB
  · have he : k = (1403 : Fin 2886) := Fin.ext h1403
    subst k
    rw [keyMomentRowsAt1403]
    exact keyMoment1403 B hB
  · have he : k = (1404 : Fin 2886) := Fin.ext h1404
    subst k
    rw [keyMomentRowsAt1404]
    exact keyMoment1404 B hB
  · have he : k = (1405 : Fin 2886) := Fin.ext h1405
    subst k
    rw [keyMomentRowsAt1405]
    exact keyMoment1405 B hB
  · have he : k = (1406 : Fin 2886) := Fin.ext h1406
    subst k
    rw [keyMomentRowsAt1406]
    exact keyMoment1406 B hB
  · have he : k = (1407 : Fin 2886) := Fin.ext h1407
    subst k
    rw [keyMomentRowsAt1407]
    exact keyMoment1407 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound43_e_oai
