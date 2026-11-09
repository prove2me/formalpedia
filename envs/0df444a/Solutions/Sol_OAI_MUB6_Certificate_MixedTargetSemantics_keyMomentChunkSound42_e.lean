-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:55:07.630469+00:00
-- url     : https://prove2.me/submissions/8fee17da-0021-4735-9e18-60d2d3fa5e1a

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E111
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40768 raw40768Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw40768 raw40768Labels = mixedMoment B raw40768step0 raw40768step0Labels := by
      have ha : raw40768step0 = (fun i j => raw40768 (permutation446 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40768step0 raw40768; decide +kernel
      have hl : raw40768step0Labels = raw40768Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40768 raw40768Labels permutation446 permutation6
    mixedMoment B raw40768step0 raw40768step0Labels = mixedMoment B raw40768step1 raw40768step1Labels := by
      have ha : raw40768step1 = -raw40768step0 := by apply Matrix.ext; change ∀ i j, raw40768step1 i j = -(raw40768step0 i j); unfold raw40768step1 raw40768step0; decide +kernel
      have hl : raw40768step1Labels = raw40768step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2105 node2105Labels := by rfl

theorem canonical40769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40769 raw40769Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw40769 raw40769Labels = mixedMoment B raw40769step0 raw40769step0Labels := by
      have hz : ∀ j, raw40769 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40769step0 = (fun i j => raw40769 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40769step0 raw40769; decide +kernel
      have hl : raw40769step0Labels = raw40769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40769 raw40769Labels permutation434 hz
    mixedMoment B raw40769step0 raw40769step0Labels = mixedMoment B raw40769step1 raw40769step1Labels := by
      have hz : ∀ j, raw40769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40769step1 = (fun i j => raw40769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40769step1 raw40769step0; decide +kernel
      have hl : raw40769step1Labels = raw40769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40769step0 raw40769step0Labels permutation80 hz
    mixedMoment B raw40769step1 raw40769step1Labels = mixedMoment B raw40769step2 raw40769step2Labels := by
      have ha : raw40769step2 = (fun i j => raw40769step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40769step2 raw40769step1; decide +kernel
      have hl : raw40769step2Labels = raw40769step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40769step1 raw40769step1Labels permutation20 permutation6
    mixedMoment B raw40769step2 raw40769step2Labels = mixedMoment B raw40769step3 raw40769step3Labels := by
      have ha : raw40769step3 = -raw40769step2 := by apply Matrix.ext; change ∀ i j, raw40769step3 i j = -(raw40769step2 i j); unfold raw40769step3 raw40769step2; decide +kernel
      have hl : raw40769step3Labels = raw40769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2112 node2112Labels := by rfl

theorem canonical40770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40770 raw40770Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw40770 raw40770Labels = mixedMoment B raw40770step0 raw40770step0Labels := by
      have hz : ∀ j, raw40770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40770step0 = (fun i j => raw40770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40770step0 raw40770; decide +kernel
      have hl : raw40770step0Labels = raw40770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40770 raw40770Labels permutation346 hz
    mixedMoment B raw40770step0 raw40770step0Labels = mixedMoment B raw40770step1 raw40770step1Labels := by
      have ha : raw40770step1 = (fun i j => raw40770step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40770step1 raw40770step0; decide +kernel
      have hl : raw40770step1Labels = raw40770step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40770step0 raw40770step0Labels permutation134 permutation6
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical40771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40771 raw40771Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw40771 raw40771Labels = mixedMoment B raw40771step0 raw40771step0Labels := by
      have hz : ∀ j, raw40771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40771step0 = (fun i j => raw40771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40771step0 raw40771; decide +kernel
      have hl : raw40771step0Labels = raw40771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40771 raw40771Labels permutation346 hz
    mixedMoment B raw40771step0 raw40771step0Labels = mixedMoment B raw40771step1 raw40771step1Labels := by
      have ha : raw40771step1 = (fun i j => raw40771step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40771step1 raw40771step0; decide +kernel
      have hl : raw40771step1Labels = raw40771step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40771step0 raw40771step0Labels permutation84 permutation6
    mixedMoment B raw40771step1 raw40771step1Labels = mixedMoment B raw40771step2 raw40771step2Labels := by
      have ha : raw40771step2 = -raw40771step1 := by apply Matrix.ext; change ∀ i j, raw40771step2 i j = -(raw40771step1 i j); unfold raw40771step2 raw40771step1; decide +kernel
      have hl : raw40771step2Labels = raw40771step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

theorem canonical40772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40772 raw40772Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw40772 raw40772Labels = mixedMoment B raw40772step0 raw40772step0Labels := by
      have ha : raw40772step0 = (fun i j => raw40772 (permutation469 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40772step0 raw40772; decide +kernel
      have hl : raw40772step0Labels = raw40772Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40772 raw40772Labels permutation469 permutation6
    mixedMoment B raw40772step0 raw40772step0Labels = mixedMoment B raw40772step1 raw40772step1Labels := by
      have ha : raw40772step1 = -raw40772step0 := by apply Matrix.ext; change ∀ i j, raw40772step1 i j = -(raw40772step0 i j); unfold raw40772step1 raw40772step0; decide +kernel
      have hl : raw40772step1Labels = raw40772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical40773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40773 raw40773Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw40773 raw40773Labels = mixedMoment B raw40773step0 raw40773step0Labels := by
      have hz : ∀ j, raw40773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40773step0 = (fun i j => raw40773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40773step0 raw40773; decide +kernel
      have hl : raw40773step0Labels = raw40773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40773 raw40773Labels permutation434 hz
    mixedMoment B raw40773step0 raw40773step0Labels = mixedMoment B raw40773step1 raw40773step1Labels := by
      have hz : ∀ j, raw40773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40773step1 = (fun i j => raw40773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40773step1 raw40773step0; decide +kernel
      have hl : raw40773step1Labels = raw40773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40773step0 raw40773step0Labels permutation80 hz
    mixedMoment B raw40773step1 raw40773step1Labels = mixedMoment B raw40773step2 raw40773step2Labels := by
      have hz : ∀ j, raw40773step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40773step2 = (fun i j => raw40773step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40773step2 raw40773step1; decide +kernel
      have hl : raw40773step2Labels = raw40773step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40773step1 raw40773step1Labels permutation14 hz
    mixedMoment B raw40773step2 raw40773step2Labels = mixedMoment B raw40773step3 raw40773step3Labels := by
      have ha : raw40773step3 = (fun i j => raw40773step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40773step3 raw40773step2; decide +kernel
      have hl : raw40773step3Labels = raw40773step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40773step2 raw40773step2Labels permutation6 permutation6
    _ = mixedMoment B node1297 node1297Labels := by rfl

theorem canonical40774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40774 raw40774Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw40774 raw40774Labels = mixedMoment B raw40774step0 raw40774step0Labels := by
      have hz : ∀ j, raw40774 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40774step0 = (fun i j => raw40774 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40774step0 raw40774; decide +kernel
      have hl : raw40774step0Labels = raw40774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40774 raw40774Labels permutation434 hz
    mixedMoment B raw40774step0 raw40774step0Labels = mixedMoment B raw40774step1 raw40774step1Labels := by
      have hz : ∀ j, raw40774step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40774step1 = (fun i j => raw40774step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40774step1 raw40774step0; decide +kernel
      have hl : raw40774step1Labels = raw40774step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40774step0 raw40774step0Labels permutation80 hz
    mixedMoment B raw40774step1 raw40774step1Labels = mixedMoment B raw40774step2 raw40774step2Labels := by
      have hz : ∀ j, raw40774step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40774step2 = (fun i j => raw40774step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40774step2 raw40774step1; decide +kernel
      have hl : raw40774step2Labels = raw40774step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40774step1 raw40774step1Labels permutation14 hz
    mixedMoment B raw40774step2 raw40774step2Labels = mixedMoment B raw40774step3 raw40774step3Labels := by
      have ha : raw40774step3 = (fun i j => raw40774step2 (permutation4 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40774step3 raw40774step2; decide +kernel
      have hl : raw40774step3Labels = raw40774step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40774step2 raw40774step2Labels permutation4 permutation6
    _ = mixedMoment B node2783 node2783Labels := by rfl

theorem canonical40775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40775 raw40775Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw40775 raw40775Labels = mixedMoment B raw40775step0 raw40775step0Labels := by
      have hz : ∀ j, raw40775 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40775step0 = (fun i j => raw40775 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40775step0 raw40775; decide +kernel
      have hl : raw40775step0Labels = raw40775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40775 raw40775Labels permutation346 hz
    mixedMoment B raw40775step0 raw40775step0Labels = mixedMoment B raw40775step1 raw40775step1Labels := by
      have hz : ∀ j, raw40775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40775step1 = (fun i j => raw40775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40775step1 raw40775step0; decide +kernel
      have hl : raw40775step1Labels = raw40775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40775step0 raw40775step0Labels permutation56 hz
    mixedMoment B raw40775step1 raw40775step1Labels = mixedMoment B raw40775step2 raw40775step2Labels := by
      have ha : raw40775step2 = (fun i j => raw40775step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40775step2 raw40775step1; decide +kernel
      have hl : raw40775step2Labels = raw40775step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40775step1 raw40775step1Labels permutation26 permutation6
    _ = mixedMoment B node1294 node1294Labels := by rfl

theorem canonical40776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40776 raw40776Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw40776 raw40776Labels = mixedMoment B raw40776step0 raw40776step0Labels := by
      have hz : ∀ j, raw40776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40776step0 = (fun i j => raw40776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40776step0 raw40776; decide +kernel
      have hl : raw40776step0Labels = raw40776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40776 raw40776Labels permutation346 hz
    mixedMoment B raw40776step0 raw40776step0Labels = mixedMoment B raw40776step1 raw40776step1Labels := by
      have hz : ∀ j, raw40776step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40776step1 = (fun i j => raw40776step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40776step1 raw40776step0; decide +kernel
      have hl : raw40776step1Labels = raw40776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40776step0 raw40776step0Labels permutation56 hz
    mixedMoment B raw40776step1 raw40776step1Labels = mixedMoment B raw40776step2 raw40776step2Labels := by
      have ha : raw40776step2 = (fun i j => raw40776step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40776step2 raw40776step1; decide +kernel
      have hl : raw40776step2Labels = raw40776step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40776step1 raw40776step1Labels permutation20 permutation6
    _ = mixedMoment B node2782 node2782Labels := by rfl

theorem canonical40777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40777 raw40777Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw40777 raw40777Labels = mixedMoment B raw40777step0 raw40777step0Labels := by
      have hz : ∀ j, raw40777 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40777step0 = (fun i j => raw40777 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40777step0 raw40777; decide +kernel
      have hl : raw40777step0Labels = raw40777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40777 raw40777Labels permutation346 hz
    mixedMoment B raw40777step0 raw40777step0Labels = mixedMoment B raw40777step1 raw40777step1Labels := by
      have hz : ∀ j, raw40777step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40777step1 = (fun i j => raw40777step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40777step1 raw40777step0; decide +kernel
      have hl : raw40777step1Labels = raw40777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40777step0 raw40777step0Labels permutation56 hz
    mixedMoment B raw40777step1 raw40777step1Labels = mixedMoment B raw40777step2 raw40777step2Labels := by
      have ha : raw40777step2 = (fun i j => raw40777step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40777step2 raw40777step1; decide +kernel
      have hl : raw40777step2Labels = raw40777step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40777step1 raw40777step1Labels permutation24 permutation6
    _ = mixedMoment B node2765 node2765Labels := by rfl

theorem canonical40778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40778 raw40778Labels = mixedMoment B node2109 node2109Labels := by
  calc
    mixedMoment B raw40778 raw40778Labels = mixedMoment B raw40778step0 raw40778step0Labels := by
      have hz : ∀ j, raw40778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40778step0 = (fun i j => raw40778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40778step0 raw40778; decide +kernel
      have hl : raw40778step0Labels = raw40778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40778 raw40778Labels permutation346 hz
    mixedMoment B raw40778step0 raw40778step0Labels = mixedMoment B raw40778step1 raw40778step1Labels := by
      have hz : ∀ j, raw40778step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40778step1 = (fun i j => raw40778step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40778step1 raw40778step0; decide +kernel
      have hl : raw40778step1Labels = raw40778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40778step0 raw40778step0Labels permutation56 hz
    mixedMoment B raw40778step1 raw40778step1Labels = mixedMoment B raw40778step2 raw40778step2Labels := by
      have ha : raw40778step2 = (fun i j => raw40778step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40778step2 raw40778step1; decide +kernel
      have hl : raw40778step2Labels = raw40778step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40778step1 raw40778step1Labels permutation15 permutation6
    mixedMoment B raw40778step2 raw40778step2Labels = mixedMoment B raw40778step3 raw40778step3Labels := by
      have ha : raw40778step3 = -raw40778step2 := by apply Matrix.ext; change ∀ i j, raw40778step3 i j = -(raw40778step2 i j); unfold raw40778step3 raw40778step2; decide +kernel
      have hl : raw40778step3Labels = raw40778step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2109 node2109Labels := by rfl

theorem canonical40779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40779 raw40779Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw40779 raw40779Labels = mixedMoment B raw40779step0 raw40779step0Labels := by
      have hz : ∀ j, raw40779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40779step0 = (fun i j => raw40779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40779step0 raw40779; decide +kernel
      have hl : raw40779step0Labels = raw40779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40779 raw40779Labels permutation346 hz
    mixedMoment B raw40779step0 raw40779step0Labels = mixedMoment B raw40779step1 raw40779step1Labels := by
      have hz : ∀ j, raw40779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40779step1 = (fun i j => raw40779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40779step1 raw40779step0; decide +kernel
      have hl : raw40779step1Labels = raw40779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40779step0 raw40779step0Labels permutation56 hz
    mixedMoment B raw40779step1 raw40779step1Labels = mixedMoment B raw40779step2 raw40779step2Labels := by
      have ha : raw40779step2 = (fun i j => raw40779step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40779step2 raw40779step1; decide +kernel
      have hl : raw40779step2Labels = raw40779step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40779step1 raw40779step1Labels permutation14 permutation6
    mixedMoment B raw40779step2 raw40779step2Labels = mixedMoment B raw40779step3 raw40779step3Labels := by
      have ha : raw40779step3 = -raw40779step2 := by apply Matrix.ext; change ∀ i j, raw40779step3 i j = -(raw40779step2 i j); unfold raw40779step3 raw40779step2; decide +kernel
      have hl : raw40779step3Labels = raw40779step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2116 node2116Labels := by rfl

theorem canonical40780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40780 raw40780Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw40780 raw40780Labels = mixedMoment B raw40780step0 raw40780step0Labels := by
      have hz : ∀ j, raw40780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40780step0 = (fun i j => raw40780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40780step0 raw40780; decide +kernel
      have hl : raw40780step0Labels = raw40780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40780 raw40780Labels permutation265 hz
    mixedMoment B raw40780step0 raw40780step0Labels = mixedMoment B raw40780step1 raw40780step1Labels := by
      have ha : raw40780step1 = (fun i j => raw40780step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40780step1 raw40780step0; decide +kernel
      have hl : raw40780step1Labels = raw40780step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40780step0 raw40780step0Labels permutation122 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

theorem canonical40781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40781 raw40781Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw40781 raw40781Labels = mixedMoment B raw40781step0 raw40781step0Labels := by
      have hz : ∀ j, raw40781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40781step0 = (fun i j => raw40781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40781step0 raw40781; decide +kernel
      have hl : raw40781step0Labels = raw40781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40781 raw40781Labels permutation265 hz
    mixedMoment B raw40781step0 raw40781step0Labels = mixedMoment B raw40781step1 raw40781step1Labels := by
      have ha : raw40781step1 = (fun i j => raw40781step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40781step1 raw40781step0; decide +kernel
      have hl : raw40781step1Labels = raw40781step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40781step0 raw40781step0Labels permutation122 permutation6
    _ = mixedMoment B node2590 node2590Labels := by rfl

theorem canonical40782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40782 raw40782Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw40782 raw40782Labels = mixedMoment B raw40782step0 raw40782step0Labels := by
      have ha : raw40782step0 = (fun i j => raw40782 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40782step0 raw40782; decide +kernel
      have hl : raw40782step0Labels = raw40782Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40782 raw40782Labels permutation569 permutation6
    _ = mixedMoment B node2589 node2589Labels := by rfl

theorem canonical40783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40783 raw40783Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40783 raw40783Labels = mixedMoment B raw40783step0 raw40783step0Labels := by
      have hz : ∀ j, raw40783 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40783step0 = (fun i j => raw40783 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40783step0 raw40783; decide +kernel
      have hl : raw40783step0Labels = raw40783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40783 raw40783Labels permutation520 hz
    mixedMoment B raw40783step0 raw40783step0Labels = mixedMoment B raw40783step1 raw40783step1Labels := by
      have hz : ∀ j, raw40783step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40783step1 = (fun i j => raw40783step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40783step1 raw40783step0; decide +kernel
      have hl : raw40783step1Labels = raw40783step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40783step0 raw40783step0Labels permutation104 hz
    mixedMoment B raw40783step1 raw40783step1Labels = mixedMoment B raw40783step2 raw40783step2Labels := by
      have hz : ∀ j, raw40783step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40783step2 = (fun i j => raw40783step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40783step2 raw40783step1; decide +kernel
      have hl : raw40783step2Labels = raw40783step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40783step1 raw40783step1Labels permutation20 hz
    mixedMoment B raw40783step2 raw40783step2Labels = mixedMoment B raw40783step3 raw40783step3Labels := by
      have ha : raw40783step3 = (fun i j => raw40783step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40783step3 raw40783step2; decide +kernel
      have hl : raw40783step3Labels = raw40783step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40783step2 raw40783step2Labels permutation7 permutation3
    mixedMoment B raw40783step3 raw40783step3Labels = mixedMoment B raw40783step4 raw40783step4Labels := by
      have ha : raw40783step4 = -raw40783step3 := by apply Matrix.ext; change ∀ i j, raw40783step4 i j = -(raw40783step3 i j); unfold raw40783step4 raw40783step3; decide +kernel
      have hl : raw40783step4Labels = raw40783step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

theorem canonical40784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40784 raw40784Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw40784 raw40784Labels = mixedMoment B raw40784step0 raw40784step0Labels := by
      have hz : ∀ j, raw40784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40784step0 = (fun i j => raw40784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40784step0 raw40784; decide +kernel
      have hl : raw40784step0Labels = raw40784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40784 raw40784Labels permutation434 hz
    mixedMoment B raw40784step0 raw40784step0Labels = mixedMoment B raw40784step1 raw40784step1Labels := by
      have hz : ∀ j, raw40784step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40784step1 = (fun i j => raw40784step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40784step1 raw40784step0; decide +kernel
      have hl : raw40784step1Labels = raw40784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40784step0 raw40784step0Labels permutation80 hz
    mixedMoment B raw40784step1 raw40784step1Labels = mixedMoment B raw40784step2 raw40784step2Labels := by
      have ha : raw40784step2 = (fun i j => raw40784step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40784step2 raw40784step1; decide +kernel
      have hl : raw40784step2Labels = raw40784step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40784step1 raw40784step1Labels permutation31 permutation3
    mixedMoment B raw40784step2 raw40784step2Labels = mixedMoment B raw40784step3 raw40784step3Labels := by
      have ha : raw40784step3 = -raw40784step2 := by apply Matrix.ext; change ∀ i j, raw40784step3 i j = -(raw40784step2 i j); unfold raw40784step3 raw40784step2; decide +kernel
      have hl : raw40784step3Labels = raw40784step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2744 node2744Labels := by rfl

theorem canonical40785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40785 raw40785Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw40785 raw40785Labels = mixedMoment B raw40785step0 raw40785step0Labels := by
      have hz : ∀ j, raw40785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40785step0 = (fun i j => raw40785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40785step0 raw40785; decide +kernel
      have hl : raw40785step0Labels = raw40785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40785 raw40785Labels permutation434 hz
    mixedMoment B raw40785step0 raw40785step0Labels = mixedMoment B raw40785step1 raw40785step1Labels := by
      have hz : ∀ j, raw40785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40785step1 = (fun i j => raw40785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40785step1 raw40785step0; decide +kernel
      have hl : raw40785step1Labels = raw40785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40785step0 raw40785step0Labels permutation80 hz
    mixedMoment B raw40785step1 raw40785step1Labels = mixedMoment B raw40785step2 raw40785step2Labels := by
      have ha : raw40785step2 = (fun i j => raw40785step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40785step2 raw40785step1; decide +kernel
      have hl : raw40785step2Labels = raw40785step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40785step1 raw40785step1Labels permutation31 permutation3
    mixedMoment B raw40785step2 raw40785step2Labels = mixedMoment B raw40785step3 raw40785step3Labels := by
      have ha : raw40785step3 = -raw40785step2 := by apply Matrix.ext; change ∀ i j, raw40785step3 i j = -(raw40785step2 i j); unfold raw40785step3 raw40785step2; decide +kernel
      have hl : raw40785step3Labels = raw40785step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3056 node3056Labels := by rfl

theorem canonical40786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40786 raw40786Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40786 raw40786Labels = mixedMoment B raw40786step0 raw40786step0Labels := by
      have hz : ∀ j, raw40786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40786step0 = (fun i j => raw40786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40786step0 raw40786; decide +kernel
      have hl : raw40786step0Labels = raw40786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40786 raw40786Labels permutation434 hz
    mixedMoment B raw40786step0 raw40786step0Labels = mixedMoment B raw40786step1 raw40786step1Labels := by
      have hz : ∀ j, raw40786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40786step1 = (fun i j => raw40786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40786step1 raw40786step0; decide +kernel
      have hl : raw40786step1Labels = raw40786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40786step0 raw40786step0Labels permutation80 hz
    mixedMoment B raw40786step1 raw40786step1Labels = mixedMoment B raw40786step2 raw40786step2Labels := by
      have ha : raw40786step2 = (fun i j => raw40786step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40786step2 raw40786step1; decide +kernel
      have hl : raw40786step2Labels = raw40786step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40786step1 raw40786step1Labels permutation17 permutation6
    _ = mixedMoment B node3626 node3626Labels := by rfl

theorem canonical40787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40787 raw40787Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw40787 raw40787Labels = mixedMoment B raw40787step0 raw40787step0Labels := by
      have hz : ∀ j, raw40787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40787step0 = (fun i j => raw40787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40787step0 raw40787; decide +kernel
      have hl : raw40787step0Labels = raw40787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40787 raw40787Labels permutation434 hz
    mixedMoment B raw40787step0 raw40787step0Labels = mixedMoment B raw40787step1 raw40787step1Labels := by
      have hz : ∀ j, raw40787step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40787step1 = (fun i j => raw40787step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40787step1 raw40787step0; decide +kernel
      have hl : raw40787step1Labels = raw40787step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40787step0 raw40787step0Labels permutation80 hz
    mixedMoment B raw40787step1 raw40787step1Labels = mixedMoment B raw40787step2 raw40787step2Labels := by
      have ha : raw40787step2 = (fun i j => raw40787step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40787step2 raw40787step1; decide +kernel
      have hl : raw40787step2Labels = raw40787step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40787step1 raw40787step1Labels permutation19 permutation6
    _ = mixedMoment B node3584 node3584Labels := by rfl

theorem canonical40788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40788 raw40788Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw40788 raw40788Labels = mixedMoment B raw40788step0 raw40788step0Labels := by
      have hz : ∀ j, raw40788 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40788step0 = (fun i j => raw40788 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40788step0 raw40788; decide +kernel
      have hl : raw40788step0Labels = raw40788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40788 raw40788Labels permutation434 hz
    mixedMoment B raw40788step0 raw40788step0Labels = mixedMoment B raw40788step1 raw40788step1Labels := by
      have hz : ∀ j, raw40788step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40788step1 = (fun i j => raw40788step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40788step1 raw40788step0; decide +kernel
      have hl : raw40788step1Labels = raw40788step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40788step0 raw40788step0Labels permutation80 hz
    mixedMoment B raw40788step1 raw40788step1Labels = mixedMoment B raw40788step2 raw40788step2Labels := by
      have ha : raw40788step2 = (fun i j => raw40788step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40788step2 raw40788step1; decide +kernel
      have hl : raw40788step2Labels = raw40788step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40788step1 raw40788step1Labels permutation18 permutation6
    _ = mixedMoment B node3396 node3396Labels := by rfl

theorem canonical40789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40789 raw40789Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw40789 raw40789Labels = mixedMoment B raw40789step0 raw40789step0Labels := by
      have hz : ∀ j, raw40789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40789step0 = (fun i j => raw40789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40789step0 raw40789; decide +kernel
      have hl : raw40789step0Labels = raw40789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40789 raw40789Labels permutation346 hz
    mixedMoment B raw40789step0 raw40789step0Labels = mixedMoment B raw40789step1 raw40789step1Labels := by
      have ha : raw40789step1 = (fun i j => raw40789step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40789step1 raw40789step0; decide +kernel
      have hl : raw40789step1Labels = raw40789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40789step0 raw40789step0Labels permutation145 permutation3
    mixedMoment B raw40789step1 raw40789step1Labels = mixedMoment B raw40789step2 raw40789step2Labels := by
      have ha : raw40789step2 = -raw40789step1 := by apply Matrix.ext; change ∀ i j, raw40789step2 i j = -(raw40789step1 i j); unfold raw40789step2 raw40789step1; decide +kernel
      have hl : raw40789step2Labels = raw40789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3079 node3079Labels := by rfl

theorem canonical40790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40790 raw40790Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw40790 raw40790Labels = mixedMoment B raw40790step0 raw40790step0Labels := by
      have hz : ∀ j, raw40790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40790step0 = (fun i j => raw40790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40790step0 raw40790; decide +kernel
      have hl : raw40790step0Labels = raw40790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40790 raw40790Labels permutation346 hz
    mixedMoment B raw40790step0 raw40790step0Labels = mixedMoment B raw40790step1 raw40790step1Labels := by
      have ha : raw40790step1 = (fun i j => raw40790step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40790step1 raw40790step0; decide +kernel
      have hl : raw40790step1Labels = raw40790step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40790step0 raw40790step0Labels permutation73 permutation6
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical40791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40791 raw40791Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw40791 raw40791Labels = mixedMoment B raw40791step0 raw40791step0Labels := by
      have hz : ∀ j, raw40791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40791step0 = (fun i j => raw40791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40791step0 raw40791; decide +kernel
      have hl : raw40791step0Labels = raw40791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40791 raw40791Labels permutation346 hz
    mixedMoment B raw40791step0 raw40791step0Labels = mixedMoment B raw40791step1 raw40791step1Labels := by
      have ha : raw40791step1 = (fun i j => raw40791step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40791step1 raw40791step0; decide +kernel
      have hl : raw40791step1Labels = raw40791step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40791step0 raw40791step0Labels permutation79 permutation6
    _ = mixedMoment B node3573 node3573Labels := by rfl

theorem canonical40792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40792 raw40792Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw40792 raw40792Labels = mixedMoment B raw40792step0 raw40792step0Labels := by
      have hz : ∀ j, raw40792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40792step0 = (fun i j => raw40792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40792step0 raw40792; decide +kernel
      have hl : raw40792step0Labels = raw40792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40792 raw40792Labels permutation346 hz
    mixedMoment B raw40792step0 raw40792step0Labels = mixedMoment B raw40792step1 raw40792step1Labels := by
      have ha : raw40792step1 = (fun i j => raw40792step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40792step1 raw40792step0; decide +kernel
      have hl : raw40792step1Labels = raw40792step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40792step0 raw40792step0Labels permutation77 permutation6
    _ = mixedMoment B node3395 node3395Labels := by rfl

theorem canonical40793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40793 raw40793Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw40793 raw40793Labels = mixedMoment B raw40793step0 raw40793step0Labels := by
      have hz : ∀ j, raw40793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40793step0 = (fun i j => raw40793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40793step0 raw40793; decide +kernel
      have hl : raw40793step0Labels = raw40793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40793 raw40793Labels permutation346 hz
    mixedMoment B raw40793step0 raw40793step0Labels = mixedMoment B raw40793step1 raw40793step1Labels := by
      have ha : raw40793step1 = (fun i j => raw40793step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40793step1 raw40793step0; decide +kernel
      have hl : raw40793step1Labels = raw40793step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40793step0 raw40793step0Labels permutation72 permutation6
    _ = mixedMoment B node3506 node3506Labels := by rfl

theorem canonical40794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40794 raw40794Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw40794 raw40794Labels = mixedMoment B raw40794step0 raw40794step0Labels := by
      have hz : ∀ j, raw40794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40794step0 = (fun i j => raw40794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40794step0 raw40794; decide +kernel
      have hl : raw40794step0Labels = raw40794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40794 raw40794Labels permutation346 hz
    mixedMoment B raw40794step0 raw40794step0Labels = mixedMoment B raw40794step1 raw40794step1Labels := by
      have ha : raw40794step1 = (fun i j => raw40794step0 (permutation78 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40794step1 raw40794step0; decide +kernel
      have hl : raw40794step1Labels = raw40794step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40794step0 raw40794step0Labels permutation78 permutation6
    _ = mixedMoment B node3379 node3379Labels := by rfl

theorem canonical40795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40795 raw40795Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw40795 raw40795Labels = mixedMoment B raw40795step0 raw40795step0Labels := by
      have ha : raw40795step0 = (fun i j => raw40795 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40795step0 raw40795; decide +kernel
      have hl : raw40795step0Labels = raw40795Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40795 raw40795Labels permutation332 permutation6
    _ = mixedMoment B node3505 node3505Labels := by rfl

theorem canonical40796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40796 raw40796Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw40796 raw40796Labels = mixedMoment B raw40796step0 raw40796step0Labels := by
      have ha : raw40796step0 = (fun i j => raw40796 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40796step0 raw40796; decide +kernel
      have hl : raw40796step0Labels = raw40796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40796 raw40796Labels permutation345 permutation6
    _ = mixedMoment B node3378 node3378Labels := by rfl

theorem canonical40797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40797 raw40797Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw40797 raw40797Labels = mixedMoment B raw40797step0 raw40797step0Labels := by
      have hz : ∀ j, raw40797 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40797step0 = (fun i j => raw40797 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40797step0 raw40797; decide +kernel
      have hl : raw40797step0Labels = raw40797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40797 raw40797Labels permutation520 hz
    mixedMoment B raw40797step0 raw40797step0Labels = mixedMoment B raw40797step1 raw40797step1Labels := by
      have hz : ∀ j, raw40797step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40797step1 = (fun i j => raw40797step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40797step1 raw40797step0; decide +kernel
      have hl : raw40797step1Labels = raw40797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40797step0 raw40797step0Labels permutation104 hz
    mixedMoment B raw40797step1 raw40797step1Labels = mixedMoment B raw40797step2 raw40797step2Labels := by
      have ha : raw40797step2 = (fun i j => raw40797step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40797step2 raw40797step1; decide +kernel
      have hl : raw40797step2Labels = raw40797step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40797step1 raw40797step1Labels permutation31 permutation3
    mixedMoment B raw40797step2 raw40797step2Labels = mixedMoment B raw40797step3 raw40797step3Labels := by
      have ha : raw40797step3 = -raw40797step2 := by apply Matrix.ext; change ∀ i j, raw40797step3 i j = -(raw40797step2 i j); unfold raw40797step3 raw40797step2; decide +kernel
      have hl : raw40797step3Labels = raw40797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

theorem canonical40798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40798 raw40798Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw40798 raw40798Labels = mixedMoment B raw40798step0 raw40798step0Labels := by
      have hz : ∀ j, raw40798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40798step0 = (fun i j => raw40798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40798step0 raw40798; decide +kernel
      have hl : raw40798step0Labels = raw40798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40798 raw40798Labels permutation434 hz
    mixedMoment B raw40798step0 raw40798step0Labels = mixedMoment B raw40798step1 raw40798step1Labels := by
      have ha : raw40798step1 = (fun i j => raw40798step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40798step1 raw40798step0; decide +kernel
      have hl : raw40798step1Labels = raw40798step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40798step0 raw40798step0Labels permutation151 permutation3
    mixedMoment B raw40798step1 raw40798step1Labels = mixedMoment B raw40798step2 raw40798step2Labels := by
      have ha : raw40798step2 = -raw40798step1 := by apply Matrix.ext; change ∀ i j, raw40798step2 i j = -(raw40798step1 i j); unfold raw40798step2 raw40798step1; decide +kernel
      have hl : raw40798step2Labels = raw40798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical40799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40799 raw40799Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw40799 raw40799Labels = mixedMoment B raw40799step0 raw40799step0Labels := by
      have hz : ∀ j, raw40799 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40799step0 = (fun i j => raw40799 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40799step0 raw40799; decide +kernel
      have hl : raw40799step0Labels = raw40799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40799 raw40799Labels permutation434 hz
    mixedMoment B raw40799step0 raw40799step0Labels = mixedMoment B raw40799step1 raw40799step1Labels := by
      have ha : raw40799step1 = (fun i j => raw40799step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40799step1 raw40799step0; decide +kernel
      have hl : raw40799step1Labels = raw40799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40799step0 raw40799step0Labels permutation151 permutation3
    mixedMoment B raw40799step1 raw40799step1Labels = mixedMoment B raw40799step2 raw40799step2Labels := by
      have ha : raw40799step2 = -raw40799step1 := by apply Matrix.ext; change ∀ i j, raw40799step2 i j = -(raw40799step1 i j); unfold raw40799step2 raw40799step1; decide +kernel
      have hl : raw40799step2Labels = raw40799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1344 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1344) =
      Integer.Sparse.eval keyMomentRow1344 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1344).leftCharge (GramAssembly.key 1344).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2105) := by
    have ha : gramCharges (GramAssembly.key 1344).leftCharge (GramAssembly.key 1344).rightCharge = raw40768 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40768Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40768 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1344).leftCharge (GramAssembly.key 1344).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1344, Integer.Sparse.eval]

theorem keyMoment1345 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1345) =
      Integer.Sparse.eval keyMomentRow1345 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1345).leftCharge (GramAssembly.key 1345).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2112) := by
    have ha : gramCharges (GramAssembly.key 1345).leftCharge (GramAssembly.key 1345).rightCharge = raw40769 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40769Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40769 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1345).leftCharge (GramAssembly.key 1345).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1345, Integer.Sparse.eval]

theorem keyMoment1346 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1346) =
      Integer.Sparse.eval keyMomentRow1346 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1346).leftCharge (GramAssembly.key 1346).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2954) := by
    have ha : gramCharges (GramAssembly.key 1346).leftCharge (GramAssembly.key 1346).rightCharge = raw40770 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40770Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40770 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1346).leftCharge (GramAssembly.key 1346).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1346, Integer.Sparse.eval]

theorem keyMoment1347 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1347) =
      Integer.Sparse.eval keyMomentRow1347 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1347).leftCharge (GramAssembly.key 1347).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3876) := by
    have ha : gramCharges (GramAssembly.key 1347).leftCharge (GramAssembly.key 1347).rightCharge = raw40771 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40771Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40771 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1347).leftCharge (GramAssembly.key 1347).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1347, Integer.Sparse.eval]

theorem keyMoment1348 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1348) =
      Integer.Sparse.eval keyMomentRow1348 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1348).leftCharge (GramAssembly.key 1348).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3787) := by
    have ha : gramCharges (GramAssembly.key 1348).leftCharge (GramAssembly.key 1348).rightCharge = raw40772 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40772Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40772 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1348).leftCharge (GramAssembly.key 1348).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1348, Integer.Sparse.eval]

theorem keyMoment1349 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1349) =
      Integer.Sparse.eval keyMomentRow1349 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1349).leftCharge (GramAssembly.key 1349).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1297) := by
    have ha : gramCharges (GramAssembly.key 1349).leftCharge (GramAssembly.key 1349).rightCharge = raw40773 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40773Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40773 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1349).leftCharge (GramAssembly.key 1349).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1349, Integer.Sparse.eval]

theorem keyMoment1350 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1350) =
      Integer.Sparse.eval keyMomentRow1350 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1350).leftCharge (GramAssembly.key 1350).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2783) := by
    have ha : gramCharges (GramAssembly.key 1350).leftCharge (GramAssembly.key 1350).rightCharge = raw40774 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40774Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40774 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1350).leftCharge (GramAssembly.key 1350).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1350, Integer.Sparse.eval]

theorem keyMoment1351 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1351) =
      Integer.Sparse.eval keyMomentRow1351 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1351).leftCharge (GramAssembly.key 1351).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1294) := by
    have ha : gramCharges (GramAssembly.key 1351).leftCharge (GramAssembly.key 1351).rightCharge = raw40775 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40775Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40775 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1351).leftCharge (GramAssembly.key 1351).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1351, Integer.Sparse.eval]

theorem keyMoment1352 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1352) =
      Integer.Sparse.eval keyMomentRow1352 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1352).leftCharge (GramAssembly.key 1352).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2782) := by
    have ha : gramCharges (GramAssembly.key 1352).leftCharge (GramAssembly.key 1352).rightCharge = raw40776 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40776Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40776 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1352).leftCharge (GramAssembly.key 1352).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1352, Integer.Sparse.eval]

theorem keyMoment1353 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1353) =
      Integer.Sparse.eval keyMomentRow1353 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1353).leftCharge (GramAssembly.key 1353).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2765) := by
    have ha : gramCharges (GramAssembly.key 1353).leftCharge (GramAssembly.key 1353).rightCharge = raw40777 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40777Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40777 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1353).leftCharge (GramAssembly.key 1353).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1353, Integer.Sparse.eval]

theorem keyMoment1354 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1354) =
      Integer.Sparse.eval keyMomentRow1354 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1354).leftCharge (GramAssembly.key 1354).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2109) := by
    have ha : gramCharges (GramAssembly.key 1354).leftCharge (GramAssembly.key 1354).rightCharge = raw40778 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40778Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40778 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1354).leftCharge (GramAssembly.key 1354).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1354, Integer.Sparse.eval]

theorem keyMoment1355 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1355) =
      Integer.Sparse.eval keyMomentRow1355 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1355).leftCharge (GramAssembly.key 1355).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2116) := by
    have ha : gramCharges (GramAssembly.key 1355).leftCharge (GramAssembly.key 1355).rightCharge = raw40779 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40779Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40779 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1355).leftCharge (GramAssembly.key 1355).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1355, Integer.Sparse.eval]

theorem keyMoment1356 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1356) =
      Integer.Sparse.eval keyMomentRow1356 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1356).leftCharge (GramAssembly.key 1356).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2764) := by
    have ha : gramCharges (GramAssembly.key 1356).leftCharge (GramAssembly.key 1356).rightCharge = raw40780 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40780Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40780 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1356).leftCharge (GramAssembly.key 1356).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1356, Integer.Sparse.eval]

theorem keyMoment1357 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1357) =
      Integer.Sparse.eval keyMomentRow1357 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1357).leftCharge (GramAssembly.key 1357).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2590) := by
    have ha : gramCharges (GramAssembly.key 1357).leftCharge (GramAssembly.key 1357).rightCharge = raw40781 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40781Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40781 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1357).leftCharge (GramAssembly.key 1357).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1357, Integer.Sparse.eval]

theorem keyMoment1358 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1358) =
      Integer.Sparse.eval keyMomentRow1358 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1358).leftCharge (GramAssembly.key 1358).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2589) := by
    have ha : gramCharges (GramAssembly.key 1358).leftCharge (GramAssembly.key 1358).rightCharge = raw40782 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40782Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40782 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1358).leftCharge (GramAssembly.key 1358).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1358, Integer.Sparse.eval]

theorem keyMoment1359 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1359) =
      Integer.Sparse.eval keyMomentRow1359 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1359).leftCharge (GramAssembly.key 1359).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2294) := by
    have ha : gramCharges (GramAssembly.key 1359).leftCharge (GramAssembly.key 1359).rightCharge = raw40783 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40783Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40783 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1359).leftCharge (GramAssembly.key 1359).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1359, Integer.Sparse.eval]

theorem keyMoment1360 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1360) =
      Integer.Sparse.eval keyMomentRow1360 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1360).leftCharge (GramAssembly.key 1360).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2744) := by
    have ha : gramCharges (GramAssembly.key 1360).leftCharge (GramAssembly.key 1360).rightCharge = raw40784 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40784Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40784 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1360).leftCharge (GramAssembly.key 1360).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1360, Integer.Sparse.eval]

theorem keyMoment1361 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1361) =
      Integer.Sparse.eval keyMomentRow1361 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1361).leftCharge (GramAssembly.key 1361).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3056) := by
    have ha : gramCharges (GramAssembly.key 1361).leftCharge (GramAssembly.key 1361).rightCharge = raw40785 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40785Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40785 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1361).leftCharge (GramAssembly.key 1361).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1361, Integer.Sparse.eval]

theorem keyMoment1362 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1362) =
      Integer.Sparse.eval keyMomentRow1362 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1362).leftCharge (GramAssembly.key 1362).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3626) := by
    have ha : gramCharges (GramAssembly.key 1362).leftCharge (GramAssembly.key 1362).rightCharge = raw40786 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40786Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40786 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1362).leftCharge (GramAssembly.key 1362).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1362, Integer.Sparse.eval]

theorem keyMoment1363 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1363) =
      Integer.Sparse.eval keyMomentRow1363 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1363).leftCharge (GramAssembly.key 1363).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3584) := by
    have ha : gramCharges (GramAssembly.key 1363).leftCharge (GramAssembly.key 1363).rightCharge = raw40787 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40787Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40787 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1363).leftCharge (GramAssembly.key 1363).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1363, Integer.Sparse.eval]

theorem keyMoment1364 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1364) =
      Integer.Sparse.eval keyMomentRow1364 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1364).leftCharge (GramAssembly.key 1364).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3396) := by
    have ha : gramCharges (GramAssembly.key 1364).leftCharge (GramAssembly.key 1364).rightCharge = raw40788 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40788Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40788 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1364).leftCharge (GramAssembly.key 1364).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1364, Integer.Sparse.eval]

theorem keyMoment1365 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1365) =
      Integer.Sparse.eval keyMomentRow1365 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1365).leftCharge (GramAssembly.key 1365).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3079) := by
    have ha : gramCharges (GramAssembly.key 1365).leftCharge (GramAssembly.key 1365).rightCharge = raw40789 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40789Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40789 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1365).leftCharge (GramAssembly.key 1365).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1365, Integer.Sparse.eval]

theorem keyMoment1366 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1366) =
      Integer.Sparse.eval keyMomentRow1366 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1366).leftCharge (GramAssembly.key 1366).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 1366).leftCharge (GramAssembly.key 1366).rightCharge = raw40790 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40790Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40790 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1366).leftCharge (GramAssembly.key 1366).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1366, Integer.Sparse.eval]

theorem keyMoment1367 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1367) =
      Integer.Sparse.eval keyMomentRow1367 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1367).leftCharge (GramAssembly.key 1367).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3573) := by
    have ha : gramCharges (GramAssembly.key 1367).leftCharge (GramAssembly.key 1367).rightCharge = raw40791 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40791Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40791 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1367).leftCharge (GramAssembly.key 1367).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1367, Integer.Sparse.eval]

theorem keyMoment1368 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1368) =
      Integer.Sparse.eval keyMomentRow1368 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1368).leftCharge (GramAssembly.key 1368).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3395) := by
    have ha : gramCharges (GramAssembly.key 1368).leftCharge (GramAssembly.key 1368).rightCharge = raw40792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40792 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1368).leftCharge (GramAssembly.key 1368).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1368, Integer.Sparse.eval]

theorem keyMoment1369 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1369) =
      Integer.Sparse.eval keyMomentRow1369 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1369).leftCharge (GramAssembly.key 1369).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3506) := by
    have ha : gramCharges (GramAssembly.key 1369).leftCharge (GramAssembly.key 1369).rightCharge = raw40793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40793 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1369).leftCharge (GramAssembly.key 1369).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1369, Integer.Sparse.eval]

theorem keyMoment1370 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1370) =
      Integer.Sparse.eval keyMomentRow1370 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1370).leftCharge (GramAssembly.key 1370).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3379) := by
    have ha : gramCharges (GramAssembly.key 1370).leftCharge (GramAssembly.key 1370).rightCharge = raw40794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40794 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1370).leftCharge (GramAssembly.key 1370).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1370, Integer.Sparse.eval]

theorem keyMoment1371 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1371) =
      Integer.Sparse.eval keyMomentRow1371 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1371).leftCharge (GramAssembly.key 1371).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3505) := by
    have ha : gramCharges (GramAssembly.key 1371).leftCharge (GramAssembly.key 1371).rightCharge = raw40795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40795 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1371).leftCharge (GramAssembly.key 1371).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1371, Integer.Sparse.eval]

theorem keyMoment1372 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1372) =
      Integer.Sparse.eval keyMomentRow1372 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1372).leftCharge (GramAssembly.key 1372).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3378) := by
    have ha : gramCharges (GramAssembly.key 1372).leftCharge (GramAssembly.key 1372).rightCharge = raw40796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40796 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1372).leftCharge (GramAssembly.key 1372).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1372, Integer.Sparse.eval]

theorem keyMoment1373 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1373) =
      Integer.Sparse.eval keyMomentRow1373 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1373).leftCharge (GramAssembly.key 1373).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2266) := by
    have ha : gramCharges (GramAssembly.key 1373).leftCharge (GramAssembly.key 1373).rightCharge = raw40797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40797 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1373).leftCharge (GramAssembly.key 1373).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1373, Integer.Sparse.eval]

theorem keyMoment1374 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1374) =
      Integer.Sparse.eval keyMomentRow1374 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1374).leftCharge (GramAssembly.key 1374).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 1374).leftCharge (GramAssembly.key 1374).rightCharge = raw40798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40798 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1374).leftCharge (GramAssembly.key 1374).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1374, Integer.Sparse.eval]

theorem keyMoment1375 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1375) =
      Integer.Sparse.eval keyMomentRow1375 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1375).leftCharge (GramAssembly.key 1375).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3040) := by
    have ha : gramCharges (GramAssembly.key 1375).leftCharge (GramAssembly.key 1375).rightCharge = raw40799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40799 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1375).leftCharge (GramAssembly.key 1375).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1375, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1344 : keyMomentRows (1344 : Fin 2886) =
    keyMomentRow1344 := by decide +kernel

theorem keyMomentRowsAt1345 : keyMomentRows (1345 : Fin 2886) =
    keyMomentRow1345 := by decide +kernel

theorem keyMomentRowsAt1346 : keyMomentRows (1346 : Fin 2886) =
    keyMomentRow1346 := by decide +kernel

theorem keyMomentRowsAt1347 : keyMomentRows (1347 : Fin 2886) =
    keyMomentRow1347 := by decide +kernel

theorem keyMomentRowsAt1348 : keyMomentRows (1348 : Fin 2886) =
    keyMomentRow1348 := by decide +kernel

theorem keyMomentRowsAt1349 : keyMomentRows (1349 : Fin 2886) =
    keyMomentRow1349 := by decide +kernel

theorem keyMomentRowsAt1350 : keyMomentRows (1350 : Fin 2886) =
    keyMomentRow1350 := by decide +kernel

theorem keyMomentRowsAt1351 : keyMomentRows (1351 : Fin 2886) =
    keyMomentRow1351 := by decide +kernel

theorem keyMomentRowsAt1352 : keyMomentRows (1352 : Fin 2886) =
    keyMomentRow1352 := by decide +kernel

theorem keyMomentRowsAt1353 : keyMomentRows (1353 : Fin 2886) =
    keyMomentRow1353 := by decide +kernel

theorem keyMomentRowsAt1354 : keyMomentRows (1354 : Fin 2886) =
    keyMomentRow1354 := by decide +kernel

theorem keyMomentRowsAt1355 : keyMomentRows (1355 : Fin 2886) =
    keyMomentRow1355 := by decide +kernel

theorem keyMomentRowsAt1356 : keyMomentRows (1356 : Fin 2886) =
    keyMomentRow1356 := by decide +kernel

theorem keyMomentRowsAt1357 : keyMomentRows (1357 : Fin 2886) =
    keyMomentRow1357 := by decide +kernel

theorem keyMomentRowsAt1358 : keyMomentRows (1358 : Fin 2886) =
    keyMomentRow1358 := by decide +kernel

theorem keyMomentRowsAt1359 : keyMomentRows (1359 : Fin 2886) =
    keyMomentRow1359 := by decide +kernel

theorem keyMomentRowsAt1360 : keyMomentRows (1360 : Fin 2886) =
    keyMomentRow1360 := by decide +kernel

theorem keyMomentRowsAt1361 : keyMomentRows (1361 : Fin 2886) =
    keyMomentRow1361 := by decide +kernel

theorem keyMomentRowsAt1362 : keyMomentRows (1362 : Fin 2886) =
    keyMomentRow1362 := by decide +kernel

theorem keyMomentRowsAt1363 : keyMomentRows (1363 : Fin 2886) =
    keyMomentRow1363 := by decide +kernel

theorem keyMomentRowsAt1364 : keyMomentRows (1364 : Fin 2886) =
    keyMomentRow1364 := by decide +kernel

theorem keyMomentRowsAt1365 : keyMomentRows (1365 : Fin 2886) =
    keyMomentRow1365 := by decide +kernel

theorem keyMomentRowsAt1366 : keyMomentRows (1366 : Fin 2886) =
    keyMomentRow1366 := by decide +kernel

theorem keyMomentRowsAt1367 : keyMomentRows (1367 : Fin 2886) =
    keyMomentRow1367 := by decide +kernel

theorem keyMomentRowsAt1368 : keyMomentRows (1368 : Fin 2886) =
    keyMomentRow1368 := by decide +kernel

theorem keyMomentRowsAt1369 : keyMomentRows (1369 : Fin 2886) =
    keyMomentRow1369 := by decide +kernel

theorem keyMomentRowsAt1370 : keyMomentRows (1370 : Fin 2886) =
    keyMomentRow1370 := by decide +kernel

theorem keyMomentRowsAt1371 : keyMomentRows (1371 : Fin 2886) =
    keyMomentRow1371 := by decide +kernel

theorem keyMomentRowsAt1372 : keyMomentRows (1372 : Fin 2886) =
    keyMomentRow1372 := by decide +kernel

theorem keyMomentRowsAt1373 : keyMomentRows (1373 : Fin 2886) =
    keyMomentRow1373 := by decide +kernel

theorem keyMomentRowsAt1374 : keyMomentRows (1374 : Fin 2886) =
    keyMomentRow1374 := by decide +kernel

theorem keyMomentRowsAt1375 : keyMomentRows (1375 : Fin 2886) =
    keyMomentRow1375 := by decide +kernel

theorem keyMomentChunkSound42_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 42) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1344 ∨ k.val = 1345 ∨ k.val = 1346 ∨ k.val = 1347 ∨ k.val = 1348 ∨ k.val = 1349 ∨ k.val = 1350 ∨ k.val = 1351 ∨ k.val = 1352 ∨ k.val = 1353 ∨ k.val = 1354 ∨ k.val = 1355 ∨ k.val = 1356 ∨ k.val = 1357 ∨ k.val = 1358 ∨ k.val = 1359 ∨ k.val = 1360 ∨ k.val = 1361 ∨ k.val = 1362 ∨ k.val = 1363 ∨ k.val = 1364 ∨ k.val = 1365 ∨ k.val = 1366 ∨ k.val = 1367 ∨ k.val = 1368 ∨ k.val = 1369 ∨ k.val = 1370 ∨ k.val = 1371 ∨ k.val = 1372 ∨ k.val = 1373 ∨ k.val = 1374 ∨ k.val = 1375 := by omega
  rcases heq with h1344 | h1345 | h1346 | h1347 | h1348 | h1349 | h1350 | h1351 | h1352 | h1353 | h1354 | h1355 | h1356 | h1357 | h1358 | h1359 | h1360 | h1361 | h1362 | h1363 | h1364 | h1365 | h1366 | h1367 | h1368 | h1369 | h1370 | h1371 | h1372 | h1373 | h1374 | h1375
  · have he : k = (1344 : Fin 2886) := Fin.ext h1344
    subst k
    rw [keyMomentRowsAt1344]
    exact keyMoment1344 B hB
  · have he : k = (1345 : Fin 2886) := Fin.ext h1345
    subst k
    rw [keyMomentRowsAt1345]
    exact keyMoment1345 B hB
  · have he : k = (1346 : Fin 2886) := Fin.ext h1346
    subst k
    rw [keyMomentRowsAt1346]
    exact keyMoment1346 B hB
  · have he : k = (1347 : Fin 2886) := Fin.ext h1347
    subst k
    rw [keyMomentRowsAt1347]
    exact keyMoment1347 B hB
  · have he : k = (1348 : Fin 2886) := Fin.ext h1348
    subst k
    rw [keyMomentRowsAt1348]
    exact keyMoment1348 B hB
  · have he : k = (1349 : Fin 2886) := Fin.ext h1349
    subst k
    rw [keyMomentRowsAt1349]
    exact keyMoment1349 B hB
  · have he : k = (1350 : Fin 2886) := Fin.ext h1350
    subst k
    rw [keyMomentRowsAt1350]
    exact keyMoment1350 B hB
  · have he : k = (1351 : Fin 2886) := Fin.ext h1351
    subst k
    rw [keyMomentRowsAt1351]
    exact keyMoment1351 B hB
  · have he : k = (1352 : Fin 2886) := Fin.ext h1352
    subst k
    rw [keyMomentRowsAt1352]
    exact keyMoment1352 B hB
  · have he : k = (1353 : Fin 2886) := Fin.ext h1353
    subst k
    rw [keyMomentRowsAt1353]
    exact keyMoment1353 B hB
  · have he : k = (1354 : Fin 2886) := Fin.ext h1354
    subst k
    rw [keyMomentRowsAt1354]
    exact keyMoment1354 B hB
  · have he : k = (1355 : Fin 2886) := Fin.ext h1355
    subst k
    rw [keyMomentRowsAt1355]
    exact keyMoment1355 B hB
  · have he : k = (1356 : Fin 2886) := Fin.ext h1356
    subst k
    rw [keyMomentRowsAt1356]
    exact keyMoment1356 B hB
  · have he : k = (1357 : Fin 2886) := Fin.ext h1357
    subst k
    rw [keyMomentRowsAt1357]
    exact keyMoment1357 B hB
  · have he : k = (1358 : Fin 2886) := Fin.ext h1358
    subst k
    rw [keyMomentRowsAt1358]
    exact keyMoment1358 B hB
  · have he : k = (1359 : Fin 2886) := Fin.ext h1359
    subst k
    rw [keyMomentRowsAt1359]
    exact keyMoment1359 B hB
  · have he : k = (1360 : Fin 2886) := Fin.ext h1360
    subst k
    rw [keyMomentRowsAt1360]
    exact keyMoment1360 B hB
  · have he : k = (1361 : Fin 2886) := Fin.ext h1361
    subst k
    rw [keyMomentRowsAt1361]
    exact keyMoment1361 B hB
  · have he : k = (1362 : Fin 2886) := Fin.ext h1362
    subst k
    rw [keyMomentRowsAt1362]
    exact keyMoment1362 B hB
  · have he : k = (1363 : Fin 2886) := Fin.ext h1363
    subst k
    rw [keyMomentRowsAt1363]
    exact keyMoment1363 B hB
  · have he : k = (1364 : Fin 2886) := Fin.ext h1364
    subst k
    rw [keyMomentRowsAt1364]
    exact keyMoment1364 B hB
  · have he : k = (1365 : Fin 2886) := Fin.ext h1365
    subst k
    rw [keyMomentRowsAt1365]
    exact keyMoment1365 B hB
  · have he : k = (1366 : Fin 2886) := Fin.ext h1366
    subst k
    rw [keyMomentRowsAt1366]
    exact keyMoment1366 B hB
  · have he : k = (1367 : Fin 2886) := Fin.ext h1367
    subst k
    rw [keyMomentRowsAt1367]
    exact keyMoment1367 B hB
  · have he : k = (1368 : Fin 2886) := Fin.ext h1368
    subst k
    rw [keyMomentRowsAt1368]
    exact keyMoment1368 B hB
  · have he : k = (1369 : Fin 2886) := Fin.ext h1369
    subst k
    rw [keyMomentRowsAt1369]
    exact keyMoment1369 B hB
  · have he : k = (1370 : Fin 2886) := Fin.ext h1370
    subst k
    rw [keyMomentRowsAt1370]
    exact keyMoment1370 B hB
  · have he : k = (1371 : Fin 2886) := Fin.ext h1371
    subst k
    rw [keyMomentRowsAt1371]
    exact keyMoment1371 B hB
  · have he : k = (1372 : Fin 2886) := Fin.ext h1372
    subst k
    rw [keyMomentRowsAt1372]
    exact keyMoment1372 B hB
  · have he : k = (1373 : Fin 2886) := Fin.ext h1373
    subst k
    rw [keyMomentRowsAt1373]
    exact keyMoment1373 B hB
  · have he : k = (1374 : Fin 2886) := Fin.ext h1374
    subst k
    rw [keyMomentRowsAt1374]
    exact keyMoment1374 B hB
  · have he : k = (1375 : Fin 2886) := Fin.ext h1375
    subst k
    rw [keyMomentRowsAt1375]
    exact keyMoment1375 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound42_e_oai
