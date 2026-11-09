-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:47:26.758815+00:00
-- url     : https://prove2.me/submissions/92edc0e7-e897-43ae-bbd5-0a4cc2c54ad6

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

theorem canonical40024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40024 raw40024Labels = mixedMoment B node116 node116Labels := by
  calc
    mixedMoment B raw40024 raw40024Labels = mixedMoment B raw40024step0 raw40024step0Labels := by
      have hz : ∀ j, raw40024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40024step0 = (fun i j => raw40024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40024step0 raw40024; decide +kernel
      have hl : raw40024step0Labels = raw40024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40024 raw40024Labels permutation434 hz
    mixedMoment B raw40024step0 raw40024step0Labels = mixedMoment B raw40024step1 raw40024step1Labels := by
      have ha : raw40024step1 = (fun i j => raw40024step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40024step1 raw40024step0; decide +kernel
      have hl : raw40024step1Labels = raw40024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40024step0 raw40024step0Labels permutation34 permutation7
    mixedMoment B raw40024step1 raw40024step1Labels = mixedMoment B raw40024step2 raw40024step2Labels := by
      have ha : raw40024step2 = -raw40024step1 := by apply Matrix.ext; change ∀ i j, raw40024step2 i j = -(raw40024step1 i j); unfold raw40024step2 raw40024step1; decide +kernel
      have hl : raw40024step2Labels = raw40024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node116 node116Labels := by rfl

theorem canonical40025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40025 raw40025Labels = mixedMoment B node115 node115Labels := by
  calc
    mixedMoment B raw40025 raw40025Labels = mixedMoment B raw40025step0 raw40025step0Labels := by
      have hz : ∀ j, raw40025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40025step0 = (fun i j => raw40025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40025step0 raw40025; decide +kernel
      have hl : raw40025step0Labels = raw40025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40025 raw40025Labels permutation434 hz
    mixedMoment B raw40025step0 raw40025step0Labels = mixedMoment B raw40025step1 raw40025step1Labels := by
      have ha : raw40025step1 = (fun i j => raw40025step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40025step1 raw40025step0; decide +kernel
      have hl : raw40025step1Labels = raw40025step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40025step0 raw40025step0Labels permutation145 permutation6
    _ = mixedMoment B node115 node115Labels := by rfl

theorem canonical40026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40026 raw40026Labels = mixedMoment B node13 node13Labels := by
  calc
    mixedMoment B raw40026 raw40026Labels = mixedMoment B raw40026step0 raw40026step0Labels := by
      have hz : ∀ j, raw40026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40026step0 = (fun i j => raw40026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40026step0 raw40026; decide +kernel
      have hl : raw40026step0Labels = raw40026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40026 raw40026Labels permutation434 hz
    mixedMoment B raw40026step0 raw40026step0Labels = mixedMoment B raw40026step1 raw40026step1Labels := by
      have hz : ∀ j, raw40026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40026step1 = (fun i j => raw40026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40026step1 raw40026step0; decide +kernel
      have hl : raw40026step1Labels = raw40026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40026step0 raw40026step0Labels permutation80 hz
    mixedMoment B raw40026step1 raw40026step1Labels = mixedMoment B raw40026step2 raw40026step2Labels := by
      have ha : raw40026step2 = (fun i j => raw40026step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40026step2 raw40026step1; decide +kernel
      have hl : raw40026step2Labels = raw40026step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40026step1 raw40026step1Labels permutation31 permutation6
    _ = mixedMoment B node13 node13Labels := by rfl

theorem canonical40027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40027 raw40027Labels = mixedMoment B node131 node131Labels := by
  calc
    mixedMoment B raw40027 raw40027Labels = mixedMoment B raw40027step0 raw40027step0Labels := by
      have hz : ∀ j, raw40027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40027step0 = (fun i j => raw40027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40027step0 raw40027; decide +kernel
      have hl : raw40027step0Labels = raw40027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40027 raw40027Labels permutation434 hz
    mixedMoment B raw40027step0 raw40027step0Labels = mixedMoment B raw40027step1 raw40027step1Labels := by
      have hz : ∀ j, raw40027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40027step1 = (fun i j => raw40027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40027step1 raw40027step0; decide +kernel
      have hl : raw40027step1Labels = raw40027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40027step0 raw40027step0Labels permutation80 hz
    mixedMoment B raw40027step1 raw40027step1Labels = mixedMoment B raw40027step2 raw40027step2Labels := by
      have ha : raw40027step2 = (fun i j => raw40027step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40027step2 raw40027step1; decide +kernel
      have hl : raw40027step2Labels = raw40027step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40027step1 raw40027step1Labels permutation11 permutation6
    mixedMoment B raw40027step2 raw40027step2Labels = mixedMoment B raw40027step3 raw40027step3Labels := by
      have ha : raw40027step3 = -raw40027step2 := by apply Matrix.ext; change ∀ i j, raw40027step3 i j = -(raw40027step2 i j); unfold raw40027step3 raw40027step2; decide +kernel
      have hl : raw40027step3Labels = raw40027step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node131 node131Labels := by rfl

theorem canonical40028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40028 raw40028Labels = mixedMoment B node143 node143Labels := by
  calc
    mixedMoment B raw40028 raw40028Labels = mixedMoment B raw40028step0 raw40028step0Labels := by
      have hz : ∀ j, raw40028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40028step0 = (fun i j => raw40028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40028step0 raw40028; decide +kernel
      have hl : raw40028step0Labels = raw40028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40028 raw40028Labels permutation434 hz
    mixedMoment B raw40028step0 raw40028step0Labels = mixedMoment B raw40028step1 raw40028step1Labels := by
      have hz : ∀ j, raw40028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40028step1 = (fun i j => raw40028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40028step1 raw40028step0; decide +kernel
      have hl : raw40028step1Labels = raw40028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40028step0 raw40028step0Labels permutation80 hz
    mixedMoment B raw40028step1 raw40028step1Labels = mixedMoment B raw40028step2 raw40028step2Labels := by
      have ha : raw40028step2 = (fun i j => raw40028step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40028step2 raw40028step1; decide +kernel
      have hl : raw40028step2Labels = raw40028step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40028step1 raw40028step1Labels permutation13 permutation6
    mixedMoment B raw40028step2 raw40028step2Labels = mixedMoment B raw40028step3 raw40028step3Labels := by
      have ha : raw40028step3 = -raw40028step2 := by apply Matrix.ext; change ∀ i j, raw40028step3 i j = -(raw40028step2 i j); unfold raw40028step3 raw40028step2; decide +kernel
      have hl : raw40028step3Labels = raw40028step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node143 node143Labels := by rfl

theorem canonical40029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40029 raw40029Labels = mixedMoment B node119 node119Labels := by
  calc
    mixedMoment B raw40029 raw40029Labels = mixedMoment B raw40029step0 raw40029step0Labels := by
      have hz : ∀ j, raw40029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40029step0 = (fun i j => raw40029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40029step0 raw40029; decide +kernel
      have hl : raw40029step0Labels = raw40029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40029 raw40029Labels permutation346 hz
    mixedMoment B raw40029step0 raw40029step0Labels = mixedMoment B raw40029step1 raw40029step1Labels := by
      have ha : raw40029step1 = (fun i j => raw40029step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40029step1 raw40029step0; decide +kernel
      have hl : raw40029step1Labels = raw40029step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40029step0 raw40029step0Labels permutation41 permutation6
    mixedMoment B raw40029step1 raw40029step1Labels = mixedMoment B raw40029step2 raw40029step2Labels := by
      have ha : raw40029step2 = -raw40029step1 := by apply Matrix.ext; change ∀ i j, raw40029step2 i j = -(raw40029step1 i j); unfold raw40029step2 raw40029step1; decide +kernel
      have hl : raw40029step2Labels = raw40029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node119 node119Labels := by rfl

theorem canonical40030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40030 raw40030Labels = mixedMoment B node127 node127Labels := by
  calc
    mixedMoment B raw40030 raw40030Labels = mixedMoment B raw40030step0 raw40030step0Labels := by
      have hz : ∀ j, raw40030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40030step0 = (fun i j => raw40030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40030step0 raw40030; decide +kernel
      have hl : raw40030step0Labels = raw40030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40030 raw40030Labels permutation434 hz
    mixedMoment B raw40030step0 raw40030step0Labels = mixedMoment B raw40030step1 raw40030step1Labels := by
      have ha : raw40030step1 = (fun i j => raw40030step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40030step1 raw40030step0; decide +kernel
      have hl : raw40030step1Labels = raw40030step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40030step0 raw40030step0Labels permutation47 permutation6
    mixedMoment B raw40030step1 raw40030step1Labels = mixedMoment B raw40030step2 raw40030step2Labels := by
      have ha : raw40030step2 = -raw40030step1 := by apply Matrix.ext; change ∀ i j, raw40030step2 i j = -(raw40030step1 i j); unfold raw40030step2 raw40030step1; decide +kernel
      have hl : raw40030step2Labels = raw40030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node127 node127Labels := by rfl

theorem canonical40031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40031 raw40031Labels = mixedMoment B node142 node142Labels := by
  calc
    mixedMoment B raw40031 raw40031Labels = mixedMoment B raw40031step0 raw40031step0Labels := by
      have hz : ∀ j, raw40031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40031step0 = (fun i j => raw40031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40031step0 raw40031; decide +kernel
      have hl : raw40031step0Labels = raw40031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40031 raw40031Labels permutation434 hz
    mixedMoment B raw40031step0 raw40031step0Labels = mixedMoment B raw40031step1 raw40031step1Labels := by
      have ha : raw40031step1 = (fun i j => raw40031step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40031step1 raw40031step0; decide +kernel
      have hl : raw40031step1Labels = raw40031step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40031step0 raw40031step0Labels permutation55 permutation6
    mixedMoment B raw40031step1 raw40031step1Labels = mixedMoment B raw40031step2 raw40031step2Labels := by
      have ha : raw40031step2 = -raw40031step1 := by apply Matrix.ext; change ∀ i j, raw40031step2 i j = -(raw40031step1 i j); unfold raw40031step2 raw40031step1; decide +kernel
      have hl : raw40031step2Labels = raw40031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node142 node142Labels := by rfl

theorem canonical40032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40032 raw40032Labels = mixedMoment B node118 node118Labels := by
  calc
    mixedMoment B raw40032 raw40032Labels = mixedMoment B raw40032step0 raw40032step0Labels := by
      have ha : raw40032step0 = (fun i j => raw40032 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40032step0 raw40032; decide +kernel
      have hl : raw40032step0Labels = raw40032Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40032 raw40032Labels permutation217 permutation6
    mixedMoment B raw40032step0 raw40032step0Labels = mixedMoment B raw40032step1 raw40032step1Labels := by
      have ha : raw40032step1 = -raw40032step0 := by apply Matrix.ext; change ∀ i j, raw40032step1 i j = -(raw40032step0 i j); unfold raw40032step1 raw40032step0; decide +kernel
      have hl : raw40032step1Labels = raw40032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node118 node118Labels := by rfl

theorem canonical40033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40033 raw40033Labels = mixedMoment B node160 node160Labels := by
  calc
    mixedMoment B raw40033 raw40033Labels = mixedMoment B raw40033step0 raw40033step0Labels := by
      have hz : ∀ j, raw40033 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40033step0 = (fun i j => raw40033 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40033step0 raw40033; decide +kernel
      have hl : raw40033step0Labels = raw40033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40033 raw40033Labels permutation520 hz
    mixedMoment B raw40033step0 raw40033step0Labels = mixedMoment B raw40033step1 raw40033step1Labels := by
      have hz : ∀ j, raw40033step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40033step1 = (fun i j => raw40033step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40033step1 raw40033step0; decide +kernel
      have hl : raw40033step1Labels = raw40033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40033step0 raw40033step0Labels permutation104 hz
    mixedMoment B raw40033step1 raw40033step1Labels = mixedMoment B raw40033step2 raw40033step2Labels := by
      have hz : ∀ j, raw40033step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40033step2 = (fun i j => raw40033step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40033step2 raw40033step1; decide +kernel
      have hl : raw40033step2Labels = raw40033step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40033step1 raw40033step1Labels permutation20 hz
    mixedMoment B raw40033step2 raw40033step2Labels = mixedMoment B raw40033step3 raw40033step3Labels := by
      have ha : raw40033step3 = (fun i j => raw40033step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40033step3 raw40033step2; decide +kernel
      have hl : raw40033step3Labels = raw40033step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40033step2 raw40033step2Labels permutation3 permutation6
    mixedMoment B raw40033step3 raw40033step3Labels = mixedMoment B raw40033step4 raw40033step4Labels := by
      have ha : raw40033step4 = -raw40033step3 := by apply Matrix.ext; change ∀ i j, raw40033step4 i j = -(raw40033step3 i j); unfold raw40033step4 raw40033step3; decide +kernel
      have hl : raw40033step4Labels = raw40033step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node160 node160Labels := by rfl

theorem canonical40034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40034 raw40034Labels = mixedMoment B node133 node133Labels := by
  calc
    mixedMoment B raw40034 raw40034Labels = mixedMoment B raw40034step0 raw40034step0Labels := by
      have hz : ∀ j, raw40034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40034step0 = (fun i j => raw40034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40034step0 raw40034; decide +kernel
      have hl : raw40034step0Labels = raw40034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40034 raw40034Labels permutation434 hz
    mixedMoment B raw40034step0 raw40034step0Labels = mixedMoment B raw40034step1 raw40034step1Labels := by
      have hz : ∀ j, raw40034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40034step1 = (fun i j => raw40034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40034step1 raw40034step0; decide +kernel
      have hl : raw40034step1Labels = raw40034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40034step0 raw40034step0Labels permutation80 hz
    mixedMoment B raw40034step1 raw40034step1Labels = mixedMoment B raw40034step2 raw40034step2Labels := by
      have ha : raw40034step2 = (fun i j => raw40034step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40034step2 raw40034step1; decide +kernel
      have hl : raw40034step2Labels = raw40034step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40034step1 raw40034step1Labels permutation10 permutation6
    mixedMoment B raw40034step2 raw40034step2Labels = mixedMoment B raw40034step3 raw40034step3Labels := by
      have ha : raw40034step3 = -raw40034step2 := by apply Matrix.ext; change ∀ i j, raw40034step3 i j = -(raw40034step2 i j); unfold raw40034step3 raw40034step2; decide +kernel
      have hl : raw40034step3Labels = raw40034step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node133 node133Labels := by rfl

theorem canonical40035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40035 raw40035Labels = mixedMoment B node149 node149Labels := by
  calc
    mixedMoment B raw40035 raw40035Labels = mixedMoment B raw40035step0 raw40035step0Labels := by
      have hz : ∀ j, raw40035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40035step0 = (fun i j => raw40035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40035step0 raw40035; decide +kernel
      have hl : raw40035step0Labels = raw40035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40035 raw40035Labels permutation434 hz
    mixedMoment B raw40035step0 raw40035step0Labels = mixedMoment B raw40035step1 raw40035step1Labels := by
      have hz : ∀ j, raw40035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40035step1 = (fun i j => raw40035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40035step1 raw40035step0; decide +kernel
      have hl : raw40035step1Labels = raw40035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40035step0 raw40035step0Labels permutation80 hz
    mixedMoment B raw40035step1 raw40035step1Labels = mixedMoment B raw40035step2 raw40035step2Labels := by
      have ha : raw40035step2 = (fun i j => raw40035step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40035step2 raw40035step1; decide +kernel
      have hl : raw40035step2Labels = raw40035step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40035step1 raw40035step1Labels permutation13 permutation6
    mixedMoment B raw40035step2 raw40035step2Labels = mixedMoment B raw40035step3 raw40035step3Labels := by
      have ha : raw40035step3 = -raw40035step2 := by apply Matrix.ext; change ∀ i j, raw40035step3 i j = -(raw40035step2 i j); unfold raw40035step3 raw40035step2; decide +kernel
      have hl : raw40035step3Labels = raw40035step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node149 node149Labels := by rfl

theorem canonical40036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40036 raw40036Labels = mixedMoment B node124 node124Labels := by
  calc
    mixedMoment B raw40036 raw40036Labels = mixedMoment B raw40036step0 raw40036step0Labels := by
      have hz : ∀ j, raw40036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40036step0 = (fun i j => raw40036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40036step0 raw40036; decide +kernel
      have hl : raw40036step0Labels = raw40036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40036 raw40036Labels permutation346 hz
    mixedMoment B raw40036step0 raw40036step0Labels = mixedMoment B raw40036step1 raw40036step1Labels := by
      have ha : raw40036step1 = (fun i j => raw40036step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40036step1 raw40036step0; decide +kernel
      have hl : raw40036step1Labels = raw40036step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40036step0 raw40036step0Labels permutation43 permutation6
    mixedMoment B raw40036step1 raw40036step1Labels = mixedMoment B raw40036step2 raw40036step2Labels := by
      have ha : raw40036step2 = -raw40036step1 := by apply Matrix.ext; change ∀ i j, raw40036step2 i j = -(raw40036step1 i j); unfold raw40036step2 raw40036step1; decide +kernel
      have hl : raw40036step2Labels = raw40036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node124 node124Labels := by rfl

theorem canonical40037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40037 raw40037Labels = mixedMoment B node125 node125Labels := by
  calc
    mixedMoment B raw40037 raw40037Labels = mixedMoment B raw40037step0 raw40037step0Labels := by
      have ha : raw40037step0 = (fun i j => raw40037 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40037step0 raw40037; decide +kernel
      have hl : raw40037step0Labels = raw40037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40037 raw40037Labels permutation224 permutation6
    mixedMoment B raw40037step0 raw40037step0Labels = mixedMoment B raw40037step1 raw40037step1Labels := by
      have ha : raw40037step1 = -raw40037step0 := by apply Matrix.ext; change ∀ i j, raw40037step1 i j = -(raw40037step0 i j); unfold raw40037step1 raw40037step0; decide +kernel
      have hl : raw40037step1Labels = raw40037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node125 node125Labels := by rfl

theorem canonical40038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40038 raw40038Labels = mixedMoment B node126 node126Labels := by
  calc
    mixedMoment B raw40038 raw40038Labels = mixedMoment B raw40038step0 raw40038step0Labels := by
      have hz : ∀ j, raw40038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40038step0 = (fun i j => raw40038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40038step0 raw40038; decide +kernel
      have hl : raw40038step0Labels = raw40038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40038 raw40038Labels permutation434 hz
    mixedMoment B raw40038step0 raw40038step0Labels = mixedMoment B raw40038step1 raw40038step1Labels := by
      have ha : raw40038step1 = (fun i j => raw40038step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40038step1 raw40038step0; decide +kernel
      have hl : raw40038step1Labels = raw40038step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40038step0 raw40038step0Labels permutation44 permutation6
    mixedMoment B raw40038step1 raw40038step1Labels = mixedMoment B raw40038step2 raw40038step2Labels := by
      have ha : raw40038step2 = -raw40038step1 := by apply Matrix.ext; change ∀ i j, raw40038step2 i j = -(raw40038step1 i j); unfold raw40038step2 raw40038step1; decide +kernel
      have hl : raw40038step2Labels = raw40038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node126 node126Labels := by rfl

theorem canonical40039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40039 raw40039Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw40039 raw40039Labels = mixedMoment B raw40039step0 raw40039step0Labels := by
      have hz : ∀ j, raw40039 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40039step0 = (fun i j => raw40039 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40039step0 raw40039; decide +kernel
      have hl : raw40039step0Labels = raw40039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40039 raw40039Labels permutation520 hz
    mixedMoment B raw40039step0 raw40039step0Labels = mixedMoment B raw40039step1 raw40039step1Labels := by
      have hz : ∀ j, raw40039step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40039step1 = (fun i j => raw40039step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40039step1 raw40039step0; decide +kernel
      have hl : raw40039step1Labels = raw40039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40039step0 raw40039step0Labels permutation104 hz
    mixedMoment B raw40039step1 raw40039step1Labels = mixedMoment B raw40039step2 raw40039step2Labels := by
      have hz : ∀ j, raw40039step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40039step2 = (fun i j => raw40039step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40039step2 raw40039step1; decide +kernel
      have hl : raw40039step2Labels = raw40039step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40039step1 raw40039step1Labels permutation20 hz
    mixedMoment B raw40039step2 raw40039step2Labels = mixedMoment B raw40039step3 raw40039step3Labels := by
      have ha : raw40039step3 = (fun i j => raw40039step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40039step3 raw40039step2; decide +kernel
      have hl : raw40039step3Labels = raw40039step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40039step2 raw40039step2Labels permutation2 permutation7
    mixedMoment B raw40039step3 raw40039step3Labels = mixedMoment B raw40039step4 raw40039step4Labels := by
      have ha : raw40039step4 = -raw40039step3 := by apply Matrix.ext; change ∀ i j, raw40039step4 i j = -(raw40039step3 i j); unfold raw40039step4 raw40039step3; decide +kernel
      have hl : raw40039step4Labels = raw40039step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node158 node158Labels := by rfl

theorem canonical40040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40040 raw40040Labels = mixedMoment B node129 node129Labels := by
  calc
    mixedMoment B raw40040 raw40040Labels = mixedMoment B raw40040step0 raw40040step0Labels := by
      have hz : ∀ j, raw40040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40040step0 = (fun i j => raw40040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40040step0 raw40040; decide +kernel
      have hl : raw40040step0Labels = raw40040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40040 raw40040Labels permutation434 hz
    mixedMoment B raw40040step0 raw40040step0Labels = mixedMoment B raw40040step1 raw40040step1Labels := by
      have hz : ∀ j, raw40040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40040step1 = (fun i j => raw40040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40040step1 raw40040step0; decide +kernel
      have hl : raw40040step1Labels = raw40040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40040step0 raw40040step0Labels permutation80 hz
    mixedMoment B raw40040step1 raw40040step1Labels = mixedMoment B raw40040step2 raw40040step2Labels := by
      have ha : raw40040step2 = (fun i j => raw40040step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40040step2 raw40040step1; decide +kernel
      have hl : raw40040step2Labels = raw40040step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40040step1 raw40040step1Labels permutation29 permutation6
    _ = mixedMoment B node129 node129Labels := by rfl

theorem canonical40041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40041 raw40041Labels = mixedMoment B node146 node146Labels := by
  calc
    mixedMoment B raw40041 raw40041Labels = mixedMoment B raw40041step0 raw40041step0Labels := by
      have hz : ∀ j, raw40041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40041step0 = (fun i j => raw40041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40041step0 raw40041; decide +kernel
      have hl : raw40041step0Labels = raw40041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40041 raw40041Labels permutation434 hz
    mixedMoment B raw40041step0 raw40041step0Labels = mixedMoment B raw40041step1 raw40041step1Labels := by
      have hz : ∀ j, raw40041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40041step1 = (fun i j => raw40041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40041step1 raw40041step0; decide +kernel
      have hl : raw40041step1Labels = raw40041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40041step0 raw40041step0Labels permutation80 hz
    mixedMoment B raw40041step1 raw40041step1Labels = mixedMoment B raw40041step2 raw40041step2Labels := by
      have ha : raw40041step2 = (fun i j => raw40041step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40041step2 raw40041step1; decide +kernel
      have hl : raw40041step2Labels = raw40041step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40041step1 raw40041step1Labels permutation12 permutation6
    mixedMoment B raw40041step2 raw40041step2Labels = mixedMoment B raw40041step3 raw40041step3Labels := by
      have ha : raw40041step3 = -raw40041step2 := by apply Matrix.ext; change ∀ i j, raw40041step3 i j = -(raw40041step2 i j); unfold raw40041step3 raw40041step2; decide +kernel
      have hl : raw40041step3Labels = raw40041step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node146 node146Labels := by rfl

theorem canonical40042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40042 raw40042Labels = mixedMoment B node121 node121Labels := by
  calc
    mixedMoment B raw40042 raw40042Labels = mixedMoment B raw40042step0 raw40042step0Labels := by
      have hz : ∀ j, raw40042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40042step0 = (fun i j => raw40042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40042step0 raw40042; decide +kernel
      have hl : raw40042step0Labels = raw40042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40042 raw40042Labels permutation346 hz
    mixedMoment B raw40042step0 raw40042step0Labels = mixedMoment B raw40042step1 raw40042step1Labels := by
      have ha : raw40042step1 = (fun i j => raw40042step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40042step1 raw40042step0; decide +kernel
      have hl : raw40042step1Labels = raw40042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40042step0 raw40042step0Labels permutation42 permutation6
    mixedMoment B raw40042step1 raw40042step1Labels = mixedMoment B raw40042step2 raw40042step2Labels := by
      have ha : raw40042step2 = -raw40042step1 := by apply Matrix.ext; change ∀ i j, raw40042step2 i j = -(raw40042step1 i j); unfold raw40042step2 raw40042step1; decide +kernel
      have hl : raw40042step2Labels = raw40042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node121 node121Labels := by rfl

theorem canonical40043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40043 raw40043Labels = mixedMoment B node162 node162Labels := by
  calc
    mixedMoment B raw40043 raw40043Labels = mixedMoment B raw40043step0 raw40043step0Labels := by
      have hz : ∀ j, raw40043 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40043step0 = (fun i j => raw40043 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40043step0 raw40043; decide +kernel
      have hl : raw40043step0Labels = raw40043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043 raw40043Labels permutation520 hz
    mixedMoment B raw40043step0 raw40043step0Labels = mixedMoment B raw40043step1 raw40043step1Labels := by
      have hz : ∀ j, raw40043step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40043step1 = (fun i j => raw40043step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40043step1 raw40043step0; decide +kernel
      have hl : raw40043step1Labels = raw40043step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043step0 raw40043step0Labels permutation104 hz
    mixedMoment B raw40043step1 raw40043step1Labels = mixedMoment B raw40043step2 raw40043step2Labels := by
      have hz : ∀ j, raw40043step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40043step2 = (fun i j => raw40043step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40043step2 raw40043step1; decide +kernel
      have hl : raw40043step2Labels = raw40043step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043step1 raw40043step1Labels permutation20 hz
    mixedMoment B raw40043step2 raw40043step2Labels = mixedMoment B raw40043step3 raw40043step3Labels := by
      have hz : ∀ j, raw40043step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw40043step3 = (fun i j => raw40043step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw40043step3 raw40043step2; decide +kernel
      have hl : raw40043step3Labels = raw40043step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40043step2 raw40043step2Labels permutation4 hz
    mixedMoment B raw40043step3 raw40043step3Labels = mixedMoment B raw40043step4 raw40043step4Labels := by
      have ha : raw40043step4 = (fun i j => raw40043step3 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40043step4 raw40043step3; decide +kernel
      have hl : raw40043step4Labels = raw40043step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40043step3 raw40043step3Labels permutation1 permutation6
    _ = mixedMoment B node162 node162Labels := by rfl

theorem canonical40044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40044 raw40044Labels = mixedMoment B node35 node35Labels := by
  calc
    mixedMoment B raw40044 raw40044Labels = mixedMoment B raw40044step0 raw40044step0Labels := by
      have hz : ∀ j, raw40044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40044step0 = (fun i j => raw40044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40044step0 raw40044; decide +kernel
      have hl : raw40044step0Labels = raw40044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40044 raw40044Labels permutation434 hz
    mixedMoment B raw40044step0 raw40044step0Labels = mixedMoment B raw40044step1 raw40044step1Labels := by
      have hz : ∀ j, raw40044step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40044step1 = (fun i j => raw40044step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40044step1 raw40044step0; decide +kernel
      have hl : raw40044step1Labels = raw40044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40044step0 raw40044step0Labels permutation80 hz
    mixedMoment B raw40044step1 raw40044step1Labels = mixedMoment B raw40044step2 raw40044step2Labels := by
      have hz : ∀ j, raw40044step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40044step2 = (fun i j => raw40044step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40044step2 raw40044step1; decide +kernel
      have hl : raw40044step2Labels = raw40044step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40044step1 raw40044step1Labels permutation14 hz
    mixedMoment B raw40044step2 raw40044step2Labels = mixedMoment B raw40044step3 raw40044step3Labels := by
      have ha : raw40044step3 = (fun i j => raw40044step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40044step3 raw40044step2; decide +kernel
      have hl : raw40044step3Labels = raw40044step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40044step2 raw40044step2Labels permutation7 permutation6
    _ = mixedMoment B node35 node35Labels := by rfl

theorem canonical40045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40045 raw40045Labels = mixedMoment B node100 node100Labels := by
  calc
    mixedMoment B raw40045 raw40045Labels = mixedMoment B raw40045step0 raw40045step0Labels := by
      have hz : ∀ j, raw40045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40045step0 = (fun i j => raw40045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40045step0 raw40045; decide +kernel
      have hl : raw40045step0Labels = raw40045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40045 raw40045Labels permutation434 hz
    mixedMoment B raw40045step0 raw40045step0Labels = mixedMoment B raw40045step1 raw40045step1Labels := by
      have hz : ∀ j, raw40045step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40045step1 = (fun i j => raw40045step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40045step1 raw40045step0; decide +kernel
      have hl : raw40045step1Labels = raw40045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40045step0 raw40045step0Labels permutation80 hz
    mixedMoment B raw40045step1 raw40045step1Labels = mixedMoment B raw40045step2 raw40045step2Labels := by
      have hz : ∀ j, raw40045step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40045step2 = (fun i j => raw40045step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40045step2 raw40045step1; decide +kernel
      have hl : raw40045step2Labels = raw40045step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40045step1 raw40045step1Labels permutation14 hz
    mixedMoment B raw40045step2 raw40045step2Labels = mixedMoment B raw40045step3 raw40045step3Labels := by
      have ha : raw40045step3 = (fun i j => raw40045step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40045step3 raw40045step2; decide +kernel
      have hl : raw40045step3Labels = raw40045step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40045step2 raw40045step2Labels permutation5 permutation6
    _ = mixedMoment B node100 node100Labels := by rfl

theorem canonical40046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40046 raw40046Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw40046 raw40046Labels = mixedMoment B raw40046step0 raw40046step0Labels := by
      have hz : ∀ j, raw40046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40046step0 = (fun i j => raw40046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40046step0 raw40046; decide +kernel
      have hl : raw40046step0Labels = raw40046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40046 raw40046Labels permutation346 hz
    mixedMoment B raw40046step0 raw40046step0Labels = mixedMoment B raw40046step1 raw40046step1Labels := by
      have hz : ∀ j, raw40046step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40046step1 = (fun i j => raw40046step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40046step1 raw40046step0; decide +kernel
      have hl : raw40046step1Labels = raw40046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40046step0 raw40046step0Labels permutation56 hz
    mixedMoment B raw40046step1 raw40046step1Labels = mixedMoment B raw40046step2 raw40046step2Labels := by
      have ha : raw40046step2 = (fun i j => raw40046step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40046step2 raw40046step1; decide +kernel
      have hl : raw40046step2Labels = raw40046step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40046step1 raw40046step1Labels permutation25 permutation6
    _ = mixedMoment B node70 node70Labels := by rfl

theorem canonical40047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40047 raw40047Labels = mixedMoment B node132 node132Labels := by
  calc
    mixedMoment B raw40047 raw40047Labels = mixedMoment B raw40047step0 raw40047step0Labels := by
      have hz : ∀ j, raw40047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40047step0 = (fun i j => raw40047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40047step0 raw40047; decide +kernel
      have hl : raw40047step0Labels = raw40047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40047 raw40047Labels permutation346 hz
    mixedMoment B raw40047step0 raw40047step0Labels = mixedMoment B raw40047step1 raw40047step1Labels := by
      have hz : ∀ j, raw40047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40047step1 = (fun i j => raw40047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40047step1 raw40047step0; decide +kernel
      have hl : raw40047step1Labels = raw40047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40047step0 raw40047step0Labels permutation56 hz
    mixedMoment B raw40047step1 raw40047step1Labels = mixedMoment B raw40047step2 raw40047step2Labels := by
      have ha : raw40047step2 = (fun i j => raw40047step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40047step2 raw40047step1; decide +kernel
      have hl : raw40047step2Labels = raw40047step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40047step1 raw40047step1Labels permutation9 permutation6
    mixedMoment B raw40047step2 raw40047step2Labels = mixedMoment B raw40047step3 raw40047step3Labels := by
      have ha : raw40047step3 = -raw40047step2 := by apply Matrix.ext; change ∀ i j, raw40047step3 i j = -(raw40047step2 i j); unfold raw40047step3 raw40047step2; decide +kernel
      have hl : raw40047step3Labels = raw40047step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node132 node132Labels := by rfl

theorem canonical40048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40048 raw40048Labels = mixedMoment B node38 node38Labels := by
  calc
    mixedMoment B raw40048 raw40048Labels = mixedMoment B raw40048step0 raw40048step0Labels := by
      have hz : ∀ j, raw40048 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40048step0 = (fun i j => raw40048 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40048step0 raw40048; decide +kernel
      have hl : raw40048step0Labels = raw40048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40048 raw40048Labels permutation520 hz
    mixedMoment B raw40048step0 raw40048step0Labels = mixedMoment B raw40048step1 raw40048step1Labels := by
      have hz : ∀ j, raw40048step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40048step1 = (fun i j => raw40048step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40048step1 raw40048step0; decide +kernel
      have hl : raw40048step1Labels = raw40048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40048step0 raw40048step0Labels permutation104 hz
    mixedMoment B raw40048step1 raw40048step1Labels = mixedMoment B raw40048step2 raw40048step2Labels := by
      have hz : ∀ j, raw40048step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40048step2 = (fun i j => raw40048step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40048step2 raw40048step1; decide +kernel
      have hl : raw40048step2Labels = raw40048step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40048step1 raw40048step1Labels permutation20 hz
    mixedMoment B raw40048step2 raw40048step2Labels = mixedMoment B raw40048step3 raw40048step3Labels := by
      have ha : raw40048step3 = (fun i j => raw40048step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40048step3 raw40048step2; decide +kernel
      have hl : raw40048step3Labels = raw40048step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40048step2 raw40048step2Labels permutation3 permutation6
    mixedMoment B raw40048step3 raw40048step3Labels = mixedMoment B raw40048step4 raw40048step4Labels := by
      have ha : raw40048step4 = -raw40048step3 := by apply Matrix.ext; change ∀ i j, raw40048step4 i j = -(raw40048step3 i j); unfold raw40048step4 raw40048step3; decide +kernel
      have hl : raw40048step4Labels = raw40048step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node38 node38Labels := by rfl

theorem canonical40049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40049 raw40049Labels = mixedMoment B node33 node33Labels := by
  calc
    mixedMoment B raw40049 raw40049Labels = mixedMoment B raw40049step0 raw40049step0Labels := by
      have hz : ∀ j, raw40049 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40049step0 = (fun i j => raw40049 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40049step0 raw40049; decide +kernel
      have hl : raw40049step0Labels = raw40049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40049 raw40049Labels permutation520 hz
    mixedMoment B raw40049step0 raw40049step0Labels = mixedMoment B raw40049step1 raw40049step1Labels := by
      have hz : ∀ j, raw40049step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40049step1 = (fun i j => raw40049step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40049step1 raw40049step0; decide +kernel
      have hl : raw40049step1Labels = raw40049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40049step0 raw40049step0Labels permutation104 hz
    mixedMoment B raw40049step1 raw40049step1Labels = mixedMoment B raw40049step2 raw40049step2Labels := by
      have ha : raw40049step2 = (fun i j => raw40049step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40049step2 raw40049step1; decide +kernel
      have hl : raw40049step2Labels = raw40049step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40049step1 raw40049step1Labels permutation11 permutation6
    mixedMoment B raw40049step2 raw40049step2Labels = mixedMoment B raw40049step3 raw40049step3Labels := by
      have ha : raw40049step3 = -raw40049step2 := by apply Matrix.ext; change ∀ i j, raw40049step3 i j = -(raw40049step2 i j); unfold raw40049step3 raw40049step2; decide +kernel
      have hl : raw40049step3Labels = raw40049step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node33 node33Labels := by rfl

theorem canonical40050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40050 raw40050Labels = mixedMoment B node40 node40Labels := by
  calc
    mixedMoment B raw40050 raw40050Labels = mixedMoment B raw40050step0 raw40050step0Labels := by
      have hz : ∀ j, raw40050 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40050step0 = (fun i j => raw40050 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40050step0 raw40050; decide +kernel
      have hl : raw40050step0Labels = raw40050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40050 raw40050Labels permutation520 hz
    mixedMoment B raw40050step0 raw40050step0Labels = mixedMoment B raw40050step1 raw40050step1Labels := by
      have hz : ∀ j, raw40050step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40050step1 = (fun i j => raw40050step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40050step1 raw40050step0; decide +kernel
      have hl : raw40050step1Labels = raw40050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40050step0 raw40050step0Labels permutation104 hz
    mixedMoment B raw40050step1 raw40050step1Labels = mixedMoment B raw40050step2 raw40050step2Labels := by
      have hz : ∀ j, raw40050step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40050step2 = (fun i j => raw40050step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40050step2 raw40050step1; decide +kernel
      have hl : raw40050step2Labels = raw40050step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40050step1 raw40050step1Labels permutation20 hz
    mixedMoment B raw40050step2 raw40050step2Labels = mixedMoment B raw40050step3 raw40050step3Labels := by
      have ha : raw40050step3 = (fun i j => raw40050step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40050step3 raw40050step2; decide +kernel
      have hl : raw40050step3Labels = raw40050step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40050step2 raw40050step2Labels permutation2 permutation6
    mixedMoment B raw40050step3 raw40050step3Labels = mixedMoment B raw40050step4 raw40050step4Labels := by
      have ha : raw40050step4 = -raw40050step3 := by apply Matrix.ext; change ∀ i j, raw40050step4 i j = -(raw40050step3 i j); unfold raw40050step4 raw40050step3; decide +kernel
      have hl : raw40050step4Labels = raw40050step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node40 node40Labels := by rfl

theorem canonical40051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40051 raw40051Labels = mixedMoment B node22 node22Labels := by
  calc
    mixedMoment B raw40051 raw40051Labels = mixedMoment B raw40051step0 raw40051step0Labels := by
      have ha : raw40051step0 = (fun i j => raw40051 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40051step0 raw40051; decide +kernel
      have hl : raw40051step0Labels = raw40051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40051 raw40051Labels permutation240 permutation6
    mixedMoment B raw40051step0 raw40051step0Labels = mixedMoment B raw40051step1 raw40051step1Labels := by
      have ha : raw40051step1 = -raw40051step0 := by apply Matrix.ext; change ∀ i j, raw40051step1 i j = -(raw40051step0 i j); unfold raw40051step1 raw40051step0; decide +kernel
      have hl : raw40051step1Labels = raw40051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node22 node22Labels := by rfl

theorem canonical40052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40052 raw40052Labels = mixedMoment B node26 node26Labels := by
  calc
    mixedMoment B raw40052 raw40052Labels = mixedMoment B raw40052step0 raw40052step0Labels := by
      have hz : ∀ j, raw40052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40052step0 = (fun i j => raw40052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40052step0 raw40052; decide +kernel
      have hl : raw40052step0Labels = raw40052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40052 raw40052Labels permutation434 hz
    mixedMoment B raw40052step0 raw40052step0Labels = mixedMoment B raw40052step1 raw40052step1Labels := by
      have ha : raw40052step1 = (fun i j => raw40052step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40052step1 raw40052step0; decide +kernel
      have hl : raw40052step1Labels = raw40052step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40052step0 raw40052step0Labels permutation50 permutation6
    mixedMoment B raw40052step1 raw40052step1Labels = mixedMoment B raw40052step2 raw40052step2Labels := by
      have ha : raw40052step2 = -raw40052step1 := by apply Matrix.ext; change ∀ i j, raw40052step2 i j = -(raw40052step1 i j); unfold raw40052step2 raw40052step1; decide +kernel
      have hl : raw40052step2Labels = raw40052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node26 node26Labels := by rfl

theorem canonical40053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40053 raw40053Labels = mixedMoment B node34 node34Labels := by
  calc
    mixedMoment B raw40053 raw40053Labels = mixedMoment B raw40053step0 raw40053step0Labels := by
      have hz : ∀ j, raw40053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40053step0 = (fun i j => raw40053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40053step0 raw40053; decide +kernel
      have hl : raw40053step0Labels = raw40053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40053 raw40053Labels permutation434 hz
    mixedMoment B raw40053step0 raw40053step0Labels = mixedMoment B raw40053step1 raw40053step1Labels := by
      have hz : ∀ j, raw40053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40053step1 = (fun i j => raw40053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40053step1 raw40053step0; decide +kernel
      have hl : raw40053step1Labels = raw40053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40053step0 raw40053step0Labels permutation80 hz
    mixedMoment B raw40053step1 raw40053step1Labels = mixedMoment B raw40053step2 raw40053step2Labels := by
      have ha : raw40053step2 = (fun i j => raw40053step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40053step2 raw40053step1; decide +kernel
      have hl : raw40053step2Labels = raw40053step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40053step1 raw40053step1Labels permutation8 permutation6
    mixedMoment B raw40053step2 raw40053step2Labels = mixedMoment B raw40053step3 raw40053step3Labels := by
      have ha : raw40053step3 = -raw40053step2 := by apply Matrix.ext; change ∀ i j, raw40053step3 i j = -(raw40053step2 i j); unfold raw40053step3 raw40053step2; decide +kernel
      have hl : raw40053step3Labels = raw40053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node34 node34Labels := by rfl

theorem canonical40054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40054 raw40054Labels = mixedMoment B node42 node42Labels := by
  calc
    mixedMoment B raw40054 raw40054Labels = mixedMoment B raw40054step0 raw40054step0Labels := by
      have hz : ∀ j, raw40054 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40054step0 = (fun i j => raw40054 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40054step0 raw40054; decide +kernel
      have hl : raw40054step0Labels = raw40054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054 raw40054Labels permutation520 hz
    mixedMoment B raw40054step0 raw40054step0Labels = mixedMoment B raw40054step1 raw40054step1Labels := by
      have hz : ∀ j, raw40054step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40054step1 = (fun i j => raw40054step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40054step1 raw40054step0; decide +kernel
      have hl : raw40054step1Labels = raw40054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054step0 raw40054step0Labels permutation104 hz
    mixedMoment B raw40054step1 raw40054step1Labels = mixedMoment B raw40054step2 raw40054step2Labels := by
      have hz : ∀ j, raw40054step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40054step2 = (fun i j => raw40054step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40054step2 raw40054step1; decide +kernel
      have hl : raw40054step2Labels = raw40054step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054step1 raw40054step1Labels permutation20 hz
    mixedMoment B raw40054step2 raw40054step2Labels = mixedMoment B raw40054step3 raw40054step3Labels := by
      have hz : ∀ j, raw40054step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw40054step3 = (fun i j => raw40054step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw40054step3 raw40054step2; decide +kernel
      have hl : raw40054step3Labels = raw40054step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40054step2 raw40054step2Labels permutation4 hz
    mixedMoment B raw40054step3 raw40054step3Labels = mixedMoment B raw40054step4 raw40054step4Labels := by
      have ha : raw40054step4 = (fun i j => raw40054step3 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40054step4 raw40054step3; decide +kernel
      have hl : raw40054step4Labels = raw40054step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40054step3 raw40054step3Labels permutation1 permutation6
    _ = mixedMoment B node42 node42Labels := by rfl

theorem canonical40055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40055 raw40055Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw40055 raw40055Labels = mixedMoment B raw40055step0 raw40055step0Labels := by
      have hz : ∀ j, raw40055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40055step0 = (fun i j => raw40055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40055step0 raw40055; decide +kernel
      have hl : raw40055step0Labels = raw40055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40055 raw40055Labels permutation434 hz
    mixedMoment B raw40055step0 raw40055step0Labels = mixedMoment B raw40055step1 raw40055step1Labels := by
      have ha : raw40055step1 = (fun i j => raw40055step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40055step1 raw40055step0; decide +kernel
      have hl : raw40055step1Labels = raw40055step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40055step0 raw40055step0Labels permutation32 permutation4
    mixedMoment B raw40055step1 raw40055step1Labels = mixedMoment B raw40055step2 raw40055step2Labels := by
      have ha : raw40055step2 = -raw40055step1 := by apply Matrix.ext; change ∀ i j, raw40055step2 i j = -(raw40055step1 i j); unfold raw40055step2 raw40055step1; decide +kernel
      have hl : raw40055step2Labels = raw40055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node397 node397Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 576) =
      Integer.Sparse.eval keyMomentRow576 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 576).leftCharge (GramAssembly.key 576).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 116) := by
    have ha : gramCharges (GramAssembly.key 576).leftCharge (GramAssembly.key 576).rightCharge = raw40024 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40024Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40024 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 576).leftCharge (GramAssembly.key 576).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow576, Integer.Sparse.eval]

theorem keyMoment577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 577) =
      Integer.Sparse.eval keyMomentRow577 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 577).leftCharge (GramAssembly.key 577).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 115) := by
    have ha : gramCharges (GramAssembly.key 577).leftCharge (GramAssembly.key 577).rightCharge = raw40025 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40025Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40025 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 577).leftCharge (GramAssembly.key 577).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow577, Integer.Sparse.eval]

theorem keyMoment578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 578) =
      Integer.Sparse.eval keyMomentRow578 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 578).leftCharge (GramAssembly.key 578).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 13) := by
    have ha : gramCharges (GramAssembly.key 578).leftCharge (GramAssembly.key 578).rightCharge = raw40026 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40026Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40026 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 578).leftCharge (GramAssembly.key 578).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow578, Integer.Sparse.eval]

theorem keyMoment579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 579) =
      Integer.Sparse.eval keyMomentRow579 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 579).leftCharge (GramAssembly.key 579).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 131) := by
    have ha : gramCharges (GramAssembly.key 579).leftCharge (GramAssembly.key 579).rightCharge = raw40027 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40027Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40027 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 579).leftCharge (GramAssembly.key 579).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow579, Integer.Sparse.eval]

theorem keyMoment580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 580) =
      Integer.Sparse.eval keyMomentRow580 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 580).leftCharge (GramAssembly.key 580).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 143) := by
    have ha : gramCharges (GramAssembly.key 580).leftCharge (GramAssembly.key 580).rightCharge = raw40028 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40028Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40028 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 580).leftCharge (GramAssembly.key 580).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow580, Integer.Sparse.eval]

theorem keyMoment581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 581) =
      Integer.Sparse.eval keyMomentRow581 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 581).leftCharge (GramAssembly.key 581).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 119) := by
    have ha : gramCharges (GramAssembly.key 581).leftCharge (GramAssembly.key 581).rightCharge = raw40029 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40029Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40029 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 581).leftCharge (GramAssembly.key 581).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow581, Integer.Sparse.eval]

theorem keyMoment582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 582) =
      Integer.Sparse.eval keyMomentRow582 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 582).leftCharge (GramAssembly.key 582).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 127) := by
    have ha : gramCharges (GramAssembly.key 582).leftCharge (GramAssembly.key 582).rightCharge = raw40030 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40030Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40030 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 582).leftCharge (GramAssembly.key 582).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow582, Integer.Sparse.eval]

theorem keyMoment583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 583) =
      Integer.Sparse.eval keyMomentRow583 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 583).leftCharge (GramAssembly.key 583).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 142) := by
    have ha : gramCharges (GramAssembly.key 583).leftCharge (GramAssembly.key 583).rightCharge = raw40031 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40031Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40031 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 583).leftCharge (GramAssembly.key 583).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow583, Integer.Sparse.eval]

theorem keyMoment584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 584) =
      Integer.Sparse.eval keyMomentRow584 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 584).leftCharge (GramAssembly.key 584).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 118) := by
    have ha : gramCharges (GramAssembly.key 584).leftCharge (GramAssembly.key 584).rightCharge = raw40032 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40032Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40032 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 584).leftCharge (GramAssembly.key 584).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow584, Integer.Sparse.eval]

theorem keyMoment585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 585) =
      Integer.Sparse.eval keyMomentRow585 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 585).leftCharge (GramAssembly.key 585).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 160) := by
    have ha : gramCharges (GramAssembly.key 585).leftCharge (GramAssembly.key 585).rightCharge = raw40033 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40033Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40033 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 585).leftCharge (GramAssembly.key 585).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow585, Integer.Sparse.eval]

theorem keyMoment586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 586) =
      Integer.Sparse.eval keyMomentRow586 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 586).leftCharge (GramAssembly.key 586).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 133) := by
    have ha : gramCharges (GramAssembly.key 586).leftCharge (GramAssembly.key 586).rightCharge = raw40034 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40034Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40034 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 586).leftCharge (GramAssembly.key 586).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow586, Integer.Sparse.eval]

theorem keyMoment587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 587) =
      Integer.Sparse.eval keyMomentRow587 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 587).leftCharge (GramAssembly.key 587).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 149) := by
    have ha : gramCharges (GramAssembly.key 587).leftCharge (GramAssembly.key 587).rightCharge = raw40035 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40035Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40035 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 587).leftCharge (GramAssembly.key 587).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow587, Integer.Sparse.eval]

theorem keyMoment588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 588) =
      Integer.Sparse.eval keyMomentRow588 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 588).leftCharge (GramAssembly.key 588).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 124) := by
    have ha : gramCharges (GramAssembly.key 588).leftCharge (GramAssembly.key 588).rightCharge = raw40036 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40036Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40036 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 588).leftCharge (GramAssembly.key 588).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow588, Integer.Sparse.eval]

theorem keyMoment589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 589) =
      Integer.Sparse.eval keyMomentRow589 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 589).leftCharge (GramAssembly.key 589).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 125) := by
    have ha : gramCharges (GramAssembly.key 589).leftCharge (GramAssembly.key 589).rightCharge = raw40037 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40037Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40037 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 589).leftCharge (GramAssembly.key 589).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow589, Integer.Sparse.eval]

theorem keyMoment590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 590) =
      Integer.Sparse.eval keyMomentRow590 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 590).leftCharge (GramAssembly.key 590).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 126) := by
    have ha : gramCharges (GramAssembly.key 590).leftCharge (GramAssembly.key 590).rightCharge = raw40038 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40038Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40038 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 590).leftCharge (GramAssembly.key 590).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow590, Integer.Sparse.eval]

theorem keyMoment591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 591) =
      Integer.Sparse.eval keyMomentRow591 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 591).leftCharge (GramAssembly.key 591).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 158) := by
    have ha : gramCharges (GramAssembly.key 591).leftCharge (GramAssembly.key 591).rightCharge = raw40039 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40039Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40039 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 591).leftCharge (GramAssembly.key 591).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow591, Integer.Sparse.eval]

theorem keyMoment592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 592) =
      Integer.Sparse.eval keyMomentRow592 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 592).leftCharge (GramAssembly.key 592).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 129) := by
    have ha : gramCharges (GramAssembly.key 592).leftCharge (GramAssembly.key 592).rightCharge = raw40040 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40040Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40040 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 592).leftCharge (GramAssembly.key 592).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow592, Integer.Sparse.eval]

theorem keyMoment593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 593) =
      Integer.Sparse.eval keyMomentRow593 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 593).leftCharge (GramAssembly.key 593).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 146) := by
    have ha : gramCharges (GramAssembly.key 593).leftCharge (GramAssembly.key 593).rightCharge = raw40041 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40041Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40041 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 593).leftCharge (GramAssembly.key 593).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow593, Integer.Sparse.eval]

theorem keyMoment594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 594) =
      Integer.Sparse.eval keyMomentRow594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 121) := by
    have ha : gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge = raw40042 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40042Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40042 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 594).leftCharge (GramAssembly.key 594).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow594, Integer.Sparse.eval]

theorem keyMoment595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 595) =
      Integer.Sparse.eval keyMomentRow595 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 595).leftCharge (GramAssembly.key 595).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 162) := by
    have ha : gramCharges (GramAssembly.key 595).leftCharge (GramAssembly.key 595).rightCharge = raw40043 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40043Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40043 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 595).leftCharge (GramAssembly.key 595).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow595, Integer.Sparse.eval]

theorem keyMoment596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 596) =
      Integer.Sparse.eval keyMomentRow596 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 596).leftCharge (GramAssembly.key 596).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 35) := by
    have ha : gramCharges (GramAssembly.key 596).leftCharge (GramAssembly.key 596).rightCharge = raw40044 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40044Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40044 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 596).leftCharge (GramAssembly.key 596).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow596, Integer.Sparse.eval]

theorem keyMoment597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 597) =
      Integer.Sparse.eval keyMomentRow597 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 597).leftCharge (GramAssembly.key 597).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 100) := by
    have ha : gramCharges (GramAssembly.key 597).leftCharge (GramAssembly.key 597).rightCharge = raw40045 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40045Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40045 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 597).leftCharge (GramAssembly.key 597).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow597, Integer.Sparse.eval]

theorem keyMoment598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 598) =
      Integer.Sparse.eval keyMomentRow598 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 598).leftCharge (GramAssembly.key 598).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 70) := by
    have ha : gramCharges (GramAssembly.key 598).leftCharge (GramAssembly.key 598).rightCharge = raw40046 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40046Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40046 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 598).leftCharge (GramAssembly.key 598).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow598, Integer.Sparse.eval]

theorem keyMoment599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 599) =
      Integer.Sparse.eval keyMomentRow599 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 599).leftCharge (GramAssembly.key 599).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 132) := by
    have ha : gramCharges (GramAssembly.key 599).leftCharge (GramAssembly.key 599).rightCharge = raw40047 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40047Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40047 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 599).leftCharge (GramAssembly.key 599).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow599, Integer.Sparse.eval]

theorem keyMoment600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 600) =
      Integer.Sparse.eval keyMomentRow600 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 600).leftCharge (GramAssembly.key 600).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 38) := by
    have ha : gramCharges (GramAssembly.key 600).leftCharge (GramAssembly.key 600).rightCharge = raw40048 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40048Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40048 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 600).leftCharge (GramAssembly.key 600).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow600, Integer.Sparse.eval]

theorem keyMoment601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 601) =
      Integer.Sparse.eval keyMomentRow601 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 601).leftCharge (GramAssembly.key 601).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 33) := by
    have ha : gramCharges (GramAssembly.key 601).leftCharge (GramAssembly.key 601).rightCharge = raw40049 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40049Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40049 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 601).leftCharge (GramAssembly.key 601).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow601, Integer.Sparse.eval]

theorem keyMoment602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 602) =
      Integer.Sparse.eval keyMomentRow602 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 602).leftCharge (GramAssembly.key 602).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 40) := by
    have ha : gramCharges (GramAssembly.key 602).leftCharge (GramAssembly.key 602).rightCharge = raw40050 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40050Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40050 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 602).leftCharge (GramAssembly.key 602).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow602, Integer.Sparse.eval]

theorem keyMoment603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 603) =
      Integer.Sparse.eval keyMomentRow603 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 603).leftCharge (GramAssembly.key 603).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 22) := by
    have ha : gramCharges (GramAssembly.key 603).leftCharge (GramAssembly.key 603).rightCharge = raw40051 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40051Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40051 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 603).leftCharge (GramAssembly.key 603).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow603, Integer.Sparse.eval]

theorem keyMoment604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 604) =
      Integer.Sparse.eval keyMomentRow604 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 604).leftCharge (GramAssembly.key 604).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 26) := by
    have ha : gramCharges (GramAssembly.key 604).leftCharge (GramAssembly.key 604).rightCharge = raw40052 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40052Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40052 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 604).leftCharge (GramAssembly.key 604).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow604, Integer.Sparse.eval]

theorem keyMoment605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 605) =
      Integer.Sparse.eval keyMomentRow605 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 605).leftCharge (GramAssembly.key 605).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 34) := by
    have ha : gramCharges (GramAssembly.key 605).leftCharge (GramAssembly.key 605).rightCharge = raw40053 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40053Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40053 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 605).leftCharge (GramAssembly.key 605).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow605, Integer.Sparse.eval]

theorem keyMoment606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 606) =
      Integer.Sparse.eval keyMomentRow606 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 606).leftCharge (GramAssembly.key 606).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 42) := by
    have ha : gramCharges (GramAssembly.key 606).leftCharge (GramAssembly.key 606).rightCharge = raw40054 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40054Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40054 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 606).leftCharge (GramAssembly.key 606).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow606, Integer.Sparse.eval]

theorem keyMoment607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 607) =
      Integer.Sparse.eval keyMomentRow607 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 607).leftCharge (GramAssembly.key 607).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 607).leftCharge (GramAssembly.key 607).rightCharge = raw40055 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40055Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40055 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 607).leftCharge (GramAssembly.key 607).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow607, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt576 : keyMomentRows (576 : Fin 2886) =
    keyMomentRow576 := by decide +kernel

theorem keyMomentRowsAt577 : keyMomentRows (577 : Fin 2886) =
    keyMomentRow577 := by decide +kernel

theorem keyMomentRowsAt578 : keyMomentRows (578 : Fin 2886) =
    keyMomentRow578 := by decide +kernel

theorem keyMomentRowsAt579 : keyMomentRows (579 : Fin 2886) =
    keyMomentRow579 := by decide +kernel

theorem keyMomentRowsAt580 : keyMomentRows (580 : Fin 2886) =
    keyMomentRow580 := by decide +kernel

theorem keyMomentRowsAt581 : keyMomentRows (581 : Fin 2886) =
    keyMomentRow581 := by decide +kernel

theorem keyMomentRowsAt582 : keyMomentRows (582 : Fin 2886) =
    keyMomentRow582 := by decide +kernel

theorem keyMomentRowsAt583 : keyMomentRows (583 : Fin 2886) =
    keyMomentRow583 := by decide +kernel

theorem keyMomentRowsAt584 : keyMomentRows (584 : Fin 2886) =
    keyMomentRow584 := by decide +kernel

theorem keyMomentRowsAt585 : keyMomentRows (585 : Fin 2886) =
    keyMomentRow585 := by decide +kernel

theorem keyMomentRowsAt586 : keyMomentRows (586 : Fin 2886) =
    keyMomentRow586 := by decide +kernel

theorem keyMomentRowsAt587 : keyMomentRows (587 : Fin 2886) =
    keyMomentRow587 := by decide +kernel

theorem keyMomentRowsAt588 : keyMomentRows (588 : Fin 2886) =
    keyMomentRow588 := by decide +kernel

theorem keyMomentRowsAt589 : keyMomentRows (589 : Fin 2886) =
    keyMomentRow589 := by decide +kernel

theorem keyMomentRowsAt590 : keyMomentRows (590 : Fin 2886) =
    keyMomentRow590 := by decide +kernel

theorem keyMomentRowsAt591 : keyMomentRows (591 : Fin 2886) =
    keyMomentRow591 := by decide +kernel

theorem keyMomentRowsAt592 : keyMomentRows (592 : Fin 2886) =
    keyMomentRow592 := by decide +kernel

theorem keyMomentRowsAt593 : keyMomentRows (593 : Fin 2886) =
    keyMomentRow593 := by decide +kernel

theorem keyMomentRowsAt594 : keyMomentRows (594 : Fin 2886) =
    keyMomentRow594 := by decide +kernel

theorem keyMomentRowsAt595 : keyMomentRows (595 : Fin 2886) =
    keyMomentRow595 := by decide +kernel

theorem keyMomentRowsAt596 : keyMomentRows (596 : Fin 2886) =
    keyMomentRow596 := by decide +kernel

theorem keyMomentRowsAt597 : keyMomentRows (597 : Fin 2886) =
    keyMomentRow597 := by decide +kernel

theorem keyMomentRowsAt598 : keyMomentRows (598 : Fin 2886) =
    keyMomentRow598 := by decide +kernel

theorem keyMomentRowsAt599 : keyMomentRows (599 : Fin 2886) =
    keyMomentRow599 := by decide +kernel

theorem keyMomentRowsAt600 : keyMomentRows (600 : Fin 2886) =
    keyMomentRow600 := by decide +kernel

theorem keyMomentRowsAt601 : keyMomentRows (601 : Fin 2886) =
    keyMomentRow601 := by decide +kernel

theorem keyMomentRowsAt602 : keyMomentRows (602 : Fin 2886) =
    keyMomentRow602 := by decide +kernel

theorem keyMomentRowsAt603 : keyMomentRows (603 : Fin 2886) =
    keyMomentRow603 := by decide +kernel

theorem keyMomentRowsAt604 : keyMomentRows (604 : Fin 2886) =
    keyMomentRow604 := by decide +kernel

theorem keyMomentRowsAt605 : keyMomentRows (605 : Fin 2886) =
    keyMomentRow605 := by decide +kernel

theorem keyMomentRowsAt606 : keyMomentRows (606 : Fin 2886) =
    keyMomentRow606 := by decide +kernel

theorem keyMomentRowsAt607 : keyMomentRows (607 : Fin 2886) =
    keyMomentRow607 := by decide +kernel

theorem keyMomentChunkSound18_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 18) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 576 ∨ k.val = 577 ∨ k.val = 578 ∨ k.val = 579 ∨ k.val = 580 ∨ k.val = 581 ∨ k.val = 582 ∨ k.val = 583 ∨ k.val = 584 ∨ k.val = 585 ∨ k.val = 586 ∨ k.val = 587 ∨ k.val = 588 ∨ k.val = 589 ∨ k.val = 590 ∨ k.val = 591 ∨ k.val = 592 ∨ k.val = 593 ∨ k.val = 594 ∨ k.val = 595 ∨ k.val = 596 ∨ k.val = 597 ∨ k.val = 598 ∨ k.val = 599 ∨ k.val = 600 ∨ k.val = 601 ∨ k.val = 602 ∨ k.val = 603 ∨ k.val = 604 ∨ k.val = 605 ∨ k.val = 606 ∨ k.val = 607 := by omega
  rcases heq with h576 | h577 | h578 | h579 | h580 | h581 | h582 | h583 | h584 | h585 | h586 | h587 | h588 | h589 | h590 | h591 | h592 | h593 | h594 | h595 | h596 | h597 | h598 | h599 | h600 | h601 | h602 | h603 | h604 | h605 | h606 | h607
  · have he : k = (576 : Fin 2886) := Fin.ext h576
    subst k
    rw [keyMomentRowsAt576]
    exact keyMoment576 B hB
  · have he : k = (577 : Fin 2886) := Fin.ext h577
    subst k
    rw [keyMomentRowsAt577]
    exact keyMoment577 B hB
  · have he : k = (578 : Fin 2886) := Fin.ext h578
    subst k
    rw [keyMomentRowsAt578]
    exact keyMoment578 B hB
  · have he : k = (579 : Fin 2886) := Fin.ext h579
    subst k
    rw [keyMomentRowsAt579]
    exact keyMoment579 B hB
  · have he : k = (580 : Fin 2886) := Fin.ext h580
    subst k
    rw [keyMomentRowsAt580]
    exact keyMoment580 B hB
  · have he : k = (581 : Fin 2886) := Fin.ext h581
    subst k
    rw [keyMomentRowsAt581]
    exact keyMoment581 B hB
  · have he : k = (582 : Fin 2886) := Fin.ext h582
    subst k
    rw [keyMomentRowsAt582]
    exact keyMoment582 B hB
  · have he : k = (583 : Fin 2886) := Fin.ext h583
    subst k
    rw [keyMomentRowsAt583]
    exact keyMoment583 B hB
  · have he : k = (584 : Fin 2886) := Fin.ext h584
    subst k
    rw [keyMomentRowsAt584]
    exact keyMoment584 B hB
  · have he : k = (585 : Fin 2886) := Fin.ext h585
    subst k
    rw [keyMomentRowsAt585]
    exact keyMoment585 B hB
  · have he : k = (586 : Fin 2886) := Fin.ext h586
    subst k
    rw [keyMomentRowsAt586]
    exact keyMoment586 B hB
  · have he : k = (587 : Fin 2886) := Fin.ext h587
    subst k
    rw [keyMomentRowsAt587]
    exact keyMoment587 B hB
  · have he : k = (588 : Fin 2886) := Fin.ext h588
    subst k
    rw [keyMomentRowsAt588]
    exact keyMoment588 B hB
  · have he : k = (589 : Fin 2886) := Fin.ext h589
    subst k
    rw [keyMomentRowsAt589]
    exact keyMoment589 B hB
  · have he : k = (590 : Fin 2886) := Fin.ext h590
    subst k
    rw [keyMomentRowsAt590]
    exact keyMoment590 B hB
  · have he : k = (591 : Fin 2886) := Fin.ext h591
    subst k
    rw [keyMomentRowsAt591]
    exact keyMoment591 B hB
  · have he : k = (592 : Fin 2886) := Fin.ext h592
    subst k
    rw [keyMomentRowsAt592]
    exact keyMoment592 B hB
  · have he : k = (593 : Fin 2886) := Fin.ext h593
    subst k
    rw [keyMomentRowsAt593]
    exact keyMoment593 B hB
  · have he : k = (594 : Fin 2886) := Fin.ext h594
    subst k
    rw [keyMomentRowsAt594]
    exact keyMoment594 B hB
  · have he : k = (595 : Fin 2886) := Fin.ext h595
    subst k
    rw [keyMomentRowsAt595]
    exact keyMoment595 B hB
  · have he : k = (596 : Fin 2886) := Fin.ext h596
    subst k
    rw [keyMomentRowsAt596]
    exact keyMoment596 B hB
  · have he : k = (597 : Fin 2886) := Fin.ext h597
    subst k
    rw [keyMomentRowsAt597]
    exact keyMoment597 B hB
  · have he : k = (598 : Fin 2886) := Fin.ext h598
    subst k
    rw [keyMomentRowsAt598]
    exact keyMoment598 B hB
  · have he : k = (599 : Fin 2886) := Fin.ext h599
    subst k
    rw [keyMomentRowsAt599]
    exact keyMoment599 B hB
  · have he : k = (600 : Fin 2886) := Fin.ext h600
    subst k
    rw [keyMomentRowsAt600]
    exact keyMoment600 B hB
  · have he : k = (601 : Fin 2886) := Fin.ext h601
    subst k
    rw [keyMomentRowsAt601]
    exact keyMoment601 B hB
  · have he : k = (602 : Fin 2886) := Fin.ext h602
    subst k
    rw [keyMomentRowsAt602]
    exact keyMoment602 B hB
  · have he : k = (603 : Fin 2886) := Fin.ext h603
    subst k
    rw [keyMomentRowsAt603]
    exact keyMoment603 B hB
  · have he : k = (604 : Fin 2886) := Fin.ext h604
    subst k
    rw [keyMomentRowsAt604]
    exact keyMoment604 B hB
  · have he : k = (605 : Fin 2886) := Fin.ext h605
    subst k
    rw [keyMomentRowsAt605]
    exact keyMoment605 B hB
  · have he : k = (606 : Fin 2886) := Fin.ext h606
    subst k
    rw [keyMomentRowsAt606]
    exact keyMoment606 B hB
  · have he : k = (607 : Fin 2886) := Fin.ext h607
    subst k
    rw [keyMomentRowsAt607]
    exact keyMoment607 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound18_e_oai
