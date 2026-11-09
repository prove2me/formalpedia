-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:55:05.990771+00:00
-- url     : https://prove2.me/submissions/0957fbeb-a72b-4f2b-b2b0-b1e3805f194c

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical318
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40736 raw40736Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw40736 raw40736Labels = mixedMoment B raw40736step0 raw40736step0Labels := by
      have hz : ∀ j, raw40736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40736step0 = (fun i j => raw40736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40736step0 raw40736; decide +kernel
      have hl : raw40736step0Labels = raw40736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40736 raw40736Labels permutation434 hz
    mixedMoment B raw40736step0 raw40736step0Labels = mixedMoment B raw40736step1 raw40736step1Labels := by
      have ha : raw40736step1 = (fun i j => raw40736step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40736step1 raw40736step0; decide +kernel
      have hl : raw40736step1Labels = raw40736step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40736step0 raw40736step0Labels permutation61 permutation6
    mixedMoment B raw40736step1 raw40736step1Labels = mixedMoment B raw40736step2 raw40736step2Labels := by
      have ha : raw40736step2 = -raw40736step1 := by apply Matrix.ext; change ∀ i j, raw40736step2 i j = -(raw40736step1 i j); unfold raw40736step2 raw40736step1; decide +kernel
      have hl : raw40736step2Labels = raw40736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical40737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40737 raw40737Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw40737 raw40737Labels = mixedMoment B raw40737step0 raw40737step0Labels := by
      have hz : ∀ j, raw40737 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40737step0 = (fun i j => raw40737 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40737step0 raw40737; decide +kernel
      have hl : raw40737step0Labels = raw40737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40737 raw40737Labels permutation434 hz
    mixedMoment B raw40737step0 raw40737step0Labels = mixedMoment B raw40737step1 raw40737step1Labels := by
      have ha : raw40737step1 = (fun i j => raw40737step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40737step1 raw40737step0; decide +kernel
      have hl : raw40737step1Labels = raw40737step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40737step0 raw40737step0Labels permutation59 permutation6
    mixedMoment B raw40737step1 raw40737step1Labels = mixedMoment B raw40737step2 raw40737step2Labels := by
      have ha : raw40737step2 = -raw40737step1 := by apply Matrix.ext; change ∀ i j, raw40737step2 i j = -(raw40737step1 i j); unfold raw40737step2 raw40737step1; decide +kernel
      have hl : raw40737step2Labels = raw40737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2620 node2620Labels := by rfl

theorem canonical40738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40738 raw40738Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw40738 raw40738Labels = mixedMoment B raw40738step0 raw40738step0Labels := by
      have ha : raw40738step0 = (fun i j => raw40738 (permutation286 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40738step0 raw40738; decide +kernel
      have hl : raw40738step0Labels = raw40738Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40738 raw40738Labels permutation286 permutation6
    mixedMoment B raw40738step0 raw40738step0Labels = mixedMoment B raw40738step1 raw40738step1Labels := by
      have ha : raw40738step1 = -raw40738step0 := by apply Matrix.ext; change ∀ i j, raw40738step1 i j = -(raw40738step0 i j); unfold raw40738step1 raw40738step0; decide +kernel
      have hl : raw40738step1Labels = raw40738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2614 node2614Labels := by rfl

theorem canonical40739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40739 raw40739Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw40739 raw40739Labels = mixedMoment B raw40739step0 raw40739step0Labels := by
      have hz : ∀ j, raw40739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40739step0 = (fun i j => raw40739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40739step0 raw40739; decide +kernel
      have hl : raw40739step0Labels = raw40739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40739 raw40739Labels permutation520 hz
    mixedMoment B raw40739step0 raw40739step0Labels = mixedMoment B raw40739step1 raw40739step1Labels := by
      have ha : raw40739step1 = (fun i j => raw40739step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40739step1 raw40739step0; decide +kernel
      have hl : raw40739step1Labels = raw40739step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40739step0 raw40739step0Labels permutation56 permutation6
    mixedMoment B raw40739step1 raw40739step1Labels = mixedMoment B raw40739step2 raw40739step2Labels := by
      have ha : raw40739step2 = -raw40739step1 := by apply Matrix.ext; change ∀ i j, raw40739step2 i j = -(raw40739step1 i j); unfold raw40739step2 raw40739step1; decide +kernel
      have hl : raw40739step2Labels = raw40739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2641 node2641Labels := by rfl

theorem canonical40740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40740 raw40740Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw40740 raw40740Labels = mixedMoment B raw40740step0 raw40740step0Labels := by
      have ha : raw40740step0 = (fun i j => raw40740 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40740step0 raw40740; decide +kernel
      have hl : raw40740step0Labels = raw40740Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40740 raw40740Labels permutation287 permutation6
    mixedMoment B raw40740step0 raw40740step0Labels = mixedMoment B raw40740step1 raw40740step1Labels := by
      have ha : raw40740step1 = -raw40740step0 := by apply Matrix.ext; change ∀ i j, raw40740step1 i j = -(raw40740step0 i j); unfold raw40740step1 raw40740step0; decide +kernel
      have hl : raw40740step1Labels = raw40740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical40741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40741 raw40741Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw40741 raw40741Labels = mixedMoment B raw40741step0 raw40741step0Labels := by
      have ha : raw40741step0 = (fun i j => raw40741 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40741step0 raw40741; decide +kernel
      have hl : raw40741step0Labels = raw40741Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40741 raw40741Labels permutation277 permutation6
    mixedMoment B raw40741step0 raw40741step0Labels = mixedMoment B raw40741step1 raw40741step1Labels := by
      have ha : raw40741step1 = -raw40741step0 := by apply Matrix.ext; change ∀ i j, raw40741step1 i j = -(raw40741step0 i j); unfold raw40741step1 raw40741step0; decide +kernel
      have hl : raw40741step1Labels = raw40741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2617 node2617Labels := by rfl

theorem canonical40742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40742 raw40742Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw40742 raw40742Labels = mixedMoment B raw40742step0 raw40742step0Labels := by
      have hz : ∀ j, raw40742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40742step0 = (fun i j => raw40742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40742step0 raw40742; decide +kernel
      have hl : raw40742step0Labels = raw40742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40742 raw40742Labels permutation434 hz
    mixedMoment B raw40742step0 raw40742step0Labels = mixedMoment B raw40742step1 raw40742step1Labels := by
      have ha : raw40742step1 = (fun i j => raw40742step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40742step1 raw40742step0; decide +kernel
      have hl : raw40742step1Labels = raw40742step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40742step0 raw40742step0Labels permutation60 permutation6
    mixedMoment B raw40742step1 raw40742step1Labels = mixedMoment B raw40742step2 raw40742step2Labels := by
      have ha : raw40742step2 = -raw40742step1 := by apply Matrix.ext; change ∀ i j, raw40742step2 i j = -(raw40742step1 i j); unfold raw40742step2 raw40742step1; decide +kernel
      have hl : raw40742step2Labels = raw40742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical40743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40743 raw40743Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw40743 raw40743Labels = mixedMoment B raw40743step0 raw40743step0Labels := by
      have hz : ∀ j, raw40743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40743step0 = (fun i j => raw40743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40743step0 raw40743; decide +kernel
      have hl : raw40743step0Labels = raw40743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40743 raw40743Labels permutation434 hz
    mixedMoment B raw40743step0 raw40743step0Labels = mixedMoment B raw40743step1 raw40743step1Labels := by
      have ha : raw40743step1 = (fun i j => raw40743step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40743step1 raw40743step0; decide +kernel
      have hl : raw40743step1Labels = raw40743step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40743step0 raw40743step0Labels permutation58 permutation6
    mixedMoment B raw40743step1 raw40743step1Labels = mixedMoment B raw40743step2 raw40743step2Labels := by
      have ha : raw40743step2 = -raw40743step1 := by apply Matrix.ext; change ∀ i j, raw40743step2 i j = -(raw40743step1 i j); unfold raw40743step2 raw40743step1; decide +kernel
      have hl : raw40743step2Labels = raw40743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

theorem canonical40744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40744 raw40744Labels = mixedMoment B node2635 node2635Labels := by
  calc
    mixedMoment B raw40744 raw40744Labels = mixedMoment B raw40744step0 raw40744step0Labels := by
      have hz : ∀ j, raw40744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40744step0 = (fun i j => raw40744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40744step0 raw40744; decide +kernel
      have hl : raw40744step0Labels = raw40744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40744 raw40744Labels permutation434 hz
    mixedMoment B raw40744step0 raw40744step0Labels = mixedMoment B raw40744step1 raw40744step1Labels := by
      have hz : ∀ j, raw40744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40744step1 = (fun i j => raw40744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40744step1 raw40744step0; decide +kernel
      have hl : raw40744step1Labels = raw40744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40744step0 raw40744step0Labels permutation80 hz
    mixedMoment B raw40744step1 raw40744step1Labels = mixedMoment B raw40744step2 raw40744step2Labels := by
      have ha : raw40744step2 = (fun i j => raw40744step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40744step2 raw40744step1; decide +kernel
      have hl : raw40744step2Labels = raw40744step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40744step1 raw40744step1Labels permutation24 permutation6
    _ = mixedMoment B node2635 node2635Labels := by rfl

theorem canonical40745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40745 raw40745Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw40745 raw40745Labels = mixedMoment B raw40745step0 raw40745step0Labels := by
      have hz : ∀ j, raw40745 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40745step0 = (fun i j => raw40745 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40745step0 raw40745; decide +kernel
      have hl : raw40745step0Labels = raw40745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40745 raw40745Labels permutation434 hz
    mixedMoment B raw40745step0 raw40745step0Labels = mixedMoment B raw40745step1 raw40745step1Labels := by
      have hz : ∀ j, raw40745step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40745step1 = (fun i j => raw40745step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40745step1 raw40745step0; decide +kernel
      have hl : raw40745step1Labels = raw40745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40745step0 raw40745step0Labels permutation80 hz
    mixedMoment B raw40745step1 raw40745step1Labels = mixedMoment B raw40745step2 raw40745step2Labels := by
      have ha : raw40745step2 = (fun i j => raw40745step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40745step2 raw40745step1; decide +kernel
      have hl : raw40745step2Labels = raw40745step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40745step1 raw40745step1Labels permutation30 permutation6
    _ = mixedMoment B node1264 node1264Labels := by rfl

theorem canonical40746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40746 raw40746Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw40746 raw40746Labels = mixedMoment B raw40746step0 raw40746step0Labels := by
      have hz : ∀ j, raw40746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40746step0 = (fun i j => raw40746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40746step0 raw40746; decide +kernel
      have hl : raw40746step0Labels = raw40746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40746 raw40746Labels permutation346 hz
    mixedMoment B raw40746step0 raw40746step0Labels = mixedMoment B raw40746step1 raw40746step1Labels := by
      have ha : raw40746step1 = (fun i j => raw40746step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40746step1 raw40746step0; decide +kernel
      have hl : raw40746step1Labels = raw40746step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40746step0 raw40746step0Labels permutation96 permutation6
    _ = mixedMoment B node2569 node2569Labels := by rfl

theorem canonical40747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40747 raw40747Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw40747 raw40747Labels = mixedMoment B raw40747step0 raw40747step0Labels := by
      have hz : ∀ j, raw40747 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40747step0 = (fun i j => raw40747 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40747step0 raw40747; decide +kernel
      have hl : raw40747step0Labels = raw40747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40747 raw40747Labels permutation520 hz
    mixedMoment B raw40747step0 raw40747step0Labels = mixedMoment B raw40747step1 raw40747step1Labels := by
      have hz : ∀ j, raw40747step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40747step1 = (fun i j => raw40747step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40747step1 raw40747step0; decide +kernel
      have hl : raw40747step1Labels = raw40747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40747step0 raw40747step0Labels permutation104 hz
    mixedMoment B raw40747step1 raw40747step1Labels = mixedMoment B raw40747step2 raw40747step2Labels := by
      have hz : ∀ j, raw40747step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40747step2 = (fun i j => raw40747step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40747step2 raw40747step1; decide +kernel
      have hl : raw40747step2Labels = raw40747step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40747step1 raw40747step1Labels permutation20 hz
    mixedMoment B raw40747step2 raw40747step2Labels = mixedMoment B raw40747step3 raw40747step3Labels := by
      have ha : raw40747step3 = (fun i j => raw40747step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40747step3 raw40747step2; decide +kernel
      have hl : raw40747step3Labels = raw40747step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40747step2 raw40747step2Labels permutation7 permutation3
    mixedMoment B raw40747step3 raw40747step3Labels = mixedMoment B raw40747step4 raw40747step4Labels := by
      have ha : raw40747step4 = -raw40747step3 := by apply Matrix.ext; change ∀ i j, raw40747step4 i j = -(raw40747step3 i j); unfold raw40747step4 raw40747step3; decide +kernel
      have hl : raw40747step4Labels = raw40747step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

theorem canonical40748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40748 raw40748Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw40748 raw40748Labels = mixedMoment B raw40748step0 raw40748step0Labels := by
      have hz : ∀ j, raw40748 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40748step0 = (fun i j => raw40748 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40748step0 raw40748; decide +kernel
      have hl : raw40748step0Labels = raw40748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40748 raw40748Labels permutation434 hz
    mixedMoment B raw40748step0 raw40748step0Labels = mixedMoment B raw40748step1 raw40748step1Labels := by
      have hz : ∀ j, raw40748step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40748step1 = (fun i j => raw40748step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40748step1 raw40748step0; decide +kernel
      have hl : raw40748step1Labels = raw40748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40748step0 raw40748step0Labels permutation80 hz
    mixedMoment B raw40748step1 raw40748step1Labels = mixedMoment B raw40748step2 raw40748step2Labels := by
      have ha : raw40748step2 = (fun i j => raw40748step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40748step2 raw40748step1; decide +kernel
      have hl : raw40748step2Labels = raw40748step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40748step1 raw40748step1Labels permutation31 permutation3
    mixedMoment B raw40748step2 raw40748step2Labels = mixedMoment B raw40748step3 raw40748step3Labels := by
      have ha : raw40748step3 = -raw40748step2 := by apply Matrix.ext; change ∀ i j, raw40748step3 i j = -(raw40748step2 i j); unfold raw40748step3 raw40748step2; decide +kernel
      have hl : raw40748step3Labels = raw40748step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

theorem canonical40749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40749 raw40749Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw40749 raw40749Labels = mixedMoment B raw40749step0 raw40749step0Labels := by
      have hz : ∀ j, raw40749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40749step0 = (fun i j => raw40749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40749step0 raw40749; decide +kernel
      have hl : raw40749step0Labels = raw40749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40749 raw40749Labels permutation434 hz
    mixedMoment B raw40749step0 raw40749step0Labels = mixedMoment B raw40749step1 raw40749step1Labels := by
      have hz : ∀ j, raw40749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40749step1 = (fun i j => raw40749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40749step1 raw40749step0; decide +kernel
      have hl : raw40749step1Labels = raw40749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40749step0 raw40749step0Labels permutation80 hz
    mixedMoment B raw40749step1 raw40749step1Labels = mixedMoment B raw40749step2 raw40749step2Labels := by
      have ha : raw40749step2 = (fun i j => raw40749step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40749step2 raw40749step1; decide +kernel
      have hl : raw40749step2Labels = raw40749step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40749step1 raw40749step1Labels permutation18 permutation6
    _ = mixedMoment B node3886 node3886Labels := by rfl

theorem canonical40750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40750 raw40750Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw40750 raw40750Labels = mixedMoment B raw40750step0 raw40750step0Labels := by
      have hz : ∀ j, raw40750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40750step0 = (fun i j => raw40750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40750step0 raw40750; decide +kernel
      have hl : raw40750step0Labels = raw40750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40750 raw40750Labels permutation434 hz
    mixedMoment B raw40750step0 raw40750step0Labels = mixedMoment B raw40750step1 raw40750step1Labels := by
      have hz : ∀ j, raw40750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40750step1 = (fun i j => raw40750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40750step1 raw40750step0; decide +kernel
      have hl : raw40750step1Labels = raw40750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40750step0 raw40750step0Labels permutation80 hz
    mixedMoment B raw40750step1 raw40750step1Labels = mixedMoment B raw40750step2 raw40750step2Labels := by
      have ha : raw40750step2 = (fun i j => raw40750step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40750step2 raw40750step1; decide +kernel
      have hl : raw40750step2Labels = raw40750step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40750step1 raw40750step1Labels permutation21 permutation6
    mixedMoment B raw40750step2 raw40750step2Labels = mixedMoment B raw40750step3 raw40750step3Labels := by
      have ha : raw40750step3 = -raw40750step2 := by apply Matrix.ext; change ∀ i j, raw40750step3 i j = -(raw40750step2 i j); unfold raw40750step3 raw40750step2; decide +kernel
      have hl : raw40750step3Labels = raw40750step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

theorem canonical40751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40751 raw40751Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw40751 raw40751Labels = mixedMoment B raw40751step0 raw40751step0Labels := by
      have hz : ∀ j, raw40751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40751step0 = (fun i j => raw40751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40751step0 raw40751; decide +kernel
      have hl : raw40751step0Labels = raw40751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40751 raw40751Labels permutation434 hz
    mixedMoment B raw40751step0 raw40751step0Labels = mixedMoment B raw40751step1 raw40751step1Labels := by
      have hz : ∀ j, raw40751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40751step1 = (fun i j => raw40751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40751step1 raw40751step0; decide +kernel
      have hl : raw40751step1Labels = raw40751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40751step0 raw40751step0Labels permutation80 hz
    mixedMoment B raw40751step1 raw40751step1Labels = mixedMoment B raw40751step2 raw40751step2Labels := by
      have ha : raw40751step2 = (fun i j => raw40751step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40751step2 raw40751step1; decide +kernel
      have hl : raw40751step2Labels = raw40751step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40751step1 raw40751step1Labels permutation27 permutation6
    mixedMoment B raw40751step2 raw40751step2Labels = mixedMoment B raw40751step3 raw40751step3Labels := by
      have ha : raw40751step3 = -raw40751step2 := by apply Matrix.ext; change ∀ i j, raw40751step3 i j = -(raw40751step2 i j); unfold raw40751step3 raw40751step2; decide +kernel
      have hl : raw40751step3Labels = raw40751step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

theorem canonical40752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40752 raw40752Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw40752 raw40752Labels = mixedMoment B raw40752step0 raw40752step0Labels := by
      have hz : ∀ j, raw40752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40752step0 = (fun i j => raw40752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40752step0 raw40752; decide +kernel
      have hl : raw40752step0Labels = raw40752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40752 raw40752Labels permutation434 hz
    mixedMoment B raw40752step0 raw40752step0Labels = mixedMoment B raw40752step1 raw40752step1Labels := by
      have hz : ∀ j, raw40752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40752step1 = (fun i j => raw40752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40752step1 raw40752step0; decide +kernel
      have hl : raw40752step1Labels = raw40752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40752step0 raw40752step0Labels permutation80 hz
    mixedMoment B raw40752step1 raw40752step1Labels = mixedMoment B raw40752step2 raw40752step2Labels := by
      have ha : raw40752step2 = (fun i j => raw40752step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40752step2 raw40752step1; decide +kernel
      have hl : raw40752step2Labels = raw40752step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40752step1 raw40752step1Labels permutation16 permutation6
    _ = mixedMoment B node3913 node3913Labels := by rfl

theorem canonical40753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40753 raw40753Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw40753 raw40753Labels = mixedMoment B raw40753step0 raw40753step0Labels := by
      have hz : ∀ j, raw40753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40753step0 = (fun i j => raw40753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40753step0 raw40753; decide +kernel
      have hl : raw40753step0Labels = raw40753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40753 raw40753Labels permutation346 hz
    mixedMoment B raw40753step0 raw40753step0Labels = mixedMoment B raw40753step1 raw40753step1Labels := by
      have ha : raw40753step1 = (fun i j => raw40753step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40753step1 raw40753step0; decide +kernel
      have hl : raw40753step1Labels = raw40753step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40753step0 raw40753step0Labels permutation74 permutation6
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical40754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40754 raw40754Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw40754 raw40754Labels = mixedMoment B raw40754step0 raw40754step0Labels := by
      have hz : ∀ j, raw40754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40754step0 = (fun i j => raw40754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40754step0 raw40754; decide +kernel
      have hl : raw40754step0Labels = raw40754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40754 raw40754Labels permutation346 hz
    mixedMoment B raw40754step0 raw40754step0Labels = mixedMoment B raw40754step1 raw40754step1Labels := by
      have ha : raw40754step1 = (fun i j => raw40754step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40754step1 raw40754step0; decide +kernel
      have hl : raw40754step1Labels = raw40754step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40754step0 raw40754step0Labels permutation74 permutation6
    _ = mixedMoment B node3732 node3732Labels := by rfl

theorem canonical40755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40755 raw40755Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw40755 raw40755Labels = mixedMoment B raw40755step0 raw40755step0Labels := by
      have hz : ∀ j, raw40755 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40755step0 = (fun i j => raw40755 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40755step0 raw40755; decide +kernel
      have hl : raw40755step0Labels = raw40755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40755 raw40755Labels permutation346 hz
    mixedMoment B raw40755step0 raw40755step0Labels = mixedMoment B raw40755step1 raw40755step1Labels := by
      have ha : raw40755step1 = (fun i j => raw40755step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40755step1 raw40755step0; decide +kernel
      have hl : raw40755step1Labels = raw40755step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40755step0 raw40755step0Labels permutation68 permutation6
    _ = mixedMoment B node3857 node3857Labels := by rfl

theorem canonical40756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40756 raw40756Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw40756 raw40756Labels = mixedMoment B raw40756step0 raw40756step0Labels := by
      have hz : ∀ j, raw40756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40756step0 = (fun i j => raw40756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40756step0 raw40756; decide +kernel
      have hl : raw40756step0Labels = raw40756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40756 raw40756Labels permutation346 hz
    mixedMoment B raw40756step0 raw40756step0Labels = mixedMoment B raw40756step1 raw40756step1Labels := by
      have ha : raw40756step1 = (fun i j => raw40756step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40756step1 raw40756step0; decide +kernel
      have hl : raw40756step1Labels = raw40756step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40756step0 raw40756step0Labels permutation72 permutation6
    _ = mixedMoment B node3910 node3910Labels := by rfl

theorem canonical40757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40757 raw40757Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw40757 raw40757Labels = mixedMoment B raw40757step0 raw40757step0Labels := by
      have hz : ∀ j, raw40757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40757step0 = (fun i j => raw40757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40757step0 raw40757; decide +kernel
      have hl : raw40757step0Labels = raw40757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40757 raw40757Labels permutation346 hz
    mixedMoment B raw40757step0 raw40757step0Labels = mixedMoment B raw40757step1 raw40757step1Labels := by
      have ha : raw40757step1 = (fun i j => raw40757step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40757step1 raw40757step0; decide +kernel
      have hl : raw40757step1Labels = raw40757step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40757step0 raw40757step0Labels permutation72 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

theorem canonical40758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40758 raw40758Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw40758 raw40758Labels = mixedMoment B raw40758step0 raw40758step0Labels := by
      have hz : ∀ j, raw40758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40758step0 = (fun i j => raw40758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40758step0 raw40758; decide +kernel
      have hl : raw40758step0Labels = raw40758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40758 raw40758Labels permutation346 hz
    mixedMoment B raw40758step0 raw40758step0Labels = mixedMoment B raw40758step1 raw40758step1Labels := by
      have ha : raw40758step1 = (fun i j => raw40758step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40758step1 raw40758step0; decide +kernel
      have hl : raw40758step1Labels = raw40758step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40758step0 raw40758step0Labels permutation83 permutation6
    mixedMoment B raw40758step1 raw40758step1Labels = mixedMoment B raw40758step2 raw40758step2Labels := by
      have ha : raw40758step2 = -raw40758step1 := by apply Matrix.ext; change ∀ i j, raw40758step2 i j = -(raw40758step1 i j); unfold raw40758step2 raw40758step1; decide +kernel
      have hl : raw40758step2Labels = raw40758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2106 node2106Labels := by rfl

theorem canonical40759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40759 raw40759Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw40759 raw40759Labels = mixedMoment B raw40759step0 raw40759step0Labels := by
      have ha : raw40759step0 = (fun i j => raw40759 (permutation333 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40759step0 raw40759; decide +kernel
      have hl : raw40759step0Labels = raw40759Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40759 raw40759Labels permutation333 permutation6
    _ = mixedMoment B node3731 node3731Labels := by rfl

theorem canonical40760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40760 raw40760Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw40760 raw40760Labels = mixedMoment B raw40760step0 raw40760step0Labels := by
      have ha : raw40760step0 = (fun i j => raw40760 (permutation329 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40760step0 raw40760; decide +kernel
      have hl : raw40760step0Labels = raw40760Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40760 raw40760Labels permutation329 permutation6
    _ = mixedMoment B node3849 node3849Labels := by rfl

theorem canonical40761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40761 raw40761Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw40761 raw40761Labels = mixedMoment B raw40761step0 raw40761step0Labels := by
      have ha : raw40761step0 = (fun i j => raw40761 (permutation468 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40761step0 raw40761; decide +kernel
      have hl : raw40761step0Labels = raw40761Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40761 raw40761Labels permutation468 permutation6
    mixedMoment B raw40761step0 raw40761step0Labels = mixedMoment B raw40761step1 raw40761step1Labels := by
      have ha : raw40761step1 = -raw40761step0 := by apply Matrix.ext; change ∀ i j, raw40761step1 i j = -(raw40761step0 i j); unfold raw40761step1 raw40761step0; decide +kernel
      have hl : raw40761step1Labels = raw40761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3786 node3786Labels := by rfl

theorem canonical40762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40762 raw40762Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw40762 raw40762Labels = mixedMoment B raw40762step0 raw40762step0Labels := by
      have hz : ∀ j, raw40762 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40762step0 = (fun i j => raw40762 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40762step0 raw40762; decide +kernel
      have hl : raw40762step0Labels = raw40762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40762 raw40762Labels permutation520 hz
    mixedMoment B raw40762step0 raw40762step0Labels = mixedMoment B raw40762step1 raw40762step1Labels := by
      have hz : ∀ j, raw40762step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40762step1 = (fun i j => raw40762step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40762step1 raw40762step0; decide +kernel
      have hl : raw40762step1Labels = raw40762step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40762step0 raw40762step0Labels permutation104 hz
    mixedMoment B raw40762step1 raw40762step1Labels = mixedMoment B raw40762step2 raw40762step2Labels := by
      have ha : raw40762step2 = (fun i j => raw40762step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40762step2 raw40762step1; decide +kernel
      have hl : raw40762step2Labels = raw40762step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40762step1 raw40762step1Labels permutation29 permutation3
    mixedMoment B raw40762step2 raw40762step2Labels = mixedMoment B raw40762step3 raw40762step3Labels := by
      have ha : raw40762step3 = -raw40762step2 := by apply Matrix.ext; change ∀ i j, raw40762step3 i j = -(raw40762step2 i j); unfold raw40762step3 raw40762step2; decide +kernel
      have hl : raw40762step3Labels = raw40762step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3623 node3623Labels := by rfl

theorem canonical40763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40763 raw40763Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw40763 raw40763Labels = mixedMoment B raw40763step0 raw40763step0Labels := by
      have hz : ∀ j, raw40763 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40763step0 = (fun i j => raw40763 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40763step0 raw40763; decide +kernel
      have hl : raw40763step0Labels = raw40763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40763 raw40763Labels permutation434 hz
    mixedMoment B raw40763step0 raw40763step0Labels = mixedMoment B raw40763step1 raw40763step1Labels := by
      have ha : raw40763step1 = (fun i j => raw40763step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40763step1 raw40763step0; decide +kernel
      have hl : raw40763step1Labels = raw40763step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40763step0 raw40763step0Labels permutation108 permutation6
    mixedMoment B raw40763step1 raw40763step1Labels = mixedMoment B raw40763step2 raw40763step2Labels := by
      have ha : raw40763step2 = -raw40763step1 := by apply Matrix.ext; change ∀ i j, raw40763step2 i j = -(raw40763step1 i j); unfold raw40763step2 raw40763step1; decide +kernel
      have hl : raw40763step2Labels = raw40763step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

theorem canonical40764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40764 raw40764Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw40764 raw40764Labels = mixedMoment B raw40764step0 raw40764step0Labels := by
      have hz : ∀ j, raw40764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40764step0 = (fun i j => raw40764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40764step0 raw40764; decide +kernel
      have hl : raw40764step0Labels = raw40764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40764 raw40764Labels permutation434 hz
    mixedMoment B raw40764step0 raw40764step0Labels = mixedMoment B raw40764step1 raw40764step1Labels := by
      have ha : raw40764step1 = (fun i j => raw40764step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40764step1 raw40764step0; decide +kernel
      have hl : raw40764step1Labels = raw40764step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40764step0 raw40764step0Labels permutation104 permutation6
    mixedMoment B raw40764step1 raw40764step1Labels = mixedMoment B raw40764step2 raw40764step2Labels := by
      have ha : raw40764step2 = -raw40764step1 := by apply Matrix.ext; change ∀ i j, raw40764step2 i j = -(raw40764step1 i j); unfold raw40764step2 raw40764step1; decide +kernel
      have hl : raw40764step2Labels = raw40764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

theorem canonical40765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40765 raw40765Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw40765 raw40765Labels = mixedMoment B raw40765step0 raw40765step0Labels := by
      have hz : ∀ j, raw40765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40765step0 = (fun i j => raw40765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40765step0 raw40765; decide +kernel
      have hl : raw40765step0Labels = raw40765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40765 raw40765Labels permutation434 hz
    mixedMoment B raw40765step0 raw40765step0Labels = mixedMoment B raw40765step1 raw40765step1Labels := by
      have ha : raw40765step1 = (fun i j => raw40765step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40765step1 raw40765step0; decide +kernel
      have hl : raw40765step1Labels = raw40765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40765step0 raw40765step0Labels permutation32 permutation3
    _ = mixedMoment B node4010 node4010Labels := by rfl

theorem canonical40766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40766 raw40766Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw40766 raw40766Labels = mixedMoment B raw40766step0 raw40766step0Labels := by
      have ha : raw40766step0 = (fun i j => raw40766 (permutation553 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40766step0 raw40766; decide +kernel
      have hl : raw40766step0Labels = raw40766Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40766 raw40766Labels permutation553 permutation6
    mixedMoment B raw40766step0 raw40766step0Labels = mixedMoment B raw40766step1 raw40766step1Labels := by
      have ha : raw40766step1 = -raw40766step0 := by apply Matrix.ext; change ∀ i j, raw40766step1 i j = -(raw40766step0 i j); unfold raw40766step1 raw40766step0; decide +kernel
      have hl : raw40766step1Labels = raw40766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

theorem canonical40767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40767 raw40767Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw40767 raw40767Labels = mixedMoment B raw40767step0 raw40767step0Labels := by
      have ha : raw40767step0 = (fun i j => raw40767 (permutation449 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40767step0 raw40767; decide +kernel
      have hl : raw40767step0Labels = raw40767Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40767 raw40767Labels permutation449 permutation6
    mixedMoment B raw40767step0 raw40767step0Labels = mixedMoment B raw40767step1 raw40767step1Labels := by
      have ha : raw40767step1 = -raw40767step0 := by apply Matrix.ext; change ∀ i j, raw40767step1 i j = -(raw40767step0 i j); unfold raw40767step1 raw40767step0; decide +kernel
      have hl : raw40767step1Labels = raw40767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1312) =
      Integer.Sparse.eval keyMomentRow1312 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1312).leftCharge (GramAssembly.key 1312).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2632) := by
    have ha : gramCharges (GramAssembly.key 1312).leftCharge (GramAssembly.key 1312).rightCharge = raw40736 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40736Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40736 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1312).leftCharge (GramAssembly.key 1312).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1312, Integer.Sparse.eval]

theorem keyMoment1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1313) =
      Integer.Sparse.eval keyMomentRow1313 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1313).leftCharge (GramAssembly.key 1313).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2620) := by
    have ha : gramCharges (GramAssembly.key 1313).leftCharge (GramAssembly.key 1313).rightCharge = raw40737 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40737Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40737 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1313).leftCharge (GramAssembly.key 1313).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1313, Integer.Sparse.eval]

theorem keyMoment1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1314) =
      Integer.Sparse.eval keyMomentRow1314 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1314).leftCharge (GramAssembly.key 1314).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2614) := by
    have ha : gramCharges (GramAssembly.key 1314).leftCharge (GramAssembly.key 1314).rightCharge = raw40738 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40738Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40738 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1314).leftCharge (GramAssembly.key 1314).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1314, Integer.Sparse.eval]

theorem keyMoment1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1315) =
      Integer.Sparse.eval keyMomentRow1315 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1315).leftCharge (GramAssembly.key 1315).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2641) := by
    have ha : gramCharges (GramAssembly.key 1315).leftCharge (GramAssembly.key 1315).rightCharge = raw40739 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40739Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40739 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1315).leftCharge (GramAssembly.key 1315).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1315, Integer.Sparse.eval]

theorem keyMoment1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1316) =
      Integer.Sparse.eval keyMomentRow1316 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1316).leftCharge (GramAssembly.key 1316).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2631) := by
    have ha : gramCharges (GramAssembly.key 1316).leftCharge (GramAssembly.key 1316).rightCharge = raw40740 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40740Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40740 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1316).leftCharge (GramAssembly.key 1316).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1316, Integer.Sparse.eval]

theorem keyMoment1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1317) =
      Integer.Sparse.eval keyMomentRow1317 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1317).leftCharge (GramAssembly.key 1317).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2617) := by
    have ha : gramCharges (GramAssembly.key 1317).leftCharge (GramAssembly.key 1317).rightCharge = raw40741 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40741Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40741 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1317).leftCharge (GramAssembly.key 1317).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1317, Integer.Sparse.eval]

theorem keyMoment1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1318) =
      Integer.Sparse.eval keyMomentRow1318 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1318).leftCharge (GramAssembly.key 1318).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2633) := by
    have ha : gramCharges (GramAssembly.key 1318).leftCharge (GramAssembly.key 1318).rightCharge = raw40742 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40742Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40742 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1318).leftCharge (GramAssembly.key 1318).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1318, Integer.Sparse.eval]

theorem keyMoment1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1319) =
      Integer.Sparse.eval keyMomentRow1319 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1319).leftCharge (GramAssembly.key 1319).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2618) := by
    have ha : gramCharges (GramAssembly.key 1319).leftCharge (GramAssembly.key 1319).rightCharge = raw40743 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40743Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40743 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1319).leftCharge (GramAssembly.key 1319).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1319, Integer.Sparse.eval]

theorem keyMoment1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1320) =
      Integer.Sparse.eval keyMomentRow1320 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1320).leftCharge (GramAssembly.key 1320).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2635) := by
    have ha : gramCharges (GramAssembly.key 1320).leftCharge (GramAssembly.key 1320).rightCharge = raw40744 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40744Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40744 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1320).leftCharge (GramAssembly.key 1320).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1320, Integer.Sparse.eval]

theorem keyMoment1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1321) =
      Integer.Sparse.eval keyMomentRow1321 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1321).leftCharge (GramAssembly.key 1321).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1264) := by
    have ha : gramCharges (GramAssembly.key 1321).leftCharge (GramAssembly.key 1321).rightCharge = raw40745 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40745Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40745 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1321).leftCharge (GramAssembly.key 1321).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1321, Integer.Sparse.eval]

theorem keyMoment1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1322) =
      Integer.Sparse.eval keyMomentRow1322 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1322).leftCharge (GramAssembly.key 1322).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2569) := by
    have ha : gramCharges (GramAssembly.key 1322).leftCharge (GramAssembly.key 1322).rightCharge = raw40746 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40746Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40746 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1322).leftCharge (GramAssembly.key 1322).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1322, Integer.Sparse.eval]

theorem keyMoment1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1323) =
      Integer.Sparse.eval keyMomentRow1323 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1323).leftCharge (GramAssembly.key 1323).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3633) := by
    have ha : gramCharges (GramAssembly.key 1323).leftCharge (GramAssembly.key 1323).rightCharge = raw40747 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40747Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40747 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1323).leftCharge (GramAssembly.key 1323).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1323, Integer.Sparse.eval]

theorem keyMoment1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1324) =
      Integer.Sparse.eval keyMomentRow1324 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1324).leftCharge (GramAssembly.key 1324).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3907) := by
    have ha : gramCharges (GramAssembly.key 1324).leftCharge (GramAssembly.key 1324).rightCharge = raw40748 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40748Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40748 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1324).leftCharge (GramAssembly.key 1324).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1324, Integer.Sparse.eval]

theorem keyMoment1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1325) =
      Integer.Sparse.eval keyMomentRow1325 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1325).leftCharge (GramAssembly.key 1325).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3886) := by
    have ha : gramCharges (GramAssembly.key 1325).leftCharge (GramAssembly.key 1325).rightCharge = raw40749 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40749Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40749 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1325).leftCharge (GramAssembly.key 1325).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1325, Integer.Sparse.eval]

theorem keyMoment1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1326) =
      Integer.Sparse.eval keyMomentRow1326 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1326).leftCharge (GramAssembly.key 1326).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2115) := by
    have ha : gramCharges (GramAssembly.key 1326).leftCharge (GramAssembly.key 1326).rightCharge = raw40750 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40750Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40750 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1326).leftCharge (GramAssembly.key 1326).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1326, Integer.Sparse.eval]

theorem keyMoment1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1327) =
      Integer.Sparse.eval keyMomentRow1327 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1327).leftCharge (GramAssembly.key 1327).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3582) := by
    have ha : gramCharges (GramAssembly.key 1327).leftCharge (GramAssembly.key 1327).rightCharge = raw40751 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40751Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40751 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1327).leftCharge (GramAssembly.key 1327).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1327, Integer.Sparse.eval]

theorem keyMoment1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1328) =
      Integer.Sparse.eval keyMomentRow1328 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1328).leftCharge (GramAssembly.key 1328).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3913) := by
    have ha : gramCharges (GramAssembly.key 1328).leftCharge (GramAssembly.key 1328).rightCharge = raw40752 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40752Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40752 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1328).leftCharge (GramAssembly.key 1328).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1328, Integer.Sparse.eval]

theorem keyMoment1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1329) =
      Integer.Sparse.eval keyMomentRow1329 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1329).leftCharge (GramAssembly.key 1329).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3885) := by
    have ha : gramCharges (GramAssembly.key 1329).leftCharge (GramAssembly.key 1329).rightCharge = raw40753 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40753Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40753 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1329).leftCharge (GramAssembly.key 1329).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1329, Integer.Sparse.eval]

theorem keyMoment1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1330) =
      Integer.Sparse.eval keyMomentRow1330 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1330).leftCharge (GramAssembly.key 1330).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3732) := by
    have ha : gramCharges (GramAssembly.key 1330).leftCharge (GramAssembly.key 1330).rightCharge = raw40754 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40754Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40754 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1330).leftCharge (GramAssembly.key 1330).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1330, Integer.Sparse.eval]

theorem keyMoment1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1331) =
      Integer.Sparse.eval keyMomentRow1331 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1331).leftCharge (GramAssembly.key 1331).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3857) := by
    have ha : gramCharges (GramAssembly.key 1331).leftCharge (GramAssembly.key 1331).rightCharge = raw40755 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40755Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40755 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1331).leftCharge (GramAssembly.key 1331).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1331, Integer.Sparse.eval]

theorem keyMoment1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1332) =
      Integer.Sparse.eval keyMomentRow1332 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1332).leftCharge (GramAssembly.key 1332).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3910) := by
    have ha : gramCharges (GramAssembly.key 1332).leftCharge (GramAssembly.key 1332).rightCharge = raw40756 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40756Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40756 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1332).leftCharge (GramAssembly.key 1332).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1332, Integer.Sparse.eval]

theorem keyMoment1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1333) =
      Integer.Sparse.eval keyMomentRow1333 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1333).leftCharge (GramAssembly.key 1333).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3850) := by
    have ha : gramCharges (GramAssembly.key 1333).leftCharge (GramAssembly.key 1333).rightCharge = raw40757 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40757Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40757 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1333).leftCharge (GramAssembly.key 1333).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1333, Integer.Sparse.eval]

theorem keyMoment1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1334) =
      Integer.Sparse.eval keyMomentRow1334 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1334).leftCharge (GramAssembly.key 1334).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2106) := by
    have ha : gramCharges (GramAssembly.key 1334).leftCharge (GramAssembly.key 1334).rightCharge = raw40758 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40758Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40758 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1334).leftCharge (GramAssembly.key 1334).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1334, Integer.Sparse.eval]

theorem keyMoment1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1335) =
      Integer.Sparse.eval keyMomentRow1335 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1335).leftCharge (GramAssembly.key 1335).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3731) := by
    have ha : gramCharges (GramAssembly.key 1335).leftCharge (GramAssembly.key 1335).rightCharge = raw40759 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40759Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40759 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1335).leftCharge (GramAssembly.key 1335).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1335, Integer.Sparse.eval]

theorem keyMoment1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1336) =
      Integer.Sparse.eval keyMomentRow1336 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1336).leftCharge (GramAssembly.key 1336).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3849) := by
    have ha : gramCharges (GramAssembly.key 1336).leftCharge (GramAssembly.key 1336).rightCharge = raw40760 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40760Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40760 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1336).leftCharge (GramAssembly.key 1336).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1336, Integer.Sparse.eval]

theorem keyMoment1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1337) =
      Integer.Sparse.eval keyMomentRow1337 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1337).leftCharge (GramAssembly.key 1337).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3786) := by
    have ha : gramCharges (GramAssembly.key 1337).leftCharge (GramAssembly.key 1337).rightCharge = raw40761 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40761Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40761 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1337).leftCharge (GramAssembly.key 1337).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1337, Integer.Sparse.eval]

theorem keyMoment1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1338) =
      Integer.Sparse.eval keyMomentRow1338 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1338).leftCharge (GramAssembly.key 1338).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3623) := by
    have ha : gramCharges (GramAssembly.key 1338).leftCharge (GramAssembly.key 1338).rightCharge = raw40762 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40762Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40762 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1338).leftCharge (GramAssembly.key 1338).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1338, Integer.Sparse.eval]

theorem keyMoment1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1339) =
      Integer.Sparse.eval keyMomentRow1339 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1339).leftCharge (GramAssembly.key 1339).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3885) := by
    have ha : gramCharges (GramAssembly.key 1339).leftCharge (GramAssembly.key 1339).rightCharge = raw40763 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40763Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40763 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1339).leftCharge (GramAssembly.key 1339).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1339, Integer.Sparse.eval]

theorem keyMoment1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1340) =
      Integer.Sparse.eval keyMomentRow1340 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1340).leftCharge (GramAssembly.key 1340).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2110) := by
    have ha : gramCharges (GramAssembly.key 1340).leftCharge (GramAssembly.key 1340).rightCharge = raw40764 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40764Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40764 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1340).leftCharge (GramAssembly.key 1340).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1340, Integer.Sparse.eval]

theorem keyMoment1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1341) =
      Integer.Sparse.eval keyMomentRow1341 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1341).leftCharge (GramAssembly.key 1341).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 4010) := by
    have ha : gramCharges (GramAssembly.key 1341).leftCharge (GramAssembly.key 1341).rightCharge = raw40765 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40765Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40765 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1341).leftCharge (GramAssembly.key 1341).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1341, Integer.Sparse.eval]

theorem keyMoment1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1342) =
      Integer.Sparse.eval keyMomentRow1342 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1342).leftCharge (GramAssembly.key 1342).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3789) := by
    have ha : gramCharges (GramAssembly.key 1342).leftCharge (GramAssembly.key 1342).rightCharge = raw40766 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40766Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40766 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1342).leftCharge (GramAssembly.key 1342).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1342, Integer.Sparse.eval]

theorem keyMoment1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1343) =
      Integer.Sparse.eval keyMomentRow1343 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1343).leftCharge (GramAssembly.key 1343).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3875) := by
    have ha : gramCharges (GramAssembly.key 1343).leftCharge (GramAssembly.key 1343).rightCharge = raw40767 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40767Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40767 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1343).leftCharge (GramAssembly.key 1343).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1343, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1312 : keyMomentRows (1312 : Fin 2886) =
    keyMomentRow1312 := by decide +kernel

theorem keyMomentRowsAt1313 : keyMomentRows (1313 : Fin 2886) =
    keyMomentRow1313 := by decide +kernel

theorem keyMomentRowsAt1314 : keyMomentRows (1314 : Fin 2886) =
    keyMomentRow1314 := by decide +kernel

theorem keyMomentRowsAt1315 : keyMomentRows (1315 : Fin 2886) =
    keyMomentRow1315 := by decide +kernel

theorem keyMomentRowsAt1316 : keyMomentRows (1316 : Fin 2886) =
    keyMomentRow1316 := by decide +kernel

theorem keyMomentRowsAt1317 : keyMomentRows (1317 : Fin 2886) =
    keyMomentRow1317 := by decide +kernel

theorem keyMomentRowsAt1318 : keyMomentRows (1318 : Fin 2886) =
    keyMomentRow1318 := by decide +kernel

theorem keyMomentRowsAt1319 : keyMomentRows (1319 : Fin 2886) =
    keyMomentRow1319 := by decide +kernel

theorem keyMomentRowsAt1320 : keyMomentRows (1320 : Fin 2886) =
    keyMomentRow1320 := by decide +kernel

theorem keyMomentRowsAt1321 : keyMomentRows (1321 : Fin 2886) =
    keyMomentRow1321 := by decide +kernel

theorem keyMomentRowsAt1322 : keyMomentRows (1322 : Fin 2886) =
    keyMomentRow1322 := by decide +kernel

theorem keyMomentRowsAt1323 : keyMomentRows (1323 : Fin 2886) =
    keyMomentRow1323 := by decide +kernel

theorem keyMomentRowsAt1324 : keyMomentRows (1324 : Fin 2886) =
    keyMomentRow1324 := by decide +kernel

theorem keyMomentRowsAt1325 : keyMomentRows (1325 : Fin 2886) =
    keyMomentRow1325 := by decide +kernel

theorem keyMomentRowsAt1326 : keyMomentRows (1326 : Fin 2886) =
    keyMomentRow1326 := by decide +kernel

theorem keyMomentRowsAt1327 : keyMomentRows (1327 : Fin 2886) =
    keyMomentRow1327 := by decide +kernel

theorem keyMomentRowsAt1328 : keyMomentRows (1328 : Fin 2886) =
    keyMomentRow1328 := by decide +kernel

theorem keyMomentRowsAt1329 : keyMomentRows (1329 : Fin 2886) =
    keyMomentRow1329 := by decide +kernel

theorem keyMomentRowsAt1330 : keyMomentRows (1330 : Fin 2886) =
    keyMomentRow1330 := by decide +kernel

theorem keyMomentRowsAt1331 : keyMomentRows (1331 : Fin 2886) =
    keyMomentRow1331 := by decide +kernel

theorem keyMomentRowsAt1332 : keyMomentRows (1332 : Fin 2886) =
    keyMomentRow1332 := by decide +kernel

theorem keyMomentRowsAt1333 : keyMomentRows (1333 : Fin 2886) =
    keyMomentRow1333 := by decide +kernel

theorem keyMomentRowsAt1334 : keyMomentRows (1334 : Fin 2886) =
    keyMomentRow1334 := by decide +kernel

theorem keyMomentRowsAt1335 : keyMomentRows (1335 : Fin 2886) =
    keyMomentRow1335 := by decide +kernel

theorem keyMomentRowsAt1336 : keyMomentRows (1336 : Fin 2886) =
    keyMomentRow1336 := by decide +kernel

theorem keyMomentRowsAt1337 : keyMomentRows (1337 : Fin 2886) =
    keyMomentRow1337 := by decide +kernel

theorem keyMomentRowsAt1338 : keyMomentRows (1338 : Fin 2886) =
    keyMomentRow1338 := by decide +kernel

theorem keyMomentRowsAt1339 : keyMomentRows (1339 : Fin 2886) =
    keyMomentRow1339 := by decide +kernel

theorem keyMomentRowsAt1340 : keyMomentRows (1340 : Fin 2886) =
    keyMomentRow1340 := by decide +kernel

theorem keyMomentRowsAt1341 : keyMomentRows (1341 : Fin 2886) =
    keyMomentRow1341 := by decide +kernel

theorem keyMomentRowsAt1342 : keyMomentRows (1342 : Fin 2886) =
    keyMomentRow1342 := by decide +kernel

theorem keyMomentRowsAt1343 : keyMomentRows (1343 : Fin 2886) =
    keyMomentRow1343 := by decide +kernel

theorem keyMomentChunkSound41_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 41) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1312 ∨ k.val = 1313 ∨ k.val = 1314 ∨ k.val = 1315 ∨ k.val = 1316 ∨ k.val = 1317 ∨ k.val = 1318 ∨ k.val = 1319 ∨ k.val = 1320 ∨ k.val = 1321 ∨ k.val = 1322 ∨ k.val = 1323 ∨ k.val = 1324 ∨ k.val = 1325 ∨ k.val = 1326 ∨ k.val = 1327 ∨ k.val = 1328 ∨ k.val = 1329 ∨ k.val = 1330 ∨ k.val = 1331 ∨ k.val = 1332 ∨ k.val = 1333 ∨ k.val = 1334 ∨ k.val = 1335 ∨ k.val = 1336 ∨ k.val = 1337 ∨ k.val = 1338 ∨ k.val = 1339 ∨ k.val = 1340 ∨ k.val = 1341 ∨ k.val = 1342 ∨ k.val = 1343 := by omega
  rcases heq with h1312 | h1313 | h1314 | h1315 | h1316 | h1317 | h1318 | h1319 | h1320 | h1321 | h1322 | h1323 | h1324 | h1325 | h1326 | h1327 | h1328 | h1329 | h1330 | h1331 | h1332 | h1333 | h1334 | h1335 | h1336 | h1337 | h1338 | h1339 | h1340 | h1341 | h1342 | h1343
  · have he : k = (1312 : Fin 2886) := Fin.ext h1312
    subst k
    rw [keyMomentRowsAt1312]
    exact keyMoment1312 B hB
  · have he : k = (1313 : Fin 2886) := Fin.ext h1313
    subst k
    rw [keyMomentRowsAt1313]
    exact keyMoment1313 B hB
  · have he : k = (1314 : Fin 2886) := Fin.ext h1314
    subst k
    rw [keyMomentRowsAt1314]
    exact keyMoment1314 B hB
  · have he : k = (1315 : Fin 2886) := Fin.ext h1315
    subst k
    rw [keyMomentRowsAt1315]
    exact keyMoment1315 B hB
  · have he : k = (1316 : Fin 2886) := Fin.ext h1316
    subst k
    rw [keyMomentRowsAt1316]
    exact keyMoment1316 B hB
  · have he : k = (1317 : Fin 2886) := Fin.ext h1317
    subst k
    rw [keyMomentRowsAt1317]
    exact keyMoment1317 B hB
  · have he : k = (1318 : Fin 2886) := Fin.ext h1318
    subst k
    rw [keyMomentRowsAt1318]
    exact keyMoment1318 B hB
  · have he : k = (1319 : Fin 2886) := Fin.ext h1319
    subst k
    rw [keyMomentRowsAt1319]
    exact keyMoment1319 B hB
  · have he : k = (1320 : Fin 2886) := Fin.ext h1320
    subst k
    rw [keyMomentRowsAt1320]
    exact keyMoment1320 B hB
  · have he : k = (1321 : Fin 2886) := Fin.ext h1321
    subst k
    rw [keyMomentRowsAt1321]
    exact keyMoment1321 B hB
  · have he : k = (1322 : Fin 2886) := Fin.ext h1322
    subst k
    rw [keyMomentRowsAt1322]
    exact keyMoment1322 B hB
  · have he : k = (1323 : Fin 2886) := Fin.ext h1323
    subst k
    rw [keyMomentRowsAt1323]
    exact keyMoment1323 B hB
  · have he : k = (1324 : Fin 2886) := Fin.ext h1324
    subst k
    rw [keyMomentRowsAt1324]
    exact keyMoment1324 B hB
  · have he : k = (1325 : Fin 2886) := Fin.ext h1325
    subst k
    rw [keyMomentRowsAt1325]
    exact keyMoment1325 B hB
  · have he : k = (1326 : Fin 2886) := Fin.ext h1326
    subst k
    rw [keyMomentRowsAt1326]
    exact keyMoment1326 B hB
  · have he : k = (1327 : Fin 2886) := Fin.ext h1327
    subst k
    rw [keyMomentRowsAt1327]
    exact keyMoment1327 B hB
  · have he : k = (1328 : Fin 2886) := Fin.ext h1328
    subst k
    rw [keyMomentRowsAt1328]
    exact keyMoment1328 B hB
  · have he : k = (1329 : Fin 2886) := Fin.ext h1329
    subst k
    rw [keyMomentRowsAt1329]
    exact keyMoment1329 B hB
  · have he : k = (1330 : Fin 2886) := Fin.ext h1330
    subst k
    rw [keyMomentRowsAt1330]
    exact keyMoment1330 B hB
  · have he : k = (1331 : Fin 2886) := Fin.ext h1331
    subst k
    rw [keyMomentRowsAt1331]
    exact keyMoment1331 B hB
  · have he : k = (1332 : Fin 2886) := Fin.ext h1332
    subst k
    rw [keyMomentRowsAt1332]
    exact keyMoment1332 B hB
  · have he : k = (1333 : Fin 2886) := Fin.ext h1333
    subst k
    rw [keyMomentRowsAt1333]
    exact keyMoment1333 B hB
  · have he : k = (1334 : Fin 2886) := Fin.ext h1334
    subst k
    rw [keyMomentRowsAt1334]
    exact keyMoment1334 B hB
  · have he : k = (1335 : Fin 2886) := Fin.ext h1335
    subst k
    rw [keyMomentRowsAt1335]
    exact keyMoment1335 B hB
  · have he : k = (1336 : Fin 2886) := Fin.ext h1336
    subst k
    rw [keyMomentRowsAt1336]
    exact keyMoment1336 B hB
  · have he : k = (1337 : Fin 2886) := Fin.ext h1337
    subst k
    rw [keyMomentRowsAt1337]
    exact keyMoment1337 B hB
  · have he : k = (1338 : Fin 2886) := Fin.ext h1338
    subst k
    rw [keyMomentRowsAt1338]
    exact keyMoment1338 B hB
  · have he : k = (1339 : Fin 2886) := Fin.ext h1339
    subst k
    rw [keyMomentRowsAt1339]
    exact keyMoment1339 B hB
  · have he : k = (1340 : Fin 2886) := Fin.ext h1340
    subst k
    rw [keyMomentRowsAt1340]
    exact keyMoment1340 B hB
  · have he : k = (1341 : Fin 2886) := Fin.ext h1341
    subst k
    rw [keyMomentRowsAt1341]
    exact keyMoment1341 B hB
  · have he : k = (1342 : Fin 2886) := Fin.ext h1342
    subst k
    rw [keyMomentRowsAt1342]
    exact keyMoment1342 B hB
  · have he : k = (1343 : Fin 2886) := Fin.ext h1343
    subst k
    rw [keyMomentRowsAt1343]
    exact keyMoment1343 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound41_e_oai
