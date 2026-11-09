-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:50:32.772835+00:00
-- url     : https://prove2.me/submissions/c97785ef-2034-4c3e-b33b-20dbd924292c

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical315
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40368 raw40368Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw40368 raw40368Labels = mixedMoment B raw40368step0 raw40368step0Labels := by
      have hz : ∀ j, raw40368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40368step0 = (fun i j => raw40368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40368step0 raw40368; decide +kernel
      have hl : raw40368step0Labels = raw40368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40368 raw40368Labels permutation346 hz
    mixedMoment B raw40368step0 raw40368step0Labels = mixedMoment B raw40368step1 raw40368step1Labels := by
      have ha : raw40368step1 = (fun i j => raw40368step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40368step1 raw40368step0; decide +kernel
      have hl : raw40368step1Labels = raw40368step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40368step0 raw40368step0Labels permutation137 permutation6
    _ = mixedMoment B node2964 node2964Labels := by rfl

theorem canonical40369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40369 raw40369Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw40369 raw40369Labels = mixedMoment B raw40369step0 raw40369step0Labels := by
      have hz : ∀ j, raw40369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40369step0 = (fun i j => raw40369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40369step0 raw40369; decide +kernel
      have hl : raw40369step0Labels = raw40369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40369 raw40369Labels permutation346 hz
    mixedMoment B raw40369step0 raw40369step0Labels = mixedMoment B raw40369step1 raw40369step1Labels := by
      have ha : raw40369step1 = (fun i j => raw40369step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40369step1 raw40369step0; decide +kernel
      have hl : raw40369step1Labels = raw40369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40369step0 raw40369step0Labels permutation32 permutation3
    _ = mixedMoment B node3096 node3096Labels := by rfl

theorem canonical40370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40370 raw40370Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw40370 raw40370Labels = mixedMoment B raw40370step0 raw40370step0Labels := by
      have hz : ∀ j, raw40370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40370step0 = (fun i j => raw40370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40370step0 raw40370; decide +kernel
      have hl : raw40370step0Labels = raw40370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40370 raw40370Labels permutation346 hz
    mixedMoment B raw40370step0 raw40370step0Labels = mixedMoment B raw40370step1 raw40370step1Labels := by
      have ha : raw40370step1 = (fun i j => raw40370step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40370step1 raw40370step0; decide +kernel
      have hl : raw40370step1Labels = raw40370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40370step0 raw40370step0Labels permutation32 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

theorem canonical40371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40371 raw40371Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw40371 raw40371Labels = mixedMoment B raw40371step0 raw40371step0Labels := by
      have ha : raw40371step0 = (fun i j => raw40371 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40371step0 raw40371; decide +kernel
      have hl : raw40371step0Labels = raw40371Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40371 raw40371Labels permutation152 permutation3
    _ = mixedMoment B node3084 node3084Labels := by rfl

theorem canonical40372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40372 raw40372Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw40372 raw40372Labels = mixedMoment B raw40372step0 raw40372step0Labels := by
      have hz : ∀ j, raw40372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40372step0 = (fun i j => raw40372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40372step0 raw40372; decide +kernel
      have hl : raw40372step0Labels = raw40372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40372 raw40372Labels permutation434 hz
    mixedMoment B raw40372step0 raw40372step0Labels = mixedMoment B raw40372step1 raw40372step1Labels := by
      have hz : ∀ j, raw40372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40372step1 = (fun i j => raw40372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40372step1 raw40372step0; decide +kernel
      have hl : raw40372step1Labels = raw40372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40372step0 raw40372step0Labels permutation80 hz
    mixedMoment B raw40372step1 raw40372step1Labels = mixedMoment B raw40372step2 raw40372step2Labels := by
      have hz : ∀ j, raw40372step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40372step2 = (fun i j => raw40372step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40372step2 raw40372step1; decide +kernel
      have hl : raw40372step2Labels = raw40372step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40372step1 raw40372step1Labels permutation14 hz
    mixedMoment B raw40372step2 raw40372step2Labels = mixedMoment B raw40372step3 raw40372step3Labels := by
      have ha : raw40372step3 = (fun i j => raw40372step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40372step3 raw40372step2; decide +kernel
      have hl : raw40372step3Labels = raw40372step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40372step2 raw40372step2Labels permutation5 permutation6
    _ = mixedMoment B node2789 node2789Labels := by rfl

theorem canonical40373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40373 raw40373Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw40373 raw40373Labels = mixedMoment B raw40373step0 raw40373step0Labels := by
      have hz : ∀ j, raw40373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40373step0 = (fun i j => raw40373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40373step0 raw40373; decide +kernel
      have hl : raw40373step0Labels = raw40373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40373 raw40373Labels permutation434 hz
    mixedMoment B raw40373step0 raw40373step0Labels = mixedMoment B raw40373step1 raw40373step1Labels := by
      have hz : ∀ j, raw40373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40373step1 = (fun i j => raw40373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40373step1 raw40373step0; decide +kernel
      have hl : raw40373step1Labels = raw40373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40373step0 raw40373step0Labels permutation80 hz
    mixedMoment B raw40373step1 raw40373step1Labels = mixedMoment B raw40373step2 raw40373step2Labels := by
      have hz : ∀ j, raw40373step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw40373step2 = (fun i j => raw40373step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw40373step2 raw40373step1; decide +kernel
      have hl : raw40373step2Labels = raw40373step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40373step1 raw40373step1Labels permutation14 hz
    mixedMoment B raw40373step2 raw40373step2Labels = mixedMoment B raw40373step3 raw40373step3Labels := by
      have ha : raw40373step3 = (fun i j => raw40373step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40373step3 raw40373step2; decide +kernel
      have hl : raw40373step3Labels = raw40373step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40373step2 raw40373step2Labels permutation6 permutation6
    _ = mixedMoment B node1310 node1310Labels := by rfl

theorem canonical40374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40374 raw40374Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw40374 raw40374Labels = mixedMoment B raw40374step0 raw40374step0Labels := by
      have hz : ∀ j, raw40374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40374step0 = (fun i j => raw40374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40374step0 raw40374; decide +kernel
      have hl : raw40374step0Labels = raw40374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40374 raw40374Labels permutation346 hz
    mixedMoment B raw40374step0 raw40374step0Labels = mixedMoment B raw40374step1 raw40374step1Labels := by
      have hz : ∀ j, raw40374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40374step1 = (fun i j => raw40374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40374step1 raw40374step0; decide +kernel
      have hl : raw40374step1Labels = raw40374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40374step0 raw40374step0Labels permutation56 hz
    mixedMoment B raw40374step1 raw40374step1Labels = mixedMoment B raw40374step2 raw40374step2Labels := by
      have ha : raw40374step2 = (fun i j => raw40374step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40374step2 raw40374step1; decide +kernel
      have hl : raw40374step2Labels = raw40374step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40374step1 raw40374step1Labels permutation25 permutation6
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical40375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40375 raw40375Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw40375 raw40375Labels = mixedMoment B raw40375step0 raw40375step0Labels := by
      have hz : ∀ j, raw40375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40375step0 = (fun i j => raw40375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40375step0 raw40375; decide +kernel
      have hl : raw40375step0Labels = raw40375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40375 raw40375Labels permutation346 hz
    mixedMoment B raw40375step0 raw40375step0Labels = mixedMoment B raw40375step1 raw40375step1Labels := by
      have hz : ∀ j, raw40375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40375step1 = (fun i j => raw40375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40375step1 raw40375step0; decide +kernel
      have hl : raw40375step1Labels = raw40375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40375step0 raw40375step0Labels permutation56 hz
    mixedMoment B raw40375step1 raw40375step1Labels = mixedMoment B raw40375step2 raw40375step2Labels := by
      have ha : raw40375step2 = (fun i j => raw40375step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40375step2 raw40375step1; decide +kernel
      have hl : raw40375step2Labels = raw40375step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40375step1 raw40375step1Labels permutation29 permutation6
    _ = mixedMoment B node1306 node1306Labels := by rfl

theorem canonical40376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40376 raw40376Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw40376 raw40376Labels = mixedMoment B raw40376step0 raw40376step0Labels := by
      have hz : ∀ j, raw40376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40376step0 = (fun i j => raw40376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40376step0 raw40376; decide +kernel
      have hl : raw40376step0Labels = raw40376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40376 raw40376Labels permutation346 hz
    mixedMoment B raw40376step0 raw40376step0Labels = mixedMoment B raw40376step1 raw40376step1Labels := by
      have hz : ∀ j, raw40376step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40376step1 = (fun i j => raw40376step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40376step1 raw40376step0; decide +kernel
      have hl : raw40376step1Labels = raw40376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40376step0 raw40376step0Labels permutation56 hz
    mixedMoment B raw40376step1 raw40376step1Labels = mixedMoment B raw40376step2 raw40376step2Labels := by
      have ha : raw40376step2 = (fun i j => raw40376step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40376step2 raw40376step1; decide +kernel
      have hl : raw40376step2Labels = raw40376step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40376step1 raw40376step1Labels permutation24 permutation6
    _ = mixedMoment B node2643 node2643Labels := by rfl

theorem canonical40377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40377 raw40377Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw40377 raw40377Labels = mixedMoment B raw40377step0 raw40377step0Labels := by
      have hz : ∀ j, raw40377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40377step0 = (fun i j => raw40377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40377step0 raw40377; decide +kernel
      have hl : raw40377step0Labels = raw40377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40377 raw40377Labels permutation346 hz
    mixedMoment B raw40377step0 raw40377step0Labels = mixedMoment B raw40377step1 raw40377step1Labels := by
      have hz : ∀ j, raw40377step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40377step1 = (fun i j => raw40377step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40377step1 raw40377step0; decide +kernel
      have hl : raw40377step1Labels = raw40377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40377step0 raw40377step0Labels permutation56 hz
    mixedMoment B raw40377step1 raw40377step1Labels = mixedMoment B raw40377step2 raw40377step2Labels := by
      have ha : raw40377step2 = (fun i j => raw40377step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40377step2 raw40377step1; decide +kernel
      have hl : raw40377step2Labels = raw40377step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40377step1 raw40377step1Labels permutation30 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

theorem canonical40378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40378 raw40378Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw40378 raw40378Labels = mixedMoment B raw40378step0 raw40378step0Labels := by
      have hz : ∀ j, raw40378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40378step0 = (fun i j => raw40378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40378step0 raw40378; decide +kernel
      have hl : raw40378step0Labels = raw40378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40378 raw40378Labels permutation346 hz
    mixedMoment B raw40378step0 raw40378step0Labels = mixedMoment B raw40378step1 raw40378step1Labels := by
      have hz : ∀ j, raw40378step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40378step1 = (fun i j => raw40378step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40378step1 raw40378step0; decide +kernel
      have hl : raw40378step1Labels = raw40378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40378step0 raw40378step0Labels permutation56 hz
    mixedMoment B raw40378step1 raw40378step1Labels = mixedMoment B raw40378step2 raw40378step2Labels := by
      have ha : raw40378step2 = (fun i j => raw40378step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40378step2 raw40378step1; decide +kernel
      have hl : raw40378step2Labels = raw40378step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40378step1 raw40378step1Labels permutation16 permutation6
    _ = mixedMoment B node2603 node2603Labels := by rfl

theorem canonical40379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40379 raw40379Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw40379 raw40379Labels = mixedMoment B raw40379step0 raw40379step0Labels := by
      have hz : ∀ j, raw40379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40379step0 = (fun i j => raw40379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40379step0 raw40379; decide +kernel
      have hl : raw40379step0Labels = raw40379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40379 raw40379Labels permutation346 hz
    mixedMoment B raw40379step0 raw40379step0Labels = mixedMoment B raw40379step1 raw40379step1Labels := by
      have hz : ∀ j, raw40379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40379step1 = (fun i j => raw40379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40379step1 raw40379step0; decide +kernel
      have hl : raw40379step1Labels = raw40379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40379step0 raw40379step0Labels permutation56 hz
    mixedMoment B raw40379step1 raw40379step1Labels = mixedMoment B raw40379step2 raw40379step2Labels := by
      have ha : raw40379step2 = (fun i j => raw40379step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40379step2 raw40379step1; decide +kernel
      have hl : raw40379step2Labels = raw40379step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40379step1 raw40379step1Labels permutation17 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical40380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40380 raw40380Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw40380 raw40380Labels = mixedMoment B raw40380step0 raw40380step0Labels := by
      have hz : ∀ j, raw40380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40380step0 = (fun i j => raw40380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40380step0 raw40380; decide +kernel
      have hl : raw40380step0Labels = raw40380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40380 raw40380Labels permutation346 hz
    mixedMoment B raw40380step0 raw40380step0Labels = mixedMoment B raw40380step1 raw40380step1Labels := by
      have hz : ∀ j, raw40380step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw40380step1 = (fun i j => raw40380step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw40380step1 raw40380step0; decide +kernel
      have hl : raw40380step1Labels = raw40380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40380step0 raw40380step0Labels permutation56 hz
    mixedMoment B raw40380step1 raw40380step1Labels = mixedMoment B raw40380step2 raw40380step2Labels := by
      have ha : raw40380step2 = (fun i j => raw40380step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40380step2 raw40380step1; decide +kernel
      have hl : raw40380step2Labels = raw40380step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40380step1 raw40380step1Labels permutation8 permutation3
    _ = mixedMoment B node3118 node3118Labels := by rfl

theorem canonical40381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40381 raw40381Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw40381 raw40381Labels = mixedMoment B raw40381step0 raw40381step0Labels := by
      have hz : ∀ j, raw40381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40381step0 = (fun i j => raw40381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40381step0 raw40381; decide +kernel
      have hl : raw40381step0Labels = raw40381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40381 raw40381Labels permutation265 hz
    mixedMoment B raw40381step0 raw40381step0Labels = mixedMoment B raw40381step1 raw40381step1Labels := by
      have ha : raw40381step1 = (fun i j => raw40381step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40381step1 raw40381step0; decide +kernel
      have hl : raw40381step1Labels = raw40381step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40381step0 raw40381step0Labels permutation125 permutation6
    _ = mixedMoment B node2641 node2641Labels := by rfl

theorem canonical40382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40382 raw40382Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw40382 raw40382Labels = mixedMoment B raw40382step0 raw40382step0Labels := by
      have hz : ∀ j, raw40382 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40382step0 = (fun i j => raw40382 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40382step0 raw40382; decide +kernel
      have hl : raw40382step0Labels = raw40382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40382 raw40382Labels permutation265 hz
    mixedMoment B raw40382step0 raw40382step0Labels = mixedMoment B raw40382step1 raw40382step1Labels := by
      have ha : raw40382step1 = (fun i j => raw40382step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40382step1 raw40382step0; decide +kernel
      have hl : raw40382step1Labels = raw40382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40382step0 raw40382step0Labels permutation149 permutation6
    _ = mixedMoment B node1270 node1270Labels := by rfl

theorem canonical40383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40383 raw40383Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw40383 raw40383Labels = mixedMoment B raw40383step0 raw40383step0Labels := by
      have hz : ∀ j, raw40383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40383step0 = (fun i j => raw40383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40383step0 raw40383; decide +kernel
      have hl : raw40383step0Labels = raw40383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40383 raw40383Labels permutation265 hz
    mixedMoment B raw40383step0 raw40383step0Labels = mixedMoment B raw40383step1 raw40383step1Labels := by
      have ha : raw40383step1 = (fun i j => raw40383step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40383step1 raw40383step0; decide +kernel
      have hl : raw40383step1Labels = raw40383step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40383step0 raw40383step0Labels permutation95 permutation6
    _ = mixedMoment B node2600 node2600Labels := by rfl

theorem canonical40384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40384 raw40384Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw40384 raw40384Labels = mixedMoment B raw40384step0 raw40384step0Labels := by
      have hz : ∀ j, raw40384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40384step0 = (fun i j => raw40384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40384step0 raw40384; decide +kernel
      have hl : raw40384step0Labels = raw40384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40384 raw40384Labels permutation265 hz
    mixedMoment B raw40384step0 raw40384step0Labels = mixedMoment B raw40384step1 raw40384step1Labels := by
      have ha : raw40384step1 = (fun i j => raw40384step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40384step1 raw40384step0; decide +kernel
      have hl : raw40384step1Labels = raw40384step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40384step0 raw40384step0Labels permutation97 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical40385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40385 raw40385Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw40385 raw40385Labels = mixedMoment B raw40385step0 raw40385step0Labels := by
      have hz : ∀ j, raw40385 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40385step0 = (fun i j => raw40385 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40385step0 raw40385; decide +kernel
      have hl : raw40385step0Labels = raw40385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40385 raw40385Labels permutation265 hz
    mixedMoment B raw40385step0 raw40385step0Labels = mixedMoment B raw40385step1 raw40385step1Labels := by
      have ha : raw40385step1 = (fun i j => raw40385step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40385step1 raw40385step0; decide +kernel
      have hl : raw40385step1Labels = raw40385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40385step0 raw40385step0Labels permutation32 permutation3
    _ = mixedMoment B node3108 node3108Labels := by rfl

theorem canonical40386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40386 raw40386Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw40386 raw40386Labels = mixedMoment B raw40386step0 raw40386step0Labels := by
      have hz : ∀ j, raw40386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw40386step0 = (fun i j => raw40386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw40386step0 raw40386; decide +kernel
      have hl : raw40386step0Labels = raw40386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40386 raw40386Labels permutation265 hz
    mixedMoment B raw40386step0 raw40386step0Labels = mixedMoment B raw40386step1 raw40386step1Labels := by
      have ha : raw40386step1 = (fun i j => raw40386step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40386step1 raw40386step0; decide +kernel
      have hl : raw40386step1Labels = raw40386step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40386step0 raw40386step0Labels permutation96 permutation6
    _ = mixedMoment B node2575 node2575Labels := by rfl

theorem canonical40387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40387 raw40387Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw40387 raw40387Labels = mixedMoment B raw40387step0 raw40387step0Labels := by
      have ha : raw40387step0 = (fun i j => raw40387 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40387step0 raw40387; decide +kernel
      have hl : raw40387step0Labels = raw40387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40387 raw40387Labels permutation502 permutation6
    _ = mixedMoment B node2573 node2573Labels := by rfl

theorem canonical40388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40388 raw40388Labels = mixedMoment B node2285 node2285Labels := by
  calc
    mixedMoment B raw40388 raw40388Labels = mixedMoment B raw40388step0 raw40388step0Labels := by
      have hz : ∀ j, raw40388 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40388step0 = (fun i j => raw40388 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40388step0 raw40388; decide +kernel
      have hl : raw40388step0Labels = raw40388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40388 raw40388Labels permutation520 hz
    mixedMoment B raw40388step0 raw40388step0Labels = mixedMoment B raw40388step1 raw40388step1Labels := by
      have hz : ∀ j, raw40388step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40388step1 = (fun i j => raw40388step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40388step1 raw40388step0; decide +kernel
      have hl : raw40388step1Labels = raw40388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40388step0 raw40388step0Labels permutation104 hz
    mixedMoment B raw40388step1 raw40388step1Labels = mixedMoment B raw40388step2 raw40388step2Labels := by
      have hz : ∀ j, raw40388step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40388step2 = (fun i j => raw40388step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40388step2 raw40388step1; decide +kernel
      have hl : raw40388step2Labels = raw40388step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40388step1 raw40388step1Labels permutation20 hz
    mixedMoment B raw40388step2 raw40388step2Labels = mixedMoment B raw40388step3 raw40388step3Labels := by
      have ha : raw40388step3 = (fun i j => raw40388step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40388step3 raw40388step2; decide +kernel
      have hl : raw40388step3Labels = raw40388step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40388step2 raw40388step2Labels permutation7 permutation3
    mixedMoment B raw40388step3 raw40388step3Labels = mixedMoment B raw40388step4 raw40388step4Labels := by
      have ha : raw40388step4 = -raw40388step3 := by apply Matrix.ext; change ∀ i j, raw40388step4 i j = -(raw40388step3 i j); unfold raw40388step4 raw40388step3; decide +kernel
      have hl : raw40388step4Labels = raw40388step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2285 node2285Labels := by rfl

theorem canonical40389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40389 raw40389Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw40389 raw40389Labels = mixedMoment B raw40389step0 raw40389step0Labels := by
      have hz : ∀ j, raw40389 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40389step0 = (fun i j => raw40389 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40389step0 raw40389; decide +kernel
      have hl : raw40389step0Labels = raw40389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40389 raw40389Labels permutation434 hz
    mixedMoment B raw40389step0 raw40389step0Labels = mixedMoment B raw40389step1 raw40389step1Labels := by
      have hz : ∀ j, raw40389step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40389step1 = (fun i j => raw40389step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40389step1 raw40389step0; decide +kernel
      have hl : raw40389step1Labels = raw40389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40389step0 raw40389step0Labels permutation80 hz
    mixedMoment B raw40389step1 raw40389step1Labels = mixedMoment B raw40389step2 raw40389step2Labels := by
      have ha : raw40389step2 = (fun i j => raw40389step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40389step2 raw40389step1; decide +kernel
      have hl : raw40389step2Labels = raw40389step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40389step1 raw40389step1Labels permutation19 permutation6
    _ = mixedMoment B node2136 node2136Labels := by rfl

theorem canonical40390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40390 raw40390Labels = mixedMoment B node1832 node1832Labels := by
  calc
    mixedMoment B raw40390 raw40390Labels = mixedMoment B raw40390step0 raw40390step0Labels := by
      have hz : ∀ j, raw40390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40390step0 = (fun i j => raw40390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40390step0 raw40390; decide +kernel
      have hl : raw40390step0Labels = raw40390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40390 raw40390Labels permutation434 hz
    mixedMoment B raw40390step0 raw40390step0Labels = mixedMoment B raw40390step1 raw40390step1Labels := by
      have hz : ∀ j, raw40390step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40390step1 = (fun i j => raw40390step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40390step1 raw40390step0; decide +kernel
      have hl : raw40390step1Labels = raw40390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40390step0 raw40390step0Labels permutation80 hz
    mixedMoment B raw40390step1 raw40390step1Labels = mixedMoment B raw40390step2 raw40390step2Labels := by
      have ha : raw40390step2 = (fun i j => raw40390step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40390step2 raw40390step1; decide +kernel
      have hl : raw40390step2Labels = raw40390step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40390step1 raw40390step1Labels permutation19 permutation6
    _ = mixedMoment B node1832 node1832Labels := by rfl

theorem canonical40391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40391 raw40391Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw40391 raw40391Labels = mixedMoment B raw40391step0 raw40391step0Labels := by
      have hz : ∀ j, raw40391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40391step0 = (fun i j => raw40391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40391step0 raw40391; decide +kernel
      have hl : raw40391step0Labels = raw40391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40391 raw40391Labels permutation434 hz
    mixedMoment B raw40391step0 raw40391step0Labels = mixedMoment B raw40391step1 raw40391step1Labels := by
      have hz : ∀ j, raw40391step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40391step1 = (fun i j => raw40391step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40391step1 raw40391step0; decide +kernel
      have hl : raw40391step1Labels = raw40391step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40391step0 raw40391step0Labels permutation80 hz
    mixedMoment B raw40391step1 raw40391step1Labels = mixedMoment B raw40391step2 raw40391step2Labels := by
      have ha : raw40391step2 = (fun i j => raw40391step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40391step2 raw40391step1; decide +kernel
      have hl : raw40391step2Labels = raw40391step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40391step1 raw40391step1Labels permutation17 permutation6
    _ = mixedMoment B node2255 node2255Labels := by rfl

theorem canonical40392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40392 raw40392Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw40392 raw40392Labels = mixedMoment B raw40392step0 raw40392step0Labels := by
      have hz : ∀ j, raw40392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40392step0 = (fun i j => raw40392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40392step0 raw40392; decide +kernel
      have hl : raw40392step0Labels = raw40392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40392 raw40392Labels permutation434 hz
    mixedMoment B raw40392step0 raw40392step0Labels = mixedMoment B raw40392step1 raw40392step1Labels := by
      have hz : ∀ j, raw40392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40392step1 = (fun i j => raw40392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40392step1 raw40392step0; decide +kernel
      have hl : raw40392step1Labels = raw40392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40392step0 raw40392step0Labels permutation80 hz
    mixedMoment B raw40392step1 raw40392step1Labels = mixedMoment B raw40392step2 raw40392step2Labels := by
      have ha : raw40392step2 = (fun i j => raw40392step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40392step2 raw40392step1; decide +kernel
      have hl : raw40392step2Labels = raw40392step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40392step1 raw40392step1Labels permutation19 permutation6
    _ = mixedMoment B node2113 node2113Labels := by rfl

theorem canonical40393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40393 raw40393Labels = mixedMoment B node1820 node1820Labels := by
  calc
    mixedMoment B raw40393 raw40393Labels = mixedMoment B raw40393step0 raw40393step0Labels := by
      have hz : ∀ j, raw40393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40393step0 = (fun i j => raw40393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40393step0 raw40393; decide +kernel
      have hl : raw40393step0Labels = raw40393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40393 raw40393Labels permutation434 hz
    mixedMoment B raw40393step0 raw40393step0Labels = mixedMoment B raw40393step1 raw40393step1Labels := by
      have hz : ∀ j, raw40393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40393step1 = (fun i j => raw40393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40393step1 raw40393step0; decide +kernel
      have hl : raw40393step1Labels = raw40393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40393step0 raw40393step0Labels permutation80 hz
    mixedMoment B raw40393step1 raw40393step1Labels = mixedMoment B raw40393step2 raw40393step2Labels := by
      have ha : raw40393step2 = (fun i j => raw40393step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40393step2 raw40393step1; decide +kernel
      have hl : raw40393step2Labels = raw40393step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40393step1 raw40393step1Labels permutation19 permutation6
    _ = mixedMoment B node1820 node1820Labels := by rfl

theorem canonical40394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40394 raw40394Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw40394 raw40394Labels = mixedMoment B raw40394step0 raw40394step0Labels := by
      have hz : ∀ j, raw40394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40394step0 = (fun i j => raw40394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40394step0 raw40394; decide +kernel
      have hl : raw40394step0Labels = raw40394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40394 raw40394Labels permutation346 hz
    mixedMoment B raw40394step0 raw40394step0Labels = mixedMoment B raw40394step1 raw40394step1Labels := by
      have ha : raw40394step1 = (fun i j => raw40394step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40394step1 raw40394step0; decide +kernel
      have hl : raw40394step1Labels = raw40394step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40394step0 raw40394step0Labels permutation77 permutation6
    _ = mixedMoment B node1828 node1828Labels := by rfl

theorem canonical40395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40395 raw40395Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw40395 raw40395Labels = mixedMoment B raw40395step0 raw40395step0Labels := by
      have hz : ∀ j, raw40395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40395step0 = (fun i j => raw40395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40395step0 raw40395; decide +kernel
      have hl : raw40395step0Labels = raw40395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40395 raw40395Labels permutation346 hz
    mixedMoment B raw40395step0 raw40395step0Labels = mixedMoment B raw40395step1 raw40395step1Labels := by
      have ha : raw40395step1 = (fun i j => raw40395step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40395step1 raw40395step0; decide +kernel
      have hl : raw40395step1Labels = raw40395step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40395step0 raw40395step0Labels permutation73 permutation6
    _ = mixedMoment B node2037 node2037Labels := by rfl

theorem canonical40396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40396 raw40396Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw40396 raw40396Labels = mixedMoment B raw40396step0 raw40396step0Labels := by
      have hz : ∀ j, raw40396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40396step0 = (fun i j => raw40396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40396step0 raw40396; decide +kernel
      have hl : raw40396step0Labels = raw40396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40396 raw40396Labels permutation346 hz
    mixedMoment B raw40396step0 raw40396step0Labels = mixedMoment B raw40396step1 raw40396step1Labels := by
      have ha : raw40396step1 = (fun i j => raw40396step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40396step1 raw40396step0; decide +kernel
      have hl : raw40396step1Labels = raw40396step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40396step0 raw40396step0Labels permutation79 permutation6
    _ = mixedMoment B node2092 node2092Labels := by rfl

theorem canonical40397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40397 raw40397Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw40397 raw40397Labels = mixedMoment B raw40397step0 raw40397step0Labels := by
      have hz : ∀ j, raw40397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40397step0 = (fun i j => raw40397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40397step0 raw40397; decide +kernel
      have hl : raw40397step0Labels = raw40397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40397 raw40397Labels permutation346 hz
    mixedMoment B raw40397step0 raw40397step0Labels = mixedMoment B raw40397step1 raw40397step1Labels := by
      have ha : raw40397step1 = (fun i j => raw40397step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40397step1 raw40397step0; decide +kernel
      have hl : raw40397step1Labels = raw40397step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40397step0 raw40397step0Labels permutation77 permutation6
    _ = mixedMoment B node1813 node1813Labels := by rfl

theorem canonical40398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40398 raw40398Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw40398 raw40398Labels = mixedMoment B raw40398step0 raw40398step0Labels := by
      have hz : ∀ j, raw40398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40398step0 = (fun i j => raw40398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40398step0 raw40398; decide +kernel
      have hl : raw40398step0Labels = raw40398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40398 raw40398Labels permutation346 hz
    mixedMoment B raw40398step0 raw40398step0Labels = mixedMoment B raw40398step1 raw40398step1Labels := by
      have ha : raw40398step1 = (fun i j => raw40398step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40398step1 raw40398step0; decide +kernel
      have hl : raw40398step1Labels = raw40398step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40398step0 raw40398step0Labels permutation73 permutation6
    _ = mixedMoment B node1980 node1980Labels := by rfl

theorem canonical40399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40399 raw40399Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw40399 raw40399Labels = mixedMoment B raw40399step0 raw40399step0Labels := by
      have hz : ∀ j, raw40399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40399step0 = (fun i j => raw40399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40399step0 raw40399; decide +kernel
      have hl : raw40399step0Labels = raw40399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40399 raw40399Labels permutation346 hz
    mixedMoment B raw40399step0 raw40399step0Labels = mixedMoment B raw40399step1 raw40399step1Labels := by
      have ha : raw40399step1 = (fun i j => raw40399step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40399step1 raw40399step0; decide +kernel
      have hl : raw40399step1Labels = raw40399step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40399step0 raw40399step0Labels permutation79 permutation6
    _ = mixedMoment B node1797 node1797Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment928 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 928) =
      Integer.Sparse.eval keyMomentRow928 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 928).leftCharge (GramAssembly.key 928).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2964) := by
    have ha : gramCharges (GramAssembly.key 928).leftCharge (GramAssembly.key 928).rightCharge = raw40368 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40368Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40368 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 928).leftCharge (GramAssembly.key 928).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow928, Integer.Sparse.eval]

theorem keyMoment929 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 929) =
      Integer.Sparse.eval keyMomentRow929 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 929).leftCharge (GramAssembly.key 929).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3096) := by
    have ha : gramCharges (GramAssembly.key 929).leftCharge (GramAssembly.key 929).rightCharge = raw40369 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40369Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40369 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 929).leftCharge (GramAssembly.key 929).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow929, Integer.Sparse.eval]

theorem keyMoment930 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 930) =
      Integer.Sparse.eval keyMomentRow930 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 930).leftCharge (GramAssembly.key 930).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3097) := by
    have ha : gramCharges (GramAssembly.key 930).leftCharge (GramAssembly.key 930).rightCharge = raw40370 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40370Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40370 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 930).leftCharge (GramAssembly.key 930).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow930, Integer.Sparse.eval]

theorem keyMoment931 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 931) =
      Integer.Sparse.eval keyMomentRow931 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 931).leftCharge (GramAssembly.key 931).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3084) := by
    have ha : gramCharges (GramAssembly.key 931).leftCharge (GramAssembly.key 931).rightCharge = raw40371 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40371Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40371 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 931).leftCharge (GramAssembly.key 931).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow931, Integer.Sparse.eval]

theorem keyMoment932 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 932) =
      Integer.Sparse.eval keyMomentRow932 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 932).leftCharge (GramAssembly.key 932).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2789) := by
    have ha : gramCharges (GramAssembly.key 932).leftCharge (GramAssembly.key 932).rightCharge = raw40372 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40372Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40372 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 932).leftCharge (GramAssembly.key 932).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow932, Integer.Sparse.eval]

theorem keyMoment933 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 933) =
      Integer.Sparse.eval keyMomentRow933 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 933).leftCharge (GramAssembly.key 933).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1310) := by
    have ha : gramCharges (GramAssembly.key 933).leftCharge (GramAssembly.key 933).rightCharge = raw40373 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40373Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40373 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 933).leftCharge (GramAssembly.key 933).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow933, Integer.Sparse.eval]

theorem keyMoment934 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 934) =
      Integer.Sparse.eval keyMomentRow934 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 934).leftCharge (GramAssembly.key 934).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 934).leftCharge (GramAssembly.key 934).rightCharge = raw40374 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40374Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40374 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 934).leftCharge (GramAssembly.key 934).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow934, Integer.Sparse.eval]

theorem keyMoment935 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 935) =
      Integer.Sparse.eval keyMomentRow935 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 935).leftCharge (GramAssembly.key 935).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1306) := by
    have ha : gramCharges (GramAssembly.key 935).leftCharge (GramAssembly.key 935).rightCharge = raw40375 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40375Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40375 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 935).leftCharge (GramAssembly.key 935).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow935, Integer.Sparse.eval]

theorem keyMoment936 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 936) =
      Integer.Sparse.eval keyMomentRow936 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 936).leftCharge (GramAssembly.key 936).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2643) := by
    have ha : gramCharges (GramAssembly.key 936).leftCharge (GramAssembly.key 936).rightCharge = raw40376 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40376Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40376 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 936).leftCharge (GramAssembly.key 936).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow936, Integer.Sparse.eval]

theorem keyMoment937 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 937) =
      Integer.Sparse.eval keyMomentRow937 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 937).leftCharge (GramAssembly.key 937).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1273) := by
    have ha : gramCharges (GramAssembly.key 937).leftCharge (GramAssembly.key 937).rightCharge = raw40377 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40377Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40377 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 937).leftCharge (GramAssembly.key 937).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow937, Integer.Sparse.eval]

theorem keyMoment938 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 938) =
      Integer.Sparse.eval keyMomentRow938 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 938).leftCharge (GramAssembly.key 938).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2603) := by
    have ha : gramCharges (GramAssembly.key 938).leftCharge (GramAssembly.key 938).rightCharge = raw40378 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40378Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40378 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 938).leftCharge (GramAssembly.key 938).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow938, Integer.Sparse.eval]

theorem keyMoment939 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 939) =
      Integer.Sparse.eval keyMomentRow939 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 939).leftCharge (GramAssembly.key 939).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 939).leftCharge (GramAssembly.key 939).rightCharge = raw40379 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40379Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40379 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 939).leftCharge (GramAssembly.key 939).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow939, Integer.Sparse.eval]

theorem keyMoment940 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 940) =
      Integer.Sparse.eval keyMomentRow940 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 940).leftCharge (GramAssembly.key 940).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3118) := by
    have ha : gramCharges (GramAssembly.key 940).leftCharge (GramAssembly.key 940).rightCharge = raw40380 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40380Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40380 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 940).leftCharge (GramAssembly.key 940).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow940, Integer.Sparse.eval]

theorem keyMoment941 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 941) =
      Integer.Sparse.eval keyMomentRow941 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 941).leftCharge (GramAssembly.key 941).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2641) := by
    have ha : gramCharges (GramAssembly.key 941).leftCharge (GramAssembly.key 941).rightCharge = raw40381 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40381Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40381 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 941).leftCharge (GramAssembly.key 941).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow941, Integer.Sparse.eval]

theorem keyMoment942 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 942) =
      Integer.Sparse.eval keyMomentRow942 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 942).leftCharge (GramAssembly.key 942).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1270) := by
    have ha : gramCharges (GramAssembly.key 942).leftCharge (GramAssembly.key 942).rightCharge = raw40382 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40382Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40382 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 942).leftCharge (GramAssembly.key 942).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow942, Integer.Sparse.eval]

theorem keyMoment943 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 943) =
      Integer.Sparse.eval keyMomentRow943 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 943).leftCharge (GramAssembly.key 943).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2600) := by
    have ha : gramCharges (GramAssembly.key 943).leftCharge (GramAssembly.key 943).rightCharge = raw40383 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40383Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40383 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 943).leftCharge (GramAssembly.key 943).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow943, Integer.Sparse.eval]

theorem keyMoment944 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 944) =
      Integer.Sparse.eval keyMomentRow944 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 944).leftCharge (GramAssembly.key 944).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 944).leftCharge (GramAssembly.key 944).rightCharge = raw40384 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40384Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40384 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 944).leftCharge (GramAssembly.key 944).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow944, Integer.Sparse.eval]

theorem keyMoment945 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 945) =
      Integer.Sparse.eval keyMomentRow945 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 945).leftCharge (GramAssembly.key 945).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3108) := by
    have ha : gramCharges (GramAssembly.key 945).leftCharge (GramAssembly.key 945).rightCharge = raw40385 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40385Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40385 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 945).leftCharge (GramAssembly.key 945).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow945, Integer.Sparse.eval]

theorem keyMoment946 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 946) =
      Integer.Sparse.eval keyMomentRow946 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 946).leftCharge (GramAssembly.key 946).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2575) := by
    have ha : gramCharges (GramAssembly.key 946).leftCharge (GramAssembly.key 946).rightCharge = raw40386 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40386Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40386 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 946).leftCharge (GramAssembly.key 946).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow946, Integer.Sparse.eval]

theorem keyMoment947 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 947) =
      Integer.Sparse.eval keyMomentRow947 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 947).leftCharge (GramAssembly.key 947).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2573) := by
    have ha : gramCharges (GramAssembly.key 947).leftCharge (GramAssembly.key 947).rightCharge = raw40387 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40387Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40387 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 947).leftCharge (GramAssembly.key 947).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow947, Integer.Sparse.eval]

theorem keyMoment948 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 948) =
      Integer.Sparse.eval keyMomentRow948 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 948).leftCharge (GramAssembly.key 948).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2285) := by
    have ha : gramCharges (GramAssembly.key 948).leftCharge (GramAssembly.key 948).rightCharge = raw40388 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40388Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40388 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 948).leftCharge (GramAssembly.key 948).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow948, Integer.Sparse.eval]

theorem keyMoment949 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 949) =
      Integer.Sparse.eval keyMomentRow949 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 949).leftCharge (GramAssembly.key 949).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2136) := by
    have ha : gramCharges (GramAssembly.key 949).leftCharge (GramAssembly.key 949).rightCharge = raw40389 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40389Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40389 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 949).leftCharge (GramAssembly.key 949).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow949, Integer.Sparse.eval]

theorem keyMoment950 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 950) =
      Integer.Sparse.eval keyMomentRow950 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 950).leftCharge (GramAssembly.key 950).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1832) := by
    have ha : gramCharges (GramAssembly.key 950).leftCharge (GramAssembly.key 950).rightCharge = raw40390 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40390Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40390 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 950).leftCharge (GramAssembly.key 950).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow950, Integer.Sparse.eval]

theorem keyMoment951 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 951) =
      Integer.Sparse.eval keyMomentRow951 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 951).leftCharge (GramAssembly.key 951).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 951).leftCharge (GramAssembly.key 951).rightCharge = raw40391 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40391Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40391 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 951).leftCharge (GramAssembly.key 951).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow951, Integer.Sparse.eval]

theorem keyMoment952 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 952) =
      Integer.Sparse.eval keyMomentRow952 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 952).leftCharge (GramAssembly.key 952).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2113) := by
    have ha : gramCharges (GramAssembly.key 952).leftCharge (GramAssembly.key 952).rightCharge = raw40392 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40392Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40392 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 952).leftCharge (GramAssembly.key 952).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow952, Integer.Sparse.eval]

theorem keyMoment953 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 953) =
      Integer.Sparse.eval keyMomentRow953 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 953).leftCharge (GramAssembly.key 953).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1820) := by
    have ha : gramCharges (GramAssembly.key 953).leftCharge (GramAssembly.key 953).rightCharge = raw40393 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40393Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40393 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 953).leftCharge (GramAssembly.key 953).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow953, Integer.Sparse.eval]

theorem keyMoment954 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 954) =
      Integer.Sparse.eval keyMomentRow954 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 954).leftCharge (GramAssembly.key 954).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1828) := by
    have ha : gramCharges (GramAssembly.key 954).leftCharge (GramAssembly.key 954).rightCharge = raw40394 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40394Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40394 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 954).leftCharge (GramAssembly.key 954).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow954, Integer.Sparse.eval]

theorem keyMoment955 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 955) =
      Integer.Sparse.eval keyMomentRow955 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 955).leftCharge (GramAssembly.key 955).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2037) := by
    have ha : gramCharges (GramAssembly.key 955).leftCharge (GramAssembly.key 955).rightCharge = raw40395 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40395Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40395 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 955).leftCharge (GramAssembly.key 955).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow955, Integer.Sparse.eval]

theorem keyMoment956 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 956) =
      Integer.Sparse.eval keyMomentRow956 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 956).leftCharge (GramAssembly.key 956).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2092) := by
    have ha : gramCharges (GramAssembly.key 956).leftCharge (GramAssembly.key 956).rightCharge = raw40396 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40396Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40396 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 956).leftCharge (GramAssembly.key 956).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow956, Integer.Sparse.eval]

theorem keyMoment957 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 957) =
      Integer.Sparse.eval keyMomentRow957 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 957).leftCharge (GramAssembly.key 957).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1813) := by
    have ha : gramCharges (GramAssembly.key 957).leftCharge (GramAssembly.key 957).rightCharge = raw40397 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40397Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40397 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 957).leftCharge (GramAssembly.key 957).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow957, Integer.Sparse.eval]

theorem keyMoment958 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 958) =
      Integer.Sparse.eval keyMomentRow958 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 958).leftCharge (GramAssembly.key 958).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1980) := by
    have ha : gramCharges (GramAssembly.key 958).leftCharge (GramAssembly.key 958).rightCharge = raw40398 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40398Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40398 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 958).leftCharge (GramAssembly.key 958).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow958, Integer.Sparse.eval]

theorem keyMoment959 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 959) =
      Integer.Sparse.eval keyMomentRow959 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 959).leftCharge (GramAssembly.key 959).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1797) := by
    have ha : gramCharges (GramAssembly.key 959).leftCharge (GramAssembly.key 959).rightCharge = raw40399 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40399Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40399 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 959).leftCharge (GramAssembly.key 959).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow959, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt928 : keyMomentRows (928 : Fin 2886) =
    keyMomentRow928 := by decide +kernel

theorem keyMomentRowsAt929 : keyMomentRows (929 : Fin 2886) =
    keyMomentRow929 := by decide +kernel

theorem keyMomentRowsAt930 : keyMomentRows (930 : Fin 2886) =
    keyMomentRow930 := by decide +kernel

theorem keyMomentRowsAt931 : keyMomentRows (931 : Fin 2886) =
    keyMomentRow931 := by decide +kernel

theorem keyMomentRowsAt932 : keyMomentRows (932 : Fin 2886) =
    keyMomentRow932 := by decide +kernel

theorem keyMomentRowsAt933 : keyMomentRows (933 : Fin 2886) =
    keyMomentRow933 := by decide +kernel

theorem keyMomentRowsAt934 : keyMomentRows (934 : Fin 2886) =
    keyMomentRow934 := by decide +kernel

theorem keyMomentRowsAt935 : keyMomentRows (935 : Fin 2886) =
    keyMomentRow935 := by decide +kernel

theorem keyMomentRowsAt936 : keyMomentRows (936 : Fin 2886) =
    keyMomentRow936 := by decide +kernel

theorem keyMomentRowsAt937 : keyMomentRows (937 : Fin 2886) =
    keyMomentRow937 := by decide +kernel

theorem keyMomentRowsAt938 : keyMomentRows (938 : Fin 2886) =
    keyMomentRow938 := by decide +kernel

theorem keyMomentRowsAt939 : keyMomentRows (939 : Fin 2886) =
    keyMomentRow939 := by decide +kernel

theorem keyMomentRowsAt940 : keyMomentRows (940 : Fin 2886) =
    keyMomentRow940 := by decide +kernel

theorem keyMomentRowsAt941 : keyMomentRows (941 : Fin 2886) =
    keyMomentRow941 := by decide +kernel

theorem keyMomentRowsAt942 : keyMomentRows (942 : Fin 2886) =
    keyMomentRow942 := by decide +kernel

theorem keyMomentRowsAt943 : keyMomentRows (943 : Fin 2886) =
    keyMomentRow943 := by decide +kernel

theorem keyMomentRowsAt944 : keyMomentRows (944 : Fin 2886) =
    keyMomentRow944 := by decide +kernel

theorem keyMomentRowsAt945 : keyMomentRows (945 : Fin 2886) =
    keyMomentRow945 := by decide +kernel

theorem keyMomentRowsAt946 : keyMomentRows (946 : Fin 2886) =
    keyMomentRow946 := by decide +kernel

theorem keyMomentRowsAt947 : keyMomentRows (947 : Fin 2886) =
    keyMomentRow947 := by decide +kernel

theorem keyMomentRowsAt948 : keyMomentRows (948 : Fin 2886) =
    keyMomentRow948 := by decide +kernel

theorem keyMomentRowsAt949 : keyMomentRows (949 : Fin 2886) =
    keyMomentRow949 := by decide +kernel

theorem keyMomentRowsAt950 : keyMomentRows (950 : Fin 2886) =
    keyMomentRow950 := by decide +kernel

theorem keyMomentRowsAt951 : keyMomentRows (951 : Fin 2886) =
    keyMomentRow951 := by decide +kernel

theorem keyMomentRowsAt952 : keyMomentRows (952 : Fin 2886) =
    keyMomentRow952 := by decide +kernel

theorem keyMomentRowsAt953 : keyMomentRows (953 : Fin 2886) =
    keyMomentRow953 := by decide +kernel

theorem keyMomentRowsAt954 : keyMomentRows (954 : Fin 2886) =
    keyMomentRow954 := by decide +kernel

theorem keyMomentRowsAt955 : keyMomentRows (955 : Fin 2886) =
    keyMomentRow955 := by decide +kernel

theorem keyMomentRowsAt956 : keyMomentRows (956 : Fin 2886) =
    keyMomentRow956 := by decide +kernel

theorem keyMomentRowsAt957 : keyMomentRows (957 : Fin 2886) =
    keyMomentRow957 := by decide +kernel

theorem keyMomentRowsAt958 : keyMomentRows (958 : Fin 2886) =
    keyMomentRow958 := by decide +kernel

theorem keyMomentRowsAt959 : keyMomentRows (959 : Fin 2886) =
    keyMomentRow959 := by decide +kernel

theorem keyMomentChunkSound29_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 29) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 928 ∨ k.val = 929 ∨ k.val = 930 ∨ k.val = 931 ∨ k.val = 932 ∨ k.val = 933 ∨ k.val = 934 ∨ k.val = 935 ∨ k.val = 936 ∨ k.val = 937 ∨ k.val = 938 ∨ k.val = 939 ∨ k.val = 940 ∨ k.val = 941 ∨ k.val = 942 ∨ k.val = 943 ∨ k.val = 944 ∨ k.val = 945 ∨ k.val = 946 ∨ k.val = 947 ∨ k.val = 948 ∨ k.val = 949 ∨ k.val = 950 ∨ k.val = 951 ∨ k.val = 952 ∨ k.val = 953 ∨ k.val = 954 ∨ k.val = 955 ∨ k.val = 956 ∨ k.val = 957 ∨ k.val = 958 ∨ k.val = 959 := by omega
  rcases heq with h928 | h929 | h930 | h931 | h932 | h933 | h934 | h935 | h936 | h937 | h938 | h939 | h940 | h941 | h942 | h943 | h944 | h945 | h946 | h947 | h948 | h949 | h950 | h951 | h952 | h953 | h954 | h955 | h956 | h957 | h958 | h959
  · have he : k = (928 : Fin 2886) := Fin.ext h928
    subst k
    rw [keyMomentRowsAt928]
    exact keyMoment928 B hB
  · have he : k = (929 : Fin 2886) := Fin.ext h929
    subst k
    rw [keyMomentRowsAt929]
    exact keyMoment929 B hB
  · have he : k = (930 : Fin 2886) := Fin.ext h930
    subst k
    rw [keyMomentRowsAt930]
    exact keyMoment930 B hB
  · have he : k = (931 : Fin 2886) := Fin.ext h931
    subst k
    rw [keyMomentRowsAt931]
    exact keyMoment931 B hB
  · have he : k = (932 : Fin 2886) := Fin.ext h932
    subst k
    rw [keyMomentRowsAt932]
    exact keyMoment932 B hB
  · have he : k = (933 : Fin 2886) := Fin.ext h933
    subst k
    rw [keyMomentRowsAt933]
    exact keyMoment933 B hB
  · have he : k = (934 : Fin 2886) := Fin.ext h934
    subst k
    rw [keyMomentRowsAt934]
    exact keyMoment934 B hB
  · have he : k = (935 : Fin 2886) := Fin.ext h935
    subst k
    rw [keyMomentRowsAt935]
    exact keyMoment935 B hB
  · have he : k = (936 : Fin 2886) := Fin.ext h936
    subst k
    rw [keyMomentRowsAt936]
    exact keyMoment936 B hB
  · have he : k = (937 : Fin 2886) := Fin.ext h937
    subst k
    rw [keyMomentRowsAt937]
    exact keyMoment937 B hB
  · have he : k = (938 : Fin 2886) := Fin.ext h938
    subst k
    rw [keyMomentRowsAt938]
    exact keyMoment938 B hB
  · have he : k = (939 : Fin 2886) := Fin.ext h939
    subst k
    rw [keyMomentRowsAt939]
    exact keyMoment939 B hB
  · have he : k = (940 : Fin 2886) := Fin.ext h940
    subst k
    rw [keyMomentRowsAt940]
    exact keyMoment940 B hB
  · have he : k = (941 : Fin 2886) := Fin.ext h941
    subst k
    rw [keyMomentRowsAt941]
    exact keyMoment941 B hB
  · have he : k = (942 : Fin 2886) := Fin.ext h942
    subst k
    rw [keyMomentRowsAt942]
    exact keyMoment942 B hB
  · have he : k = (943 : Fin 2886) := Fin.ext h943
    subst k
    rw [keyMomentRowsAt943]
    exact keyMoment943 B hB
  · have he : k = (944 : Fin 2886) := Fin.ext h944
    subst k
    rw [keyMomentRowsAt944]
    exact keyMoment944 B hB
  · have he : k = (945 : Fin 2886) := Fin.ext h945
    subst k
    rw [keyMomentRowsAt945]
    exact keyMoment945 B hB
  · have he : k = (946 : Fin 2886) := Fin.ext h946
    subst k
    rw [keyMomentRowsAt946]
    exact keyMoment946 B hB
  · have he : k = (947 : Fin 2886) := Fin.ext h947
    subst k
    rw [keyMomentRowsAt947]
    exact keyMoment947 B hB
  · have he : k = (948 : Fin 2886) := Fin.ext h948
    subst k
    rw [keyMomentRowsAt948]
    exact keyMoment948 B hB
  · have he : k = (949 : Fin 2886) := Fin.ext h949
    subst k
    rw [keyMomentRowsAt949]
    exact keyMoment949 B hB
  · have he : k = (950 : Fin 2886) := Fin.ext h950
    subst k
    rw [keyMomentRowsAt950]
    exact keyMoment950 B hB
  · have he : k = (951 : Fin 2886) := Fin.ext h951
    subst k
    rw [keyMomentRowsAt951]
    exact keyMoment951 B hB
  · have he : k = (952 : Fin 2886) := Fin.ext h952
    subst k
    rw [keyMomentRowsAt952]
    exact keyMoment952 B hB
  · have he : k = (953 : Fin 2886) := Fin.ext h953
    subst k
    rw [keyMomentRowsAt953]
    exact keyMoment953 B hB
  · have he : k = (954 : Fin 2886) := Fin.ext h954
    subst k
    rw [keyMomentRowsAt954]
    exact keyMoment954 B hB
  · have he : k = (955 : Fin 2886) := Fin.ext h955
    subst k
    rw [keyMomentRowsAt955]
    exact keyMoment955 B hB
  · have he : k = (956 : Fin 2886) := Fin.ext h956
    subst k
    rw [keyMomentRowsAt956]
    exact keyMoment956 B hB
  · have he : k = (957 : Fin 2886) := Fin.ext h957
    subst k
    rw [keyMomentRowsAt957]
    exact keyMoment957 B hB
  · have he : k = (958 : Fin 2886) := Fin.ext h958
    subst k
    rw [keyMomentRowsAt958]
    exact keyMoment958 B hB
  · have he : k = (959 : Fin 2886) := Fin.ext h959
    subst k
    rw [keyMomentRowsAt959]
    exact keyMoment959 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound29_e_oai
