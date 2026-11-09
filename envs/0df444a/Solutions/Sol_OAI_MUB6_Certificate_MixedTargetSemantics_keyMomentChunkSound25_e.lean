-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:49:35.281953+00:00
-- url     : https://prove2.me/submissions/74698f85-099c-4870-abca-1579ef335fe4

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical314
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40247 raw40247Labels = mixedMoment B node93 node93Labels := by
  calc
    mixedMoment B raw40247 raw40247Labels = mixedMoment B raw40247step0 raw40247step0Labels := by
      have hz : ∀ j, raw40247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40247step0 = (fun i j => raw40247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40247step0 raw40247; decide +kernel
      have hl : raw40247step0Labels = raw40247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40247 raw40247Labels permutation346 hz
    mixedMoment B raw40247step0 raw40247step0Labels = mixedMoment B raw40247step1 raw40247step1Labels := by
      have ha : raw40247step1 = (fun i j => raw40247step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40247step1 raw40247step0; decide +kernel
      have hl : raw40247step1Labels = raw40247step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40247step0 raw40247step0Labels permutation123 permutation6
    _ = mixedMoment B node93 node93Labels := by rfl

theorem canonical40248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40248 raw40248Labels = mixedMoment B node509 node509Labels := by
  calc
    mixedMoment B raw40248 raw40248Labels = mixedMoment B raw40248step0 raw40248step0Labels := by
      have hz : ∀ j, raw40248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40248step0 = (fun i j => raw40248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40248step0 raw40248; decide +kernel
      have hl : raw40248step0Labels = raw40248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40248 raw40248Labels permutation346 hz
    mixedMoment B raw40248step0 raw40248step0Labels = mixedMoment B raw40248step1 raw40248step1Labels := by
      have ha : raw40248step1 = (fun i j => raw40248step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40248step1 raw40248step0; decide +kernel
      have hl : raw40248step1Labels = raw40248step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40248step0 raw40248step0Labels permutation123 permutation6
    _ = mixedMoment B node509 node509Labels := by rfl

theorem canonical40249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40249 raw40249Labels = mixedMoment B node63 node63Labels := by
  calc
    mixedMoment B raw40249 raw40249Labels = mixedMoment B raw40249step0 raw40249step0Labels := by
      have ha : raw40249step0 = (fun i j => raw40249 (permutation572 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40249step0 raw40249; decide +kernel
      have hl : raw40249step0Labels = raw40249Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40249 raw40249Labels permutation572 permutation6
    _ = mixedMoment B node63 node63Labels := by rfl

theorem canonical40250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40250 raw40250Labels = mixedMoment B node247 node247Labels := by
  calc
    mixedMoment B raw40250 raw40250Labels = mixedMoment B raw40250step0 raw40250step0Labels := by
      have hz : ∀ j, raw40250 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40250step0 = (fun i j => raw40250 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40250step0 raw40250; decide +kernel
      have hl : raw40250step0Labels = raw40250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40250 raw40250Labels permutation520 hz
    mixedMoment B raw40250step0 raw40250step0Labels = mixedMoment B raw40250step1 raw40250step1Labels := by
      have hz : ∀ j, raw40250step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40250step1 = (fun i j => raw40250step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40250step1 raw40250step0; decide +kernel
      have hl : raw40250step1Labels = raw40250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40250step0 raw40250step0Labels permutation104 hz
    mixedMoment B raw40250step1 raw40250step1Labels = mixedMoment B raw40250step2 raw40250step2Labels := by
      have ha : raw40250step2 = (fun i j => raw40250step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40250step2 raw40250step1; decide +kernel
      have hl : raw40250step2Labels = raw40250step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40250step1 raw40250step1Labels permutation24 permutation6
    _ = mixedMoment B node247 node247Labels := by rfl

theorem canonical40251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40251 raw40251Labels = mixedMoment B node175 node175Labels := by
  calc
    mixedMoment B raw40251 raw40251Labels = mixedMoment B raw40251step0 raw40251step0Labels := by
      have hz : ∀ j, raw40251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40251step0 = (fun i j => raw40251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40251step0 raw40251; decide +kernel
      have hl : raw40251step0Labels = raw40251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40251 raw40251Labels permutation434 hz
    mixedMoment B raw40251step0 raw40251step0Labels = mixedMoment B raw40251step1 raw40251step1Labels := by
      have ha : raw40251step1 = (fun i j => raw40251step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40251step1 raw40251step0; decide +kernel
      have hl : raw40251step1Labels = raw40251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40251step0 raw40251step0Labels permutation99 permutation6
    _ = mixedMoment B node175 node175Labels := by rfl

theorem canonical40252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40252 raw40252Labels = mixedMoment B node222 node222Labels := by
  calc
    mixedMoment B raw40252 raw40252Labels = mixedMoment B raw40252step0 raw40252step0Labels := by
      have hz : ∀ j, raw40252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40252step0 = (fun i j => raw40252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40252step0 raw40252; decide +kernel
      have hl : raw40252step0Labels = raw40252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40252 raw40252Labels permutation434 hz
    mixedMoment B raw40252step0 raw40252step0Labels = mixedMoment B raw40252step1 raw40252step1Labels := by
      have ha : raw40252step1 = (fun i j => raw40252step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40252step1 raw40252step0; decide +kernel
      have hl : raw40252step1Labels = raw40252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40252step0 raw40252step0Labels permutation96 permutation6
    _ = mixedMoment B node222 node222Labels := by rfl

theorem canonical40253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40253 raw40253Labels = mixedMoment B node332 node332Labels := by
  calc
    mixedMoment B raw40253 raw40253Labels = mixedMoment B raw40253step0 raw40253step0Labels := by
      have hz : ∀ j, raw40253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40253step0 = (fun i j => raw40253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40253step0 raw40253; decide +kernel
      have hl : raw40253step0Labels = raw40253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40253 raw40253Labels permutation520 hz
    mixedMoment B raw40253step0 raw40253step0Labels = mixedMoment B raw40253step1 raw40253step1Labels := by
      have ha : raw40253step1 = (fun i j => raw40253step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40253step1 raw40253step0; decide +kernel
      have hl : raw40253step1Labels = raw40253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40253step0 raw40253step0Labels permutation61 permutation6
    mixedMoment B raw40253step1 raw40253step1Labels = mixedMoment B raw40253step2 raw40253step2Labels := by
      have ha : raw40253step2 = -raw40253step1 := by apply Matrix.ext; change ∀ i j, raw40253step2 i j = -(raw40253step1 i j); unfold raw40253step2 raw40253step1; decide +kernel
      have hl : raw40253step2Labels = raw40253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node332 node332Labels := by rfl

theorem canonical40254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40254 raw40254Labels = mixedMoment B node343 node343Labels := by
  calc
    mixedMoment B raw40254 raw40254Labels = mixedMoment B raw40254step0 raw40254step0Labels := by
      have hz : ∀ j, raw40254 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40254step0 = (fun i j => raw40254 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40254step0 raw40254; decide +kernel
      have hl : raw40254step0Labels = raw40254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40254 raw40254Labels permutation520 hz
    mixedMoment B raw40254step0 raw40254step0Labels = mixedMoment B raw40254step1 raw40254step1Labels := by
      have hz : ∀ j, raw40254step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40254step1 = (fun i j => raw40254step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40254step1 raw40254step0; decide +kernel
      have hl : raw40254step1Labels = raw40254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40254step0 raw40254step0Labels permutation104 hz
    mixedMoment B raw40254step1 raw40254step1Labels = mixedMoment B raw40254step2 raw40254step2Labels := by
      have ha : raw40254step2 = (fun i j => raw40254step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40254step2 raw40254step1; decide +kernel
      have hl : raw40254step2Labels = raw40254step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40254step1 raw40254step1Labels permutation15 permutation6
    mixedMoment B raw40254step2 raw40254step2Labels = mixedMoment B raw40254step3 raw40254step3Labels := by
      have ha : raw40254step3 = -raw40254step2 := by apply Matrix.ext; change ∀ i j, raw40254step3 i j = -(raw40254step2 i j); unfold raw40254step3 raw40254step2; decide +kernel
      have hl : raw40254step3Labels = raw40254step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node343 node343Labels := by rfl

theorem canonical40255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40255 raw40255Labels = mixedMoment B node285 node285Labels := by
  calc
    mixedMoment B raw40255 raw40255Labels = mixedMoment B raw40255step0 raw40255step0Labels := by
      have hz : ∀ j, raw40255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40255step0 = (fun i j => raw40255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40255step0 raw40255; decide +kernel
      have hl : raw40255step0Labels = raw40255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40255 raw40255Labels permutation434 hz
    mixedMoment B raw40255step0 raw40255step0Labels = mixedMoment B raw40255step1 raw40255step1Labels := by
      have ha : raw40255step1 = (fun i j => raw40255step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40255step1 raw40255step0; decide +kernel
      have hl : raw40255step1Labels = raw40255step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40255step0 raw40255step0Labels permutation144 permutation7
    _ = mixedMoment B node285 node285Labels := by rfl

theorem canonical40256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40256 raw40256Labels = mixedMoment B node325 node325Labels := by
  calc
    mixedMoment B raw40256 raw40256Labels = mixedMoment B raw40256step0 raw40256step0Labels := by
      have hz : ∀ j, raw40256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40256step0 = (fun i j => raw40256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40256step0 raw40256; decide +kernel
      have hl : raw40256step0Labels = raw40256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40256 raw40256Labels permutation434 hz
    mixedMoment B raw40256step0 raw40256step0Labels = mixedMoment B raw40256step1 raw40256step1Labels := by
      have ha : raw40256step1 = (fun i j => raw40256step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40256step1 raw40256step0; decide +kernel
      have hl : raw40256step1Labels = raw40256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40256step0 raw40256step0Labels permutation61 permutation6
    mixedMoment B raw40256step1 raw40256step1Labels = mixedMoment B raw40256step2 raw40256step2Labels := by
      have ha : raw40256step2 = -raw40256step1 := by apply Matrix.ext; change ∀ i j, raw40256step2 i j = -(raw40256step1 i j); unfold raw40256step2 raw40256step1; decide +kernel
      have hl : raw40256step2Labels = raw40256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node325 node325Labels := by rfl

theorem canonical40257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40257 raw40257Labels = mixedMoment B node293 node293Labels := by
  calc
    mixedMoment B raw40257 raw40257Labels = mixedMoment B raw40257step0 raw40257step0Labels := by
      have ha : raw40257step0 = (fun i j => raw40257 (permutation310 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40257step0 raw40257; decide +kernel
      have hl : raw40257step0Labels = raw40257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40257 raw40257Labels permutation310 permutation6
    mixedMoment B raw40257step0 raw40257step0Labels = mixedMoment B raw40257step1 raw40257step1Labels := by
      have ha : raw40257step1 = -raw40257step0 := by apply Matrix.ext; change ∀ i j, raw40257step1 i j = -(raw40257step0 i j); unfold raw40257step1 raw40257step0; decide +kernel
      have hl : raw40257step1Labels = raw40257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node293 node293Labels := by rfl

theorem canonical40258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40258 raw40258Labels = mixedMoment B node339 node339Labels := by
  calc
    mixedMoment B raw40258 raw40258Labels = mixedMoment B raw40258step0 raw40258step0Labels := by
      have hz : ∀ j, raw40258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40258step0 = (fun i j => raw40258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40258step0 raw40258; decide +kernel
      have hl : raw40258step0Labels = raw40258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40258 raw40258Labels permutation520 hz
    mixedMoment B raw40258step0 raw40258step0Labels = mixedMoment B raw40258step1 raw40258step1Labels := by
      have ha : raw40258step1 = (fun i j => raw40258step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40258step1 raw40258step0; decide +kernel
      have hl : raw40258step1Labels = raw40258step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40258step0 raw40258step0Labels permutation56 permutation6
    mixedMoment B raw40258step1 raw40258step1Labels = mixedMoment B raw40258step2 raw40258step2Labels := by
      have ha : raw40258step2 = -raw40258step1 := by apply Matrix.ext; change ∀ i j, raw40258step2 i j = -(raw40258step1 i j); unfold raw40258step2 raw40258step1; decide +kernel
      have hl : raw40258step2Labels = raw40258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node339 node339Labels := by rfl

theorem canonical40259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40259 raw40259Labels = mixedMoment B node294 node294Labels := by
  calc
    mixedMoment B raw40259 raw40259Labels = mixedMoment B raw40259step0 raw40259step0Labels := by
      have ha : raw40259step0 = (fun i j => raw40259 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40259step0 raw40259; decide +kernel
      have hl : raw40259step0Labels = raw40259Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40259 raw40259Labels permutation322 permutation6
    mixedMoment B raw40259step0 raw40259step0Labels = mixedMoment B raw40259step1 raw40259step1Labels := by
      have ha : raw40259step1 = -raw40259step0 := by apply Matrix.ext; change ∀ i j, raw40259step1 i j = -(raw40259step0 i j); unfold raw40259step1 raw40259step0; decide +kernel
      have hl : raw40259step1Labels = raw40259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node294 node294Labels := by rfl

theorem canonical40260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40260 raw40260Labels = mixedMoment B node321 node321Labels := by
  calc
    mixedMoment B raw40260 raw40260Labels = mixedMoment B raw40260step0 raw40260step0Labels := by
      have ha : raw40260step0 = (fun i j => raw40260 (permutation283 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40260step0 raw40260; decide +kernel
      have hl : raw40260step0Labels = raw40260Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40260 raw40260Labels permutation283 permutation6
    mixedMoment B raw40260step0 raw40260step0Labels = mixedMoment B raw40260step1 raw40260step1Labels := by
      have ha : raw40260step1 = -raw40260step0 := by apply Matrix.ext; change ∀ i j, raw40260step1 i j = -(raw40260step0 i j); unfold raw40260step1 raw40260step0; decide +kernel
      have hl : raw40260step1Labels = raw40260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node321 node321Labels := by rfl

theorem canonical40261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40261 raw40261Labels = mixedMoment B node341 node341Labels := by
  calc
    mixedMoment B raw40261 raw40261Labels = mixedMoment B raw40261step0 raw40261step0Labels := by
      have hz : ∀ j, raw40261 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40261step0 = (fun i j => raw40261 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40261step0 raw40261; decide +kernel
      have hl : raw40261step0Labels = raw40261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40261 raw40261Labels permutation520 hz
    mixedMoment B raw40261step0 raw40261step0Labels = mixedMoment B raw40261step1 raw40261step1Labels := by
      have hz : ∀ j, raw40261step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40261step1 = (fun i j => raw40261step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40261step1 raw40261step0; decide +kernel
      have hl : raw40261step1Labels = raw40261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40261step0 raw40261step0Labels permutation104 hz
    mixedMoment B raw40261step1 raw40261step1Labels = mixedMoment B raw40261step2 raw40261step2Labels := by
      have ha : raw40261step2 = (fun i j => raw40261step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40261step2 raw40261step1; decide +kernel
      have hl : raw40261step2Labels = raw40261step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40261step1 raw40261step1Labels permutation14 permutation6
    mixedMoment B raw40261step2 raw40261step2Labels = mixedMoment B raw40261step3 raw40261step3Labels := by
      have ha : raw40261step3 = -raw40261step2 := by apply Matrix.ext; change ∀ i j, raw40261step3 i j = -(raw40261step2 i j); unfold raw40261step3 raw40261step2; decide +kernel
      have hl : raw40261step3Labels = raw40261step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node341 node341Labels := by rfl

theorem canonical40262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40262 raw40262Labels = mixedMoment B node303 node303Labels := by
  calc
    mixedMoment B raw40262 raw40262Labels = mixedMoment B raw40262step0 raw40262step0Labels := by
      have hz : ∀ j, raw40262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40262step0 = (fun i j => raw40262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40262step0 raw40262; decide +kernel
      have hl : raw40262step0Labels = raw40262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40262 raw40262Labels permutation434 hz
    mixedMoment B raw40262step0 raw40262step0Labels = mixedMoment B raw40262step1 raw40262step1Labels := by
      have ha : raw40262step1 = (fun i j => raw40262step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40262step1 raw40262step0; decide +kernel
      have hl : raw40262step1Labels = raw40262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40262step0 raw40262step0Labels permutation120 permutation6
    _ = mixedMoment B node303 node303Labels := by rfl

theorem canonical40263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40263 raw40263Labels = mixedMoment B node291 node291Labels := by
  calc
    mixedMoment B raw40263 raw40263Labels = mixedMoment B raw40263step0 raw40263step0Labels := by
      have ha : raw40263step0 = (fun i j => raw40263 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40263step0 raw40263; decide +kernel
      have hl : raw40263step0Labels = raw40263Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40263 raw40263Labels permutation548 permutation6
    _ = mixedMoment B node291 node291Labels := by rfl

theorem canonical40264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40264 raw40264Labels = mixedMoment B node158 node158Labels := by
  calc
    mixedMoment B raw40264 raw40264Labels = mixedMoment B raw40264step0 raw40264step0Labels := by
      have hz : ∀ j, raw40264 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40264step0 = (fun i j => raw40264 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40264step0 raw40264; decide +kernel
      have hl : raw40264step0Labels = raw40264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40264 raw40264Labels permutation520 hz
    mixedMoment B raw40264step0 raw40264step0Labels = mixedMoment B raw40264step1 raw40264step1Labels := by
      have hz : ∀ j, raw40264step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40264step1 = (fun i j => raw40264step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40264step1 raw40264step0; decide +kernel
      have hl : raw40264step1Labels = raw40264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40264step0 raw40264step0Labels permutation104 hz
    mixedMoment B raw40264step1 raw40264step1Labels = mixedMoment B raw40264step2 raw40264step2Labels := by
      have hz : ∀ j, raw40264step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40264step2 = (fun i j => raw40264step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40264step2 raw40264step1; decide +kernel
      have hl : raw40264step2Labels = raw40264step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40264step1 raw40264step1Labels permutation20 hz
    mixedMoment B raw40264step2 raw40264step2Labels = mixedMoment B raw40264step3 raw40264step3Labels := by
      have ha : raw40264step3 = (fun i j => raw40264step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40264step3 raw40264step2; decide +kernel
      have hl : raw40264step3Labels = raw40264step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40264step2 raw40264step2Labels permutation6 permutation6
    _ = mixedMoment B node158 node158Labels := by rfl

theorem canonical40265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40265 raw40265Labels = mixedMoment B node28 node28Labels := by
  calc
    mixedMoment B raw40265 raw40265Labels = mixedMoment B raw40265step0 raw40265step0Labels := by
      have hz : ∀ j, raw40265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40265step0 = (fun i j => raw40265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40265step0 raw40265; decide +kernel
      have hl : raw40265step0Labels = raw40265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40265 raw40265Labels permutation434 hz
    mixedMoment B raw40265step0 raw40265step0Labels = mixedMoment B raw40265step1 raw40265step1Labels := by
      have hz : ∀ j, raw40265step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40265step1 = (fun i j => raw40265step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40265step1 raw40265step0; decide +kernel
      have hl : raw40265step1Labels = raw40265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40265step0 raw40265step0Labels permutation80 hz
    mixedMoment B raw40265step1 raw40265step1Labels = mixedMoment B raw40265step2 raw40265step2Labels := by
      have ha : raw40265step2 = (fun i j => raw40265step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40265step2 raw40265step1; decide +kernel
      have hl : raw40265step2Labels = raw40265step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40265step1 raw40265step1Labels permutation27 permutation6
    _ = mixedMoment B node28 node28Labels := by rfl

theorem canonical40266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40266 raw40266Labels = mixedMoment B node94 node94Labels := by
  calc
    mixedMoment B raw40266 raw40266Labels = mixedMoment B raw40266step0 raw40266step0Labels := by
      have hz : ∀ j, raw40266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40266step0 = (fun i j => raw40266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40266step0 raw40266; decide +kernel
      have hl : raw40266step0Labels = raw40266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40266 raw40266Labels permutation434 hz
    mixedMoment B raw40266step0 raw40266step0Labels = mixedMoment B raw40266step1 raw40266step1Labels := by
      have hz : ∀ j, raw40266step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40266step1 = (fun i j => raw40266step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40266step1 raw40266step0; decide +kernel
      have hl : raw40266step1Labels = raw40266step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40266step0 raw40266step0Labels permutation80 hz
    mixedMoment B raw40266step1 raw40266step1Labels = mixedMoment B raw40266step2 raw40266step2Labels := by
      have ha : raw40266step2 = (fun i j => raw40266step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40266step2 raw40266step1; decide +kernel
      have hl : raw40266step2Labels = raw40266step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40266step1 raw40266step1Labels permutation24 permutation6
    _ = mixedMoment B node94 node94Labels := by rfl

theorem canonical40267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40267 raw40267Labels = mixedMoment B node71 node71Labels := by
  calc
    mixedMoment B raw40267 raw40267Labels = mixedMoment B raw40267step0 raw40267step0Labels := by
      have hz : ∀ j, raw40267 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40267step0 = (fun i j => raw40267 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40267step0 raw40267; decide +kernel
      have hl : raw40267step0Labels = raw40267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40267 raw40267Labels permutation520 hz
    mixedMoment B raw40267step0 raw40267step0Labels = mixedMoment B raw40267step1 raw40267step1Labels := by
      have hz : ∀ j, raw40267step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40267step1 = (fun i j => raw40267step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40267step1 raw40267step0; decide +kernel
      have hl : raw40267step1Labels = raw40267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40267step0 raw40267step0Labels permutation104 hz
    mixedMoment B raw40267step1 raw40267step1Labels = mixedMoment B raw40267step2 raw40267step2Labels := by
      have ha : raw40267step2 = (fun i j => raw40267step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40267step2 raw40267step1; decide +kernel
      have hl : raw40267step2Labels = raw40267step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40267step1 raw40267step1Labels permutation15 permutation6
    mixedMoment B raw40267step2 raw40267step2Labels = mixedMoment B raw40267step3 raw40267step3Labels := by
      have ha : raw40267step3 = -raw40267step2 := by apply Matrix.ext; change ∀ i j, raw40267step3 i j = -(raw40267step2 i j); unfold raw40267step3 raw40267step2; decide +kernel
      have hl : raw40267step3Labels = raw40267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node71 node71Labels := by rfl

theorem canonical40268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40268 raw40268Labels = mixedMoment B node68 node68Labels := by
  calc
    mixedMoment B raw40268 raw40268Labels = mixedMoment B raw40268step0 raw40268step0Labels := by
      have hz : ∀ j, raw40268 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40268step0 = (fun i j => raw40268 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40268step0 raw40268; decide +kernel
      have hl : raw40268step0Labels = raw40268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40268 raw40268Labels permutation520 hz
    mixedMoment B raw40268step0 raw40268step0Labels = mixedMoment B raw40268step1 raw40268step1Labels := by
      have ha : raw40268step1 = (fun i j => raw40268step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40268step1 raw40268step0; decide +kernel
      have hl : raw40268step1Labels = raw40268step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40268step0 raw40268step0Labels permutation59 permutation6
    mixedMoment B raw40268step1 raw40268step1Labels = mixedMoment B raw40268step2 raw40268step2Labels := by
      have ha : raw40268step2 = -raw40268step1 := by apply Matrix.ext; change ∀ i j, raw40268step2 i j = -(raw40268step1 i j); unfold raw40268step2 raw40268step1; decide +kernel
      have hl : raw40268step2Labels = raw40268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node68 node68Labels := by rfl

theorem canonical40269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40269 raw40269Labels = mixedMoment B node72 node72Labels := by
  calc
    mixedMoment B raw40269 raw40269Labels = mixedMoment B raw40269step0 raw40269step0Labels := by
      have hz : ∀ j, raw40269 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40269step0 = (fun i j => raw40269 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40269step0 raw40269; decide +kernel
      have hl : raw40269step0Labels = raw40269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40269 raw40269Labels permutation520 hz
    mixedMoment B raw40269step0 raw40269step0Labels = mixedMoment B raw40269step1 raw40269step1Labels := by
      have hz : ∀ j, raw40269step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40269step1 = (fun i j => raw40269step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40269step1 raw40269step0; decide +kernel
      have hl : raw40269step1Labels = raw40269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40269step0 raw40269step0Labels permutation104 hz
    mixedMoment B raw40269step1 raw40269step1Labels = mixedMoment B raw40269step2 raw40269step2Labels := by
      have ha : raw40269step2 = (fun i j => raw40269step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40269step2 raw40269step1; decide +kernel
      have hl : raw40269step2Labels = raw40269step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40269step1 raw40269step1Labels permutation14 permutation6
    mixedMoment B raw40269step2 raw40269step2Labels = mixedMoment B raw40269step3 raw40269step3Labels := by
      have ha : raw40269step3 = -raw40269step2 := by apply Matrix.ext; change ∀ i j, raw40269step3 i j = -(raw40269step2 i j); unfold raw40269step3 raw40269step2; decide +kernel
      have hl : raw40269step3Labels = raw40269step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node72 node72Labels := by rfl

theorem canonical40270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40270 raw40270Labels = mixedMoment B node70 node70Labels := by
  calc
    mixedMoment B raw40270 raw40270Labels = mixedMoment B raw40270step0 raw40270step0Labels := by
      have hz : ∀ j, raw40270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40270step0 = (fun i j => raw40270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40270step0 raw40270; decide +kernel
      have hl : raw40270step0Labels = raw40270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40270 raw40270Labels permutation520 hz
    mixedMoment B raw40270step0 raw40270step0Labels = mixedMoment B raw40270step1 raw40270step1Labels := by
      have hz : ∀ j, raw40270step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40270step1 = (fun i j => raw40270step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40270step1 raw40270step0; decide +kernel
      have hl : raw40270step1Labels = raw40270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40270step0 raw40270step0Labels permutation104 hz
    mixedMoment B raw40270step1 raw40270step1Labels = mixedMoment B raw40270step2 raw40270step2Labels := by
      have ha : raw40270step2 = (fun i j => raw40270step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40270step2 raw40270step1; decide +kernel
      have hl : raw40270step2Labels = raw40270step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40270step1 raw40270step1Labels permutation14 permutation6
    mixedMoment B raw40270step2 raw40270step2Labels = mixedMoment B raw40270step3 raw40270step3Labels := by
      have ha : raw40270step3 = -raw40270step2 := by apply Matrix.ext; change ∀ i j, raw40270step3 i j = -(raw40270step2 i j); unfold raw40270step3 raw40270step2; decide +kernel
      have hl : raw40270step3Labels = raw40270step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node70 node70Labels := by rfl

theorem canonical40271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40271 raw40271Labels = mixedMoment B node252 node252Labels := by
  calc
    mixedMoment B raw40271 raw40271Labels = mixedMoment B raw40271step0 raw40271step0Labels := by
      have hz : ∀ j, raw40271 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40271step0 = (fun i j => raw40271 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40271step0 raw40271; decide +kernel
      have hl : raw40271step0Labels = raw40271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40271 raw40271Labels permutation520 hz
    mixedMoment B raw40271step0 raw40271step0Labels = mixedMoment B raw40271step1 raw40271step1Labels := by
      have hz : ∀ j, raw40271step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40271step1 = (fun i j => raw40271step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40271step1 raw40271step0; decide +kernel
      have hl : raw40271step1Labels = raw40271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40271step0 raw40271step0Labels permutation104 hz
    mixedMoment B raw40271step1 raw40271step1Labels = mixedMoment B raw40271step2 raw40271step2Labels := by
      have ha : raw40271step2 = (fun i j => raw40271step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40271step2 raw40271step1; decide +kernel
      have hl : raw40271step2Labels = raw40271step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40271step1 raw40271step1Labels permutation24 permutation6
    _ = mixedMoment B node252 node252Labels := by rfl

theorem canonical40272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40272 raw40272Labels = mixedMoment B node183 node183Labels := by
  calc
    mixedMoment B raw40272 raw40272Labels = mixedMoment B raw40272step0 raw40272step0Labels := by
      have hz : ∀ j, raw40272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40272step0 = (fun i j => raw40272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40272step0 raw40272; decide +kernel
      have hl : raw40272step0Labels = raw40272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40272 raw40272Labels permutation434 hz
    mixedMoment B raw40272step0 raw40272step0Labels = mixedMoment B raw40272step1 raw40272step1Labels := by
      have ha : raw40272step1 = (fun i j => raw40272step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40272step1 raw40272step0; decide +kernel
      have hl : raw40272step1Labels = raw40272step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40272step0 raw40272step0Labels permutation102 permutation6
    _ = mixedMoment B node183 node183Labels := by rfl

theorem canonical40273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40273 raw40273Labels = mixedMoment B node227 node227Labels := by
  calc
    mixedMoment B raw40273 raw40273Labels = mixedMoment B raw40273step0 raw40273step0Labels := by
      have hz : ∀ j, raw40273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40273step0 = (fun i j => raw40273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40273step0 raw40273; decide +kernel
      have hl : raw40273step0Labels = raw40273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40273 raw40273Labels permutation434 hz
    mixedMoment B raw40273step0 raw40273step0Labels = mixedMoment B raw40273step1 raw40273step1Labels := by
      have ha : raw40273step1 = (fun i j => raw40273step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40273step1 raw40273step0; decide +kernel
      have hl : raw40273step1Labels = raw40273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40273step0 raw40273step0Labels permutation96 permutation6
    _ = mixedMoment B node227 node227Labels := by rfl

theorem canonical40274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40274 raw40274Labels = mixedMoment B node210 node210Labels := by
  calc
    mixedMoment B raw40274 raw40274Labels = mixedMoment B raw40274step0 raw40274step0Labels := by
      have ha : raw40274step0 = (fun i j => raw40274 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40274step0 raw40274; decide +kernel
      have hl : raw40274step0Labels = raw40274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40274 raw40274Labels permutation413 permutation6
    _ = mixedMoment B node210 node210Labels := by rfl

theorem canonical40275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40275 raw40275Labels = mixedMoment B node452 node452Labels := by
  calc
    mixedMoment B raw40275 raw40275Labels = mixedMoment B raw40275step0 raw40275step0Labels := by
      have hz : ∀ j, raw40275 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40275step0 = (fun i j => raw40275 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40275step0 raw40275; decide +kernel
      have hl : raw40275step0Labels = raw40275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40275 raw40275Labels permutation520 hz
    mixedMoment B raw40275step0 raw40275step0Labels = mixedMoment B raw40275step1 raw40275step1Labels := by
      have hz : ∀ j, raw40275step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40275step1 = (fun i j => raw40275step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40275step1 raw40275step0; decide +kernel
      have hl : raw40275step1Labels = raw40275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40275step0 raw40275step0Labels permutation104 hz
    mixedMoment B raw40275step1 raw40275step1Labels = mixedMoment B raw40275step2 raw40275step2Labels := by
      have ha : raw40275step2 = (fun i j => raw40275step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40275step2 raw40275step1; decide +kernel
      have hl : raw40275step2Labels = raw40275step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40275step1 raw40275step1Labels permutation24 permutation6
    _ = mixedMoment B node452 node452Labels := by rfl

theorem canonical40276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40276 raw40276Labels = mixedMoment B node508 node508Labels := by
  calc
    mixedMoment B raw40276 raw40276Labels = mixedMoment B raw40276step0 raw40276step0Labels := by
      have ha : raw40276step0 = (fun i j => raw40276 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40276step0 raw40276; decide +kernel
      have hl : raw40276step0Labels = raw40276Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40276 raw40276Labels permutation168 permutation6
    mixedMoment B raw40276step0 raw40276step0Labels = mixedMoment B raw40276step1 raw40276step1Labels := by
      have ha : raw40276step1 = -raw40276step0 := by apply Matrix.ext; change ∀ i j, raw40276step1 i j = -(raw40276step0 i j); unfold raw40276step1 raw40276step0; decide +kernel
      have hl : raw40276step1Labels = raw40276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node508 node508Labels := by rfl

theorem canonical40277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40277 raw40277Labels = mixedMoment B node509 node509Labels := by
  calc
    mixedMoment B raw40277 raw40277Labels = mixedMoment B raw40277step0 raw40277step0Labels := by
      have hz : ∀ j, raw40277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40277step0 = (fun i j => raw40277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40277step0 raw40277; decide +kernel
      have hl : raw40277step0Labels = raw40277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40277 raw40277Labels permutation434 hz
    mixedMoment B raw40277step0 raw40277step0Labels = mixedMoment B raw40277step1 raw40277step1Labels := by
      have ha : raw40277step1 = (fun i j => raw40277step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40277step1 raw40277step0; decide +kernel
      have hl : raw40277step1Labels = raw40277step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40277step0 raw40277step0Labels permutation36 permutation6
    mixedMoment B raw40277step1 raw40277step1Labels = mixedMoment B raw40277step2 raw40277step2Labels := by
      have ha : raw40277step2 = -raw40277step1 := by apply Matrix.ext; change ∀ i j, raw40277step2 i j = -(raw40277step1 i j); unfold raw40277step2 raw40277step1; decide +kernel
      have hl : raw40277step2Labels = raw40277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node509 node509Labels := by rfl

theorem canonical40278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40278 raw40278Labels = mixedMoment B node161 node161Labels := by
  calc
    mixedMoment B raw40278 raw40278Labels = mixedMoment B raw40278step0 raw40278step0Labels := by
      have hz : ∀ j, raw40278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40278step0 = (fun i j => raw40278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40278step0 raw40278; decide +kernel
      have hl : raw40278step0Labels = raw40278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40278 raw40278Labels permutation520 hz
    mixedMoment B raw40278step0 raw40278step0Labels = mixedMoment B raw40278step1 raw40278step1Labels := by
      have hz : ∀ j, raw40278step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40278step1 = (fun i j => raw40278step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40278step1 raw40278step0; decide +kernel
      have hl : raw40278step1Labels = raw40278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40278step0 raw40278step0Labels permutation104 hz
    mixedMoment B raw40278step1 raw40278step1Labels = mixedMoment B raw40278step2 raw40278step2Labels := by
      have hz : ∀ j, raw40278step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40278step2 = (fun i j => raw40278step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40278step2 raw40278step1; decide +kernel
      have hl : raw40278step2Labels = raw40278step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40278step1 raw40278step1Labels permutation20 hz
    mixedMoment B raw40278step2 raw40278step2Labels = mixedMoment B raw40278step3 raw40278step3Labels := by
      have ha : raw40278step3 = (fun i j => raw40278step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40278step3 raw40278step2; decide +kernel
      have hl : raw40278step3Labels = raw40278step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40278step2 raw40278step2Labels permutation6 permutation6
    _ = mixedMoment B node161 node161Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment800 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 800) =
      Integer.Sparse.eval keyMomentRow800 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 800).leftCharge (GramAssembly.key 800).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 93) := by
    have ha : gramCharges (GramAssembly.key 800).leftCharge (GramAssembly.key 800).rightCharge = raw40247 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40247Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40247 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 800).leftCharge (GramAssembly.key 800).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow800, Integer.Sparse.eval]

theorem keyMoment801 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 801) =
      Integer.Sparse.eval keyMomentRow801 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 801).leftCharge (GramAssembly.key 801).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 509) := by
    have ha : gramCharges (GramAssembly.key 801).leftCharge (GramAssembly.key 801).rightCharge = raw40248 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40248Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40248 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 801).leftCharge (GramAssembly.key 801).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow801, Integer.Sparse.eval]

theorem keyMoment802 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 802) =
      Integer.Sparse.eval keyMomentRow802 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 802).leftCharge (GramAssembly.key 802).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 63) := by
    have ha : gramCharges (GramAssembly.key 802).leftCharge (GramAssembly.key 802).rightCharge = raw40249 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40249Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40249 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 802).leftCharge (GramAssembly.key 802).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow802, Integer.Sparse.eval]

theorem keyMoment803 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 803) =
      Integer.Sparse.eval keyMomentRow803 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 803).leftCharge (GramAssembly.key 803).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 247) := by
    have ha : gramCharges (GramAssembly.key 803).leftCharge (GramAssembly.key 803).rightCharge = raw40250 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40250Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40250 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 803).leftCharge (GramAssembly.key 803).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow803, Integer.Sparse.eval]

theorem keyMoment804 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 804) =
      Integer.Sparse.eval keyMomentRow804 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 804).leftCharge (GramAssembly.key 804).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 175) := by
    have ha : gramCharges (GramAssembly.key 804).leftCharge (GramAssembly.key 804).rightCharge = raw40251 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40251Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40251 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 804).leftCharge (GramAssembly.key 804).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow804, Integer.Sparse.eval]

theorem keyMoment805 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 805) =
      Integer.Sparse.eval keyMomentRow805 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 805).leftCharge (GramAssembly.key 805).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 222) := by
    have ha : gramCharges (GramAssembly.key 805).leftCharge (GramAssembly.key 805).rightCharge = raw40252 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40252Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40252 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 805).leftCharge (GramAssembly.key 805).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow805, Integer.Sparse.eval]

theorem keyMoment806 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 806) =
      Integer.Sparse.eval keyMomentRow806 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 806).leftCharge (GramAssembly.key 806).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 332) := by
    have ha : gramCharges (GramAssembly.key 806).leftCharge (GramAssembly.key 806).rightCharge = raw40253 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40253Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40253 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 806).leftCharge (GramAssembly.key 806).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow806, Integer.Sparse.eval]

theorem keyMoment807 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 807) =
      Integer.Sparse.eval keyMomentRow807 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 807).leftCharge (GramAssembly.key 807).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 343) := by
    have ha : gramCharges (GramAssembly.key 807).leftCharge (GramAssembly.key 807).rightCharge = raw40254 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40254Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40254 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 807).leftCharge (GramAssembly.key 807).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow807, Integer.Sparse.eval]

theorem keyMoment808 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 808) =
      Integer.Sparse.eval keyMomentRow808 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 808).leftCharge (GramAssembly.key 808).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 285) := by
    have ha : gramCharges (GramAssembly.key 808).leftCharge (GramAssembly.key 808).rightCharge = raw40255 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40255Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40255 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 808).leftCharge (GramAssembly.key 808).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow808, Integer.Sparse.eval]

theorem keyMoment809 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 809) =
      Integer.Sparse.eval keyMomentRow809 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 809).leftCharge (GramAssembly.key 809).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 325) := by
    have ha : gramCharges (GramAssembly.key 809).leftCharge (GramAssembly.key 809).rightCharge = raw40256 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40256Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40256 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 809).leftCharge (GramAssembly.key 809).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow809, Integer.Sparse.eval]

theorem keyMoment810 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 810) =
      Integer.Sparse.eval keyMomentRow810 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 810).leftCharge (GramAssembly.key 810).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 293) := by
    have ha : gramCharges (GramAssembly.key 810).leftCharge (GramAssembly.key 810).rightCharge = raw40257 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40257Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40257 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 810).leftCharge (GramAssembly.key 810).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow810, Integer.Sparse.eval]

theorem keyMoment811 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 811) =
      Integer.Sparse.eval keyMomentRow811 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 811).leftCharge (GramAssembly.key 811).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 339) := by
    have ha : gramCharges (GramAssembly.key 811).leftCharge (GramAssembly.key 811).rightCharge = raw40258 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40258Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40258 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 811).leftCharge (GramAssembly.key 811).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow811, Integer.Sparse.eval]

theorem keyMoment812 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 812) =
      Integer.Sparse.eval keyMomentRow812 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 812).leftCharge (GramAssembly.key 812).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 294) := by
    have ha : gramCharges (GramAssembly.key 812).leftCharge (GramAssembly.key 812).rightCharge = raw40259 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40259Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40259 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 812).leftCharge (GramAssembly.key 812).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow812, Integer.Sparse.eval]

theorem keyMoment813 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 813) =
      Integer.Sparse.eval keyMomentRow813 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 813).leftCharge (GramAssembly.key 813).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 321) := by
    have ha : gramCharges (GramAssembly.key 813).leftCharge (GramAssembly.key 813).rightCharge = raw40260 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40260Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40260 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 813).leftCharge (GramAssembly.key 813).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow813, Integer.Sparse.eval]

theorem keyMoment814 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 814) =
      Integer.Sparse.eval keyMomentRow814 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 814).leftCharge (GramAssembly.key 814).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 341) := by
    have ha : gramCharges (GramAssembly.key 814).leftCharge (GramAssembly.key 814).rightCharge = raw40261 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40261Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40261 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 814).leftCharge (GramAssembly.key 814).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow814, Integer.Sparse.eval]

theorem keyMoment815 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 815) =
      Integer.Sparse.eval keyMomentRow815 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 815).leftCharge (GramAssembly.key 815).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 303) := by
    have ha : gramCharges (GramAssembly.key 815).leftCharge (GramAssembly.key 815).rightCharge = raw40262 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40262Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40262 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 815).leftCharge (GramAssembly.key 815).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow815, Integer.Sparse.eval]

theorem keyMoment816 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 816) =
      Integer.Sparse.eval keyMomentRow816 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 816).leftCharge (GramAssembly.key 816).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 291) := by
    have ha : gramCharges (GramAssembly.key 816).leftCharge (GramAssembly.key 816).rightCharge = raw40263 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40263Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40263 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 816).leftCharge (GramAssembly.key 816).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow816, Integer.Sparse.eval]

theorem keyMoment817 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 817) =
      Integer.Sparse.eval keyMomentRow817 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 817).leftCharge (GramAssembly.key 817).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 158) := by
    have ha : gramCharges (GramAssembly.key 817).leftCharge (GramAssembly.key 817).rightCharge = raw40264 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40264Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40264 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 817).leftCharge (GramAssembly.key 817).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow817, Integer.Sparse.eval]

theorem keyMoment818 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 818) =
      Integer.Sparse.eval keyMomentRow818 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 818).leftCharge (GramAssembly.key 818).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 28) := by
    have ha : gramCharges (GramAssembly.key 818).leftCharge (GramAssembly.key 818).rightCharge = raw40265 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40265Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40265 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 818).leftCharge (GramAssembly.key 818).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow818, Integer.Sparse.eval]

theorem keyMoment819 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 819) =
      Integer.Sparse.eval keyMomentRow819 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 819).leftCharge (GramAssembly.key 819).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 94) := by
    have ha : gramCharges (GramAssembly.key 819).leftCharge (GramAssembly.key 819).rightCharge = raw40266 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40266Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40266 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 819).leftCharge (GramAssembly.key 819).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow819, Integer.Sparse.eval]

theorem keyMoment820 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 820) =
      Integer.Sparse.eval keyMomentRow820 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 820).leftCharge (GramAssembly.key 820).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 71) := by
    have ha : gramCharges (GramAssembly.key 820).leftCharge (GramAssembly.key 820).rightCharge = raw40267 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40267Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40267 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 820).leftCharge (GramAssembly.key 820).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow820, Integer.Sparse.eval]

theorem keyMoment821 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 821) =
      Integer.Sparse.eval keyMomentRow821 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 821).leftCharge (GramAssembly.key 821).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 68) := by
    have ha : gramCharges (GramAssembly.key 821).leftCharge (GramAssembly.key 821).rightCharge = raw40268 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40268Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40268 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 821).leftCharge (GramAssembly.key 821).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow821, Integer.Sparse.eval]

theorem keyMoment822 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 822) =
      Integer.Sparse.eval keyMomentRow822 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 822).leftCharge (GramAssembly.key 822).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 72) := by
    have ha : gramCharges (GramAssembly.key 822).leftCharge (GramAssembly.key 822).rightCharge = raw40269 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40269Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40269 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 822).leftCharge (GramAssembly.key 822).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow822, Integer.Sparse.eval]

theorem keyMoment823 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 823) =
      Integer.Sparse.eval keyMomentRow823 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 823).leftCharge (GramAssembly.key 823).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 70) := by
    have ha : gramCharges (GramAssembly.key 823).leftCharge (GramAssembly.key 823).rightCharge = raw40270 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40270Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40270 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 823).leftCharge (GramAssembly.key 823).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow823, Integer.Sparse.eval]

theorem keyMoment824 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 824) =
      Integer.Sparse.eval keyMomentRow824 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 824).leftCharge (GramAssembly.key 824).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 252) := by
    have ha : gramCharges (GramAssembly.key 824).leftCharge (GramAssembly.key 824).rightCharge = raw40271 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40271Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40271 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 824).leftCharge (GramAssembly.key 824).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow824, Integer.Sparse.eval]

theorem keyMoment825 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 825) =
      Integer.Sparse.eval keyMomentRow825 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 825).leftCharge (GramAssembly.key 825).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 183) := by
    have ha : gramCharges (GramAssembly.key 825).leftCharge (GramAssembly.key 825).rightCharge = raw40272 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40272Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40272 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 825).leftCharge (GramAssembly.key 825).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow825, Integer.Sparse.eval]

theorem keyMoment826 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 826) =
      Integer.Sparse.eval keyMomentRow826 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 826).leftCharge (GramAssembly.key 826).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 227) := by
    have ha : gramCharges (GramAssembly.key 826).leftCharge (GramAssembly.key 826).rightCharge = raw40273 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40273Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40273 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 826).leftCharge (GramAssembly.key 826).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow826, Integer.Sparse.eval]

theorem keyMoment827 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 827) =
      Integer.Sparse.eval keyMomentRow827 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 827).leftCharge (GramAssembly.key 827).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 210) := by
    have ha : gramCharges (GramAssembly.key 827).leftCharge (GramAssembly.key 827).rightCharge = raw40274 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40274Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40274 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 827).leftCharge (GramAssembly.key 827).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow827, Integer.Sparse.eval]

theorem keyMoment828 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 828) =
      Integer.Sparse.eval keyMomentRow828 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 828).leftCharge (GramAssembly.key 828).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 452) := by
    have ha : gramCharges (GramAssembly.key 828).leftCharge (GramAssembly.key 828).rightCharge = raw40275 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40275Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40275 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 828).leftCharge (GramAssembly.key 828).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow828, Integer.Sparse.eval]

theorem keyMoment829 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 829) =
      Integer.Sparse.eval keyMomentRow829 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 829).leftCharge (GramAssembly.key 829).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 508) := by
    have ha : gramCharges (GramAssembly.key 829).leftCharge (GramAssembly.key 829).rightCharge = raw40276 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40276Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40276 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 829).leftCharge (GramAssembly.key 829).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow829, Integer.Sparse.eval]

theorem keyMoment830 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 830) =
      Integer.Sparse.eval keyMomentRow830 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 830).leftCharge (GramAssembly.key 830).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 509) := by
    have ha : gramCharges (GramAssembly.key 830).leftCharge (GramAssembly.key 830).rightCharge = raw40277 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40277Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40277 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 830).leftCharge (GramAssembly.key 830).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow830, Integer.Sparse.eval]

theorem keyMoment831 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 831) =
      Integer.Sparse.eval keyMomentRow831 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 831).leftCharge (GramAssembly.key 831).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 161) := by
    have ha : gramCharges (GramAssembly.key 831).leftCharge (GramAssembly.key 831).rightCharge = raw40278 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40278Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40278 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 831).leftCharge (GramAssembly.key 831).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow831, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt800 : keyMomentRows (800 : Fin 2886) =
    keyMomentRow800 := by decide +kernel

theorem keyMomentRowsAt801 : keyMomentRows (801 : Fin 2886) =
    keyMomentRow801 := by decide +kernel

theorem keyMomentRowsAt802 : keyMomentRows (802 : Fin 2886) =
    keyMomentRow802 := by decide +kernel

theorem keyMomentRowsAt803 : keyMomentRows (803 : Fin 2886) =
    keyMomentRow803 := by decide +kernel

theorem keyMomentRowsAt804 : keyMomentRows (804 : Fin 2886) =
    keyMomentRow804 := by decide +kernel

theorem keyMomentRowsAt805 : keyMomentRows (805 : Fin 2886) =
    keyMomentRow805 := by decide +kernel

theorem keyMomentRowsAt806 : keyMomentRows (806 : Fin 2886) =
    keyMomentRow806 := by decide +kernel

theorem keyMomentRowsAt807 : keyMomentRows (807 : Fin 2886) =
    keyMomentRow807 := by decide +kernel

theorem keyMomentRowsAt808 : keyMomentRows (808 : Fin 2886) =
    keyMomentRow808 := by decide +kernel

theorem keyMomentRowsAt809 : keyMomentRows (809 : Fin 2886) =
    keyMomentRow809 := by decide +kernel

theorem keyMomentRowsAt810 : keyMomentRows (810 : Fin 2886) =
    keyMomentRow810 := by decide +kernel

theorem keyMomentRowsAt811 : keyMomentRows (811 : Fin 2886) =
    keyMomentRow811 := by decide +kernel

theorem keyMomentRowsAt812 : keyMomentRows (812 : Fin 2886) =
    keyMomentRow812 := by decide +kernel

theorem keyMomentRowsAt813 : keyMomentRows (813 : Fin 2886) =
    keyMomentRow813 := by decide +kernel

theorem keyMomentRowsAt814 : keyMomentRows (814 : Fin 2886) =
    keyMomentRow814 := by decide +kernel

theorem keyMomentRowsAt815 : keyMomentRows (815 : Fin 2886) =
    keyMomentRow815 := by decide +kernel

theorem keyMomentRowsAt816 : keyMomentRows (816 : Fin 2886) =
    keyMomentRow816 := by decide +kernel

theorem keyMomentRowsAt817 : keyMomentRows (817 : Fin 2886) =
    keyMomentRow817 := by decide +kernel

theorem keyMomentRowsAt818 : keyMomentRows (818 : Fin 2886) =
    keyMomentRow818 := by decide +kernel

theorem keyMomentRowsAt819 : keyMomentRows (819 : Fin 2886) =
    keyMomentRow819 := by decide +kernel

theorem keyMomentRowsAt820 : keyMomentRows (820 : Fin 2886) =
    keyMomentRow820 := by decide +kernel

theorem keyMomentRowsAt821 : keyMomentRows (821 : Fin 2886) =
    keyMomentRow821 := by decide +kernel

theorem keyMomentRowsAt822 : keyMomentRows (822 : Fin 2886) =
    keyMomentRow822 := by decide +kernel

theorem keyMomentRowsAt823 : keyMomentRows (823 : Fin 2886) =
    keyMomentRow823 := by decide +kernel

theorem keyMomentRowsAt824 : keyMomentRows (824 : Fin 2886) =
    keyMomentRow824 := by decide +kernel

theorem keyMomentRowsAt825 : keyMomentRows (825 : Fin 2886) =
    keyMomentRow825 := by decide +kernel

theorem keyMomentRowsAt826 : keyMomentRows (826 : Fin 2886) =
    keyMomentRow826 := by decide +kernel

theorem keyMomentRowsAt827 : keyMomentRows (827 : Fin 2886) =
    keyMomentRow827 := by decide +kernel

theorem keyMomentRowsAt828 : keyMomentRows (828 : Fin 2886) =
    keyMomentRow828 := by decide +kernel

theorem keyMomentRowsAt829 : keyMomentRows (829 : Fin 2886) =
    keyMomentRow829 := by decide +kernel

theorem keyMomentRowsAt830 : keyMomentRows (830 : Fin 2886) =
    keyMomentRow830 := by decide +kernel

theorem keyMomentRowsAt831 : keyMomentRows (831 : Fin 2886) =
    keyMomentRow831 := by decide +kernel

theorem keyMomentChunkSound25_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 25) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 800 ∨ k.val = 801 ∨ k.val = 802 ∨ k.val = 803 ∨ k.val = 804 ∨ k.val = 805 ∨ k.val = 806 ∨ k.val = 807 ∨ k.val = 808 ∨ k.val = 809 ∨ k.val = 810 ∨ k.val = 811 ∨ k.val = 812 ∨ k.val = 813 ∨ k.val = 814 ∨ k.val = 815 ∨ k.val = 816 ∨ k.val = 817 ∨ k.val = 818 ∨ k.val = 819 ∨ k.val = 820 ∨ k.val = 821 ∨ k.val = 822 ∨ k.val = 823 ∨ k.val = 824 ∨ k.val = 825 ∨ k.val = 826 ∨ k.val = 827 ∨ k.val = 828 ∨ k.val = 829 ∨ k.val = 830 ∨ k.val = 831 := by omega
  rcases heq with h800 | h801 | h802 | h803 | h804 | h805 | h806 | h807 | h808 | h809 | h810 | h811 | h812 | h813 | h814 | h815 | h816 | h817 | h818 | h819 | h820 | h821 | h822 | h823 | h824 | h825 | h826 | h827 | h828 | h829 | h830 | h831
  · have he : k = (800 : Fin 2886) := Fin.ext h800
    subst k
    rw [keyMomentRowsAt800]
    exact keyMoment800 B hB
  · have he : k = (801 : Fin 2886) := Fin.ext h801
    subst k
    rw [keyMomentRowsAt801]
    exact keyMoment801 B hB
  · have he : k = (802 : Fin 2886) := Fin.ext h802
    subst k
    rw [keyMomentRowsAt802]
    exact keyMoment802 B hB
  · have he : k = (803 : Fin 2886) := Fin.ext h803
    subst k
    rw [keyMomentRowsAt803]
    exact keyMoment803 B hB
  · have he : k = (804 : Fin 2886) := Fin.ext h804
    subst k
    rw [keyMomentRowsAt804]
    exact keyMoment804 B hB
  · have he : k = (805 : Fin 2886) := Fin.ext h805
    subst k
    rw [keyMomentRowsAt805]
    exact keyMoment805 B hB
  · have he : k = (806 : Fin 2886) := Fin.ext h806
    subst k
    rw [keyMomentRowsAt806]
    exact keyMoment806 B hB
  · have he : k = (807 : Fin 2886) := Fin.ext h807
    subst k
    rw [keyMomentRowsAt807]
    exact keyMoment807 B hB
  · have he : k = (808 : Fin 2886) := Fin.ext h808
    subst k
    rw [keyMomentRowsAt808]
    exact keyMoment808 B hB
  · have he : k = (809 : Fin 2886) := Fin.ext h809
    subst k
    rw [keyMomentRowsAt809]
    exact keyMoment809 B hB
  · have he : k = (810 : Fin 2886) := Fin.ext h810
    subst k
    rw [keyMomentRowsAt810]
    exact keyMoment810 B hB
  · have he : k = (811 : Fin 2886) := Fin.ext h811
    subst k
    rw [keyMomentRowsAt811]
    exact keyMoment811 B hB
  · have he : k = (812 : Fin 2886) := Fin.ext h812
    subst k
    rw [keyMomentRowsAt812]
    exact keyMoment812 B hB
  · have he : k = (813 : Fin 2886) := Fin.ext h813
    subst k
    rw [keyMomentRowsAt813]
    exact keyMoment813 B hB
  · have he : k = (814 : Fin 2886) := Fin.ext h814
    subst k
    rw [keyMomentRowsAt814]
    exact keyMoment814 B hB
  · have he : k = (815 : Fin 2886) := Fin.ext h815
    subst k
    rw [keyMomentRowsAt815]
    exact keyMoment815 B hB
  · have he : k = (816 : Fin 2886) := Fin.ext h816
    subst k
    rw [keyMomentRowsAt816]
    exact keyMoment816 B hB
  · have he : k = (817 : Fin 2886) := Fin.ext h817
    subst k
    rw [keyMomentRowsAt817]
    exact keyMoment817 B hB
  · have he : k = (818 : Fin 2886) := Fin.ext h818
    subst k
    rw [keyMomentRowsAt818]
    exact keyMoment818 B hB
  · have he : k = (819 : Fin 2886) := Fin.ext h819
    subst k
    rw [keyMomentRowsAt819]
    exact keyMoment819 B hB
  · have he : k = (820 : Fin 2886) := Fin.ext h820
    subst k
    rw [keyMomentRowsAt820]
    exact keyMoment820 B hB
  · have he : k = (821 : Fin 2886) := Fin.ext h821
    subst k
    rw [keyMomentRowsAt821]
    exact keyMoment821 B hB
  · have he : k = (822 : Fin 2886) := Fin.ext h822
    subst k
    rw [keyMomentRowsAt822]
    exact keyMoment822 B hB
  · have he : k = (823 : Fin 2886) := Fin.ext h823
    subst k
    rw [keyMomentRowsAt823]
    exact keyMoment823 B hB
  · have he : k = (824 : Fin 2886) := Fin.ext h824
    subst k
    rw [keyMomentRowsAt824]
    exact keyMoment824 B hB
  · have he : k = (825 : Fin 2886) := Fin.ext h825
    subst k
    rw [keyMomentRowsAt825]
    exact keyMoment825 B hB
  · have he : k = (826 : Fin 2886) := Fin.ext h826
    subst k
    rw [keyMomentRowsAt826]
    exact keyMoment826 B hB
  · have he : k = (827 : Fin 2886) := Fin.ext h827
    subst k
    rw [keyMomentRowsAt827]
    exact keyMoment827 B hB
  · have he : k = (828 : Fin 2886) := Fin.ext h828
    subst k
    rw [keyMomentRowsAt828]
    exact keyMoment828 B hB
  · have he : k = (829 : Fin 2886) := Fin.ext h829
    subst k
    rw [keyMomentRowsAt829]
    exact keyMoment829 B hB
  · have he : k = (830 : Fin 2886) := Fin.ext h830
    subst k
    rw [keyMomentRowsAt830]
    exact keyMoment830 B hB
  · have he : k = (831 : Fin 2886) := Fin.ext h831
    subst k
    rw [keyMomentRowsAt831]
    exact keyMoment831 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound25_e_oai
