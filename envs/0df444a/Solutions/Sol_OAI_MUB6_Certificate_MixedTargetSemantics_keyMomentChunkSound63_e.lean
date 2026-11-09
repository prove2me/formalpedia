-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:59:12.438215+00:00
-- url     : https://prove2.me/submissions/200e86b1-3f3a-4dc5-846d-4a54bceedd60

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical323
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41429 raw41429Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw41429 raw41429Labels = mixedMoment B raw41429step0 raw41429step0Labels := by
      have ha : raw41429step0 = (fun i j => raw41429 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41429step0 raw41429; decide +kernel
      have hl : raw41429step0Labels = raw41429Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41429 raw41429Labels permutation547 permutation6
    _ = mixedMoment B node2479 node2479Labels := by rfl

theorem canonical41430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41430 raw41430Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw41430 raw41430Labels = mixedMoment B raw41430step0 raw41430step0Labels := by
      have ha : raw41430step0 = (fun i j => raw41430 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41430step0 raw41430; decide +kernel
      have hl : raw41430step0Labels = raw41430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41430 raw41430Labels permutation590 permutation6
    _ = mixedMoment B node599 node599Labels := by rfl

theorem canonical41431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41431 raw41431Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw41431 raw41431Labels = mixedMoment B raw41431step0 raw41431step0Labels := by
      have ha : raw41431step0 = (fun i j => raw41431 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41431step0 raw41431; decide +kernel
      have hl : raw41431step0Labels = raw41431Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41431 raw41431Labels permutation569 permutation6
    _ = mixedMoment B node1039 node1039Labels := by rfl

theorem canonical41432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41432 raw41432Labels = mixedMoment B node1827 node1827Labels := by
  calc
    mixedMoment B raw41432 raw41432Labels = mixedMoment B raw41432step0 raw41432step0Labels := by
      have hz : ∀ j, raw41432 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41432step0 = (fun i j => raw41432 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41432step0 raw41432; decide +kernel
      have hl : raw41432step0Labels = raw41432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41432 raw41432Labels permutation520 hz
    mixedMoment B raw41432step0 raw41432step0Labels = mixedMoment B raw41432step1 raw41432step1Labels := by
      have ha : raw41432step1 = (fun i j => raw41432step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41432step1 raw41432step0; decide +kernel
      have hl : raw41432step1Labels = raw41432step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41432step0 raw41432step0Labels permutation122 permutation6
    _ = mixedMoment B node1827 node1827Labels := by rfl

theorem canonical41433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41433 raw41433Labels = mixedMoment B node1792 node1792Labels := by
  calc
    mixedMoment B raw41433 raw41433Labels = mixedMoment B raw41433step0 raw41433step0Labels := by
      have ha : raw41433step0 = (fun i j => raw41433 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41433step0 raw41433; decide +kernel
      have hl : raw41433step0Labels = raw41433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41433 raw41433Labels permutation514 permutation6
    _ = mixedMoment B node1792 node1792Labels := by rfl

theorem canonical41434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41434 raw41434Labels = mixedMoment B node583 node583Labels := by
  calc
    mixedMoment B raw41434 raw41434Labels = mixedMoment B raw41434step0 raw41434step0Labels := by
      have hz : ∀ j, raw41434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41434step0 = (fun i j => raw41434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41434step0 raw41434; decide +kernel
      have hl : raw41434step0Labels = raw41434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41434 raw41434Labels permutation434 hz
    mixedMoment B raw41434step0 raw41434step0Labels = mixedMoment B raw41434step1 raw41434step1Labels := by
      have ha : raw41434step1 = (fun i j => raw41434step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41434step1 raw41434step0; decide +kernel
      have hl : raw41434step1Labels = raw41434step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41434step0 raw41434step0Labels permutation146 permutation6
    _ = mixedMoment B node583 node583Labels := by rfl

theorem canonical41435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41435 raw41435Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw41435 raw41435Labels = mixedMoment B raw41435step0 raw41435step0Labels := by
      have hz : ∀ j, raw41435 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41435step0 = (fun i j => raw41435 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41435step0 raw41435; decide +kernel
      have hl : raw41435step0Labels = raw41435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41435 raw41435Labels permutation520 hz
    mixedMoment B raw41435step0 raw41435step0Labels = mixedMoment B raw41435step1 raw41435step1Labels := by
      have hz : ∀ j, raw41435step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41435step1 = (fun i j => raw41435step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41435step1 raw41435step0; decide +kernel
      have hl : raw41435step1Labels = raw41435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41435step0 raw41435step0Labels permutation104 hz
    mixedMoment B raw41435step1 raw41435step1Labels = mixedMoment B raw41435step2 raw41435step2Labels := by
      have ha : raw41435step2 = (fun i j => raw41435step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41435step2 raw41435step1; decide +kernel
      have hl : raw41435step2Labels = raw41435step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41435step1 raw41435step1Labels permutation24 permutation6
    _ = mixedMoment B node2278 node2278Labels := by rfl

theorem canonical41436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41436 raw41436Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw41436 raw41436Labels = mixedMoment B raw41436step0 raw41436step0Labels := by
      have hz : ∀ j, raw41436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41436step0 = (fun i j => raw41436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41436step0 raw41436; decide +kernel
      have hl : raw41436step0Labels = raw41436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41436 raw41436Labels permutation434 hz
    mixedMoment B raw41436step0 raw41436step0Labels = mixedMoment B raw41436step1 raw41436step1Labels := by
      have ha : raw41436step1 = (fun i j => raw41436step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41436step1 raw41436step0; decide +kernel
      have hl : raw41436step1Labels = raw41436step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41436step0 raw41436step0Labels permutation99 permutation6
    _ = mixedMoment B node2107 node2107Labels := by rfl

theorem canonical41437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41437 raw41437Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw41437 raw41437Labels = mixedMoment B raw41437step0 raw41437step0Labels := by
      have hz : ∀ j, raw41437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41437step0 = (fun i j => raw41437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41437step0 raw41437; decide +kernel
      have hl : raw41437step0Labels = raw41437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41437 raw41437Labels permutation434 hz
    mixedMoment B raw41437step0 raw41437step0Labels = mixedMoment B raw41437step1 raw41437step1Labels := by
      have ha : raw41437step1 = (fun i j => raw41437step0 (permutation98 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41437step1 raw41437step0; decide +kernel
      have hl : raw41437step1Labels = raw41437step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41437step0 raw41437step0Labels permutation98 permutation6
    _ = mixedMoment B node1810 node1810Labels := by rfl

theorem canonical41438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41438 raw41438Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw41438 raw41438Labels = mixedMoment B raw41438step0 raw41438step0Labels := by
      have hz : ∀ j, raw41438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41438step0 = (fun i j => raw41438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41438step0 raw41438; decide +kernel
      have hl : raw41438step0Labels = raw41438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41438 raw41438Labels permutation434 hz
    mixedMoment B raw41438step0 raw41438step0Labels = mixedMoment B raw41438step1 raw41438step1Labels := by
      have ha : raw41438step1 = (fun i j => raw41438step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41438step1 raw41438step0; decide +kernel
      have hl : raw41438step1Labels = raw41438step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41438step0 raw41438step0Labels permutation93 permutation6
    _ = mixedMoment B node2054 node2054Labels := by rfl

theorem canonical41439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41439 raw41439Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw41439 raw41439Labels = mixedMoment B raw41439step0 raw41439step0Labels := by
      have hz : ∀ j, raw41439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41439step0 = (fun i j => raw41439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41439step0 raw41439; decide +kernel
      have hl : raw41439step0Labels = raw41439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41439 raw41439Labels permutation434 hz
    mixedMoment B raw41439step0 raw41439step0Labels = mixedMoment B raw41439step1 raw41439step1Labels := by
      have ha : raw41439step1 = (fun i j => raw41439step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41439step1 raw41439step0; decide +kernel
      have hl : raw41439step1Labels = raw41439step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41439step0 raw41439step0Labels permutation96 permutation6
    _ = mixedMoment B node2244 node2244Labels := by rfl

theorem canonical41440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41440 raw41440Labels = mixedMoment B node1805 node1805Labels := by
  calc
    mixedMoment B raw41440 raw41440Labels = mixedMoment B raw41440step0 raw41440step0Labels := by
      have ha : raw41440step0 = (fun i j => raw41440 (permutation416 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41440step0 raw41440; decide +kernel
      have hl : raw41440step0Labels = raw41440Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41440 raw41440Labels permutation416 permutation6
    _ = mixedMoment B node1805 node1805Labels := by rfl

theorem canonical41441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41441 raw41441Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw41441 raw41441Labels = mixedMoment B raw41441step0 raw41441step0Labels := by
      have ha : raw41441step0 = (fun i j => raw41441 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41441step0 raw41441; decide +kernel
      have hl : raw41441step0Labels = raw41441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41441 raw41441Labels permutation410 permutation6
    _ = mixedMoment B node2020 node2020Labels := by rfl

theorem canonical41442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41442 raw41442Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw41442 raw41442Labels = mixedMoment B raw41442step0 raw41442step0Labels := by
      have hz : ∀ j, raw41442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41442step0 = (fun i j => raw41442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41442step0 raw41442; decide +kernel
      have hl : raw41442step0Labels = raw41442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41442 raw41442Labels permutation520 hz
    mixedMoment B raw41442step0 raw41442step0Labels = mixedMoment B raw41442step1 raw41442step1Labels := by
      have ha : raw41442step1 = (fun i j => raw41442step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41442step1 raw41442step0; decide +kernel
      have hl : raw41442step1Labels = raw41442step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41442step0 raw41442step0Labels permutation96 permutation6
    _ = mixedMoment B node3813 node3813Labels := by rfl

theorem canonical41443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41443 raw41443Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw41443 raw41443Labels = mixedMoment B raw41443step0 raw41443step0Labels := by
      have ha : raw41443step0 = (fun i j => raw41443 (permutation396 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41443step0 raw41443; decide +kernel
      have hl : raw41443step0Labels = raw41443Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41443 raw41443Labels permutation396 permutation6
    _ = mixedMoment B node3787 node3787Labels := by rfl

theorem canonical41444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41444 raw41444Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw41444 raw41444Labels = mixedMoment B raw41444step0 raw41444step0Labels := by
      have ha : raw41444step0 = (fun i j => raw41444 (permutation530 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41444step0 raw41444; decide +kernel
      have hl : raw41444step0Labels = raw41444Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41444 raw41444Labels permutation530 permutation6
    mixedMoment B raw41444step0 raw41444step0Labels = mixedMoment B raw41444step1 raw41444step1Labels := by
      have ha : raw41444step1 = -raw41444step0 := by apply Matrix.ext; change ∀ i j, raw41444step1 i j = -(raw41444step0 i j); unfold raw41444step1 raw41444step0; decide +kernel
      have hl : raw41444step1Labels = raw41444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3671 node3671Labels := by rfl

theorem canonical41445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41445 raw41445Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw41445 raw41445Labels = mixedMoment B raw41445step0 raw41445step0Labels := by
      have ha : raw41445step0 = (fun i j => raw41445 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41445step0 raw41445; decide +kernel
      have hl : raw41445step0Labels = raw41445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41445 raw41445Labels permutation390 permutation6
    _ = mixedMoment B node3781 node3781Labels := by rfl

theorem canonical41446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41446 raw41446Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw41446 raw41446Labels = mixedMoment B raw41446step0 raw41446step0Labels := by
      have ha : raw41446step0 = (fun i j => raw41446 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41446step0 raw41446; decide +kernel
      have hl : raw41446step0Labels = raw41446Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41446 raw41446Labels permutation393 permutation6
    _ = mixedMoment B node3800 node3800Labels := by rfl

theorem canonical41447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41447 raw41447Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw41447 raw41447Labels = mixedMoment B raw41447step0 raw41447step0Labels := by
      have hz : ∀ j, raw41447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41447step0 = (fun i j => raw41447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41447step0 raw41447; decide +kernel
      have hl : raw41447step0Labels = raw41447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41447 raw41447Labels permutation434 hz
    mixedMoment B raw41447step0 raw41447step0Labels = mixedMoment B raw41447step1 raw41447step1Labels := by
      have ha : raw41447step1 = (fun i j => raw41447step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41447step1 raw41447step0; decide +kernel
      have hl : raw41447step1Labels = raw41447step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41447step0 raw41447step0Labels permutation140 permutation6
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical41448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41448 raw41448Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw41448 raw41448Labels = mixedMoment B raw41448step0 raw41448step0Labels := by
      have hz : ∀ j, raw41448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41448step0 = (fun i j => raw41448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41448step0 raw41448; decide +kernel
      have hl : raw41448step0Labels = raw41448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41448 raw41448Labels permutation434 hz
    mixedMoment B raw41448step0 raw41448step0Labels = mixedMoment B raw41448step1 raw41448step1Labels := by
      have ha : raw41448step1 = (fun i j => raw41448step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41448step1 raw41448step0; decide +kernel
      have hl : raw41448step1Labels = raw41448step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41448step0 raw41448step0Labels permutation93 permutation6
    _ = mixedMoment B node3705 node3705Labels := by rfl

theorem canonical41449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41449 raw41449Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw41449 raw41449Labels = mixedMoment B raw41449step0 raw41449step0Labels := by
      have ha : raw41449step0 = (fun i j => raw41449 (permutation626 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41449step0 raw41449; decide +kernel
      have hl : raw41449step0Labels = raw41449Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41449 raw41449Labels permutation626 permutation6
    _ = mixedMoment B node2809 node2809Labels := by rfl

theorem canonical41450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41450 raw41450Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw41450 raw41450Labels = mixedMoment B raw41450step0 raw41450step0Labels := by
      have ha : raw41450step0 = (fun i j => raw41450 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41450step0 raw41450; decide +kernel
      have hl : raw41450step0Labels = raw41450Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41450 raw41450Labels permutation410 permutation6
    _ = mixedMoment B node3690 node3690Labels := by rfl

theorem canonical41451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41451 raw41451Labels = mixedMoment B node3670 node3670Labels := by
  calc
    mixedMoment B raw41451 raw41451Labels = mixedMoment B raw41451step0 raw41451step0Labels := by
      have ha : raw41451step0 = (fun i j => raw41451 (permutation409 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41451step0 raw41451; decide +kernel
      have hl : raw41451step0Labels = raw41451Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41451 raw41451Labels permutation409 permutation6
    _ = mixedMoment B node3670 node3670Labels := by rfl

theorem canonical41452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41452 raw41452Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw41452 raw41452Labels = mixedMoment B raw41452step0 raw41452step0Labels := by
      have ha : raw41452step0 = (fun i j => raw41452 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41452step0 raw41452; decide +kernel
      have hl : raw41452step0Labels = raw41452Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41452 raw41452Labels permutation640 permutation3
    mixedMoment B raw41452step0 raw41452step0Labels = mixedMoment B raw41452step1 raw41452step1Labels := by
      have ha : raw41452step1 = -raw41452step0 := by apply Matrix.ext; change ∀ i j, raw41452step1 i j = -(raw41452step0 i j); unfold raw41452step1 raw41452step0; decide +kernel
      have hl : raw41452step1Labels = raw41452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3909 node3909Labels := by rfl

theorem canonical41453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41453 raw41453Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw41453 raw41453Labels = mixedMoment B raw41453step0 raw41453step0Labels := by
      have ha : raw41453step0 = (fun i j => raw41453 (permutation635 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41453step0 raw41453; decide +kernel
      have hl : raw41453step0Labels = raw41453Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41453 raw41453Labels permutation635 permutation6
    _ = mixedMoment B node2893 node2893Labels := by rfl

theorem canonical41454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41454 raw41454Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw41454 raw41454Labels = mixedMoment B raw41454step0 raw41454step0Labels := by
      have ha : raw41454step0 = (fun i j => raw41454 (permutation333 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41454step0 raw41454; decide +kernel
      have hl : raw41454step0Labels = raw41454Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41454 raw41454Labels permutation333 permutation6
    mixedMoment B raw41454step0 raw41454step0Labels = mixedMoment B raw41454step1 raw41454step1Labels := by
      have ha : raw41454step1 = -raw41454step0 := by apply Matrix.ext; change ∀ i j, raw41454step1 i j = -(raw41454step0 i j); unfold raw41454step1 raw41454step0; decide +kernel
      have hl : raw41454step1Labels = raw41454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

theorem canonical41455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41455 raw41455Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw41455 raw41455Labels = mixedMoment B raw41455step0 raw41455step0Labels := by
      have hz : ∀ j, raw41455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41455step0 = (fun i j => raw41455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41455step0 raw41455; decide +kernel
      have hl : raw41455step0Labels = raw41455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41455 raw41455Labels permutation434 hz
    mixedMoment B raw41455step0 raw41455step0Labels = mixedMoment B raw41455step1 raw41455step1Labels := by
      have ha : raw41455step1 = (fun i j => raw41455step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41455step1 raw41455step0; decide +kernel
      have hl : raw41455step1Labels = raw41455step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41455step0 raw41455step0Labels permutation140 permutation6
    _ = mixedMoment B node1134 node1134Labels := by rfl

theorem canonical41456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41456 raw41456Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw41456 raw41456Labels = mixedMoment B raw41456step0 raw41456step0Labels := by
      have hz : ∀ j, raw41456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41456step0 = (fun i j => raw41456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41456step0 raw41456; decide +kernel
      have hl : raw41456step0Labels = raw41456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41456 raw41456Labels permutation434 hz
    mixedMoment B raw41456step0 raw41456step0Labels = mixedMoment B raw41456step1 raw41456step1Labels := by
      have ha : raw41456step1 = (fun i j => raw41456step0 (permutation117 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41456step1 raw41456step0; decide +kernel
      have hl : raw41456step1Labels = raw41456step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41456step0 raw41456step0Labels permutation117 permutation6
    _ = mixedMoment B node2512 node2512Labels := by rfl

theorem canonical41457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41457 raw41457Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw41457 raw41457Labels = mixedMoment B raw41457step0 raw41457step0Labels := by
      have ha : raw41457step0 = (fun i j => raw41457 (permutation626 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41457step0 raw41457; decide +kernel
      have hl : raw41457step0Labels = raw41457Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41457 raw41457Labels permutation626 permutation6
    _ = mixedMoment B node1129 node1129Labels := by rfl

theorem canonical41458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41458 raw41458Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw41458 raw41458Labels = mixedMoment B raw41458step0 raw41458step0Labels := by
      have ha : raw41458step0 = (fun i j => raw41458 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41458step0 raw41458; decide +kernel
      have hl : raw41458step0Labels = raw41458Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41458 raw41458Labels permutation548 permutation6
    _ = mixedMoment B node2480 node2480Labels := by rfl

theorem canonical41459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41459 raw41459Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw41459 raw41459Labels = mixedMoment B raw41459step0 raw41459step0Labels := by
      have ha : raw41459step0 = (fun i j => raw41459 (permutation547 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41459step0 raw41459; decide +kernel
      have hl : raw41459step0Labels = raw41459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41459 raw41459Labels permutation547 permutation6
    _ = mixedMoment B node2428 node2428Labels := by rfl

theorem canonical41460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41460 raw41460Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw41460 raw41460Labels = mixedMoment B raw41460step0 raw41460step0Labels := by
      have hz : ∀ j, raw41460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41460step0 = (fun i j => raw41460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41460step0 raw41460; decide +kernel
      have hl : raw41460step0Labels = raw41460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41460 raw41460Labels permutation434 hz
    mixedMoment B raw41460step0 raw41460step0Labels = mixedMoment B raw41460step1 raw41460step1Labels := by
      have hz : ∀ j, raw41460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41460step1 = (fun i j => raw41460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41460step1 raw41460step0; decide +kernel
      have hl : raw41460step1Labels = raw41460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41460step0 raw41460step0Labels permutation80 hz
    mixedMoment B raw41460step1 raw41460step1Labels = mixedMoment B raw41460step2 raw41460step2Labels := by
      have ha : raw41460step2 = (fun i j => raw41460step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41460step2 raw41460step1; decide +kernel
      have hl : raw41460step2Labels = raw41460step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41460step1 raw41460step1Labels permutation26 permutation6
    _ = mixedMoment B node608 node608Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2016 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2016) =
      Integer.Sparse.eval keyMomentRow2016 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2016).leftCharge (GramAssembly.key 2016).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2479) := by
    have ha : gramCharges (GramAssembly.key 2016).leftCharge (GramAssembly.key 2016).rightCharge = raw41429 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41429Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41429 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2016).leftCharge (GramAssembly.key 2016).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2016, Integer.Sparse.eval]

theorem keyMoment2017 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2017) =
      Integer.Sparse.eval keyMomentRow2017 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2017).leftCharge (GramAssembly.key 2017).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 599) := by
    have ha : gramCharges (GramAssembly.key 2017).leftCharge (GramAssembly.key 2017).rightCharge = raw41430 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41430Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41430 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2017).leftCharge (GramAssembly.key 2017).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2017, Integer.Sparse.eval]

theorem keyMoment2018 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2018) =
      Integer.Sparse.eval keyMomentRow2018 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2018).leftCharge (GramAssembly.key 2018).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1039) := by
    have ha : gramCharges (GramAssembly.key 2018).leftCharge (GramAssembly.key 2018).rightCharge = raw41431 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41431Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41431 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2018).leftCharge (GramAssembly.key 2018).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2018, Integer.Sparse.eval]

theorem keyMoment2019 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2019) =
      Integer.Sparse.eval keyMomentRow2019 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2019).leftCharge (GramAssembly.key 2019).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1827) := by
    have ha : gramCharges (GramAssembly.key 2019).leftCharge (GramAssembly.key 2019).rightCharge = raw41432 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41432Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41432 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2019).leftCharge (GramAssembly.key 2019).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2019, Integer.Sparse.eval]

theorem keyMoment2020 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2020) =
      Integer.Sparse.eval keyMomentRow2020 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2020).leftCharge (GramAssembly.key 2020).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1792) := by
    have ha : gramCharges (GramAssembly.key 2020).leftCharge (GramAssembly.key 2020).rightCharge = raw41433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41433 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2020).leftCharge (GramAssembly.key 2020).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2020, Integer.Sparse.eval]

theorem keyMoment2021 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2021) =
      Integer.Sparse.eval keyMomentRow2021 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2021).leftCharge (GramAssembly.key 2021).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 583) := by
    have ha : gramCharges (GramAssembly.key 2021).leftCharge (GramAssembly.key 2021).rightCharge = raw41434 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41434Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41434 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2021).leftCharge (GramAssembly.key 2021).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2021, Integer.Sparse.eval]

theorem keyMoment2022 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2022) =
      Integer.Sparse.eval keyMomentRow2022 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2022).leftCharge (GramAssembly.key 2022).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2278) := by
    have ha : gramCharges (GramAssembly.key 2022).leftCharge (GramAssembly.key 2022).rightCharge = raw41435 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41435Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41435 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2022).leftCharge (GramAssembly.key 2022).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2022, Integer.Sparse.eval]

theorem keyMoment2023 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2023) =
      Integer.Sparse.eval keyMomentRow2023 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2023).leftCharge (GramAssembly.key 2023).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2107) := by
    have ha : gramCharges (GramAssembly.key 2023).leftCharge (GramAssembly.key 2023).rightCharge = raw41436 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41436Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41436 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2023).leftCharge (GramAssembly.key 2023).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2023, Integer.Sparse.eval]

theorem keyMoment2024 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2024) =
      Integer.Sparse.eval keyMomentRow2024 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2024).leftCharge (GramAssembly.key 2024).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1810) := by
    have ha : gramCharges (GramAssembly.key 2024).leftCharge (GramAssembly.key 2024).rightCharge = raw41437 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41437Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41437 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2024).leftCharge (GramAssembly.key 2024).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2024, Integer.Sparse.eval]

theorem keyMoment2025 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2025) =
      Integer.Sparse.eval keyMomentRow2025 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2025).leftCharge (GramAssembly.key 2025).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2054) := by
    have ha : gramCharges (GramAssembly.key 2025).leftCharge (GramAssembly.key 2025).rightCharge = raw41438 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41438Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41438 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2025).leftCharge (GramAssembly.key 2025).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2025, Integer.Sparse.eval]

theorem keyMoment2026 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2026) =
      Integer.Sparse.eval keyMomentRow2026 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2026).leftCharge (GramAssembly.key 2026).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2244) := by
    have ha : gramCharges (GramAssembly.key 2026).leftCharge (GramAssembly.key 2026).rightCharge = raw41439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41439 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2026).leftCharge (GramAssembly.key 2026).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2026, Integer.Sparse.eval]

theorem keyMoment2027 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2027) =
      Integer.Sparse.eval keyMomentRow2027 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2027).leftCharge (GramAssembly.key 2027).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1805) := by
    have ha : gramCharges (GramAssembly.key 2027).leftCharge (GramAssembly.key 2027).rightCharge = raw41440 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41440Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41440 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2027).leftCharge (GramAssembly.key 2027).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2027, Integer.Sparse.eval]

theorem keyMoment2028 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2028) =
      Integer.Sparse.eval keyMomentRow2028 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2028).leftCharge (GramAssembly.key 2028).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2020) := by
    have ha : gramCharges (GramAssembly.key 2028).leftCharge (GramAssembly.key 2028).rightCharge = raw41441 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41441Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41441 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2028).leftCharge (GramAssembly.key 2028).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2028, Integer.Sparse.eval]

theorem keyMoment2029 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2029) =
      Integer.Sparse.eval keyMomentRow2029 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2029).leftCharge (GramAssembly.key 2029).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3813) := by
    have ha : gramCharges (GramAssembly.key 2029).leftCharge (GramAssembly.key 2029).rightCharge = raw41442 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41442Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41442 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2029).leftCharge (GramAssembly.key 2029).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2029, Integer.Sparse.eval]

theorem keyMoment2030 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2030) =
      Integer.Sparse.eval keyMomentRow2030 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2030).leftCharge (GramAssembly.key 2030).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3787) := by
    have ha : gramCharges (GramAssembly.key 2030).leftCharge (GramAssembly.key 2030).rightCharge = raw41443 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41443Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41443 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2030).leftCharge (GramAssembly.key 2030).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2030, Integer.Sparse.eval]

theorem keyMoment2031 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2031) =
      Integer.Sparse.eval keyMomentRow2031 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2031).leftCharge (GramAssembly.key 2031).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3671) := by
    have ha : gramCharges (GramAssembly.key 2031).leftCharge (GramAssembly.key 2031).rightCharge = raw41444 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41444Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41444 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2031).leftCharge (GramAssembly.key 2031).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2031, Integer.Sparse.eval]

theorem keyMoment2032 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2032) =
      Integer.Sparse.eval keyMomentRow2032 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2032).leftCharge (GramAssembly.key 2032).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3781) := by
    have ha : gramCharges (GramAssembly.key 2032).leftCharge (GramAssembly.key 2032).rightCharge = raw41445 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41445Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41445 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2032).leftCharge (GramAssembly.key 2032).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2032, Integer.Sparse.eval]

theorem keyMoment2033 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2033) =
      Integer.Sparse.eval keyMomentRow2033 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2033).leftCharge (GramAssembly.key 2033).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3800) := by
    have ha : gramCharges (GramAssembly.key 2033).leftCharge (GramAssembly.key 2033).rightCharge = raw41446 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41446Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41446 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2033).leftCharge (GramAssembly.key 2033).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2033, Integer.Sparse.eval]

theorem keyMoment2034 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2034) =
      Integer.Sparse.eval keyMomentRow2034 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2034).leftCharge (GramAssembly.key 2034).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2813) := by
    have ha : gramCharges (GramAssembly.key 2034).leftCharge (GramAssembly.key 2034).rightCharge = raw41447 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41447Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41447 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2034).leftCharge (GramAssembly.key 2034).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2034, Integer.Sparse.eval]

theorem keyMoment2035 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2035) =
      Integer.Sparse.eval keyMomentRow2035 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2035).leftCharge (GramAssembly.key 2035).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3705) := by
    have ha : gramCharges (GramAssembly.key 2035).leftCharge (GramAssembly.key 2035).rightCharge = raw41448 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41448Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41448 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2035).leftCharge (GramAssembly.key 2035).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2035, Integer.Sparse.eval]

theorem keyMoment2036 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2036) =
      Integer.Sparse.eval keyMomentRow2036 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2036).leftCharge (GramAssembly.key 2036).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2809) := by
    have ha : gramCharges (GramAssembly.key 2036).leftCharge (GramAssembly.key 2036).rightCharge = raw41449 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41449Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41449 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2036).leftCharge (GramAssembly.key 2036).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2036, Integer.Sparse.eval]

theorem keyMoment2037 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2037) =
      Integer.Sparse.eval keyMomentRow2037 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2037).leftCharge (GramAssembly.key 2037).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3690) := by
    have ha : gramCharges (GramAssembly.key 2037).leftCharge (GramAssembly.key 2037).rightCharge = raw41450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41450 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2037).leftCharge (GramAssembly.key 2037).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2037, Integer.Sparse.eval]

theorem keyMoment2038 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2038) =
      Integer.Sparse.eval keyMomentRow2038 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2038).leftCharge (GramAssembly.key 2038).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3670) := by
    have ha : gramCharges (GramAssembly.key 2038).leftCharge (GramAssembly.key 2038).rightCharge = raw41451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41451 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2038).leftCharge (GramAssembly.key 2038).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2038, Integer.Sparse.eval]

theorem keyMoment2039 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2039) =
      Integer.Sparse.eval keyMomentRow2039 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2039).leftCharge (GramAssembly.key 2039).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3909) := by
    have ha : gramCharges (GramAssembly.key 2039).leftCharge (GramAssembly.key 2039).rightCharge = raw41452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41452 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2039).leftCharge (GramAssembly.key 2039).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2039, Integer.Sparse.eval]

theorem keyMoment2040 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2040) =
      Integer.Sparse.eval keyMomentRow2040 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2040).leftCharge (GramAssembly.key 2040).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2893) := by
    have ha : gramCharges (GramAssembly.key 2040).leftCharge (GramAssembly.key 2040).rightCharge = raw41453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41453 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2040).leftCharge (GramAssembly.key 2040).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2040, Integer.Sparse.eval]

theorem keyMoment2041 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2041) =
      Integer.Sparse.eval keyMomentRow2041 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2041).leftCharge (GramAssembly.key 2041).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3945) := by
    have ha : gramCharges (GramAssembly.key 2041).leftCharge (GramAssembly.key 2041).rightCharge = raw41454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41454 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2041).leftCharge (GramAssembly.key 2041).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2041, Integer.Sparse.eval]

theorem keyMoment2042 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2042) =
      Integer.Sparse.eval keyMomentRow2042 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2042).leftCharge (GramAssembly.key 2042).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1134) := by
    have ha : gramCharges (GramAssembly.key 2042).leftCharge (GramAssembly.key 2042).rightCharge = raw41455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41455 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2042).leftCharge (GramAssembly.key 2042).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2042, Integer.Sparse.eval]

theorem keyMoment2043 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2043) =
      Integer.Sparse.eval keyMomentRow2043 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2043).leftCharge (GramAssembly.key 2043).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2512) := by
    have ha : gramCharges (GramAssembly.key 2043).leftCharge (GramAssembly.key 2043).rightCharge = raw41456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41456 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2043).leftCharge (GramAssembly.key 2043).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2043, Integer.Sparse.eval]

theorem keyMoment2044 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2044) =
      Integer.Sparse.eval keyMomentRow2044 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2044).leftCharge (GramAssembly.key 2044).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1129) := by
    have ha : gramCharges (GramAssembly.key 2044).leftCharge (GramAssembly.key 2044).rightCharge = raw41457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41457 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2044).leftCharge (GramAssembly.key 2044).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2044, Integer.Sparse.eval]

theorem keyMoment2045 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2045) =
      Integer.Sparse.eval keyMomentRow2045 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2045).leftCharge (GramAssembly.key 2045).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2480) := by
    have ha : gramCharges (GramAssembly.key 2045).leftCharge (GramAssembly.key 2045).rightCharge = raw41458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41458 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2045).leftCharge (GramAssembly.key 2045).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2045, Integer.Sparse.eval]

theorem keyMoment2046 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2046) =
      Integer.Sparse.eval keyMomentRow2046 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2046).leftCharge (GramAssembly.key 2046).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2428) := by
    have ha : gramCharges (GramAssembly.key 2046).leftCharge (GramAssembly.key 2046).rightCharge = raw41459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41459 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2046).leftCharge (GramAssembly.key 2046).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2046, Integer.Sparse.eval]

theorem keyMoment2047 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2047) =
      Integer.Sparse.eval keyMomentRow2047 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2047).leftCharge (GramAssembly.key 2047).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 608) := by
    have ha : gramCharges (GramAssembly.key 2047).leftCharge (GramAssembly.key 2047).rightCharge = raw41460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 2047).leftCharge (GramAssembly.key 2047).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow2047, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2016 : keyMomentRows (2016 : Fin 2886) =
    keyMomentRow2016 := by decide +kernel

theorem keyMomentRowsAt2017 : keyMomentRows (2017 : Fin 2886) =
    keyMomentRow2017 := by decide +kernel

theorem keyMomentRowsAt2018 : keyMomentRows (2018 : Fin 2886) =
    keyMomentRow2018 := by decide +kernel

theorem keyMomentRowsAt2019 : keyMomentRows (2019 : Fin 2886) =
    keyMomentRow2019 := by decide +kernel

theorem keyMomentRowsAt2020 : keyMomentRows (2020 : Fin 2886) =
    keyMomentRow2020 := by decide +kernel

theorem keyMomentRowsAt2021 : keyMomentRows (2021 : Fin 2886) =
    keyMomentRow2021 := by decide +kernel

theorem keyMomentRowsAt2022 : keyMomentRows (2022 : Fin 2886) =
    keyMomentRow2022 := by decide +kernel

theorem keyMomentRowsAt2023 : keyMomentRows (2023 : Fin 2886) =
    keyMomentRow2023 := by decide +kernel

theorem keyMomentRowsAt2024 : keyMomentRows (2024 : Fin 2886) =
    keyMomentRow2024 := by decide +kernel

theorem keyMomentRowsAt2025 : keyMomentRows (2025 : Fin 2886) =
    keyMomentRow2025 := by decide +kernel

theorem keyMomentRowsAt2026 : keyMomentRows (2026 : Fin 2886) =
    keyMomentRow2026 := by decide +kernel

theorem keyMomentRowsAt2027 : keyMomentRows (2027 : Fin 2886) =
    keyMomentRow2027 := by decide +kernel

theorem keyMomentRowsAt2028 : keyMomentRows (2028 : Fin 2886) =
    keyMomentRow2028 := by decide +kernel

theorem keyMomentRowsAt2029 : keyMomentRows (2029 : Fin 2886) =
    keyMomentRow2029 := by decide +kernel

theorem keyMomentRowsAt2030 : keyMomentRows (2030 : Fin 2886) =
    keyMomentRow2030 := by decide +kernel

theorem keyMomentRowsAt2031 : keyMomentRows (2031 : Fin 2886) =
    keyMomentRow2031 := by decide +kernel

theorem keyMomentRowsAt2032 : keyMomentRows (2032 : Fin 2886) =
    keyMomentRow2032 := by decide +kernel

theorem keyMomentRowsAt2033 : keyMomentRows (2033 : Fin 2886) =
    keyMomentRow2033 := by decide +kernel

theorem keyMomentRowsAt2034 : keyMomentRows (2034 : Fin 2886) =
    keyMomentRow2034 := by decide +kernel

theorem keyMomentRowsAt2035 : keyMomentRows (2035 : Fin 2886) =
    keyMomentRow2035 := by decide +kernel

theorem keyMomentRowsAt2036 : keyMomentRows (2036 : Fin 2886) =
    keyMomentRow2036 := by decide +kernel

theorem keyMomentRowsAt2037 : keyMomentRows (2037 : Fin 2886) =
    keyMomentRow2037 := by decide +kernel

theorem keyMomentRowsAt2038 : keyMomentRows (2038 : Fin 2886) =
    keyMomentRow2038 := by decide +kernel

theorem keyMomentRowsAt2039 : keyMomentRows (2039 : Fin 2886) =
    keyMomentRow2039 := by decide +kernel

theorem keyMomentRowsAt2040 : keyMomentRows (2040 : Fin 2886) =
    keyMomentRow2040 := by decide +kernel

theorem keyMomentRowsAt2041 : keyMomentRows (2041 : Fin 2886) =
    keyMomentRow2041 := by decide +kernel

theorem keyMomentRowsAt2042 : keyMomentRows (2042 : Fin 2886) =
    keyMomentRow2042 := by decide +kernel

theorem keyMomentRowsAt2043 : keyMomentRows (2043 : Fin 2886) =
    keyMomentRow2043 := by decide +kernel

theorem keyMomentRowsAt2044 : keyMomentRows (2044 : Fin 2886) =
    keyMomentRow2044 := by decide +kernel

theorem keyMomentRowsAt2045 : keyMomentRows (2045 : Fin 2886) =
    keyMomentRow2045 := by decide +kernel

theorem keyMomentRowsAt2046 : keyMomentRows (2046 : Fin 2886) =
    keyMomentRow2046 := by decide +kernel

theorem keyMomentRowsAt2047 : keyMomentRows (2047 : Fin 2886) =
    keyMomentRow2047 := by decide +kernel

theorem keyMomentChunkSound63_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 63) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2016 ∨ k.val = 2017 ∨ k.val = 2018 ∨ k.val = 2019 ∨ k.val = 2020 ∨ k.val = 2021 ∨ k.val = 2022 ∨ k.val = 2023 ∨ k.val = 2024 ∨ k.val = 2025 ∨ k.val = 2026 ∨ k.val = 2027 ∨ k.val = 2028 ∨ k.val = 2029 ∨ k.val = 2030 ∨ k.val = 2031 ∨ k.val = 2032 ∨ k.val = 2033 ∨ k.val = 2034 ∨ k.val = 2035 ∨ k.val = 2036 ∨ k.val = 2037 ∨ k.val = 2038 ∨ k.val = 2039 ∨ k.val = 2040 ∨ k.val = 2041 ∨ k.val = 2042 ∨ k.val = 2043 ∨ k.val = 2044 ∨ k.val = 2045 ∨ k.val = 2046 ∨ k.val = 2047 := by omega
  rcases heq with h2016 | h2017 | h2018 | h2019 | h2020 | h2021 | h2022 | h2023 | h2024 | h2025 | h2026 | h2027 | h2028 | h2029 | h2030 | h2031 | h2032 | h2033 | h2034 | h2035 | h2036 | h2037 | h2038 | h2039 | h2040 | h2041 | h2042 | h2043 | h2044 | h2045 | h2046 | h2047
  · have he : k = (2016 : Fin 2886) := Fin.ext h2016
    subst k
    rw [keyMomentRowsAt2016]
    exact keyMoment2016 B hB
  · have he : k = (2017 : Fin 2886) := Fin.ext h2017
    subst k
    rw [keyMomentRowsAt2017]
    exact keyMoment2017 B hB
  · have he : k = (2018 : Fin 2886) := Fin.ext h2018
    subst k
    rw [keyMomentRowsAt2018]
    exact keyMoment2018 B hB
  · have he : k = (2019 : Fin 2886) := Fin.ext h2019
    subst k
    rw [keyMomentRowsAt2019]
    exact keyMoment2019 B hB
  · have he : k = (2020 : Fin 2886) := Fin.ext h2020
    subst k
    rw [keyMomentRowsAt2020]
    exact keyMoment2020 B hB
  · have he : k = (2021 : Fin 2886) := Fin.ext h2021
    subst k
    rw [keyMomentRowsAt2021]
    exact keyMoment2021 B hB
  · have he : k = (2022 : Fin 2886) := Fin.ext h2022
    subst k
    rw [keyMomentRowsAt2022]
    exact keyMoment2022 B hB
  · have he : k = (2023 : Fin 2886) := Fin.ext h2023
    subst k
    rw [keyMomentRowsAt2023]
    exact keyMoment2023 B hB
  · have he : k = (2024 : Fin 2886) := Fin.ext h2024
    subst k
    rw [keyMomentRowsAt2024]
    exact keyMoment2024 B hB
  · have he : k = (2025 : Fin 2886) := Fin.ext h2025
    subst k
    rw [keyMomentRowsAt2025]
    exact keyMoment2025 B hB
  · have he : k = (2026 : Fin 2886) := Fin.ext h2026
    subst k
    rw [keyMomentRowsAt2026]
    exact keyMoment2026 B hB
  · have he : k = (2027 : Fin 2886) := Fin.ext h2027
    subst k
    rw [keyMomentRowsAt2027]
    exact keyMoment2027 B hB
  · have he : k = (2028 : Fin 2886) := Fin.ext h2028
    subst k
    rw [keyMomentRowsAt2028]
    exact keyMoment2028 B hB
  · have he : k = (2029 : Fin 2886) := Fin.ext h2029
    subst k
    rw [keyMomentRowsAt2029]
    exact keyMoment2029 B hB
  · have he : k = (2030 : Fin 2886) := Fin.ext h2030
    subst k
    rw [keyMomentRowsAt2030]
    exact keyMoment2030 B hB
  · have he : k = (2031 : Fin 2886) := Fin.ext h2031
    subst k
    rw [keyMomentRowsAt2031]
    exact keyMoment2031 B hB
  · have he : k = (2032 : Fin 2886) := Fin.ext h2032
    subst k
    rw [keyMomentRowsAt2032]
    exact keyMoment2032 B hB
  · have he : k = (2033 : Fin 2886) := Fin.ext h2033
    subst k
    rw [keyMomentRowsAt2033]
    exact keyMoment2033 B hB
  · have he : k = (2034 : Fin 2886) := Fin.ext h2034
    subst k
    rw [keyMomentRowsAt2034]
    exact keyMoment2034 B hB
  · have he : k = (2035 : Fin 2886) := Fin.ext h2035
    subst k
    rw [keyMomentRowsAt2035]
    exact keyMoment2035 B hB
  · have he : k = (2036 : Fin 2886) := Fin.ext h2036
    subst k
    rw [keyMomentRowsAt2036]
    exact keyMoment2036 B hB
  · have he : k = (2037 : Fin 2886) := Fin.ext h2037
    subst k
    rw [keyMomentRowsAt2037]
    exact keyMoment2037 B hB
  · have he : k = (2038 : Fin 2886) := Fin.ext h2038
    subst k
    rw [keyMomentRowsAt2038]
    exact keyMoment2038 B hB
  · have he : k = (2039 : Fin 2886) := Fin.ext h2039
    subst k
    rw [keyMomentRowsAt2039]
    exact keyMoment2039 B hB
  · have he : k = (2040 : Fin 2886) := Fin.ext h2040
    subst k
    rw [keyMomentRowsAt2040]
    exact keyMoment2040 B hB
  · have he : k = (2041 : Fin 2886) := Fin.ext h2041
    subst k
    rw [keyMomentRowsAt2041]
    exact keyMoment2041 B hB
  · have he : k = (2042 : Fin 2886) := Fin.ext h2042
    subst k
    rw [keyMomentRowsAt2042]
    exact keyMoment2042 B hB
  · have he : k = (2043 : Fin 2886) := Fin.ext h2043
    subst k
    rw [keyMomentRowsAt2043]
    exact keyMoment2043 B hB
  · have he : k = (2044 : Fin 2886) := Fin.ext h2044
    subst k
    rw [keyMomentRowsAt2044]
    exact keyMoment2044 B hB
  · have he : k = (2045 : Fin 2886) := Fin.ext h2045
    subst k
    rw [keyMomentRowsAt2045]
    exact keyMoment2045 B hB
  · have he : k = (2046 : Fin 2886) := Fin.ext h2046
    subst k
    rw [keyMomentRowsAt2046]
    exact keyMoment2046 B hB
  · have he : k = (2047 : Fin 2886) := Fin.ext h2047
    subst k
    rw [keyMomentRowsAt2047]
    exact keyMoment2047 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound63_e_oai
