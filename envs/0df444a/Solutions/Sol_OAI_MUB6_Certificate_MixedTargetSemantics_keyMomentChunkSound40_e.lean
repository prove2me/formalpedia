-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:55:04.681054+00:00
-- url     : https://prove2.me/submissions/dd66dfc3-4969-4277-979a-ab2bf1a5d2c9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E092
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical131
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical16795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16795 raw16795Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw16795 raw16795Labels = mixedMoment B raw16795step0 raw16795step0Labels := by
      have hz : ∀ j, raw16795 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16795step0 = (fun i j => raw16795 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16795step0 raw16795; decide +kernel
      have hl : raw16795step0Labels = raw16795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16795 raw16795Labels permutation520 hz
    mixedMoment B raw16795step0 raw16795step0Labels = mixedMoment B raw16795step1 raw16795step1Labels := by
      have ha : raw16795step1 = (fun i j => raw16795step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16795step1 raw16795step0; decide +kernel
      have hl : raw16795step1Labels = raw16795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16795step0 raw16795step0Labels permutation145 permutation3
    mixedMoment B raw16795step1 raw16795step1Labels = mixedMoment B raw16795step2 raw16795step2Labels := by
      have ha : raw16795step2 = -raw16795step1 := by apply Matrix.ext; change ∀ i j, raw16795step2 i j = -(raw16795step1 i j); unfold raw16795step2 raw16795step1; decide +kernel
      have hl : raw16795step2Labels = raw16795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2751 node2751Labels := by rfl

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

theorem canonical40705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40705 raw40705Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw40705 raw40705Labels = mixedMoment B raw40705step0 raw40705step0Labels := by
      have ha : raw40705step0 = (fun i j => raw40705 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40705step0 raw40705; decide +kernel
      have hl : raw40705step0Labels = raw40705Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40705 raw40705Labels permutation623 permutation6
    _ = mixedMoment B node2951 node2951Labels := by rfl

theorem canonical40706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40706 raw40706Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw40706 raw40706Labels = mixedMoment B raw40706step0 raw40706step0Labels := by
      have ha : raw40706step0 = (fun i j => raw40706 (permutation455 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40706step0 raw40706; decide +kernel
      have hl : raw40706step0Labels = raw40706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40706 raw40706Labels permutation455 permutation6
    mixedMoment B raw40706step0 raw40706step0Labels = mixedMoment B raw40706step1 raw40706step1Labels := by
      have ha : raw40706step1 = -raw40706step0 := by apply Matrix.ext; change ∀ i j, raw40706step1 i j = -(raw40706step0 i j); unfold raw40706step1 raw40706step0; decide +kernel
      have hl : raw40706step1Labels = raw40706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3827 node3827Labels := by rfl

theorem canonical40707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40707 raw40707Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw40707 raw40707Labels = mixedMoment B raw40707step0 raw40707step0Labels := by
      have ha : raw40707step0 = (fun i j => raw40707 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40707step0 raw40707; decide +kernel
      have hl : raw40707step0Labels = raw40707Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40707 raw40707Labels permutation641 permutation6
    _ = mixedMoment B node2933 node2933Labels := by rfl

theorem canonical40708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40708 raw40708Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw40708 raw40708Labels = mixedMoment B raw40708step0 raw40708step0Labels := by
      have hz : ∀ j, raw40708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40708step0 = (fun i j => raw40708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40708step0 raw40708; decide +kernel
      have hl : raw40708step0Labels = raw40708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40708 raw40708Labels permutation434 hz
    mixedMoment B raw40708step0 raw40708step0Labels = mixedMoment B raw40708step1 raw40708step1Labels := by
      have hz : ∀ j, raw40708step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40708step1 = (fun i j => raw40708step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40708step1 raw40708step0; decide +kernel
      have hl : raw40708step1Labels = raw40708step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40708step0 raw40708step0Labels permutation80 hz
    mixedMoment B raw40708step1 raw40708step1Labels = mixedMoment B raw40708step2 raw40708step2Labels := by
      have ha : raw40708step2 = (fun i j => raw40708step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40708step2 raw40708step1; decide +kernel
      have hl : raw40708step2Labels = raw40708step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40708step1 raw40708step1Labels permutation26 permutation6
    _ = mixedMoment B node1292 node1292Labels := by rfl

theorem canonical40709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40709 raw40709Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw40709 raw40709Labels = mixedMoment B raw40709step0 raw40709step0Labels := by
      have hz : ∀ j, raw40709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40709step0 = (fun i j => raw40709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40709step0 raw40709; decide +kernel
      have hl : raw40709step0Labels = raw40709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40709 raw40709Labels permutation346 hz
    mixedMoment B raw40709step0 raw40709step0Labels = mixedMoment B raw40709step1 raw40709step1Labels := by
      have ha : raw40709step1 = (fun i j => raw40709step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40709step1 raw40709step0; decide +kernel
      have hl : raw40709step1Labels = raw40709step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40709step0 raw40709step0Labels permutation122 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical40710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40710 raw40710Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw40710 raw40710Labels = mixedMoment B raw40710step0 raw40710step0Labels := by
      have hz : ∀ j, raw40710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40710step0 = (fun i j => raw40710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40710step0 raw40710; decide +kernel
      have hl : raw40710step0Labels = raw40710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40710 raw40710Labels permutation346 hz
    mixedMoment B raw40710step0 raw40710step0Labels = mixedMoment B raw40710step1 raw40710step1Labels := by
      have ha : raw40710step1 = (fun i j => raw40710step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40710step1 raw40710step0; decide +kernel
      have hl : raw40710step1Labels = raw40710step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40710step0 raw40710step0Labels permutation128 permutation6
    _ = mixedMoment B node1291 node1291Labels := by rfl

theorem canonical40711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40711 raw40711Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw40711 raw40711Labels = mixedMoment B raw40711step0 raw40711step0Labels := by
      have hz : ∀ j, raw40711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40711step0 = (fun i j => raw40711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40711step0 raw40711; decide +kernel
      have hl : raw40711step0Labels = raw40711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40711 raw40711Labels permutation346 hz
    mixedMoment B raw40711step0 raw40711step0Labels = mixedMoment B raw40711step1 raw40711step1Labels := by
      have ha : raw40711step1 = (fun i j => raw40711step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40711step1 raw40711step0; decide +kernel
      have hl : raw40711step1Labels = raw40711step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40711step0 raw40711step0Labels permutation122 permutation6
    _ = mixedMoment B node2632 node2632Labels := by rfl

theorem canonical40712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40712 raw40712Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw40712 raw40712Labels = mixedMoment B raw40712step0 raw40712step0Labels := by
      have hz : ∀ j, raw40712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40712step0 = (fun i j => raw40712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40712step0 raw40712; decide +kernel
      have hl : raw40712step0Labels = raw40712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40712 raw40712Labels permutation346 hz
    mixedMoment B raw40712step0 raw40712step0Labels = mixedMoment B raw40712step1 raw40712step1Labels := by
      have ha : raw40712step1 = (fun i j => raw40712step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40712step1 raw40712step0; decide +kernel
      have hl : raw40712step1Labels = raw40712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40712step0 raw40712step0Labels permutation146 permutation6
    _ = mixedMoment B node1261 node1261Labels := by rfl

theorem canonical40713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40713 raw40713Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw40713 raw40713Labels = mixedMoment B raw40713step0 raw40713step0Labels := by
      have ha : raw40713step0 = (fun i j => raw40713 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40713step0 raw40713; decide +kernel
      have hl : raw40713step0Labels = raw40713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40713 raw40713Labels permutation569 permutation6
    _ = mixedMoment B node2631 node2631Labels := by rfl

theorem canonical40714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40714 raw40714Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw40714 raw40714Labels = mixedMoment B raw40714step0 raw40714step0Labels := by
      have ha : raw40714step0 = (fun i j => raw40714 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40714step0 raw40714; decide +kernel
      have hl : raw40714step0Labels = raw40714Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40714 raw40714Labels permutation665 permutation6
    _ = mixedMoment B node1260 node1260Labels := by rfl

theorem canonical40715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40715 raw40715Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw40715 raw40715Labels = mixedMoment B raw40715step0 raw40715step0Labels := by
      have ha : raw40715step0 = (fun i j => raw40715 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40715step0 raw40715; decide +kernel
      have hl : raw40715step0Labels = raw40715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40715 raw40715Labels permutation484 permutation6
    _ = mixedMoment B node2587 node2587Labels := by rfl

theorem canonical40716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40716 raw40716Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw40716 raw40716Labels = mixedMoment B raw40716step0 raw40716step0Labels := by
      have ha : raw40716step0 = (fun i j => raw40716 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40716step0 raw40716; decide +kernel
      have hl : raw40716step0Labels = raw40716Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40716 raw40716Labels permutation499 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical40717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40717 raw40717Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw40717 raw40717Labels = mixedMoment B raw40717step0 raw40717step0Labels := by
      have ha : raw40717step0 = (fun i j => raw40717 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40717step0 raw40717; decide +kernel
      have hl : raw40717step0Labels = raw40717Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40717 raw40717Labels permutation499 permutation6
    _ = mixedMoment B node2566 node2566Labels := by rfl

theorem canonical40718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40718 raw40718Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw40718 raw40718Labels = mixedMoment B raw40718step0 raw40718step0Labels := by
      have hz : ∀ j, raw40718 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40718step0 = (fun i j => raw40718 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40718step0 raw40718; decide +kernel
      have hl : raw40718step0Labels = raw40718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40718 raw40718Labels permutation520 hz
    mixedMoment B raw40718step0 raw40718step0Labels = mixedMoment B raw40718step1 raw40718step1Labels := by
      have hz : ∀ j, raw40718step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40718step1 = (fun i j => raw40718step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40718step1 raw40718step0; decide +kernel
      have hl : raw40718step1Labels = raw40718step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40718step0 raw40718step0Labels permutation104 hz
    mixedMoment B raw40718step1 raw40718step1Labels = mixedMoment B raw40718step2 raw40718step2Labels := by
      have ha : raw40718step2 = (fun i j => raw40718step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40718step2 raw40718step1; decide +kernel
      have hl : raw40718step2Labels = raw40718step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40718step1 raw40718step1Labels permutation31 permutation3
    mixedMoment B raw40718step2 raw40718step2Labels = mixedMoment B raw40718step3 raw40718step3Labels := by
      have ha : raw40718step3 = -raw40718step2 := by apply Matrix.ext; change ∀ i j, raw40718step3 i j = -(raw40718step2 i j); unfold raw40718step3 raw40718step2; decide +kernel
      have hl : raw40718step3Labels = raw40718step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical40719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40719 raw40719Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw40719 raw40719Labels = mixedMoment B raw40719step0 raw40719step0Labels := by
      have hz : ∀ j, raw40719 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40719step0 = (fun i j => raw40719 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40719step0 raw40719; decide +kernel
      have hl : raw40719step0Labels = raw40719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40719 raw40719Labels permutation434 hz
    mixedMoment B raw40719step0 raw40719step0Labels = mixedMoment B raw40719step1 raw40719step1Labels := by
      have ha : raw40719step1 = (fun i j => raw40719step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40719step1 raw40719step0; decide +kernel
      have hl : raw40719step1Labels = raw40719step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40719step0 raw40719step0Labels permutation151 permutation3
    mixedMoment B raw40719step1 raw40719step1Labels = mixedMoment B raw40719step2 raw40719step2Labels := by
      have ha : raw40719step2 = -raw40719step1 := by apply Matrix.ext; change ∀ i j, raw40719step2 i j = -(raw40719step1 i j); unfold raw40719step2 raw40719step1; decide +kernel
      have hl : raw40719step2Labels = raw40719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3092 node3092Labels := by rfl

theorem canonical40720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40720 raw40720Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw40720 raw40720Labels = mixedMoment B raw40720step0 raw40720step0Labels := by
      have hz : ∀ j, raw40720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40720step0 = (fun i j => raw40720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40720step0 raw40720; decide +kernel
      have hl : raw40720step0Labels = raw40720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40720 raw40720Labels permutation434 hz
    mixedMoment B raw40720step0 raw40720step0Labels = mixedMoment B raw40720step1 raw40720step1Labels := by
      have ha : raw40720step1 = (fun i j => raw40720step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40720step1 raw40720step0; decide +kernel
      have hl : raw40720step1Labels = raw40720step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40720step0 raw40720step0Labels permutation151 permutation3
    mixedMoment B raw40720step1 raw40720step1Labels = mixedMoment B raw40720step2 raw40720step2Labels := by
      have ha : raw40720step2 = -raw40720step1 := by apply Matrix.ext; change ∀ i j, raw40720step2 i j = -(raw40720step1 i j); unfold raw40720step2 raw40720step1; decide +kernel
      have hl : raw40720step2Labels = raw40720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

theorem canonical40721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40721 raw40721Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw40721 raw40721Labels = mixedMoment B raw40721step0 raw40721step0Labels := by
      have hz : ∀ j, raw40721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40721step0 = (fun i j => raw40721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40721step0 raw40721; decide +kernel
      have hl : raw40721step0Labels = raw40721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40721 raw40721Labels permutation434 hz
    mixedMoment B raw40721step0 raw40721step0Labels = mixedMoment B raw40721step1 raw40721step1Labels := by
      have ha : raw40721step1 = (fun i j => raw40721step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40721step1 raw40721step0; decide +kernel
      have hl : raw40721step1Labels = raw40721step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40721step0 raw40721step0Labels permutation102 permutation6
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical40722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40722 raw40722Labels = mixedMoment B node3733 node3733Labels := by
  calc
    mixedMoment B raw40722 raw40722Labels = mixedMoment B raw40722step0 raw40722step0Labels := by
      have hz : ∀ j, raw40722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40722step0 = (fun i j => raw40722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40722step0 raw40722; decide +kernel
      have hl : raw40722step0Labels = raw40722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40722 raw40722Labels permutation434 hz
    mixedMoment B raw40722step0 raw40722step0Labels = mixedMoment B raw40722step1 raw40722step1Labels := by
      have ha : raw40722step1 = (fun i j => raw40722step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40722step1 raw40722step0; decide +kernel
      have hl : raw40722step1Labels = raw40722step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40722step0 raw40722step0Labels permutation99 permutation6
    _ = mixedMoment B node3733 node3733Labels := by rfl

theorem canonical40723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40723 raw40723Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw40723 raw40723Labels = mixedMoment B raw40723step0 raw40723step0Labels := by
      have ha : raw40723step0 = (fun i j => raw40723 (permutation410 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40723step0 raw40723; decide +kernel
      have hl : raw40723step0Labels = raw40723Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40723 raw40723Labels permutation410 permutation6
    _ = mixedMoment B node3827 node3827Labels := by rfl

theorem canonical40724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40724 raw40724Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw40724 raw40724Labels = mixedMoment B raw40724step0 raw40724step0Labels := by
      have ha : raw40724step0 = (fun i j => raw40724 (permutation429 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40724step0 raw40724; decide +kernel
      have hl : raw40724step0Labels = raw40724Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40724 raw40724Labels permutation429 permutation6
    _ = mixedMoment B node3724 node3724Labels := by rfl

theorem canonical40725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40725 raw40725Labels = mixedMoment B node3819 node3819Labels := by
  calc
    mixedMoment B raw40725 raw40725Labels = mixedMoment B raw40725step0 raw40725step0Labels := by
      have ha : raw40725step0 = (fun i j => raw40725 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40725step0 raw40725; decide +kernel
      have hl : raw40725step0Labels = raw40725Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40725 raw40725Labels permutation390 permutation6
    _ = mixedMoment B node3819 node3819Labels := by rfl

theorem canonical40726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40726 raw40726Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw40726 raw40726Labels = mixedMoment B raw40726step0 raw40726step0Labels := by
      have ha : raw40726step0 = (fun i j => raw40726 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40726step0 raw40726; decide +kernel
      have hl : raw40726step0Labels = raw40726Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40726 raw40726Labels permutation393 permutation6
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical40727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40727 raw40727Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw40727 raw40727Labels = mixedMoment B raw40727step0 raw40727step0Labels := by
      have ha : raw40727step0 = (fun i j => raw40727 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40727step0 raw40727; decide +kernel
      have hl : raw40727step0Labels = raw40727Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40727 raw40727Labels permutation322 permutation6
    mixedMoment B raw40727step0 raw40727step0Labels = mixedMoment B raw40727step1 raw40727step1Labels := by
      have ha : raw40727step1 = -raw40727step0 := by apply Matrix.ext; change ∀ i j, raw40727step1 i j = -(raw40727step0 i j); unfold raw40727step1 raw40727step0; decide +kernel
      have hl : raw40727step1Labels = raw40727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

theorem canonical40728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40728 raw40728Labels = mixedMoment B node2955 node2955Labels := by
  calc
    mixedMoment B raw40728 raw40728Labels = mixedMoment B raw40728step0 raw40728step0Labels := by
      have hz : ∀ j, raw40728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40728step0 = (fun i j => raw40728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40728step0 raw40728; decide +kernel
      have hl : raw40728step0Labels = raw40728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40728 raw40728Labels permutation434 hz
    mixedMoment B raw40728step0 raw40728step0Labels = mixedMoment B raw40728step1 raw40728step1Labels := by
      have ha : raw40728step1 = (fun i j => raw40728step0 (permutation141 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40728step1 raw40728step0; decide +kernel
      have hl : raw40728step1Labels = raw40728step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40728step0 raw40728step0Labels permutation141 permutation6
    _ = mixedMoment B node2955 node2955Labels := by rfl

theorem canonical40729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40729 raw40729Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw40729 raw40729Labels = mixedMoment B raw40729step0 raw40729step0Labels := by
      have hz : ∀ j, raw40729 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40729step0 = (fun i j => raw40729 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40729step0 raw40729; decide +kernel
      have hl : raw40729step0Labels = raw40729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40729 raw40729Labels permutation434 hz
    mixedMoment B raw40729step0 raw40729step0Labels = mixedMoment B raw40729step1 raw40729step1Labels := by
      have hz : ∀ j, raw40729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40729step1 = (fun i j => raw40729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40729step1 raw40729step0; decide +kernel
      have hl : raw40729step1Labels = raw40729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40729step0 raw40729step0Labels permutation80 hz
    mixedMoment B raw40729step1 raw40729step1Labels = mixedMoment B raw40729step2 raw40729step2Labels := by
      have ha : raw40729step2 = (fun i j => raw40729step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40729step2 raw40729step1; decide +kernel
      have hl : raw40729step2Labels = raw40729step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40729step1 raw40729step1Labels permutation24 permutation6
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical40730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40730 raw40730Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw40730 raw40730Labels = mixedMoment B raw40730step0 raw40730step0Labels := by
      have hz : ∀ j, raw40730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40730step0 = (fun i j => raw40730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40730step0 raw40730; decide +kernel
      have hl : raw40730step0Labels = raw40730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40730 raw40730Labels permutation434 hz
    mixedMoment B raw40730step0 raw40730step0Labels = mixedMoment B raw40730step1 raw40730step1Labels := by
      have hz : ∀ j, raw40730step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40730step1 = (fun i j => raw40730step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40730step1 raw40730step0; decide +kernel
      have hl : raw40730step1Labels = raw40730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40730step0 raw40730step0Labels permutation80 hz
    mixedMoment B raw40730step1 raw40730step1Labels = mixedMoment B raw40730step2 raw40730step2Labels := by
      have ha : raw40730step2 = (fun i j => raw40730step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40730step2 raw40730step1; decide +kernel
      have hl : raw40730step2Labels = raw40730step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40730step1 raw40730step1Labels permutation27 permutation6
    _ = mixedMoment B node1295 node1295Labels := by rfl

theorem canonical40731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40731 raw40731Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw40731 raw40731Labels = mixedMoment B raw40731step0 raw40731step0Labels := by
      have hz : ∀ j, raw40731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40731step0 = (fun i j => raw40731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40731step0 raw40731; decide +kernel
      have hl : raw40731step0Labels = raw40731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40731 raw40731Labels permutation346 hz
    mixedMoment B raw40731step0 raw40731step0Labels = mixedMoment B raw40731step1 raw40731step1Labels := by
      have ha : raw40731step1 = (fun i j => raw40731step0 (permutation123 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40731step1 raw40731step0; decide +kernel
      have hl : raw40731step1Labels = raw40731step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40731step0 raw40731step0Labels permutation123 permutation6
    _ = mixedMoment B node2633 node2633Labels := by rfl

theorem canonical40732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40732 raw40732Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw40732 raw40732Labels = mixedMoment B raw40732step0 raw40732step0Labels := by
      have hz : ∀ j, raw40732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40732step0 = (fun i j => raw40732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40732step0 raw40732; decide +kernel
      have hl : raw40732step0Labels = raw40732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40732 raw40732Labels permutation346 hz
    mixedMoment B raw40732step0 raw40732step0Labels = mixedMoment B raw40732step1 raw40732step1Labels := by
      have ha : raw40732step1 = (fun i j => raw40732step0 (permutation147 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40732step1 raw40732step0; decide +kernel
      have hl : raw40732step1Labels = raw40732step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40732step0 raw40732step0Labels permutation147 permutation6
    _ = mixedMoment B node1262 node1262Labels := by rfl

theorem canonical40733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40733 raw40733Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw40733 raw40733Labels = mixedMoment B raw40733step0 raw40733step0Labels := by
      have hz : ∀ j, raw40733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40733step0 = (fun i j => raw40733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40733step0 raw40733; decide +kernel
      have hl : raw40733step0Labels = raw40733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40733 raw40733Labels permutation346 hz
    mixedMoment B raw40733step0 raw40733step0Labels = mixedMoment B raw40733step1 raw40733step1Labels := by
      have ha : raw40733step1 = (fun i j => raw40733step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40733step1 raw40733step0; decide +kernel
      have hl : raw40733step1Labels = raw40733step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40733step0 raw40733step0Labels permutation93 permutation6
    _ = mixedMoment B node2591 node2591Labels := by rfl

theorem canonical40734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40734 raw40734Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw40734 raw40734Labels = mixedMoment B raw40734step0 raw40734step0Labels := by
      have hz : ∀ j, raw40734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40734step0 = (fun i j => raw40734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40734step0 raw40734; decide +kernel
      have hl : raw40734step0Labels = raw40734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40734 raw40734Labels permutation346 hz
    mixedMoment B raw40734step0 raw40734step0Labels = mixedMoment B raw40734step1 raw40734step1Labels := by
      have ha : raw40734step1 = (fun i j => raw40734step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40734step1 raw40734step0; decide +kernel
      have hl : raw40734step1Labels = raw40734step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40734step0 raw40734step0Labels permutation96 permutation6
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical40735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40735 raw40735Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw40735 raw40735Labels = mixedMoment B raw40735step0 raw40735step0Labels := by
      have hz : ∀ j, raw40735 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40735step0 = (fun i j => raw40735 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40735step0 raw40735; decide +kernel
      have hl : raw40735step0Labels = raw40735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40735 raw40735Labels permutation520 hz
    mixedMoment B raw40735step0 raw40735step0Labels = mixedMoment B raw40735step1 raw40735step1Labels := by
      have hz : ∀ j, raw40735step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40735step1 = (fun i j => raw40735step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40735step1 raw40735step0; decide +kernel
      have hl : raw40735step1Labels = raw40735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40735step0 raw40735step0Labels permutation104 hz
    mixedMoment B raw40735step1 raw40735step1Labels = mixedMoment B raw40735step2 raw40735step2Labels := by
      have ha : raw40735step2 = (fun i j => raw40735step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40735step2 raw40735step1; decide +kernel
      have hl : raw40735step2Labels = raw40735step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40735step1 raw40735step1Labels permutation15 permutation6
    mixedMoment B raw40735step2 raw40735step2Labels = mixedMoment B raw40735step3 raw40735step3Labels := by
      have ha : raw40735step3 = -raw40735step2 := by apply Matrix.ext; change ∀ i j, raw40735step3 i j = -(raw40735step2 i j); unfold raw40735step3 raw40735step2; decide +kernel
      have hl : raw40735step3Labels = raw40735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2643 node2643Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1280) =
      Integer.Sparse.eval keyMomentRow1280 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1280).leftCharge (GramAssembly.key 1280).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2951) := by
    have ha : gramCharges (GramAssembly.key 1280).leftCharge (GramAssembly.key 1280).rightCharge = raw40705 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40705Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40705 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1280).leftCharge (GramAssembly.key 1280).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1280, Integer.Sparse.eval]

theorem keyMoment1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1281) =
      Integer.Sparse.eval keyMomentRow1281 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1281).leftCharge (GramAssembly.key 1281).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3827) := by
    have ha : gramCharges (GramAssembly.key 1281).leftCharge (GramAssembly.key 1281).rightCharge = raw40706 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40706Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40706 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1281).leftCharge (GramAssembly.key 1281).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1281, Integer.Sparse.eval]

theorem keyMoment1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1282) =
      Integer.Sparse.eval keyMomentRow1282 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1282).leftCharge (GramAssembly.key 1282).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2933) := by
    have ha : gramCharges (GramAssembly.key 1282).leftCharge (GramAssembly.key 1282).rightCharge = raw40707 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40707Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40707 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1282).leftCharge (GramAssembly.key 1282).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1282, Integer.Sparse.eval]

theorem keyMoment1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1283) =
      Integer.Sparse.eval keyMomentRow1283 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1283).leftCharge (GramAssembly.key 1283).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1292) := by
    have ha : gramCharges (GramAssembly.key 1283).leftCharge (GramAssembly.key 1283).rightCharge = raw40708 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40708Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40708 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1283).leftCharge (GramAssembly.key 1283).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1283, Integer.Sparse.eval]

theorem keyMoment1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1284) =
      Integer.Sparse.eval keyMomentRow1284 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1284).leftCharge (GramAssembly.key 1284).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 1284).leftCharge (GramAssembly.key 1284).rightCharge = raw40709 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40709Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40709 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1284).leftCharge (GramAssembly.key 1284).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1284, Integer.Sparse.eval]

theorem keyMoment1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1285) =
      Integer.Sparse.eval keyMomentRow1285 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1285).leftCharge (GramAssembly.key 1285).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1291) := by
    have ha : gramCharges (GramAssembly.key 1285).leftCharge (GramAssembly.key 1285).rightCharge = raw40710 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40710Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40710 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1285).leftCharge (GramAssembly.key 1285).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1285, Integer.Sparse.eval]

theorem keyMoment1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1286) =
      Integer.Sparse.eval keyMomentRow1286 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1286).leftCharge (GramAssembly.key 1286).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2632) := by
    have ha : gramCharges (GramAssembly.key 1286).leftCharge (GramAssembly.key 1286).rightCharge = raw40711 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40711Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40711 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1286).leftCharge (GramAssembly.key 1286).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1286, Integer.Sparse.eval]

theorem keyMoment1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1287) =
      Integer.Sparse.eval keyMomentRow1287 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1287).leftCharge (GramAssembly.key 1287).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1261) := by
    have ha : gramCharges (GramAssembly.key 1287).leftCharge (GramAssembly.key 1287).rightCharge = raw40712 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40712Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40712 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1287).leftCharge (GramAssembly.key 1287).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1287, Integer.Sparse.eval]

theorem keyMoment1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1288) =
      Integer.Sparse.eval keyMomentRow1288 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1288).leftCharge (GramAssembly.key 1288).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2631) := by
    have ha : gramCharges (GramAssembly.key 1288).leftCharge (GramAssembly.key 1288).rightCharge = raw40713 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40713Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40713 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1288).leftCharge (GramAssembly.key 1288).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1288, Integer.Sparse.eval]

theorem keyMoment1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1289) =
      Integer.Sparse.eval keyMomentRow1289 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1289).leftCharge (GramAssembly.key 1289).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1260) := by
    have ha : gramCharges (GramAssembly.key 1289).leftCharge (GramAssembly.key 1289).rightCharge = raw40714 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40714Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40714 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1289).leftCharge (GramAssembly.key 1289).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1289, Integer.Sparse.eval]

theorem keyMoment1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1290) =
      Integer.Sparse.eval keyMomentRow1290 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1290).leftCharge (GramAssembly.key 1290).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2587) := by
    have ha : gramCharges (GramAssembly.key 1290).leftCharge (GramAssembly.key 1290).rightCharge = raw40715 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40715Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40715 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1290).leftCharge (GramAssembly.key 1290).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1290, Integer.Sparse.eval]

theorem keyMoment1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1291) =
      Integer.Sparse.eval keyMomentRow1291 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1291).leftCharge (GramAssembly.key 1291).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 1291).leftCharge (GramAssembly.key 1291).rightCharge = raw40716 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40716Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40716 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1291).leftCharge (GramAssembly.key 1291).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1291, Integer.Sparse.eval]

theorem keyMoment1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1292) =
      Integer.Sparse.eval keyMomentRow1292 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1292).leftCharge (GramAssembly.key 1292).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2566) := by
    have ha : gramCharges (GramAssembly.key 1292).leftCharge (GramAssembly.key 1292).rightCharge = raw40717 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40717Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40717 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1292).leftCharge (GramAssembly.key 1292).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1292, Integer.Sparse.eval]

theorem keyMoment1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1293) =
      Integer.Sparse.eval keyMomentRow1293 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1293).leftCharge (GramAssembly.key 1293).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 1293).leftCharge (GramAssembly.key 1293).rightCharge = raw40718 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40718Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40718 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1293).leftCharge (GramAssembly.key 1293).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1293, Integer.Sparse.eval]

theorem keyMoment1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1294) =
      Integer.Sparse.eval keyMomentRow1294 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1294).leftCharge (GramAssembly.key 1294).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3092) := by
    have ha : gramCharges (GramAssembly.key 1294).leftCharge (GramAssembly.key 1294).rightCharge = raw40719 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40719Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40719 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1294).leftCharge (GramAssembly.key 1294).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1294, Integer.Sparse.eval]

theorem keyMoment1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1295) =
      Integer.Sparse.eval keyMomentRow1295 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1295).leftCharge (GramAssembly.key 1295).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3854) := by
    have ha : gramCharges (GramAssembly.key 1295).leftCharge (GramAssembly.key 1295).rightCharge = raw40720 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40720Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40720 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1295).leftCharge (GramAssembly.key 1295).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1295, Integer.Sparse.eval]

theorem keyMoment1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1296) =
      Integer.Sparse.eval keyMomentRow1296 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1296).leftCharge (GramAssembly.key 1296).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 1296).leftCharge (GramAssembly.key 1296).rightCharge = raw40721 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40721Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40721 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1296).leftCharge (GramAssembly.key 1296).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1296, Integer.Sparse.eval]

theorem keyMoment1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1297) =
      Integer.Sparse.eval keyMomentRow1297 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1297).leftCharge (GramAssembly.key 1297).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3733) := by
    have ha : gramCharges (GramAssembly.key 1297).leftCharge (GramAssembly.key 1297).rightCharge = raw40722 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40722Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40722 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1297).leftCharge (GramAssembly.key 1297).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1297, Integer.Sparse.eval]

theorem keyMoment1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1298) =
      Integer.Sparse.eval keyMomentRow1298 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1298).leftCharge (GramAssembly.key 1298).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3827) := by
    have ha : gramCharges (GramAssembly.key 1298).leftCharge (GramAssembly.key 1298).rightCharge = raw40723 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40723Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40723 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1298).leftCharge (GramAssembly.key 1298).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1298, Integer.Sparse.eval]

theorem keyMoment1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1299) =
      Integer.Sparse.eval keyMomentRow1299 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1299).leftCharge (GramAssembly.key 1299).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3724) := by
    have ha : gramCharges (GramAssembly.key 1299).leftCharge (GramAssembly.key 1299).rightCharge = raw40724 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40724Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40724 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1299).leftCharge (GramAssembly.key 1299).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1299, Integer.Sparse.eval]

theorem keyMoment1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1300) =
      Integer.Sparse.eval keyMomentRow1300 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1300).leftCharge (GramAssembly.key 1300).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3819) := by
    have ha : gramCharges (GramAssembly.key 1300).leftCharge (GramAssembly.key 1300).rightCharge = raw40725 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40725Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40725 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1300).leftCharge (GramAssembly.key 1300).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1300, Integer.Sparse.eval]

theorem keyMoment1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1301) =
      Integer.Sparse.eval keyMomentRow1301 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1301).leftCharge (GramAssembly.key 1301).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 1301).leftCharge (GramAssembly.key 1301).rightCharge = raw40726 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40726Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40726 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1301).leftCharge (GramAssembly.key 1301).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1301, Integer.Sparse.eval]

theorem keyMoment1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1302) =
      Integer.Sparse.eval keyMomentRow1302 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1302).leftCharge (GramAssembly.key 1302).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 1302).leftCharge (GramAssembly.key 1302).rightCharge = raw16795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw16795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical16795 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1302).leftCharge (GramAssembly.key 1302).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1302, Integer.Sparse.eval]

theorem keyMoment1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1303) =
      Integer.Sparse.eval keyMomentRow1303 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1303).leftCharge (GramAssembly.key 1303).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3949) := by
    have ha : gramCharges (GramAssembly.key 1303).leftCharge (GramAssembly.key 1303).rightCharge = raw40727 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40727Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40727 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1303).leftCharge (GramAssembly.key 1303).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1303, Integer.Sparse.eval]

theorem keyMoment1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1304) =
      Integer.Sparse.eval keyMomentRow1304 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1304).leftCharge (GramAssembly.key 1304).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2955) := by
    have ha : gramCharges (GramAssembly.key 1304).leftCharge (GramAssembly.key 1304).rightCharge = raw40728 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40728Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40728 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1304).leftCharge (GramAssembly.key 1304).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1304, Integer.Sparse.eval]

theorem keyMoment1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1305) =
      Integer.Sparse.eval keyMomentRow1305 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1305).leftCharge (GramAssembly.key 1305).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 1305).leftCharge (GramAssembly.key 1305).rightCharge = raw40729 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40729Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40729 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1305).leftCharge (GramAssembly.key 1305).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1305, Integer.Sparse.eval]

theorem keyMoment1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1306) =
      Integer.Sparse.eval keyMomentRow1306 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1306).leftCharge (GramAssembly.key 1306).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1295) := by
    have ha : gramCharges (GramAssembly.key 1306).leftCharge (GramAssembly.key 1306).rightCharge = raw40730 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40730Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40730 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1306).leftCharge (GramAssembly.key 1306).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1306, Integer.Sparse.eval]

theorem keyMoment1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1307) =
      Integer.Sparse.eval keyMomentRow1307 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1307).leftCharge (GramAssembly.key 1307).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2633) := by
    have ha : gramCharges (GramAssembly.key 1307).leftCharge (GramAssembly.key 1307).rightCharge = raw40731 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40731Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40731 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1307).leftCharge (GramAssembly.key 1307).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1307, Integer.Sparse.eval]

theorem keyMoment1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1308) =
      Integer.Sparse.eval keyMomentRow1308 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1308).leftCharge (GramAssembly.key 1308).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1262) := by
    have ha : gramCharges (GramAssembly.key 1308).leftCharge (GramAssembly.key 1308).rightCharge = raw40732 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40732Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40732 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1308).leftCharge (GramAssembly.key 1308).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1308, Integer.Sparse.eval]

theorem keyMoment1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1309) =
      Integer.Sparse.eval keyMomentRow1309 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1309).leftCharge (GramAssembly.key 1309).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2591) := by
    have ha : gramCharges (GramAssembly.key 1309).leftCharge (GramAssembly.key 1309).rightCharge = raw40733 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40733Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40733 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1309).leftCharge (GramAssembly.key 1309).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1309, Integer.Sparse.eval]

theorem keyMoment1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1310) =
      Integer.Sparse.eval keyMomentRow1310 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1310).leftCharge (GramAssembly.key 1310).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 1310).leftCharge (GramAssembly.key 1310).rightCharge = raw40734 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40734Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40734 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1310).leftCharge (GramAssembly.key 1310).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1310, Integer.Sparse.eval]

theorem keyMoment1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1311) =
      Integer.Sparse.eval keyMomentRow1311 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1311).leftCharge (GramAssembly.key 1311).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2643) := by
    have ha : gramCharges (GramAssembly.key 1311).leftCharge (GramAssembly.key 1311).rightCharge = raw40735 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw40735Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40735 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1311).leftCharge (GramAssembly.key 1311).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1311, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1280 : keyMomentRows (1280 : Fin 2886) =
    keyMomentRow1280 := by decide +kernel

theorem keyMomentRowsAt1281 : keyMomentRows (1281 : Fin 2886) =
    keyMomentRow1281 := by decide +kernel

theorem keyMomentRowsAt1282 : keyMomentRows (1282 : Fin 2886) =
    keyMomentRow1282 := by decide +kernel

theorem keyMomentRowsAt1283 : keyMomentRows (1283 : Fin 2886) =
    keyMomentRow1283 := by decide +kernel

theorem keyMomentRowsAt1284 : keyMomentRows (1284 : Fin 2886) =
    keyMomentRow1284 := by decide +kernel

theorem keyMomentRowsAt1285 : keyMomentRows (1285 : Fin 2886) =
    keyMomentRow1285 := by decide +kernel

theorem keyMomentRowsAt1286 : keyMomentRows (1286 : Fin 2886) =
    keyMomentRow1286 := by decide +kernel

theorem keyMomentRowsAt1287 : keyMomentRows (1287 : Fin 2886) =
    keyMomentRow1287 := by decide +kernel

theorem keyMomentRowsAt1288 : keyMomentRows (1288 : Fin 2886) =
    keyMomentRow1288 := by decide +kernel

theorem keyMomentRowsAt1289 : keyMomentRows (1289 : Fin 2886) =
    keyMomentRow1289 := by decide +kernel

theorem keyMomentRowsAt1290 : keyMomentRows (1290 : Fin 2886) =
    keyMomentRow1290 := by decide +kernel

theorem keyMomentRowsAt1291 : keyMomentRows (1291 : Fin 2886) =
    keyMomentRow1291 := by decide +kernel

theorem keyMomentRowsAt1292 : keyMomentRows (1292 : Fin 2886) =
    keyMomentRow1292 := by decide +kernel

theorem keyMomentRowsAt1293 : keyMomentRows (1293 : Fin 2886) =
    keyMomentRow1293 := by decide +kernel

theorem keyMomentRowsAt1294 : keyMomentRows (1294 : Fin 2886) =
    keyMomentRow1294 := by decide +kernel

theorem keyMomentRowsAt1295 : keyMomentRows (1295 : Fin 2886) =
    keyMomentRow1295 := by decide +kernel

theorem keyMomentRowsAt1296 : keyMomentRows (1296 : Fin 2886) =
    keyMomentRow1296 := by decide +kernel

theorem keyMomentRowsAt1297 : keyMomentRows (1297 : Fin 2886) =
    keyMomentRow1297 := by decide +kernel

theorem keyMomentRowsAt1298 : keyMomentRows (1298 : Fin 2886) =
    keyMomentRow1298 := by decide +kernel

theorem keyMomentRowsAt1299 : keyMomentRows (1299 : Fin 2886) =
    keyMomentRow1299 := by decide +kernel

theorem keyMomentRowsAt1300 : keyMomentRows (1300 : Fin 2886) =
    keyMomentRow1300 := by decide +kernel

theorem keyMomentRowsAt1301 : keyMomentRows (1301 : Fin 2886) =
    keyMomentRow1301 := by decide +kernel

theorem keyMomentRowsAt1302 : keyMomentRows (1302 : Fin 2886) =
    keyMomentRow1302 := by decide +kernel

theorem keyMomentRowsAt1303 : keyMomentRows (1303 : Fin 2886) =
    keyMomentRow1303 := by decide +kernel

theorem keyMomentRowsAt1304 : keyMomentRows (1304 : Fin 2886) =
    keyMomentRow1304 := by decide +kernel

theorem keyMomentRowsAt1305 : keyMomentRows (1305 : Fin 2886) =
    keyMomentRow1305 := by decide +kernel

theorem keyMomentRowsAt1306 : keyMomentRows (1306 : Fin 2886) =
    keyMomentRow1306 := by decide +kernel

theorem keyMomentRowsAt1307 : keyMomentRows (1307 : Fin 2886) =
    keyMomentRow1307 := by decide +kernel

theorem keyMomentRowsAt1308 : keyMomentRows (1308 : Fin 2886) =
    keyMomentRow1308 := by decide +kernel

theorem keyMomentRowsAt1309 : keyMomentRows (1309 : Fin 2886) =
    keyMomentRow1309 := by decide +kernel

theorem keyMomentRowsAt1310 : keyMomentRows (1310 : Fin 2886) =
    keyMomentRow1310 := by decide +kernel

theorem keyMomentRowsAt1311 : keyMomentRows (1311 : Fin 2886) =
    keyMomentRow1311 := by decide +kernel

theorem keyMomentChunkSound40_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 40) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1280 ∨ k.val = 1281 ∨ k.val = 1282 ∨ k.val = 1283 ∨ k.val = 1284 ∨ k.val = 1285 ∨ k.val = 1286 ∨ k.val = 1287 ∨ k.val = 1288 ∨ k.val = 1289 ∨ k.val = 1290 ∨ k.val = 1291 ∨ k.val = 1292 ∨ k.val = 1293 ∨ k.val = 1294 ∨ k.val = 1295 ∨ k.val = 1296 ∨ k.val = 1297 ∨ k.val = 1298 ∨ k.val = 1299 ∨ k.val = 1300 ∨ k.val = 1301 ∨ k.val = 1302 ∨ k.val = 1303 ∨ k.val = 1304 ∨ k.val = 1305 ∨ k.val = 1306 ∨ k.val = 1307 ∨ k.val = 1308 ∨ k.val = 1309 ∨ k.val = 1310 ∨ k.val = 1311 := by omega
  rcases heq with h1280 | h1281 | h1282 | h1283 | h1284 | h1285 | h1286 | h1287 | h1288 | h1289 | h1290 | h1291 | h1292 | h1293 | h1294 | h1295 | h1296 | h1297 | h1298 | h1299 | h1300 | h1301 | h1302 | h1303 | h1304 | h1305 | h1306 | h1307 | h1308 | h1309 | h1310 | h1311
  · have he : k = (1280 : Fin 2886) := Fin.ext h1280
    subst k
    rw [keyMomentRowsAt1280]
    exact keyMoment1280 B hB
  · have he : k = (1281 : Fin 2886) := Fin.ext h1281
    subst k
    rw [keyMomentRowsAt1281]
    exact keyMoment1281 B hB
  · have he : k = (1282 : Fin 2886) := Fin.ext h1282
    subst k
    rw [keyMomentRowsAt1282]
    exact keyMoment1282 B hB
  · have he : k = (1283 : Fin 2886) := Fin.ext h1283
    subst k
    rw [keyMomentRowsAt1283]
    exact keyMoment1283 B hB
  · have he : k = (1284 : Fin 2886) := Fin.ext h1284
    subst k
    rw [keyMomentRowsAt1284]
    exact keyMoment1284 B hB
  · have he : k = (1285 : Fin 2886) := Fin.ext h1285
    subst k
    rw [keyMomentRowsAt1285]
    exact keyMoment1285 B hB
  · have he : k = (1286 : Fin 2886) := Fin.ext h1286
    subst k
    rw [keyMomentRowsAt1286]
    exact keyMoment1286 B hB
  · have he : k = (1287 : Fin 2886) := Fin.ext h1287
    subst k
    rw [keyMomentRowsAt1287]
    exact keyMoment1287 B hB
  · have he : k = (1288 : Fin 2886) := Fin.ext h1288
    subst k
    rw [keyMomentRowsAt1288]
    exact keyMoment1288 B hB
  · have he : k = (1289 : Fin 2886) := Fin.ext h1289
    subst k
    rw [keyMomentRowsAt1289]
    exact keyMoment1289 B hB
  · have he : k = (1290 : Fin 2886) := Fin.ext h1290
    subst k
    rw [keyMomentRowsAt1290]
    exact keyMoment1290 B hB
  · have he : k = (1291 : Fin 2886) := Fin.ext h1291
    subst k
    rw [keyMomentRowsAt1291]
    exact keyMoment1291 B hB
  · have he : k = (1292 : Fin 2886) := Fin.ext h1292
    subst k
    rw [keyMomentRowsAt1292]
    exact keyMoment1292 B hB
  · have he : k = (1293 : Fin 2886) := Fin.ext h1293
    subst k
    rw [keyMomentRowsAt1293]
    exact keyMoment1293 B hB
  · have he : k = (1294 : Fin 2886) := Fin.ext h1294
    subst k
    rw [keyMomentRowsAt1294]
    exact keyMoment1294 B hB
  · have he : k = (1295 : Fin 2886) := Fin.ext h1295
    subst k
    rw [keyMomentRowsAt1295]
    exact keyMoment1295 B hB
  · have he : k = (1296 : Fin 2886) := Fin.ext h1296
    subst k
    rw [keyMomentRowsAt1296]
    exact keyMoment1296 B hB
  · have he : k = (1297 : Fin 2886) := Fin.ext h1297
    subst k
    rw [keyMomentRowsAt1297]
    exact keyMoment1297 B hB
  · have he : k = (1298 : Fin 2886) := Fin.ext h1298
    subst k
    rw [keyMomentRowsAt1298]
    exact keyMoment1298 B hB
  · have he : k = (1299 : Fin 2886) := Fin.ext h1299
    subst k
    rw [keyMomentRowsAt1299]
    exact keyMoment1299 B hB
  · have he : k = (1300 : Fin 2886) := Fin.ext h1300
    subst k
    rw [keyMomentRowsAt1300]
    exact keyMoment1300 B hB
  · have he : k = (1301 : Fin 2886) := Fin.ext h1301
    subst k
    rw [keyMomentRowsAt1301]
    exact keyMoment1301 B hB
  · have he : k = (1302 : Fin 2886) := Fin.ext h1302
    subst k
    rw [keyMomentRowsAt1302]
    exact keyMoment1302 B hB
  · have he : k = (1303 : Fin 2886) := Fin.ext h1303
    subst k
    rw [keyMomentRowsAt1303]
    exact keyMoment1303 B hB
  · have he : k = (1304 : Fin 2886) := Fin.ext h1304
    subst k
    rw [keyMomentRowsAt1304]
    exact keyMoment1304 B hB
  · have he : k = (1305 : Fin 2886) := Fin.ext h1305
    subst k
    rw [keyMomentRowsAt1305]
    exact keyMoment1305 B hB
  · have he : k = (1306 : Fin 2886) := Fin.ext h1306
    subst k
    rw [keyMomentRowsAt1306]
    exact keyMoment1306 B hB
  · have he : k = (1307 : Fin 2886) := Fin.ext h1307
    subst k
    rw [keyMomentRowsAt1307]
    exact keyMoment1307 B hB
  · have he : k = (1308 : Fin 2886) := Fin.ext h1308
    subst k
    rw [keyMomentRowsAt1308]
    exact keyMoment1308 B hB
  · have he : k = (1309 : Fin 2886) := Fin.ext h1309
    subst k
    rw [keyMomentRowsAt1309]
    exact keyMoment1309 B hB
  · have he : k = (1310 : Fin 2886) := Fin.ext h1310
    subst k
    rw [keyMomentRowsAt1310]
    exact keyMoment1310 B hB
  · have he : k = (1311 : Fin 2886) := Fin.ext h1311
    subst k
    rw [keyMomentRowsAt1311]
    exact keyMoment1311 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound40_e_oai
