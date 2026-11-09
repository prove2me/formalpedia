-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:58:05.348046+00:00
-- url     : https://prove2.me/submissions/093a915d-35d9-450c-81a3-575dc96e8e44

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E112
import Definitions.Def_OAIQ106E115
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical320
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41078 raw41078Labels = mixedMoment B node1964 node1964Labels := by
  calc
    mixedMoment B raw41078 raw41078Labels = mixedMoment B raw41078step0 raw41078step0Labels := by
      have ha : raw41078step0 = (fun i j => raw41078 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41078step0 raw41078; decide +kernel
      have hl : raw41078step0Labels = raw41078Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41078 raw41078Labels permutation332 permutation6
    _ = mixedMoment B node1964 node1964Labels := by rfl

theorem canonical41079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41079 raw41079Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw41079 raw41079Labels = mixedMoment B raw41079step0 raw41079step0Labels := by
      have hz : ∀ j, raw41079 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41079step0 = (fun i j => raw41079 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41079step0 raw41079; decide +kernel
      have hl : raw41079step0Labels = raw41079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41079 raw41079Labels permutation520 hz
    mixedMoment B raw41079step0 raw41079step0Labels = mixedMoment B raw41079step1 raw41079step1Labels := by
      have hz : ∀ j, raw41079step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41079step1 = (fun i j => raw41079step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41079step1 raw41079step0; decide +kernel
      have hl : raw41079step1Labels = raw41079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41079step0 raw41079step0Labels permutation104 hz
    mixedMoment B raw41079step1 raw41079step1Labels = mixedMoment B raw41079step2 raw41079step2Labels := by
      have ha : raw41079step2 = (fun i j => raw41079step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41079step2 raw41079step1; decide +kernel
      have hl : raw41079step2Labels = raw41079step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41079step1 raw41079step1Labels permutation13 permutation6
    mixedMoment B raw41079step2 raw41079step2Labels = mixedMoment B raw41079step3 raw41079step3Labels := by
      have ha : raw41079step3 = -raw41079step2 := by apply Matrix.ext; change ∀ i j, raw41079step3 i j = -(raw41079step2 i j); unfold raw41079step3 raw41079step2; decide +kernel
      have hl : raw41079step3Labels = raw41079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

theorem canonical41080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41080 raw41080Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw41080 raw41080Labels = mixedMoment B raw41080step0 raw41080step0Labels := by
      have hz : ∀ j, raw41080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41080step0 = (fun i j => raw41080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41080step0 raw41080; decide +kernel
      have hl : raw41080step0Labels = raw41080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41080 raw41080Labels permutation434 hz
    mixedMoment B raw41080step0 raw41080step0Labels = mixedMoment B raw41080step1 raw41080step1Labels := by
      have ha : raw41080step1 = (fun i j => raw41080step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41080step1 raw41080step0; decide +kernel
      have hl : raw41080step1Labels = raw41080step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41080step0 raw41080step0Labels permutation49 permutation6
    mixedMoment B raw41080step1 raw41080step1Labels = mixedMoment B raw41080step2 raw41080step2Labels := by
      have ha : raw41080step2 = -raw41080step1 := by apply Matrix.ext; change ∀ i j, raw41080step2 i j = -(raw41080step1 i j); unfold raw41080step2 raw41080step1; decide +kernel
      have hl : raw41080step2Labels = raw41080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2954 node2954Labels := by rfl

theorem canonical41081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41081 raw41081Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw41081 raw41081Labels = mixedMoment B raw41081step0 raw41081step0Labels := by
      have hz : ∀ j, raw41081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41081step0 = (fun i j => raw41081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41081step0 raw41081; decide +kernel
      have hl : raw41081step0Labels = raw41081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41081 raw41081Labels permutation434 hz
    mixedMoment B raw41081step0 raw41081step0Labels = mixedMoment B raw41081step1 raw41081step1Labels := by
      have ha : raw41081step1 = (fun i j => raw41081step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41081step1 raw41081step0; decide +kernel
      have hl : raw41081step1Labels = raw41081step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41081step0 raw41081step0Labels permutation47 permutation6
    mixedMoment B raw41081step1 raw41081step1Labels = mixedMoment B raw41081step2 raw41081step2Labels := by
      have ha : raw41081step2 = -raw41081step1 := by apply Matrix.ext; change ∀ i j, raw41081step2 i j = -(raw41081step1 i j); unfold raw41081step2 raw41081step1; decide +kernel
      have hl : raw41081step2Labels = raw41081step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2817 node2817Labels := by rfl

theorem canonical41082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41082 raw41082Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw41082 raw41082Labels = mixedMoment B raw41082step0 raw41082step0Labels := by
      have hz : ∀ j, raw41082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41082step0 = (fun i j => raw41082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41082step0 raw41082; decide +kernel
      have hl : raw41082step0Labels = raw41082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41082 raw41082Labels permutation434 hz
    mixedMoment B raw41082step0 raw41082step0Labels = mixedMoment B raw41082step1 raw41082step1Labels := by
      have ha : raw41082step1 = (fun i j => raw41082step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41082step1 raw41082step0; decide +kernel
      have hl : raw41082step1Labels = raw41082step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41082step0 raw41082step0Labels permutation55 permutation6
    mixedMoment B raw41082step1 raw41082step1Labels = mixedMoment B raw41082step2 raw41082step2Labels := by
      have ha : raw41082step2 = -raw41082step1 := by apply Matrix.ext; change ∀ i j, raw41082step2 i j = -(raw41082step1 i j); unfold raw41082step2 raw41082step1; decide +kernel
      have hl : raw41082step2Labels = raw41082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2881 node2881Labels := by rfl

theorem canonical41083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41083 raw41083Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw41083 raw41083Labels = mixedMoment B raw41083step0 raw41083step0Labels := by
      have hz : ∀ j, raw41083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41083step0 = (fun i j => raw41083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41083step0 raw41083; decide +kernel
      have hl : raw41083step0Labels = raw41083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41083 raw41083Labels permutation434 hz
    mixedMoment B raw41083step0 raw41083step0Labels = mixedMoment B raw41083step1 raw41083step1Labels := by
      have ha : raw41083step1 = (fun i j => raw41083step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41083step1 raw41083step0; decide +kernel
      have hl : raw41083step1Labels = raw41083step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41083step0 raw41083step0Labels permutation49 permutation6
    mixedMoment B raw41083step1 raw41083step1Labels = mixedMoment B raw41083step2 raw41083step2Labels := by
      have ha : raw41083step2 = -raw41083step1 := by apply Matrix.ext; change ∀ i j, raw41083step2 i j = -(raw41083step1 i j); unfold raw41083step2 raw41083step1; decide +kernel
      have hl : raw41083step2Labels = raw41083step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

theorem canonical41084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41084 raw41084Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw41084 raw41084Labels = mixedMoment B raw41084step0 raw41084step0Labels := by
      have ha : raw41084step0 = (fun i j => raw41084 (permutation215 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41084step0 raw41084; decide +kernel
      have hl : raw41084step0Labels = raw41084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41084 raw41084Labels permutation215 permutation6
    mixedMoment B raw41084step0 raw41084step0Labels = mixedMoment B raw41084step1 raw41084step1Labels := by
      have ha : raw41084step1 = -raw41084step0 := by apply Matrix.ext; change ∀ i j, raw41084step1 i j = -(raw41084step0 i j); unfold raw41084step1 raw41084step0; decide +kernel
      have hl : raw41084step1Labels = raw41084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2896 node2896Labels := by rfl

theorem canonical41085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41085 raw41085Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw41085 raw41085Labels = mixedMoment B raw41085step0 raw41085step0Labels := by
      have ha : raw41085step0 = (fun i j => raw41085 (permutation223 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41085step0 raw41085; decide +kernel
      have hl : raw41085step0Labels = raw41085Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41085 raw41085Labels permutation223 permutation6
    mixedMoment B raw41085step0 raw41085step0Labels = mixedMoment B raw41085step1 raw41085step1Labels := by
      have ha : raw41085step1 = -raw41085step0 := by apply Matrix.ext; change ∀ i j, raw41085step1 i j = -(raw41085step0 i j); unfold raw41085step1 raw41085step0; decide +kernel
      have hl : raw41085step1Labels = raw41085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2924 node2924Labels := by rfl

theorem canonical41086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41086 raw41086Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw41086 raw41086Labels = mixedMoment B raw41086step0 raw41086step0Labels := by
      have ha : raw41086step0 = (fun i j => raw41086 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41086step0 raw41086; decide +kernel
      have hl : raw41086step0Labels = raw41086Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41086 raw41086Labels permutation217 permutation6
    mixedMoment B raw41086step0 raw41086step0Labels = mixedMoment B raw41086step1 raw41086step1Labels := by
      have ha : raw41086step1 = -raw41086step0 := by apply Matrix.ext; change ∀ i j, raw41086step1 i j = -(raw41086step0 i j); unfold raw41086step1 raw41086step0; decide +kernel
      have hl : raw41086step1Labels = raw41086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2807 node2807Labels := by rfl

theorem canonical41087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41087 raw41087Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw41087 raw41087Labels = mixedMoment B raw41087step0 raw41087step0Labels := by
      have hz : ∀ j, raw41087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41087step0 = (fun i j => raw41087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41087step0 raw41087; decide +kernel
      have hl : raw41087step0Labels = raw41087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41087 raw41087Labels permutation434 hz
    mixedMoment B raw41087step0 raw41087step0Labels = mixedMoment B raw41087step1 raw41087step1Labels := by
      have hz : ∀ j, raw41087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41087step1 = (fun i j => raw41087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41087step1 raw41087step0; decide +kernel
      have hl : raw41087step1Labels = raw41087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41087step0 raw41087step0Labels permutation80 hz
    mixedMoment B raw41087step1 raw41087step1Labels = mixedMoment B raw41087step2 raw41087step2Labels := by
      have ha : raw41087step2 = (fun i j => raw41087step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41087step2 raw41087step1; decide +kernel
      have hl : raw41087step2Labels = raw41087step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41087step1 raw41087step1Labels permutation29 permutation6
    _ = mixedMoment B node2820 node2820Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical321
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41088 raw41088Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw41088 raw41088Labels = mixedMoment B raw41088step0 raw41088step0Labels := by
      have hz : ∀ j, raw41088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41088step0 = (fun i j => raw41088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41088step0 raw41088; decide +kernel
      have hl : raw41088step0Labels = raw41088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41088 raw41088Labels permutation434 hz
    mixedMoment B raw41088step0 raw41088step0Labels = mixedMoment B raw41088step1 raw41088step1Labels := by
      have hz : ∀ j, raw41088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41088step1 = (fun i j => raw41088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41088step1 raw41088step0; decide +kernel
      have hl : raw41088step1Labels = raw41088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41088step0 raw41088step0Labels permutation80 hz
    mixedMoment B raw41088step1 raw41088step1Labels = mixedMoment B raw41088step2 raw41088step2Labels := by
      have ha : raw41088step2 = (fun i j => raw41088step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41088step2 raw41088step1; decide +kernel
      have hl : raw41088step2Labels = raw41088step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41088step1 raw41088step1Labels permutation13 permutation6
    mixedMoment B raw41088step2 raw41088step2Labels = mixedMoment B raw41088step3 raw41088step3Labels := by
      have ha : raw41088step3 = -raw41088step2 := by apply Matrix.ext; change ∀ i j, raw41088step3 i j = -(raw41088step2 i j); unfold raw41088step3 raw41088step2; decide +kernel
      have hl : raw41088step3Labels = raw41088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2889 node2889Labels := by rfl

theorem canonical41089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41089 raw41089Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw41089 raw41089Labels = mixedMoment B raw41089step0 raw41089step0Labels := by
      have hz : ∀ j, raw41089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41089step0 = (fun i j => raw41089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41089step0 raw41089; decide +kernel
      have hl : raw41089step0Labels = raw41089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41089 raw41089Labels permutation346 hz
    mixedMoment B raw41089step0 raw41089step0Labels = mixedMoment B raw41089step1 raw41089step1Labels := by
      have ha : raw41089step1 = (fun i j => raw41089step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41089step1 raw41089step0; decide +kernel
      have hl : raw41089step1Labels = raw41089step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41089step0 raw41089step0Labels permutation137 permutation6
    _ = mixedMoment B node2815 node2815Labels := by rfl

theorem canonical41090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41090 raw41090Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw41090 raw41090Labels = mixedMoment B raw41090step0 raw41090step0Labels := by
      have hz : ∀ j, raw41090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41090step0 = (fun i j => raw41090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41090step0 raw41090; decide +kernel
      have hl : raw41090step0Labels = raw41090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41090 raw41090Labels permutation346 hz
    mixedMoment B raw41090step0 raw41090step0Labels = mixedMoment B raw41090step1 raw41090step1Labels := by
      have ha : raw41090step1 = (fun i j => raw41090step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41090step1 raw41090step0; decide +kernel
      have hl : raw41090step1Labels = raw41090step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41090step0 raw41090step0Labels permutation43 permutation6
    mixedMoment B raw41090step1 raw41090step1Labels = mixedMoment B raw41090step2 raw41090step2Labels := by
      have ha : raw41090step2 = -raw41090step1 := by apply Matrix.ext; change ∀ i j, raw41090step2 i j = -(raw41090step1 i j); unfold raw41090step2 raw41090step1; decide +kernel
      have hl : raw41090step2Labels = raw41090step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2931 node2931Labels := by rfl

theorem canonical41091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41091 raw41091Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw41091 raw41091Labels = mixedMoment B raw41091step0 raw41091step0Labels := by
      have hz : ∀ j, raw41091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41091step0 = (fun i j => raw41091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41091step0 raw41091; decide +kernel
      have hl : raw41091step0Labels = raw41091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41091 raw41091Labels permutation346 hz
    mixedMoment B raw41091step0 raw41091step0Labels = mixedMoment B raw41091step1 raw41091step1Labels := by
      have ha : raw41091step1 = (fun i j => raw41091step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41091step1 raw41091step0; decide +kernel
      have hl : raw41091step1Labels = raw41091step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41091step0 raw41091step0Labels permutation43 permutation6
    mixedMoment B raw41091step1 raw41091step1Labels = mixedMoment B raw41091step2 raw41091step2Labels := by
      have ha : raw41091step2 = -raw41091step1 := by apply Matrix.ext; change ∀ i j, raw41091step2 i j = -(raw41091step1 i j); unfold raw41091step2 raw41091step1; decide +kernel
      have hl : raw41091step2Labels = raw41091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2813 node2813Labels := by rfl

theorem canonical41092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41092 raw41092Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw41092 raw41092Labels = mixedMoment B raw41092step0 raw41092step0Labels := by
      have ha : raw41092step0 = (fun i j => raw41092 (permutation187 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41092step0 raw41092; decide +kernel
      have hl : raw41092step0Labels = raw41092Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41092 raw41092Labels permutation187 permutation6
    mixedMoment B raw41092step0 raw41092step0Labels = mixedMoment B raw41092step1 raw41092step1Labels := by
      have ha : raw41092step1 = -raw41092step0 := by apply Matrix.ext; change ∀ i j, raw41092step1 i j = -(raw41092step0 i j); unfold raw41092step1 raw41092step0; decide +kernel
      have hl : raw41092step1Labels = raw41092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2893 node2893Labels := by rfl

theorem canonical41093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41093 raw41093Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw41093 raw41093Labels = mixedMoment B raw41093step0 raw41093step0Labels := by
      have ha : raw41093step0 = (fun i j => raw41093 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41093step0 raw41093; decide +kernel
      have hl : raw41093step0Labels = raw41093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41093 raw41093Labels permutation224 permutation6
    mixedMoment B raw41093step0 raw41093step0Labels = mixedMoment B raw41093step1 raw41093step1Labels := by
      have ha : raw41093step1 = -raw41093step0 := by apply Matrix.ext; change ∀ i j, raw41093step1 i j = -(raw41093step0 i j); unfold raw41093step1 raw41093step0; decide +kernel
      have hl : raw41093step1Labels = raw41093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2814 node2814Labels := by rfl

theorem canonical41094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41094 raw41094Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw41094 raw41094Labels = mixedMoment B raw41094step0 raw41094step0Labels := by
      have hz : ∀ j, raw41094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41094step0 = (fun i j => raw41094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41094step0 raw41094; decide +kernel
      have hl : raw41094step0Labels = raw41094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41094 raw41094Labels permutation434 hz
    mixedMoment B raw41094step0 raw41094step0Labels = mixedMoment B raw41094step1 raw41094step1Labels := by
      have ha : raw41094step1 = (fun i j => raw41094step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41094step1 raw41094step0; decide +kernel
      have hl : raw41094step1Labels = raw41094step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41094step0 raw41094step0Labels permutation44 permutation6
    mixedMoment B raw41094step1 raw41094step1Labels = mixedMoment B raw41094step2 raw41094step2Labels := by
      have ha : raw41094step2 = -raw41094step1 := by apply Matrix.ext; change ∀ i j, raw41094step2 i j = -(raw41094step1 i j); unfold raw41094step2 raw41094step1; decide +kernel
      have hl : raw41094step2Labels = raw41094step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2815 node2815Labels := by rfl

theorem canonical41095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41095 raw41095Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw41095 raw41095Labels = mixedMoment B raw41095step0 raw41095step0Labels := by
      have ha : raw41095step0 = (fun i j => raw41095 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41095step0 raw41095; decide +kernel
      have hl : raw41095step0Labels = raw41095Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41095 raw41095Labels permutation218 permutation6
    mixedMoment B raw41095step0 raw41095step0Labels = mixedMoment B raw41095step1 raw41095step1Labels := by
      have ha : raw41095step1 = -raw41095step0 := by apply Matrix.ext; change ∀ i j, raw41095step1 i j = -(raw41095step0 i j); unfold raw41095step1 raw41095step0; decide +kernel
      have hl : raw41095step1Labels = raw41095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2809 node2809Labels := by rfl

theorem canonical41096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41096 raw41096Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw41096 raw41096Labels = mixedMoment B raw41096step0 raw41096step0Labels := by
      have hz : ∀ j, raw41096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41096step0 = (fun i j => raw41096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41096step0 raw41096; decide +kernel
      have hl : raw41096step0Labels = raw41096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41096 raw41096Labels permutation434 hz
    mixedMoment B raw41096step0 raw41096step0Labels = mixedMoment B raw41096step1 raw41096step1Labels := by
      have hz : ∀ j, raw41096step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41096step1 = (fun i j => raw41096step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41096step1 raw41096step0; decide +kernel
      have hl : raw41096step1Labels = raw41096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41096step0 raw41096step0Labels permutation80 hz
    mixedMoment B raw41096step1 raw41096step1Labels = mixedMoment B raw41096step2 raw41096step2Labels := by
      have ha : raw41096step2 = (fun i j => raw41096step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41096step2 raw41096step1; decide +kernel
      have hl : raw41096step2Labels = raw41096step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41096step1 raw41096step1Labels permutation29 permutation6
    _ = mixedMoment B node1145 node1145Labels := by rfl

theorem canonical41097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41097 raw41097Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw41097 raw41097Labels = mixedMoment B raw41097step0 raw41097step0Labels := by
      have hz : ∀ j, raw41097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41097step0 = (fun i j => raw41097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41097step0 raw41097; decide +kernel
      have hl : raw41097step0Labels = raw41097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41097 raw41097Labels permutation434 hz
    mixedMoment B raw41097step0 raw41097step0Labels = mixedMoment B raw41097step1 raw41097step1Labels := by
      have hz : ∀ j, raw41097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41097step1 = (fun i j => raw41097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41097step1 raw41097step0; decide +kernel
      have hl : raw41097step1Labels = raw41097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41097step0 raw41097step0Labels permutation80 hz
    mixedMoment B raw41097step1 raw41097step1Labels = mixedMoment B raw41097step2 raw41097step2Labels := by
      have ha : raw41097step2 = (fun i j => raw41097step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41097step2 raw41097step1; decide +kernel
      have hl : raw41097step2Labels = raw41097step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41097step1 raw41097step1Labels permutation23 permutation6
    _ = mixedMoment B node2519 node2519Labels := by rfl

theorem canonical41098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41098 raw41098Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw41098 raw41098Labels = mixedMoment B raw41098step0 raw41098step0Labels := by
      have hz : ∀ j, raw41098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41098step0 = (fun i j => raw41098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41098step0 raw41098; decide +kernel
      have hl : raw41098step0Labels = raw41098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41098 raw41098Labels permutation346 hz
    mixedMoment B raw41098step0 raw41098step0Labels = mixedMoment B raw41098step1 raw41098step1Labels := by
      have ha : raw41098step1 = (fun i j => raw41098step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41098step1 raw41098step0; decide +kernel
      have hl : raw41098step1Labels = raw41098step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41098step0 raw41098step0Labels permutation115 permutation6
    _ = mixedMoment B node2485 node2485Labels := by rfl

theorem canonical41099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41099 raw41099Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw41099 raw41099Labels = mixedMoment B raw41099step0 raw41099step0Labels := by
      have hz : ∀ j, raw41099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41099step0 = (fun i j => raw41099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41099step0 raw41099; decide +kernel
      have hl : raw41099step0Labels = raw41099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41099 raw41099Labels permutation346 hz
    mixedMoment B raw41099step0 raw41099step0Labels = mixedMoment B raw41099step1 raw41099step1Labels := by
      have ha : raw41099step1 = (fun i j => raw41099step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41099step1 raw41099step0; decide +kernel
      have hl : raw41099step1Labels = raw41099step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41099step0 raw41099step0Labels permutation115 permutation6
    _ = mixedMoment B node2434 node2434Labels := by rfl

theorem canonical41100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41100 raw41100Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw41100 raw41100Labels = mixedMoment B raw41100step0 raw41100step0Labels := by
      have hz : ∀ j, raw41100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41100step0 = (fun i j => raw41100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41100step0 raw41100; decide +kernel
      have hl : raw41100step0Labels = raw41100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41100 raw41100Labels permutation346 hz
    mixedMoment B raw41100step0 raw41100step0Labels = mixedMoment B raw41100step1 raw41100step1Labels := by
      have ha : raw41100step1 = (fun i j => raw41100step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41100step1 raw41100step0; decide +kernel
      have hl : raw41100step1Labels = raw41100step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41100step0 raw41100step0Labels permutation38 permutation6
    mixedMoment B raw41100step1 raw41100step1Labels = mixedMoment B raw41100step2 raw41100step2Labels := by
      have ha : raw41100step2 = -raw41100step1 := by apply Matrix.ext; change ∀ i j, raw41100step2 i j = -(raw41100step1 i j); unfold raw41100step2 raw41100step1; decide +kernel
      have hl : raw41100step2Labels = raw41100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2818 node2818Labels := by rfl

theorem canonical41101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41101 raw41101Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw41101 raw41101Labels = mixedMoment B raw41101step0 raw41101step0Labels := by
      have ha : raw41101step0 = (fun i j => raw41101 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41101step0 raw41101; decide +kernel
      have hl : raw41101step0Labels = raw41101Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41101 raw41101Labels permutation540 permutation6
    _ = mixedMoment B node2429 node2429Labels := by rfl

theorem canonical41102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41102 raw41102Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw41102 raw41102Labels = mixedMoment B raw41102step0 raw41102step0Labels := by
      have hz : ∀ j, raw41102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41102step0 = (fun i j => raw41102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41102step0 raw41102; decide +kernel
      have hl : raw41102step0Labels = raw41102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41102 raw41102Labels permutation434 hz
    mixedMoment B raw41102step0 raw41102step0Labels = mixedMoment B raw41102step1 raw41102step1Labels := by
      have hz : ∀ j, raw41102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41102step1 = (fun i j => raw41102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41102step1 raw41102step0; decide +kernel
      have hl : raw41102step1Labels = raw41102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41102step0 raw41102step0Labels permutation80 hz
    mixedMoment B raw41102step1 raw41102step1Labels = mixedMoment B raw41102step2 raw41102step2Labels := by
      have hz : ∀ j, raw41102step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41102step2 = (fun i j => raw41102step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41102step2 raw41102step1; decide +kernel
      have hl : raw41102step2Labels = raw41102step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41102step1 raw41102step1Labels permutation14 hz
    mixedMoment B raw41102step2 raw41102step2Labels = mixedMoment B raw41102step3 raw41102step3Labels := by
      have ha : raw41102step3 = (fun i j => raw41102step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41102step3 raw41102step2; decide +kernel
      have hl : raw41102step3Labels = raw41102step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41102step2 raw41102step2Labels permutation7 permutation6
    _ = mixedMoment B node620 node620Labels := by rfl

theorem canonical41103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41103 raw41103Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw41103 raw41103Labels = mixedMoment B raw41103step0 raw41103step0Labels := by
      have hz : ∀ j, raw41103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41103step0 = (fun i j => raw41103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41103step0 raw41103; decide +kernel
      have hl : raw41103step0Labels = raw41103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41103 raw41103Labels permutation434 hz
    mixedMoment B raw41103step0 raw41103step0Labels = mixedMoment B raw41103step1 raw41103step1Labels := by
      have hz : ∀ j, raw41103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41103step1 = (fun i j => raw41103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41103step1 raw41103step0; decide +kernel
      have hl : raw41103step1Labels = raw41103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41103step0 raw41103step0Labels permutation80 hz
    mixedMoment B raw41103step1 raw41103step1Labels = mixedMoment B raw41103step2 raw41103step2Labels := by
      have hz : ∀ j, raw41103step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41103step2 = (fun i j => raw41103step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41103step2 raw41103step1; decide +kernel
      have hl : raw41103step2Labels = raw41103step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41103step1 raw41103step1Labels permutation14 hz
    mixedMoment B raw41103step2 raw41103step2Labels = mixedMoment B raw41103step3 raw41103step3Labels := by
      have ha : raw41103step3 = (fun i j => raw41103step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41103step3 raw41103step2; decide +kernel
      have hl : raw41103step3Labels = raw41103step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41103step2 raw41103step2Labels permutation5 permutation6
    _ = mixedMoment B node1091 node1091Labels := by rfl

theorem canonical41104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41104 raw41104Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw41104 raw41104Labels = mixedMoment B raw41104step0 raw41104step0Labels := by
      have hz : ∀ j, raw41104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41104step0 = (fun i j => raw41104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41104step0 raw41104; decide +kernel
      have hl : raw41104step0Labels = raw41104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41104 raw41104Labels permutation346 hz
    mixedMoment B raw41104step0 raw41104step0Labels = mixedMoment B raw41104step1 raw41104step1Labels := by
      have hz : ∀ j, raw41104step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41104step1 = (fun i j => raw41104step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41104step1 raw41104step0; decide +kernel
      have hl : raw41104step1Labels = raw41104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41104step0 raw41104step0Labels permutation56 hz
    mixedMoment B raw41104step1 raw41104step1Labels = mixedMoment B raw41104step2 raw41104step2Labels := by
      have ha : raw41104step2 = (fun i j => raw41104step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41104step2 raw41104step1; decide +kernel
      have hl : raw41104step2Labels = raw41104step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41104step1 raw41104step1Labels permutation29 permutation6
    _ = mixedMoment B node611 node611Labels := by rfl

theorem canonical41105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41105 raw41105Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw41105 raw41105Labels = mixedMoment B raw41105step0 raw41105step0Labels := by
      have hz : ∀ j, raw41105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41105step0 = (fun i j => raw41105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41105step0 raw41105; decide +kernel
      have hl : raw41105step0Labels = raw41105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41105 raw41105Labels permutation346 hz
    mixedMoment B raw41105step0 raw41105step0Labels = mixedMoment B raw41105step1 raw41105step1Labels := by
      have hz : ∀ j, raw41105step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41105step1 = (fun i j => raw41105step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41105step1 raw41105step0; decide +kernel
      have hl : raw41105step1Labels = raw41105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41105step0 raw41105step0Labels permutation56 hz
    mixedMoment B raw41105step1 raw41105step1Labels = mixedMoment B raw41105step2 raw41105step2Labels := by
      have ha : raw41105step2 = (fun i j => raw41105step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41105step2 raw41105step1; decide +kernel
      have hl : raw41105step2Labels = raw41105step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41105step1 raw41105step1Labels permutation25 permutation6
    _ = mixedMoment B node1046 node1046Labels := by rfl

theorem canonical41106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41106 raw41106Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw41106 raw41106Labels = mixedMoment B raw41106step0 raw41106step0Labels := by
      have hz : ∀ j, raw41106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41106step0 = (fun i j => raw41106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41106step0 raw41106; decide +kernel
      have hl : raw41106step0Labels = raw41106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41106 raw41106Labels permutation346 hz
    mixedMoment B raw41106step0 raw41106step0Labels = mixedMoment B raw41106step1 raw41106step1Labels := by
      have hz : ∀ j, raw41106step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41106step1 = (fun i j => raw41106step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41106step1 raw41106step0; decide +kernel
      have hl : raw41106step1Labels = raw41106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41106step0 raw41106step0Labels permutation56 hz
    mixedMoment B raw41106step1 raw41106step1Labels = mixedMoment B raw41106step2 raw41106step2Labels := by
      have ha : raw41106step2 = (fun i j => raw41106step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41106step2 raw41106step1; decide +kernel
      have hl : raw41106step2Labels = raw41106step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41106step1 raw41106step1Labels permutation25 permutation6
    _ = mixedMoment B node939 node939Labels := by rfl

theorem canonical41107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41107 raw41107Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw41107 raw41107Labels = mixedMoment B raw41107step0 raw41107step0Labels := by
      have hz : ∀ j, raw41107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41107step0 = (fun i j => raw41107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41107step0 raw41107; decide +kernel
      have hl : raw41107step0Labels = raw41107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41107 raw41107Labels permutation346 hz
    mixedMoment B raw41107step0 raw41107step0Labels = mixedMoment B raw41107step1 raw41107step1Labels := by
      have hz : ∀ j, raw41107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41107step1 = (fun i j => raw41107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41107step1 raw41107step0; decide +kernel
      have hl : raw41107step1Labels = raw41107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41107step0 raw41107step0Labels permutation56 hz
    mixedMoment B raw41107step1 raw41107step1Labels = mixedMoment B raw41107step2 raw41107step2Labels := by
      have ha : raw41107step2 = (fun i j => raw41107step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41107step2 raw41107step1; decide +kernel
      have hl : raw41107step2Labels = raw41107step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41107step1 raw41107step1Labels permutation25 permutation6
    _ = mixedMoment B node2345 node2345Labels := by rfl

theorem canonical41108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41108 raw41108Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw41108 raw41108Labels = mixedMoment B raw41108step0 raw41108step0Labels := by
      have hz : ∀ j, raw41108 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41108step0 = (fun i j => raw41108 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41108step0 raw41108; decide +kernel
      have hl : raw41108step0Labels = raw41108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41108 raw41108Labels permutation265 hz
    mixedMoment B raw41108step0 raw41108step0Labels = mixedMoment B raw41108step1 raw41108step1Labels := by
      have ha : raw41108step1 = (fun i j => raw41108step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41108step1 raw41108step0; decide +kernel
      have hl : raw41108step1Labels = raw41108step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41108step0 raw41108step0Labels permutation125 permutation6
    _ = mixedMoment B node930 node930Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical5460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5460 raw5460Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw5460 raw5460Labels = mixedMoment B raw5460step0 raw5460step0Labels := by
      have hz : ∀ j, raw5460 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5460step0 = (fun i j => raw5460 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5460step0 raw5460; decide +kernel
      have hl : raw5460step0Labels = raw5460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5460 raw5460Labels permutation520 hz
    mixedMoment B raw5460step0 raw5460step0Labels = mixedMoment B raw5460step1 raw5460step1Labels := by
      have ha : raw5460step1 = (fun i j => raw5460step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5460step1 raw5460step0; decide +kernel
      have hl : raw5460step1Labels = raw5460step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5460step0 raw5460step0Labels permutation50 permutation6
    mixedMoment B raw5460step1 raw5460step1Labels = mixedMoment B raw5460step2 raw5460step2Labels := by
      have ha : raw5460step2 = -raw5460step1 := by apply Matrix.ext; change ∀ i j, raw5460step2 i j = -(raw5460step1 i j); unfold raw5460step2 raw5460step1; decide +kernel
      have hl : raw5460step2Labels = raw5460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3053 node3053Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment1664 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1664) =
      Integer.Sparse.eval keyMomentRow1664 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1664).leftCharge (GramAssembly.key 1664).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1964) := by
    have ha : gramCharges (GramAssembly.key 1664).leftCharge (GramAssembly.key 1664).rightCharge = raw41078 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41078Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41078 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1664).leftCharge (GramAssembly.key 1664).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1664, Integer.Sparse.eval]

theorem keyMoment1665 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1665) =
      Integer.Sparse.eval keyMomentRow1665 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1665).leftCharge (GramAssembly.key 1665).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3054) := by
    have ha : gramCharges (GramAssembly.key 1665).leftCharge (GramAssembly.key 1665).rightCharge = raw41079 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41079Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41079 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1665).leftCharge (GramAssembly.key 1665).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1665, Integer.Sparse.eval]

theorem keyMoment1666 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1666) =
      Integer.Sparse.eval keyMomentRow1666 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1666).leftCharge (GramAssembly.key 1666).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2954) := by
    have ha : gramCharges (GramAssembly.key 1666).leftCharge (GramAssembly.key 1666).rightCharge = raw41080 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41080Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41080 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1666).leftCharge (GramAssembly.key 1666).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1666, Integer.Sparse.eval]

theorem keyMoment1667 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1667) =
      Integer.Sparse.eval keyMomentRow1667 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1667).leftCharge (GramAssembly.key 1667).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2817) := by
    have ha : gramCharges (GramAssembly.key 1667).leftCharge (GramAssembly.key 1667).rightCharge = raw41081 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41081Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41081 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1667).leftCharge (GramAssembly.key 1667).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1667, Integer.Sparse.eval]

theorem keyMoment1668 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1668) =
      Integer.Sparse.eval keyMomentRow1668 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1668).leftCharge (GramAssembly.key 1668).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2881) := by
    have ha : gramCharges (GramAssembly.key 1668).leftCharge (GramAssembly.key 1668).rightCharge = raw41082 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41082Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41082 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1668).leftCharge (GramAssembly.key 1668).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1668, Integer.Sparse.eval]

theorem keyMoment1669 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1669) =
      Integer.Sparse.eval keyMomentRow1669 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1669).leftCharge (GramAssembly.key 1669).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3077) := by
    have ha : gramCharges (GramAssembly.key 1669).leftCharge (GramAssembly.key 1669).rightCharge = raw41083 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41083Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41083 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1669).leftCharge (GramAssembly.key 1669).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1669, Integer.Sparse.eval]

theorem keyMoment1670 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1670) =
      Integer.Sparse.eval keyMomentRow1670 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1670).leftCharge (GramAssembly.key 1670).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2896) := by
    have ha : gramCharges (GramAssembly.key 1670).leftCharge (GramAssembly.key 1670).rightCharge = raw41084 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41084Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41084 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1670).leftCharge (GramAssembly.key 1670).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1670, Integer.Sparse.eval]

theorem keyMoment1671 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1671) =
      Integer.Sparse.eval keyMomentRow1671 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1671).leftCharge (GramAssembly.key 1671).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2924) := by
    have ha : gramCharges (GramAssembly.key 1671).leftCharge (GramAssembly.key 1671).rightCharge = raw41085 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41085Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41085 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1671).leftCharge (GramAssembly.key 1671).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1671, Integer.Sparse.eval]

theorem keyMoment1672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1672) =
      Integer.Sparse.eval keyMomentRow1672 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1672).leftCharge (GramAssembly.key 1672).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2807) := by
    have ha : gramCharges (GramAssembly.key 1672).leftCharge (GramAssembly.key 1672).rightCharge = raw41086 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41086Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41086 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1672).leftCharge (GramAssembly.key 1672).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1672, Integer.Sparse.eval]

theorem keyMoment1673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1673) =
      Integer.Sparse.eval keyMomentRow1673 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1673).leftCharge (GramAssembly.key 1673).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2820) := by
    have ha : gramCharges (GramAssembly.key 1673).leftCharge (GramAssembly.key 1673).rightCharge = raw41087 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41087Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41087 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1673).leftCharge (GramAssembly.key 1673).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1673, Integer.Sparse.eval]

theorem keyMoment1674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1674) =
      Integer.Sparse.eval keyMomentRow1674 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1674).leftCharge (GramAssembly.key 1674).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2889) := by
    have ha : gramCharges (GramAssembly.key 1674).leftCharge (GramAssembly.key 1674).rightCharge = raw41088 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41088Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41088 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1674).leftCharge (GramAssembly.key 1674).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1674, Integer.Sparse.eval]

theorem keyMoment1675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1675) =
      Integer.Sparse.eval keyMomentRow1675 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1675).leftCharge (GramAssembly.key 1675).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2815) := by
    have ha : gramCharges (GramAssembly.key 1675).leftCharge (GramAssembly.key 1675).rightCharge = raw41089 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41089Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41089 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1675).leftCharge (GramAssembly.key 1675).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1675, Integer.Sparse.eval]

theorem keyMoment1676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1676) =
      Integer.Sparse.eval keyMomentRow1676 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1676).leftCharge (GramAssembly.key 1676).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2931) := by
    have ha : gramCharges (GramAssembly.key 1676).leftCharge (GramAssembly.key 1676).rightCharge = raw41090 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41090Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41090 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1676).leftCharge (GramAssembly.key 1676).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1676, Integer.Sparse.eval]

theorem keyMoment1677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1677) =
      Integer.Sparse.eval keyMomentRow1677 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1677).leftCharge (GramAssembly.key 1677).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2813) := by
    have ha : gramCharges (GramAssembly.key 1677).leftCharge (GramAssembly.key 1677).rightCharge = raw41091 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41091Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41091 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1677).leftCharge (GramAssembly.key 1677).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1677, Integer.Sparse.eval]

theorem keyMoment1678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1678) =
      Integer.Sparse.eval keyMomentRow1678 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1678).leftCharge (GramAssembly.key 1678).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2893) := by
    have ha : gramCharges (GramAssembly.key 1678).leftCharge (GramAssembly.key 1678).rightCharge = raw41092 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41092Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41092 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1678).leftCharge (GramAssembly.key 1678).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1678, Integer.Sparse.eval]

theorem keyMoment1679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1679) =
      Integer.Sparse.eval keyMomentRow1679 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1679).leftCharge (GramAssembly.key 1679).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 3053) := by
    have ha : gramCharges (GramAssembly.key 1679).leftCharge (GramAssembly.key 1679).rightCharge = raw5460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw5460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical5460 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1679).leftCharge (GramAssembly.key 1679).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1679, Integer.Sparse.eval]

theorem keyMoment1680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1680) =
      Integer.Sparse.eval keyMomentRow1680 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1680).leftCharge (GramAssembly.key 1680).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2814) := by
    have ha : gramCharges (GramAssembly.key 1680).leftCharge (GramAssembly.key 1680).rightCharge = raw41093 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41093Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41093 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1680).leftCharge (GramAssembly.key 1680).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1680, Integer.Sparse.eval]

theorem keyMoment1681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1681) =
      Integer.Sparse.eval keyMomentRow1681 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1681).leftCharge (GramAssembly.key 1681).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2815) := by
    have ha : gramCharges (GramAssembly.key 1681).leftCharge (GramAssembly.key 1681).rightCharge = raw41094 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41094Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41094 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1681).leftCharge (GramAssembly.key 1681).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1681, Integer.Sparse.eval]

theorem keyMoment1682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1682) =
      Integer.Sparse.eval keyMomentRow1682 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1682).leftCharge (GramAssembly.key 1682).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2809) := by
    have ha : gramCharges (GramAssembly.key 1682).leftCharge (GramAssembly.key 1682).rightCharge = raw41095 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41095Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41095 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1682).leftCharge (GramAssembly.key 1682).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1682, Integer.Sparse.eval]

theorem keyMoment1683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1683) =
      Integer.Sparse.eval keyMomentRow1683 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1683).leftCharge (GramAssembly.key 1683).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1145) := by
    have ha : gramCharges (GramAssembly.key 1683).leftCharge (GramAssembly.key 1683).rightCharge = raw41096 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41096Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41096 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1683).leftCharge (GramAssembly.key 1683).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1683, Integer.Sparse.eval]

theorem keyMoment1684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1684) =
      Integer.Sparse.eval keyMomentRow1684 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1684).leftCharge (GramAssembly.key 1684).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2519) := by
    have ha : gramCharges (GramAssembly.key 1684).leftCharge (GramAssembly.key 1684).rightCharge = raw41097 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41097Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41097 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1684).leftCharge (GramAssembly.key 1684).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1684, Integer.Sparse.eval]

theorem keyMoment1685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1685) =
      Integer.Sparse.eval keyMomentRow1685 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1685).leftCharge (GramAssembly.key 1685).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2485) := by
    have ha : gramCharges (GramAssembly.key 1685).leftCharge (GramAssembly.key 1685).rightCharge = raw41098 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41098Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41098 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1685).leftCharge (GramAssembly.key 1685).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1685, Integer.Sparse.eval]

theorem keyMoment1686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1686) =
      Integer.Sparse.eval keyMomentRow1686 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1686).leftCharge (GramAssembly.key 1686).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2434) := by
    have ha : gramCharges (GramAssembly.key 1686).leftCharge (GramAssembly.key 1686).rightCharge = raw41099 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41099Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41099 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1686).leftCharge (GramAssembly.key 1686).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1686, Integer.Sparse.eval]

theorem keyMoment1687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1687) =
      Integer.Sparse.eval keyMomentRow1687 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1687).leftCharge (GramAssembly.key 1687).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2818) := by
    have ha : gramCharges (GramAssembly.key 1687).leftCharge (GramAssembly.key 1687).rightCharge = raw41100 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41100Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41100 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1687).leftCharge (GramAssembly.key 1687).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1687, Integer.Sparse.eval]

theorem keyMoment1688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1688) =
      Integer.Sparse.eval keyMomentRow1688 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1688).leftCharge (GramAssembly.key 1688).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2429) := by
    have ha : gramCharges (GramAssembly.key 1688).leftCharge (GramAssembly.key 1688).rightCharge = raw41101 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41101Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41101 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1688).leftCharge (GramAssembly.key 1688).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1688, Integer.Sparse.eval]

theorem keyMoment1689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1689) =
      Integer.Sparse.eval keyMomentRow1689 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1689).leftCharge (GramAssembly.key 1689).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 620) := by
    have ha : gramCharges (GramAssembly.key 1689).leftCharge (GramAssembly.key 1689).rightCharge = raw41102 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41102Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41102 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1689).leftCharge (GramAssembly.key 1689).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1689, Integer.Sparse.eval]

theorem keyMoment1690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1690) =
      Integer.Sparse.eval keyMomentRow1690 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1690).leftCharge (GramAssembly.key 1690).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1091) := by
    have ha : gramCharges (GramAssembly.key 1690).leftCharge (GramAssembly.key 1690).rightCharge = raw41103 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41103Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41103 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1690).leftCharge (GramAssembly.key 1690).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1690, Integer.Sparse.eval]

theorem keyMoment1691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1691) =
      Integer.Sparse.eval keyMomentRow1691 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1691).leftCharge (GramAssembly.key 1691).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 611) := by
    have ha : gramCharges (GramAssembly.key 1691).leftCharge (GramAssembly.key 1691).rightCharge = raw41104 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41104Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41104 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1691).leftCharge (GramAssembly.key 1691).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1691, Integer.Sparse.eval]

theorem keyMoment1692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1692) =
      Integer.Sparse.eval keyMomentRow1692 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1692).leftCharge (GramAssembly.key 1692).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 1046) := by
    have ha : gramCharges (GramAssembly.key 1692).leftCharge (GramAssembly.key 1692).rightCharge = raw41105 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41105Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41105 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1692).leftCharge (GramAssembly.key 1692).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1692, Integer.Sparse.eval]

theorem keyMoment1693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1693) =
      Integer.Sparse.eval keyMomentRow1693 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1693).leftCharge (GramAssembly.key 1693).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 939) := by
    have ha : gramCharges (GramAssembly.key 1693).leftCharge (GramAssembly.key 1693).rightCharge = raw41106 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41106Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41106 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1693).leftCharge (GramAssembly.key 1693).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1693, Integer.Sparse.eval]

theorem keyMoment1694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1694) =
      Integer.Sparse.eval keyMomentRow1694 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1694).leftCharge (GramAssembly.key 1694).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 2345) := by
    have ha : gramCharges (GramAssembly.key 1694).leftCharge (GramAssembly.key 1694).rightCharge = raw41107 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41107Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41107 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1694).leftCharge (GramAssembly.key 1694).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1694, Integer.Sparse.eval]

theorem keyMoment1695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 1695) =
      Integer.Sparse.eval keyMomentRow1695 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 1695).leftCharge (GramAssembly.key 1695).rightCharge) (gramLabels 0 1) =
      originalVector B (Sum.inl 930) := by
    have ha : gramCharges (GramAssembly.key 1695).leftCharge (GramAssembly.key 1695).rightCharge = raw41108 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41108Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41108 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 1695).leftCharge (GramAssembly.key 1695).rightCharge) (gramLabels 0 1) = _
  rw [hfirst]
  norm_num [keyMomentRow1695, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt1664 : keyMomentRows (1664 : Fin 2886) =
    keyMomentRow1664 := by decide +kernel

theorem keyMomentRowsAt1665 : keyMomentRows (1665 : Fin 2886) =
    keyMomentRow1665 := by decide +kernel

theorem keyMomentRowsAt1666 : keyMomentRows (1666 : Fin 2886) =
    keyMomentRow1666 := by decide +kernel

theorem keyMomentRowsAt1667 : keyMomentRows (1667 : Fin 2886) =
    keyMomentRow1667 := by decide +kernel

theorem keyMomentRowsAt1668 : keyMomentRows (1668 : Fin 2886) =
    keyMomentRow1668 := by decide +kernel

theorem keyMomentRowsAt1669 : keyMomentRows (1669 : Fin 2886) =
    keyMomentRow1669 := by decide +kernel

theorem keyMomentRowsAt1670 : keyMomentRows (1670 : Fin 2886) =
    keyMomentRow1670 := by decide +kernel

theorem keyMomentRowsAt1671 : keyMomentRows (1671 : Fin 2886) =
    keyMomentRow1671 := by decide +kernel

theorem keyMomentRowsAt1672 : keyMomentRows (1672 : Fin 2886) =
    keyMomentRow1672 := by decide +kernel

theorem keyMomentRowsAt1673 : keyMomentRows (1673 : Fin 2886) =
    keyMomentRow1673 := by decide +kernel

theorem keyMomentRowsAt1674 : keyMomentRows (1674 : Fin 2886) =
    keyMomentRow1674 := by decide +kernel

theorem keyMomentRowsAt1675 : keyMomentRows (1675 : Fin 2886) =
    keyMomentRow1675 := by decide +kernel

theorem keyMomentRowsAt1676 : keyMomentRows (1676 : Fin 2886) =
    keyMomentRow1676 := by decide +kernel

theorem keyMomentRowsAt1677 : keyMomentRows (1677 : Fin 2886) =
    keyMomentRow1677 := by decide +kernel

theorem keyMomentRowsAt1678 : keyMomentRows (1678 : Fin 2886) =
    keyMomentRow1678 := by decide +kernel

theorem keyMomentRowsAt1679 : keyMomentRows (1679 : Fin 2886) =
    keyMomentRow1679 := by decide +kernel

theorem keyMomentRowsAt1680 : keyMomentRows (1680 : Fin 2886) =
    keyMomentRow1680 := by decide +kernel

theorem keyMomentRowsAt1681 : keyMomentRows (1681 : Fin 2886) =
    keyMomentRow1681 := by decide +kernel

theorem keyMomentRowsAt1682 : keyMomentRows (1682 : Fin 2886) =
    keyMomentRow1682 := by decide +kernel

theorem keyMomentRowsAt1683 : keyMomentRows (1683 : Fin 2886) =
    keyMomentRow1683 := by decide +kernel

theorem keyMomentRowsAt1684 : keyMomentRows (1684 : Fin 2886) =
    keyMomentRow1684 := by decide +kernel

theorem keyMomentRowsAt1685 : keyMomentRows (1685 : Fin 2886) =
    keyMomentRow1685 := by decide +kernel

theorem keyMomentRowsAt1686 : keyMomentRows (1686 : Fin 2886) =
    keyMomentRow1686 := by decide +kernel

theorem keyMomentRowsAt1687 : keyMomentRows (1687 : Fin 2886) =
    keyMomentRow1687 := by decide +kernel

theorem keyMomentRowsAt1688 : keyMomentRows (1688 : Fin 2886) =
    keyMomentRow1688 := by decide +kernel

theorem keyMomentRowsAt1689 : keyMomentRows (1689 : Fin 2886) =
    keyMomentRow1689 := by decide +kernel

theorem keyMomentRowsAt1690 : keyMomentRows (1690 : Fin 2886) =
    keyMomentRow1690 := by decide +kernel

theorem keyMomentRowsAt1691 : keyMomentRows (1691 : Fin 2886) =
    keyMomentRow1691 := by decide +kernel

theorem keyMomentRowsAt1692 : keyMomentRows (1692 : Fin 2886) =
    keyMomentRow1692 := by decide +kernel

theorem keyMomentRowsAt1693 : keyMomentRows (1693 : Fin 2886) =
    keyMomentRow1693 := by decide +kernel

theorem keyMomentRowsAt1694 : keyMomentRows (1694 : Fin 2886) =
    keyMomentRow1694 := by decide +kernel

theorem keyMomentRowsAt1695 : keyMomentRows (1695 : Fin 2886) =
    keyMomentRow1695 := by decide +kernel

theorem keyMomentChunkSound52_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 52) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 1664 ∨ k.val = 1665 ∨ k.val = 1666 ∨ k.val = 1667 ∨ k.val = 1668 ∨ k.val = 1669 ∨ k.val = 1670 ∨ k.val = 1671 ∨ k.val = 1672 ∨ k.val = 1673 ∨ k.val = 1674 ∨ k.val = 1675 ∨ k.val = 1676 ∨ k.val = 1677 ∨ k.val = 1678 ∨ k.val = 1679 ∨ k.val = 1680 ∨ k.val = 1681 ∨ k.val = 1682 ∨ k.val = 1683 ∨ k.val = 1684 ∨ k.val = 1685 ∨ k.val = 1686 ∨ k.val = 1687 ∨ k.val = 1688 ∨ k.val = 1689 ∨ k.val = 1690 ∨ k.val = 1691 ∨ k.val = 1692 ∨ k.val = 1693 ∨ k.val = 1694 ∨ k.val = 1695 := by omega
  rcases heq with h1664 | h1665 | h1666 | h1667 | h1668 | h1669 | h1670 | h1671 | h1672 | h1673 | h1674 | h1675 | h1676 | h1677 | h1678 | h1679 | h1680 | h1681 | h1682 | h1683 | h1684 | h1685 | h1686 | h1687 | h1688 | h1689 | h1690 | h1691 | h1692 | h1693 | h1694 | h1695
  · have he : k = (1664 : Fin 2886) := Fin.ext h1664
    subst k
    rw [keyMomentRowsAt1664]
    exact keyMoment1664 B hB
  · have he : k = (1665 : Fin 2886) := Fin.ext h1665
    subst k
    rw [keyMomentRowsAt1665]
    exact keyMoment1665 B hB
  · have he : k = (1666 : Fin 2886) := Fin.ext h1666
    subst k
    rw [keyMomentRowsAt1666]
    exact keyMoment1666 B hB
  · have he : k = (1667 : Fin 2886) := Fin.ext h1667
    subst k
    rw [keyMomentRowsAt1667]
    exact keyMoment1667 B hB
  · have he : k = (1668 : Fin 2886) := Fin.ext h1668
    subst k
    rw [keyMomentRowsAt1668]
    exact keyMoment1668 B hB
  · have he : k = (1669 : Fin 2886) := Fin.ext h1669
    subst k
    rw [keyMomentRowsAt1669]
    exact keyMoment1669 B hB
  · have he : k = (1670 : Fin 2886) := Fin.ext h1670
    subst k
    rw [keyMomentRowsAt1670]
    exact keyMoment1670 B hB
  · have he : k = (1671 : Fin 2886) := Fin.ext h1671
    subst k
    rw [keyMomentRowsAt1671]
    exact keyMoment1671 B hB
  · have he : k = (1672 : Fin 2886) := Fin.ext h1672
    subst k
    rw [keyMomentRowsAt1672]
    exact keyMoment1672 B hB
  · have he : k = (1673 : Fin 2886) := Fin.ext h1673
    subst k
    rw [keyMomentRowsAt1673]
    exact keyMoment1673 B hB
  · have he : k = (1674 : Fin 2886) := Fin.ext h1674
    subst k
    rw [keyMomentRowsAt1674]
    exact keyMoment1674 B hB
  · have he : k = (1675 : Fin 2886) := Fin.ext h1675
    subst k
    rw [keyMomentRowsAt1675]
    exact keyMoment1675 B hB
  · have he : k = (1676 : Fin 2886) := Fin.ext h1676
    subst k
    rw [keyMomentRowsAt1676]
    exact keyMoment1676 B hB
  · have he : k = (1677 : Fin 2886) := Fin.ext h1677
    subst k
    rw [keyMomentRowsAt1677]
    exact keyMoment1677 B hB
  · have he : k = (1678 : Fin 2886) := Fin.ext h1678
    subst k
    rw [keyMomentRowsAt1678]
    exact keyMoment1678 B hB
  · have he : k = (1679 : Fin 2886) := Fin.ext h1679
    subst k
    rw [keyMomentRowsAt1679]
    exact keyMoment1679 B hB
  · have he : k = (1680 : Fin 2886) := Fin.ext h1680
    subst k
    rw [keyMomentRowsAt1680]
    exact keyMoment1680 B hB
  · have he : k = (1681 : Fin 2886) := Fin.ext h1681
    subst k
    rw [keyMomentRowsAt1681]
    exact keyMoment1681 B hB
  · have he : k = (1682 : Fin 2886) := Fin.ext h1682
    subst k
    rw [keyMomentRowsAt1682]
    exact keyMoment1682 B hB
  · have he : k = (1683 : Fin 2886) := Fin.ext h1683
    subst k
    rw [keyMomentRowsAt1683]
    exact keyMoment1683 B hB
  · have he : k = (1684 : Fin 2886) := Fin.ext h1684
    subst k
    rw [keyMomentRowsAt1684]
    exact keyMoment1684 B hB
  · have he : k = (1685 : Fin 2886) := Fin.ext h1685
    subst k
    rw [keyMomentRowsAt1685]
    exact keyMoment1685 B hB
  · have he : k = (1686 : Fin 2886) := Fin.ext h1686
    subst k
    rw [keyMomentRowsAt1686]
    exact keyMoment1686 B hB
  · have he : k = (1687 : Fin 2886) := Fin.ext h1687
    subst k
    rw [keyMomentRowsAt1687]
    exact keyMoment1687 B hB
  · have he : k = (1688 : Fin 2886) := Fin.ext h1688
    subst k
    rw [keyMomentRowsAt1688]
    exact keyMoment1688 B hB
  · have he : k = (1689 : Fin 2886) := Fin.ext h1689
    subst k
    rw [keyMomentRowsAt1689]
    exact keyMoment1689 B hB
  · have he : k = (1690 : Fin 2886) := Fin.ext h1690
    subst k
    rw [keyMomentRowsAt1690]
    exact keyMoment1690 B hB
  · have he : k = (1691 : Fin 2886) := Fin.ext h1691
    subst k
    rw [keyMomentRowsAt1691]
    exact keyMoment1691 B hB
  · have he : k = (1692 : Fin 2886) := Fin.ext h1692
    subst k
    rw [keyMomentRowsAt1692]
    exact keyMoment1692 B hB
  · have he : k = (1693 : Fin 2886) := Fin.ext h1693
    subst k
    rw [keyMomentRowsAt1693]
    exact keyMoment1693 B hB
  · have he : k = (1694 : Fin 2886) := Fin.ext h1694
    subst k
    rw [keyMomentRowsAt1694]
    exact keyMoment1694 B hB
  · have he : k = (1695 : Fin 2886) := Fin.ext h1695
    subst k
    rw [keyMomentRowsAt1695]
    exact keyMoment1695 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound52_e_oai
