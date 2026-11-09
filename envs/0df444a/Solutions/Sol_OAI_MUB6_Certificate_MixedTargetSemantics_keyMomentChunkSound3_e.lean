-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:51:01.461205+00:00
-- url     : https://prove2.me/submissions/225ad8cf-a6cd-41b3-a81c-f420be046087

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E110
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical308
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39546 raw39546Labels = mixedMoment B node256 node256Labels := by
  calc
    mixedMoment B raw39546 raw39546Labels = mixedMoment B raw39546step0 raw39546step0Labels := by
      have hz : ∀ j, raw39546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39546step0 = (fun i j => raw39546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39546step0 raw39546; decide +kernel
      have hl : raw39546step0Labels = raw39546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39546 raw39546Labels permutation434 hz
    mixedMoment B raw39546step0 raw39546step0Labels = mixedMoment B raw39546step1 raw39546step1Labels := by
      have hz : ∀ j, raw39546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39546step1 = (fun i j => raw39546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39546step1 raw39546step0; decide +kernel
      have hl : raw39546step1Labels = raw39546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39546step0 raw39546step0Labels permutation80 hz
    mixedMoment B raw39546step1 raw39546step1Labels = mixedMoment B raw39546step2 raw39546step2Labels := by
      have ha : raw39546step2 = (fun i j => raw39546step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39546step2 raw39546step1; decide +kernel
      have hl : raw39546step2Labels = raw39546step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39546step1 raw39546step1Labels permutation12 permutation7
    mixedMoment B raw39546step2 raw39546step2Labels = mixedMoment B raw39546step3 raw39546step3Labels := by
      have ha : raw39546step3 = -raw39546step2 := by apply Matrix.ext; change ∀ i j, raw39546step3 i j = -(raw39546step2 i j); unfold raw39546step3 raw39546step2; decide +kernel
      have hl : raw39546step3Labels = raw39546step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node256 node256Labels := by rfl

theorem canonical39547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39547 raw39547Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39547 raw39547Labels = mixedMoment B raw39547step0 raw39547step0Labels := by
      have hz : ∀ j, raw39547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39547step0 = (fun i j => raw39547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39547step0 raw39547; decide +kernel
      have hl : raw39547step0Labels = raw39547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39547 raw39547Labels permutation434 hz
    mixedMoment B raw39547step0 raw39547step0Labels = mixedMoment B raw39547step1 raw39547step1Labels := by
      have hz : ∀ j, raw39547step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39547step1 = (fun i j => raw39547step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39547step1 raw39547step0; decide +kernel
      have hl : raw39547step1Labels = raw39547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39547step0 raw39547step0Labels permutation80 hz
    mixedMoment B raw39547step1 raw39547step1Labels = mixedMoment B raw39547step2 raw39547step2Labels := by
      have ha : raw39547step2 = (fun i j => raw39547step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39547step2 raw39547step1; decide +kernel
      have hl : raw39547step2Labels = raw39547step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39547step1 raw39547step1Labels permutation11 permutation7
    mixedMoment B raw39547step2 raw39547step2Labels = mixedMoment B raw39547step3 raw39547step3Labels := by
      have ha : raw39547step3 = -raw39547step2 := by apply Matrix.ext; change ∀ i j, raw39547step3 i j = -(raw39547step2 i j); unfold raw39547step3 raw39547step2; decide +kernel
      have hl : raw39547step3Labels = raw39547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

theorem canonical39548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39548 raw39548Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw39548 raw39548Labels = mixedMoment B raw39548step0 raw39548step0Labels := by
      have hz : ∀ j, raw39548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39548step0 = (fun i j => raw39548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39548step0 raw39548; decide +kernel
      have hl : raw39548step0Labels = raw39548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39548 raw39548Labels permutation434 hz
    mixedMoment B raw39548step0 raw39548step0Labels = mixedMoment B raw39548step1 raw39548step1Labels := by
      have hz : ∀ j, raw39548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39548step1 = (fun i j => raw39548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39548step1 raw39548step0; decide +kernel
      have hl : raw39548step1Labels = raw39548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39548step0 raw39548step0Labels permutation80 hz
    mixedMoment B raw39548step1 raw39548step1Labels = mixedMoment B raw39548step2 raw39548step2Labels := by
      have ha : raw39548step2 = (fun i j => raw39548step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39548step2 raw39548step1; decide +kernel
      have hl : raw39548step2Labels = raw39548step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39548step1 raw39548step1Labels permutation10 permutation7
    mixedMoment B raw39548step2 raw39548step2Labels = mixedMoment B raw39548step3 raw39548step3Labels := by
      have ha : raw39548step3 = -raw39548step2 := by apply Matrix.ext; change ∀ i j, raw39548step3 i j = -(raw39548step2 i j); unfold raw39548step3 raw39548step2; decide +kernel
      have hl : raw39548step3Labels = raw39548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node251 node251Labels := by rfl

theorem canonical39549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39549 raw39549Labels = mixedMoment B node196 node196Labels := by
  calc
    mixedMoment B raw39549 raw39549Labels = mixedMoment B raw39549step0 raw39549step0Labels := by
      have hz : ∀ j, raw39549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39549step0 = (fun i j => raw39549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39549step0 raw39549; decide +kernel
      have hl : raw39549step0Labels = raw39549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39549 raw39549Labels permutation434 hz
    mixedMoment B raw39549step0 raw39549step0Labels = mixedMoment B raw39549step1 raw39549step1Labels := by
      have hz : ∀ j, raw39549step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39549step1 = (fun i j => raw39549step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39549step1 raw39549step0; decide +kernel
      have hl : raw39549step1Labels = raw39549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39549step0 raw39549step0Labels permutation80 hz
    mixedMoment B raw39549step1 raw39549step1Labels = mixedMoment B raw39549step2 raw39549step2Labels := by
      have ha : raw39549step2 = (fun i j => raw39549step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39549step2 raw39549step1; decide +kernel
      have hl : raw39549step2Labels = raw39549step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39549step1 raw39549step1Labels permutation10 permutation7
    mixedMoment B raw39549step2 raw39549step2Labels = mixedMoment B raw39549step3 raw39549step3Labels := by
      have ha : raw39549step3 = -raw39549step2 := by apply Matrix.ext; change ∀ i j, raw39549step3 i j = -(raw39549step2 i j); unfold raw39549step3 raw39549step2; decide +kernel
      have hl : raw39549step3Labels = raw39549step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node196 node196Labels := by rfl

theorem canonical39550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39550 raw39550Labels = mixedMoment B node229 node229Labels := by
  calc
    mixedMoment B raw39550 raw39550Labels = mixedMoment B raw39550step0 raw39550step0Labels := by
      have hz : ∀ j, raw39550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39550step0 = (fun i j => raw39550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39550step0 raw39550; decide +kernel
      have hl : raw39550step0Labels = raw39550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39550 raw39550Labels permutation346 hz
    mixedMoment B raw39550step0 raw39550step0Labels = mixedMoment B raw39550step1 raw39550step1Labels := by
      have ha : raw39550step1 = (fun i j => raw39550step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39550step1 raw39550step0; decide +kernel
      have hl : raw39550step1Labels = raw39550step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39550step0 raw39550step0Labels permutation42 permutation7
    mixedMoment B raw39550step1 raw39550step1Labels = mixedMoment B raw39550step2 raw39550step2Labels := by
      have ha : raw39550step2 = -raw39550step1 := by apply Matrix.ext; change ∀ i j, raw39550step2 i j = -(raw39550step1 i j); unfold raw39550step2 raw39550step1; decide +kernel
      have hl : raw39550step2Labels = raw39550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node229 node229Labels := by rfl

theorem canonical39551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39551 raw39551Labels = mixedMoment B node214 node214Labels := by
  calc
    mixedMoment B raw39551 raw39551Labels = mixedMoment B raw39551step0 raw39551step0Labels := by
      have hz : ∀ j, raw39551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39551step0 = (fun i j => raw39551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39551step0 raw39551; decide +kernel
      have hl : raw39551step0Labels = raw39551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39551 raw39551Labels permutation346 hz
    mixedMoment B raw39551step0 raw39551step0Labels = mixedMoment B raw39551step1 raw39551step1Labels := by
      have ha : raw39551step1 = (fun i j => raw39551step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39551step1 raw39551step0; decide +kernel
      have hl : raw39551step1Labels = raw39551step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39551step0 raw39551step0Labels permutation40 permutation7
    mixedMoment B raw39551step1 raw39551step1Labels = mixedMoment B raw39551step2 raw39551step2Labels := by
      have ha : raw39551step2 = -raw39551step1 := by apply Matrix.ext; change ∀ i j, raw39551step2 i j = -(raw39551step1 i j); unfold raw39551step2 raw39551step1; decide +kernel
      have hl : raw39551step2Labels = raw39551step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node214 node214Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical309
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical39552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39552 raw39552Labels = mixedMoment B node168 node168Labels := by
  calc
    mixedMoment B raw39552 raw39552Labels = mixedMoment B raw39552step0 raw39552step0Labels := by
      have hz : ∀ j, raw39552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39552step0 = (fun i j => raw39552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39552step0 raw39552; decide +kernel
      have hl : raw39552step0Labels = raw39552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39552 raw39552Labels permutation346 hz
    mixedMoment B raw39552step0 raw39552step0Labels = mixedMoment B raw39552step1 raw39552step1Labels := by
      have ha : raw39552step1 = (fun i j => raw39552step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39552step1 raw39552step0; decide +kernel
      have hl : raw39552step1Labels = raw39552step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39552step0 raw39552step0Labels permutation40 permutation7
    mixedMoment B raw39552step1 raw39552step1Labels = mixedMoment B raw39552step2 raw39552step2Labels := by
      have ha : raw39552step2 = -raw39552step1 := by apply Matrix.ext; change ∀ i j, raw39552step2 i j = -(raw39552step1 i j); unfold raw39552step2 raw39552step1; decide +kernel
      have hl : raw39552step2Labels = raw39552step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node168 node168Labels := by rfl

theorem canonical39553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39553 raw39553Labels = mixedMoment B node195 node195Labels := by
  calc
    mixedMoment B raw39553 raw39553Labels = mixedMoment B raw39553step0 raw39553step0Labels := by
      have hz : ∀ j, raw39553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39553step0 = (fun i j => raw39553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39553step0 raw39553; decide +kernel
      have hl : raw39553step0Labels = raw39553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39553 raw39553Labels permutation346 hz
    mixedMoment B raw39553step0 raw39553step0Labels = mixedMoment B raw39553step1 raw39553step1Labels := by
      have ha : raw39553step1 = (fun i j => raw39553step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39553step1 raw39553step0; decide +kernel
      have hl : raw39553step1Labels = raw39553step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39553step0 raw39553step0Labels permutation54 permutation7
    mixedMoment B raw39553step1 raw39553step1Labels = mixedMoment B raw39553step2 raw39553step2Labels := by
      have ha : raw39553step2 = -raw39553step1 := by apply Matrix.ext; change ∀ i j, raw39553step2 i j = -(raw39553step1 i j); unfold raw39553step2 raw39553step1; decide +kernel
      have hl : raw39553step2Labels = raw39553step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node195 node195Labels := by rfl

theorem canonical39554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39554 raw39554Labels = mixedMoment B node240 node240Labels := by
  calc
    mixedMoment B raw39554 raw39554Labels = mixedMoment B raw39554step0 raw39554step0Labels := by
      have hz : ∀ j, raw39554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39554step0 = (fun i j => raw39554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39554step0 raw39554; decide +kernel
      have hl : raw39554step0Labels = raw39554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39554 raw39554Labels permutation346 hz
    mixedMoment B raw39554step0 raw39554step0Labels = mixedMoment B raw39554step1 raw39554step1Labels := by
      have ha : raw39554step1 = (fun i j => raw39554step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39554step1 raw39554step0; decide +kernel
      have hl : raw39554step1Labels = raw39554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39554step0 raw39554step0Labels permutation54 permutation7
    mixedMoment B raw39554step1 raw39554step1Labels = mixedMoment B raw39554step2 raw39554step2Labels := by
      have ha : raw39554step2 = -raw39554step1 := by apply Matrix.ext; change ∀ i j, raw39554step2 i j = -(raw39554step1 i j); unfold raw39554step2 raw39554step1; decide +kernel
      have hl : raw39554step2Labels = raw39554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node240 node240Labels := by rfl

theorem canonical39555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39555 raw39555Labels = mixedMoment B node248 node248Labels := by
  calc
    mixedMoment B raw39555 raw39555Labels = mixedMoment B raw39555step0 raw39555step0Labels := by
      have hz : ∀ j, raw39555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39555step0 = (fun i j => raw39555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39555step0 raw39555; decide +kernel
      have hl : raw39555step0Labels = raw39555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39555 raw39555Labels permutation346 hz
    mixedMoment B raw39555step0 raw39555step0Labels = mixedMoment B raw39555step1 raw39555step1Labels := by
      have ha : raw39555step1 = (fun i j => raw39555step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39555step1 raw39555step0; decide +kernel
      have hl : raw39555step1Labels = raw39555step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39555step0 raw39555step0Labels permutation53 permutation7
    mixedMoment B raw39555step1 raw39555step1Labels = mixedMoment B raw39555step2 raw39555step2Labels := by
      have ha : raw39555step2 = -raw39555step1 := by apply Matrix.ext; change ∀ i j, raw39555step2 i j = -(raw39555step1 i j); unfold raw39555step2 raw39555step1; decide +kernel
      have hl : raw39555step2Labels = raw39555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node248 node248Labels := by rfl

theorem canonical39556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39556 raw39556Labels = mixedMoment B node213 node213Labels := by
  calc
    mixedMoment B raw39556 raw39556Labels = mixedMoment B raw39556step0 raw39556step0Labels := by
      have ha : raw39556step0 = (fun i j => raw39556 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39556step0 raw39556; decide +kernel
      have hl : raw39556step0Labels = raw39556Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39556 raw39556Labels permutation198 permutation7
    mixedMoment B raw39556step0 raw39556step0Labels = mixedMoment B raw39556step1 raw39556step1Labels := by
      have ha : raw39556step1 = -raw39556step0 := by apply Matrix.ext; change ∀ i j, raw39556step1 i j = -(raw39556step0 i j); unfold raw39556step1 raw39556step0; decide +kernel
      have hl : raw39556step1Labels = raw39556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node213 node213Labels := by rfl

theorem canonical39557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39557 raw39557Labels = mixedMoment B node167 node167Labels := by
  calc
    mixedMoment B raw39557 raw39557Labels = mixedMoment B raw39557step0 raw39557step0Labels := by
      have ha : raw39557step0 = (fun i j => raw39557 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39557step0 raw39557; decide +kernel
      have hl : raw39557step0Labels = raw39557Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39557 raw39557Labels permutation198 permutation7
    mixedMoment B raw39557step0 raw39557step0Labels = mixedMoment B raw39557step1 raw39557step1Labels := by
      have ha : raw39557step1 = -raw39557step0 := by apply Matrix.ext; change ∀ i j, raw39557step1 i j = -(raw39557step0 i j); unfold raw39557step1 raw39557step0; decide +kernel
      have hl : raw39557step1Labels = raw39557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node167 node167Labels := by rfl

theorem canonical39558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39558 raw39558Labels = mixedMoment B node253 node253Labels := by
  calc
    mixedMoment B raw39558 raw39558Labels = mixedMoment B raw39558step0 raw39558step0Labels := by
      have ha : raw39558step0 = (fun i j => raw39558 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39558step0 raw39558; decide +kernel
      have hl : raw39558step0Labels = raw39558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39558 raw39558Labels permutation246 permutation7
    mixedMoment B raw39558step0 raw39558step0Labels = mixedMoment B raw39558step1 raw39558step1Labels := by
      have ha : raw39558step1 = -raw39558step0 := by apply Matrix.ext; change ∀ i j, raw39558step1 i j = -(raw39558step0 i j); unfold raw39558step1 raw39558step0; decide +kernel
      have hl : raw39558step1Labels = raw39558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node253 node253Labels := by rfl

theorem canonical39559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39559 raw39559Labels = mixedMoment B node257 node257Labels := by
  calc
    _ = mixedMoment B node257 node257Labels := by rfl

theorem canonical39560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39560 raw39560Labels = mixedMoment B node189 node189Labels := by
  calc
    mixedMoment B raw39560 raw39560Labels = mixedMoment B raw39560step0 raw39560step0Labels := by
      have ha : raw39560step0 = (fun i j => raw39560 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39560step0 raw39560; decide +kernel
      have hl : raw39560step0Labels = raw39560Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39560 raw39560Labels permutation224 permutation7
    mixedMoment B raw39560step0 raw39560step0Labels = mixedMoment B raw39560step1 raw39560step1Labels := by
      have ha : raw39560step1 = -raw39560step0 := by apply Matrix.ext; change ∀ i j, raw39560step1 i j = -(raw39560step0 i j); unfold raw39560step1 raw39560step0; decide +kernel
      have hl : raw39560step1Labels = raw39560step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node189 node189Labels := by rfl

theorem canonical39561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39561 raw39561Labels = mixedMoment B node254 node254Labels := by
  calc
    mixedMoment B raw39561 raw39561Labels = mixedMoment B raw39561step0 raw39561step0Labels := by
      have hz : ∀ j, raw39561 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39561step0 = (fun i j => raw39561 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39561step0 raw39561; decide +kernel
      have hl : raw39561step0Labels = raw39561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39561 raw39561Labels permutation434 hz
    mixedMoment B raw39561step0 raw39561step0Labels = mixedMoment B raw39561step1 raw39561step1Labels := by
      have ha : raw39561step1 = (fun i j => raw39561step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39561step1 raw39561step0; decide +kernel
      have hl : raw39561step1Labels = raw39561step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39561step0 raw39561step0Labels permutation50 permutation7
    mixedMoment B raw39561step1 raw39561step1Labels = mixedMoment B raw39561step2 raw39561step2Labels := by
      have ha : raw39561step2 = -raw39561step1 := by apply Matrix.ext; change ∀ i j, raw39561step2 i j = -(raw39561step1 i j); unfold raw39561step2 raw39561step1; decide +kernel
      have hl : raw39561step2Labels = raw39561step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node254 node254Labels := by rfl

theorem canonical39562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39562 raw39562Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw39562 raw39562Labels = mixedMoment B raw39562step0 raw39562step0Labels := by
      have hz : ∀ j, raw39562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39562step0 = (fun i j => raw39562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39562step0 raw39562; decide +kernel
      have hl : raw39562step0Labels = raw39562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39562 raw39562Labels permutation434 hz
    _ = mixedMoment B node260 node260Labels := by rfl

theorem canonical39563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39563 raw39563Labels = mixedMoment B node190 node190Labels := by
  calc
    mixedMoment B raw39563 raw39563Labels = mixedMoment B raw39563step0 raw39563step0Labels := by
      have hz : ∀ j, raw39563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39563step0 = (fun i j => raw39563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39563step0 raw39563; decide +kernel
      have hl : raw39563step0Labels = raw39563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39563 raw39563Labels permutation434 hz
    mixedMoment B raw39563step0 raw39563step0Labels = mixedMoment B raw39563step1 raw39563step1Labels := by
      have ha : raw39563step1 = (fun i j => raw39563step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39563step1 raw39563step0; decide +kernel
      have hl : raw39563step1Labels = raw39563step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39563step0 raw39563step0Labels permutation44 permutation7
    mixedMoment B raw39563step1 raw39563step1Labels = mixedMoment B raw39563step2 raw39563step2Labels := by
      have ha : raw39563step2 = -raw39563step1 := by apply Matrix.ext; change ∀ i j, raw39563step2 i j = -(raw39563step1 i j); unfold raw39563step2 raw39563step1; decide +kernel
      have hl : raw39563step2Labels = raw39563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node190 node190Labels := by rfl

theorem canonical39564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39564 raw39564Labels = mixedMoment B node220 node220Labels := by
  calc
    mixedMoment B raw39564 raw39564Labels = mixedMoment B raw39564step0 raw39564step0Labels := by
      have ha : raw39564step0 = (fun i j => raw39564 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39564step0 raw39564; decide +kernel
      have hl : raw39564step0Labels = raw39564Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39564 raw39564Labels permutation212 permutation7
    mixedMoment B raw39564step0 raw39564step0Labels = mixedMoment B raw39564step1 raw39564step1Labels := by
      have ha : raw39564step1 = -raw39564step0 := by apply Matrix.ext; change ∀ i j, raw39564step1 i j = -(raw39564step0 i j); unfold raw39564step1 raw39564step0; decide +kernel
      have hl : raw39564step1Labels = raw39564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node220 node220Labels := by rfl

theorem canonical39565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39565 raw39565Labels = mixedMoment B node163 node163Labels := by
  calc
    mixedMoment B raw39565 raw39565Labels = mixedMoment B raw39565step0 raw39565step0Labels := by
      have ha : raw39565step0 = (fun i j => raw39565 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39565step0 raw39565; decide +kernel
      have hl : raw39565step0Labels = raw39565Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39565 raw39565Labels permutation212 permutation7
    mixedMoment B raw39565step0 raw39565step0Labels = mixedMoment B raw39565step1 raw39565step1Labels := by
      have ha : raw39565step1 = -raw39565step0 := by apply Matrix.ext; change ∀ i j, raw39565step1 i j = -(raw39565step0 i j); unfold raw39565step1 raw39565step0; decide +kernel
      have hl : raw39565step1Labels = raw39565step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node163 node163Labels := by rfl

theorem canonical39566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39566 raw39566Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw39566 raw39566Labels = mixedMoment B raw39566step0 raw39566step0Labels := by
      have ha : raw39566step0 = (fun i j => raw39566 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39566step0 raw39566; decide +kernel
      have hl : raw39566step0Labels = raw39566Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39566 raw39566Labels permutation155 permutation2
    _ = mixedMoment B node259 node259Labels := by rfl

theorem canonical39567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39567 raw39567Labels = mixedMoment B node255 node255Labels := by
  calc
    mixedMoment B raw39567 raw39567Labels = mixedMoment B raw39567step0 raw39567step0Labels := by
      have hz : ∀ j, raw39567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39567step0 = (fun i j => raw39567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39567step0 raw39567; decide +kernel
      have hl : raw39567step0Labels = raw39567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39567 raw39567Labels permutation434 hz
    mixedMoment B raw39567step0 raw39567step0Labels = mixedMoment B raw39567step1 raw39567step1Labels := by
      have hz : ∀ j, raw39567step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39567step1 = (fun i j => raw39567step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39567step1 raw39567step0; decide +kernel
      have hl : raw39567step1Labels = raw39567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39567step0 raw39567step0Labels permutation80 hz
    mixedMoment B raw39567step1 raw39567step1Labels = mixedMoment B raw39567step2 raw39567step2Labels := by
      have ha : raw39567step2 = (fun i j => raw39567step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39567step2 raw39567step1; decide +kernel
      have hl : raw39567step2Labels = raw39567step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39567step1 raw39567step1Labels permutation12 permutation7
    mixedMoment B raw39567step2 raw39567step2Labels = mixedMoment B raw39567step3 raw39567step3Labels := by
      have ha : raw39567step3 = -raw39567step2 := by apply Matrix.ext; change ∀ i j, raw39567step3 i j = -(raw39567step2 i j); unfold raw39567step3 raw39567step2; decide +kernel
      have hl : raw39567step3Labels = raw39567step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node255 node255Labels := by rfl

theorem canonical39568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39568 raw39568Labels = mixedMoment B node134 node134Labels := by
  calc
    mixedMoment B raw39568 raw39568Labels = mixedMoment B raw39568step0 raw39568step0Labels := by
      have hz : ∀ j, raw39568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39568step0 = (fun i j => raw39568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39568step0 raw39568; decide +kernel
      have hl : raw39568step0Labels = raw39568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39568 raw39568Labels permutation434 hz
    mixedMoment B raw39568step0 raw39568step0Labels = mixedMoment B raw39568step1 raw39568step1Labels := by
      have hz : ∀ j, raw39568step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39568step1 = (fun i j => raw39568step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39568step1 raw39568step0; decide +kernel
      have hl : raw39568step1Labels = raw39568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39568step0 raw39568step0Labels permutation80 hz
    mixedMoment B raw39568step1 raw39568step1Labels = mixedMoment B raw39568step2 raw39568step2Labels := by
      have ha : raw39568step2 = (fun i j => raw39568step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39568step2 raw39568step1; decide +kernel
      have hl : raw39568step2Labels = raw39568step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39568step1 raw39568step1Labels permutation29 permutation6
    _ = mixedMoment B node134 node134Labels := by rfl

theorem canonical39569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39569 raw39569Labels = mixedMoment B node5503 node5503Labels := by
  calc
    mixedMoment B raw39569 raw39569Labels = mixedMoment B raw39569step0 raw39569step0Labels := by
      have hz : ∀ j, raw39569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39569step0 = (fun i j => raw39569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39569step0 raw39569; decide +kernel
      have hl : raw39569step0Labels = raw39569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39569 raw39569Labels permutation346 hz
    mixedMoment B raw39569step0 raw39569step0Labels = mixedMoment B raw39569step1 raw39569step1Labels := by
      have ha : raw39569step1 = (fun i j => raw39569step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39569step1 raw39569step0; decide +kernel
      have hl : raw39569step1Labels = raw39569step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39569step0 raw39569step0Labels permutation42 permutation7
    mixedMoment B raw39569step1 raw39569step1Labels = mixedMoment B raw39569step2 raw39569step2Labels := by
      have ha : raw39569step2 = -raw39569step1 := by apply Matrix.ext; change ∀ i j, raw39569step2 i j = -(raw39569step1 i j); unfold raw39569step2 raw39569step1; decide +kernel
      have hl : raw39569step2Labels = raw39569step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5503 node5503Labels := by rfl

theorem canonical39570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39570 raw39570Labels = mixedMoment B node222 node222Labels := by
  calc
    mixedMoment B raw39570 raw39570Labels = mixedMoment B raw39570step0 raw39570step0Labels := by
      have hz : ∀ j, raw39570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39570step0 = (fun i j => raw39570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39570step0 raw39570; decide +kernel
      have hl : raw39570step0Labels = raw39570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39570 raw39570Labels permutation346 hz
    mixedMoment B raw39570step0 raw39570step0Labels = mixedMoment B raw39570step1 raw39570step1Labels := by
      have ha : raw39570step1 = (fun i j => raw39570step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39570step1 raw39570step0; decide +kernel
      have hl : raw39570step1Labels = raw39570step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39570step0 raw39570step0Labels permutation40 permutation7
    mixedMoment B raw39570step1 raw39570step1Labels = mixedMoment B raw39570step2 raw39570step2Labels := by
      have ha : raw39570step2 = -raw39570step1 := by apply Matrix.ext; change ∀ i j, raw39570step2 i j = -(raw39570step1 i j); unfold raw39570step2 raw39570step1; decide +kernel
      have hl : raw39570step2Labels = raw39570step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node222 node222Labels := by rfl

theorem canonical39571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39571 raw39571Labels = mixedMoment B node117 node117Labels := by
  calc
    mixedMoment B raw39571 raw39571Labels = mixedMoment B raw39571step0 raw39571step0Labels := by
      have hz : ∀ j, raw39571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39571step0 = (fun i j => raw39571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39571step0 raw39571; decide +kernel
      have hl : raw39571step0Labels = raw39571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39571 raw39571Labels permutation346 hz
    mixedMoment B raw39571step0 raw39571step0Labels = mixedMoment B raw39571step1 raw39571step1Labels := by
      have ha : raw39571step1 = (fun i j => raw39571step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39571step1 raw39571step0; decide +kernel
      have hl : raw39571step1Labels = raw39571step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39571step0 raw39571step0Labels permutation139 permutation6
    _ = mixedMoment B node117 node117Labels := by rfl

theorem canonical39572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39572 raw39572Labels = mixedMoment B node192 node192Labels := by
  calc
    mixedMoment B raw39572 raw39572Labels = mixedMoment B raw39572step0 raw39572step0Labels := by
      have hz : ∀ j, raw39572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39572step0 = (fun i j => raw39572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39572step0 raw39572; decide +kernel
      have hl : raw39572step0Labels = raw39572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39572 raw39572Labels permutation346 hz
    mixedMoment B raw39572step0 raw39572step0Labels = mixedMoment B raw39572step1 raw39572step1Labels := by
      have ha : raw39572step1 = (fun i j => raw39572step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39572step1 raw39572step0; decide +kernel
      have hl : raw39572step1Labels = raw39572step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39572step0 raw39572step0Labels permutation51 permutation7
    mixedMoment B raw39572step1 raw39572step1Labels = mixedMoment B raw39572step2 raw39572step2Labels := by
      have ha : raw39572step2 = -raw39572step1 := by apply Matrix.ext; change ∀ i j, raw39572step2 i j = -(raw39572step1 i j); unfold raw39572step2 raw39572step1; decide +kernel
      have hl : raw39572step2Labels = raw39572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node192 node192Labels := by rfl

theorem canonical39573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39573 raw39573Labels = mixedMoment B node239 node239Labels := by
  calc
    mixedMoment B raw39573 raw39573Labels = mixedMoment B raw39573step0 raw39573step0Labels := by
      have hz : ∀ j, raw39573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39573step0 = (fun i j => raw39573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39573step0 raw39573; decide +kernel
      have hl : raw39573step0Labels = raw39573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39573 raw39573Labels permutation346 hz
    mixedMoment B raw39573step0 raw39573step0Labels = mixedMoment B raw39573step1 raw39573step1Labels := by
      have ha : raw39573step1 = (fun i j => raw39573step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39573step1 raw39573step0; decide +kernel
      have hl : raw39573step1Labels = raw39573step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39573step0 raw39573step0Labels permutation54 permutation7
    mixedMoment B raw39573step1 raw39573step1Labels = mixedMoment B raw39573step2 raw39573step2Labels := by
      have ha : raw39573step2 = -raw39573step1 := by apply Matrix.ext; change ∀ i j, raw39573step2 i j = -(raw39573step1 i j); unfold raw39573step2 raw39573step1; decide +kernel
      have hl : raw39573step2Labels = raw39573step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node239 node239Labels := by rfl

theorem canonical39574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39574 raw39574Labels = mixedMoment B node260 node260Labels := by
  calc
    mixedMoment B raw39574 raw39574Labels = mixedMoment B raw39574step0 raw39574step0Labels := by
      have hz : ∀ j, raw39574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39574step0 = (fun i j => raw39574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39574step0 raw39574; decide +kernel
      have hl : raw39574step0Labels = raw39574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39574 raw39574Labels permutation346 hz
    mixedMoment B raw39574step0 raw39574step0Labels = mixedMoment B raw39574step1 raw39574step1Labels := by
      have ha : raw39574step1 = (fun i j => raw39574step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39574step1 raw39574step0; decide +kernel
      have hl : raw39574step1Labels = raw39574step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39574step0 raw39574step0Labels permutation48 permutation7
    mixedMoment B raw39574step1 raw39574step1Labels = mixedMoment B raw39574step2 raw39574step2Labels := by
      have ha : raw39574step2 = -raw39574step1 := by apply Matrix.ext; change ∀ i j, raw39574step2 i j = -(raw39574step1 i j); unfold raw39574step2 raw39574step1; decide +kernel
      have hl : raw39574step2Labels = raw39574step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node260 node260Labels := by rfl

theorem canonical39575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39575 raw39575Labels = mixedMoment B node212 node212Labels := by
  calc
    mixedMoment B raw39575 raw39575Labels = mixedMoment B raw39575step0 raw39575step0Labels := by
      have ha : raw39575step0 = (fun i j => raw39575 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39575step0 raw39575; decide +kernel
      have hl : raw39575step0Labels = raw39575Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39575 raw39575Labels permutation195 permutation7
    mixedMoment B raw39575step0 raw39575step0Labels = mixedMoment B raw39575step1 raw39575step1Labels := by
      have ha : raw39575step1 = -raw39575step0 := by apply Matrix.ext; change ∀ i j, raw39575step1 i j = -(raw39575step0 i j); unfold raw39575step1 raw39575step0; decide +kernel
      have hl : raw39575step1Labels = raw39575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node212 node212Labels := by rfl

theorem canonical39576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39576 raw39576Labels = mixedMoment B node221 node221Labels := by
  calc
    mixedMoment B raw39576 raw39576Labels = mixedMoment B raw39576step0 raw39576step0Labels := by
      have ha : raw39576step0 = (fun i j => raw39576 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39576step0 raw39576; decide +kernel
      have hl : raw39576step0Labels = raw39576Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39576 raw39576Labels permutation195 permutation7
    mixedMoment B raw39576step0 raw39576step0Labels = mixedMoment B raw39576step1 raw39576step1Labels := by
      have ha : raw39576step1 = -raw39576step0 := by apply Matrix.ext; change ∀ i j, raw39576step1 i j = -(raw39576step0 i j); unfold raw39576step1 raw39576step0; decide +kernel
      have hl : raw39576step1Labels = raw39576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node221 node221Labels := by rfl

theorem canonical39577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39577 raw39577Labels = mixedMoment B node164 node164Labels := by
  calc
    mixedMoment B raw39577 raw39577Labels = mixedMoment B raw39577step0 raw39577step0Labels := by
      have ha : raw39577step0 = (fun i j => raw39577 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39577step0 raw39577; decide +kernel
      have hl : raw39577step0Labels = raw39577Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39577 raw39577Labels permutation195 permutation7
    mixedMoment B raw39577step0 raw39577step0Labels = mixedMoment B raw39577step1 raw39577step1Labels := by
      have ha : raw39577step1 = -raw39577step0 := by apply Matrix.ext; change ∀ i j, raw39577step1 i j = -(raw39577step0 i j); unfold raw39577step1 raw39577step0; decide +kernel
      have hl : raw39577step1Labels = raw39577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node164 node164Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment96 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 96) =
      Integer.Sparse.eval keyMomentRow96 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 96).leftCharge (GramAssembly.key 96).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 256) := by
    have ha : gramCharges (GramAssembly.key 96).leftCharge (GramAssembly.key 96).rightCharge = raw39546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39546 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 96).leftCharge (GramAssembly.key 96).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow96, Integer.Sparse.eval]

theorem keyMoment97 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 97) =
      Integer.Sparse.eval keyMomentRow97 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 97).leftCharge (GramAssembly.key 97).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 268) := by
    have ha : gramCharges (GramAssembly.key 97).leftCharge (GramAssembly.key 97).rightCharge = raw39547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39547 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 97).leftCharge (GramAssembly.key 97).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow97, Integer.Sparse.eval]

theorem keyMoment98 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 98) =
      Integer.Sparse.eval keyMomentRow98 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 98).leftCharge (GramAssembly.key 98).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 251) := by
    have ha : gramCharges (GramAssembly.key 98).leftCharge (GramAssembly.key 98).rightCharge = raw39548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39548 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 98).leftCharge (GramAssembly.key 98).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow98, Integer.Sparse.eval]

theorem keyMoment99 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 99) =
      Integer.Sparse.eval keyMomentRow99 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 99).leftCharge (GramAssembly.key 99).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 196) := by
    have ha : gramCharges (GramAssembly.key 99).leftCharge (GramAssembly.key 99).rightCharge = raw39549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39549 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 99).leftCharge (GramAssembly.key 99).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow99, Integer.Sparse.eval]

theorem keyMoment100 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 100) =
      Integer.Sparse.eval keyMomentRow100 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 100).leftCharge (GramAssembly.key 100).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 229) := by
    have ha : gramCharges (GramAssembly.key 100).leftCharge (GramAssembly.key 100).rightCharge = raw39550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39550 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 100).leftCharge (GramAssembly.key 100).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow100, Integer.Sparse.eval]

theorem keyMoment101 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 101) =
      Integer.Sparse.eval keyMomentRow101 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 101).leftCharge (GramAssembly.key 101).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 214) := by
    have ha : gramCharges (GramAssembly.key 101).leftCharge (GramAssembly.key 101).rightCharge = raw39551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39551 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 101).leftCharge (GramAssembly.key 101).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow101, Integer.Sparse.eval]

theorem keyMoment102 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 102) =
      Integer.Sparse.eval keyMomentRow102 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 102).leftCharge (GramAssembly.key 102).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 168) := by
    have ha : gramCharges (GramAssembly.key 102).leftCharge (GramAssembly.key 102).rightCharge = raw39552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39552 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 102).leftCharge (GramAssembly.key 102).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow102, Integer.Sparse.eval]

theorem keyMoment103 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 103) =
      Integer.Sparse.eval keyMomentRow103 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 103).leftCharge (GramAssembly.key 103).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 195) := by
    have ha : gramCharges (GramAssembly.key 103).leftCharge (GramAssembly.key 103).rightCharge = raw39553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39553 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 103).leftCharge (GramAssembly.key 103).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow103, Integer.Sparse.eval]

theorem keyMoment104 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 104) =
      Integer.Sparse.eval keyMomentRow104 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 104).leftCharge (GramAssembly.key 104).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 240) := by
    have ha : gramCharges (GramAssembly.key 104).leftCharge (GramAssembly.key 104).rightCharge = raw39554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39554 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 104).leftCharge (GramAssembly.key 104).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow104, Integer.Sparse.eval]

theorem keyMoment105 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 105) =
      Integer.Sparse.eval keyMomentRow105 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 105).leftCharge (GramAssembly.key 105).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 248) := by
    have ha : gramCharges (GramAssembly.key 105).leftCharge (GramAssembly.key 105).rightCharge = raw39555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39555 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 105).leftCharge (GramAssembly.key 105).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow105, Integer.Sparse.eval]

theorem keyMoment106 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 106) =
      Integer.Sparse.eval keyMomentRow106 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 106).leftCharge (GramAssembly.key 106).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 213) := by
    have ha : gramCharges (GramAssembly.key 106).leftCharge (GramAssembly.key 106).rightCharge = raw39556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39556 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 106).leftCharge (GramAssembly.key 106).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow106, Integer.Sparse.eval]

theorem keyMoment107 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 107) =
      Integer.Sparse.eval keyMomentRow107 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 107).leftCharge (GramAssembly.key 107).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 167) := by
    have ha : gramCharges (GramAssembly.key 107).leftCharge (GramAssembly.key 107).rightCharge = raw39557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39557 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 107).leftCharge (GramAssembly.key 107).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow107, Integer.Sparse.eval]

theorem keyMoment108 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 108) =
      Integer.Sparse.eval keyMomentRow108 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 108).leftCharge (GramAssembly.key 108).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 253) := by
    have ha : gramCharges (GramAssembly.key 108).leftCharge (GramAssembly.key 108).rightCharge = raw39558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39558 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 108).leftCharge (GramAssembly.key 108).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow108, Integer.Sparse.eval]

theorem keyMoment109 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 109) =
      Integer.Sparse.eval keyMomentRow109 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 109).leftCharge (GramAssembly.key 109).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 257) := by
    have ha : gramCharges (GramAssembly.key 109).leftCharge (GramAssembly.key 109).rightCharge = raw39559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39559 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 109).leftCharge (GramAssembly.key 109).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow109, Integer.Sparse.eval]

theorem keyMoment110 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 110) =
      Integer.Sparse.eval keyMomentRow110 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 110).leftCharge (GramAssembly.key 110).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 189) := by
    have ha : gramCharges (GramAssembly.key 110).leftCharge (GramAssembly.key 110).rightCharge = raw39560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39560 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 110).leftCharge (GramAssembly.key 110).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow110, Integer.Sparse.eval]

theorem keyMoment111 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 111) =
      Integer.Sparse.eval keyMomentRow111 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 111).leftCharge (GramAssembly.key 111).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 254) := by
    have ha : gramCharges (GramAssembly.key 111).leftCharge (GramAssembly.key 111).rightCharge = raw39561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39561 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 111).leftCharge (GramAssembly.key 111).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow111, Integer.Sparse.eval]

theorem keyMoment112 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 112) =
      Integer.Sparse.eval keyMomentRow112 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 112).leftCharge (GramAssembly.key 112).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 112).leftCharge (GramAssembly.key 112).rightCharge = raw39562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39562 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 112).leftCharge (GramAssembly.key 112).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow112, Integer.Sparse.eval]

theorem keyMoment113 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 113) =
      Integer.Sparse.eval keyMomentRow113 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 113).leftCharge (GramAssembly.key 113).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 190) := by
    have ha : gramCharges (GramAssembly.key 113).leftCharge (GramAssembly.key 113).rightCharge = raw39563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39563 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 113).leftCharge (GramAssembly.key 113).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow113, Integer.Sparse.eval]

theorem keyMoment114 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 114) =
      Integer.Sparse.eval keyMomentRow114 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 114).leftCharge (GramAssembly.key 114).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 220) := by
    have ha : gramCharges (GramAssembly.key 114).leftCharge (GramAssembly.key 114).rightCharge = raw39564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39564 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 114).leftCharge (GramAssembly.key 114).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow114, Integer.Sparse.eval]

theorem keyMoment115 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 115) =
      Integer.Sparse.eval keyMomentRow115 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 115).leftCharge (GramAssembly.key 115).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 163) := by
    have ha : gramCharges (GramAssembly.key 115).leftCharge (GramAssembly.key 115).rightCharge = raw39565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39565 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 115).leftCharge (GramAssembly.key 115).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow115, Integer.Sparse.eval]

theorem keyMoment116 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 116) =
      Integer.Sparse.eval keyMomentRow116 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 116).leftCharge (GramAssembly.key 116).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 116).leftCharge (GramAssembly.key 116).rightCharge = raw39566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39566 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 116).leftCharge (GramAssembly.key 116).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow116, Integer.Sparse.eval]

theorem keyMoment117 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 117) =
      Integer.Sparse.eval keyMomentRow117 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 117).leftCharge (GramAssembly.key 117).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 255) := by
    have ha : gramCharges (GramAssembly.key 117).leftCharge (GramAssembly.key 117).rightCharge = raw39567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39567 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 117).leftCharge (GramAssembly.key 117).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow117, Integer.Sparse.eval]

theorem keyMoment118 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 118) =
      Integer.Sparse.eval keyMomentRow118 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 118).leftCharge (GramAssembly.key 118).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 134) := by
    have ha : gramCharges (GramAssembly.key 118).leftCharge (GramAssembly.key 118).rightCharge = raw39568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39568 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 118).leftCharge (GramAssembly.key 118).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow118, Integer.Sparse.eval]

theorem keyMoment119 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 119) =
      Integer.Sparse.eval keyMomentRow119 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 119).leftCharge (GramAssembly.key 119).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 1) := by
    have ha : gramCharges (GramAssembly.key 119).leftCharge (GramAssembly.key 119).rightCharge = raw39569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39569 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 119).leftCharge (GramAssembly.key 119).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow119, Integer.Sparse.eval]

theorem keyMoment120 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 120) =
      Integer.Sparse.eval keyMomentRow120 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 120).leftCharge (GramAssembly.key 120).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 222) := by
    have ha : gramCharges (GramAssembly.key 120).leftCharge (GramAssembly.key 120).rightCharge = raw39570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39570 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 120).leftCharge (GramAssembly.key 120).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow120, Integer.Sparse.eval]

theorem keyMoment121 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 121) =
      Integer.Sparse.eval keyMomentRow121 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 121).leftCharge (GramAssembly.key 121).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 117) := by
    have ha : gramCharges (GramAssembly.key 121).leftCharge (GramAssembly.key 121).rightCharge = raw39571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39571 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 121).leftCharge (GramAssembly.key 121).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow121, Integer.Sparse.eval]

theorem keyMoment122 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 122) =
      Integer.Sparse.eval keyMomentRow122 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 122).leftCharge (GramAssembly.key 122).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 192) := by
    have ha : gramCharges (GramAssembly.key 122).leftCharge (GramAssembly.key 122).rightCharge = raw39572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39572 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 122).leftCharge (GramAssembly.key 122).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow122, Integer.Sparse.eval]

theorem keyMoment123 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 123) =
      Integer.Sparse.eval keyMomentRow123 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 123).leftCharge (GramAssembly.key 123).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 239) := by
    have ha : gramCharges (GramAssembly.key 123).leftCharge (GramAssembly.key 123).rightCharge = raw39573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39573 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 123).leftCharge (GramAssembly.key 123).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow123, Integer.Sparse.eval]

theorem keyMoment124 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 124) =
      Integer.Sparse.eval keyMomentRow124 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 124).leftCharge (GramAssembly.key 124).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 260) := by
    have ha : gramCharges (GramAssembly.key 124).leftCharge (GramAssembly.key 124).rightCharge = raw39574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39574 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 124).leftCharge (GramAssembly.key 124).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow124, Integer.Sparse.eval]

theorem keyMoment125 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 125) =
      Integer.Sparse.eval keyMomentRow125 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 125).leftCharge (GramAssembly.key 125).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 212) := by
    have ha : gramCharges (GramAssembly.key 125).leftCharge (GramAssembly.key 125).rightCharge = raw39575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39575 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 125).leftCharge (GramAssembly.key 125).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow125, Integer.Sparse.eval]

theorem keyMoment126 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 126) =
      Integer.Sparse.eval keyMomentRow126 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 126).leftCharge (GramAssembly.key 126).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 221) := by
    have ha : gramCharges (GramAssembly.key 126).leftCharge (GramAssembly.key 126).rightCharge = raw39576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39576 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 126).leftCharge (GramAssembly.key 126).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow126, Integer.Sparse.eval]

theorem keyMoment127 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 127) =
      Integer.Sparse.eval keyMomentRow127 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 127).leftCharge (GramAssembly.key 127).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 164) := by
    have ha : gramCharges (GramAssembly.key 127).leftCharge (GramAssembly.key 127).rightCharge = raw39577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw39577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical39577 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 127).leftCharge (GramAssembly.key 127).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow127, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt96 : keyMomentRows (96 : Fin 2886) =
    keyMomentRow96 := by decide +kernel

theorem keyMomentRowsAt97 : keyMomentRows (97 : Fin 2886) =
    keyMomentRow97 := by decide +kernel

theorem keyMomentRowsAt98 : keyMomentRows (98 : Fin 2886) =
    keyMomentRow98 := by decide +kernel

theorem keyMomentRowsAt99 : keyMomentRows (99 : Fin 2886) =
    keyMomentRow99 := by decide +kernel

theorem keyMomentRowsAt100 : keyMomentRows (100 : Fin 2886) =
    keyMomentRow100 := by decide +kernel

theorem keyMomentRowsAt101 : keyMomentRows (101 : Fin 2886) =
    keyMomentRow101 := by decide +kernel

theorem keyMomentRowsAt102 : keyMomentRows (102 : Fin 2886) =
    keyMomentRow102 := by decide +kernel

theorem keyMomentRowsAt103 : keyMomentRows (103 : Fin 2886) =
    keyMomentRow103 := by decide +kernel

theorem keyMomentRowsAt104 : keyMomentRows (104 : Fin 2886) =
    keyMomentRow104 := by decide +kernel

theorem keyMomentRowsAt105 : keyMomentRows (105 : Fin 2886) =
    keyMomentRow105 := by decide +kernel

theorem keyMomentRowsAt106 : keyMomentRows (106 : Fin 2886) =
    keyMomentRow106 := by decide +kernel

theorem keyMomentRowsAt107 : keyMomentRows (107 : Fin 2886) =
    keyMomentRow107 := by decide +kernel

theorem keyMomentRowsAt108 : keyMomentRows (108 : Fin 2886) =
    keyMomentRow108 := by decide +kernel

theorem keyMomentRowsAt109 : keyMomentRows (109 : Fin 2886) =
    keyMomentRow109 := by decide +kernel

theorem keyMomentRowsAt110 : keyMomentRows (110 : Fin 2886) =
    keyMomentRow110 := by decide +kernel

theorem keyMomentRowsAt111 : keyMomentRows (111 : Fin 2886) =
    keyMomentRow111 := by decide +kernel

theorem keyMomentRowsAt112 : keyMomentRows (112 : Fin 2886) =
    keyMomentRow112 := by decide +kernel

theorem keyMomentRowsAt113 : keyMomentRows (113 : Fin 2886) =
    keyMomentRow113 := by decide +kernel

theorem keyMomentRowsAt114 : keyMomentRows (114 : Fin 2886) =
    keyMomentRow114 := by decide +kernel

theorem keyMomentRowsAt115 : keyMomentRows (115 : Fin 2886) =
    keyMomentRow115 := by decide +kernel

theorem keyMomentRowsAt116 : keyMomentRows (116 : Fin 2886) =
    keyMomentRow116 := by decide +kernel

theorem keyMomentRowsAt117 : keyMomentRows (117 : Fin 2886) =
    keyMomentRow117 := by decide +kernel

theorem keyMomentRowsAt118 : keyMomentRows (118 : Fin 2886) =
    keyMomentRow118 := by decide +kernel

theorem keyMomentRowsAt119 : keyMomentRows (119 : Fin 2886) =
    keyMomentRow119 := by decide +kernel

theorem keyMomentRowsAt120 : keyMomentRows (120 : Fin 2886) =
    keyMomentRow120 := by decide +kernel

theorem keyMomentRowsAt121 : keyMomentRows (121 : Fin 2886) =
    keyMomentRow121 := by decide +kernel

theorem keyMomentRowsAt122 : keyMomentRows (122 : Fin 2886) =
    keyMomentRow122 := by decide +kernel

theorem keyMomentRowsAt123 : keyMomentRows (123 : Fin 2886) =
    keyMomentRow123 := by decide +kernel

theorem keyMomentRowsAt124 : keyMomentRows (124 : Fin 2886) =
    keyMomentRow124 := by decide +kernel

theorem keyMomentRowsAt125 : keyMomentRows (125 : Fin 2886) =
    keyMomentRow125 := by decide +kernel

theorem keyMomentRowsAt126 : keyMomentRows (126 : Fin 2886) =
    keyMomentRow126 := by decide +kernel

theorem keyMomentRowsAt127 : keyMomentRows (127 : Fin 2886) =
    keyMomentRow127 := by decide +kernel

theorem keyMomentChunkSound3_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 3) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 96 ∨ k.val = 97 ∨ k.val = 98 ∨ k.val = 99 ∨ k.val = 100 ∨ k.val = 101 ∨ k.val = 102 ∨ k.val = 103 ∨ k.val = 104 ∨ k.val = 105 ∨ k.val = 106 ∨ k.val = 107 ∨ k.val = 108 ∨ k.val = 109 ∨ k.val = 110 ∨ k.val = 111 ∨ k.val = 112 ∨ k.val = 113 ∨ k.val = 114 ∨ k.val = 115 ∨ k.val = 116 ∨ k.val = 117 ∨ k.val = 118 ∨ k.val = 119 ∨ k.val = 120 ∨ k.val = 121 ∨ k.val = 122 ∨ k.val = 123 ∨ k.val = 124 ∨ k.val = 125 ∨ k.val = 126 ∨ k.val = 127 := by omega
  rcases heq with h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127
  · have he : k = (96 : Fin 2886) := Fin.ext h96
    subst k
    rw [keyMomentRowsAt96]
    exact keyMoment96 B hB
  · have he : k = (97 : Fin 2886) := Fin.ext h97
    subst k
    rw [keyMomentRowsAt97]
    exact keyMoment97 B hB
  · have he : k = (98 : Fin 2886) := Fin.ext h98
    subst k
    rw [keyMomentRowsAt98]
    exact keyMoment98 B hB
  · have he : k = (99 : Fin 2886) := Fin.ext h99
    subst k
    rw [keyMomentRowsAt99]
    exact keyMoment99 B hB
  · have he : k = (100 : Fin 2886) := Fin.ext h100
    subst k
    rw [keyMomentRowsAt100]
    exact keyMoment100 B hB
  · have he : k = (101 : Fin 2886) := Fin.ext h101
    subst k
    rw [keyMomentRowsAt101]
    exact keyMoment101 B hB
  · have he : k = (102 : Fin 2886) := Fin.ext h102
    subst k
    rw [keyMomentRowsAt102]
    exact keyMoment102 B hB
  · have he : k = (103 : Fin 2886) := Fin.ext h103
    subst k
    rw [keyMomentRowsAt103]
    exact keyMoment103 B hB
  · have he : k = (104 : Fin 2886) := Fin.ext h104
    subst k
    rw [keyMomentRowsAt104]
    exact keyMoment104 B hB
  · have he : k = (105 : Fin 2886) := Fin.ext h105
    subst k
    rw [keyMomentRowsAt105]
    exact keyMoment105 B hB
  · have he : k = (106 : Fin 2886) := Fin.ext h106
    subst k
    rw [keyMomentRowsAt106]
    exact keyMoment106 B hB
  · have he : k = (107 : Fin 2886) := Fin.ext h107
    subst k
    rw [keyMomentRowsAt107]
    exact keyMoment107 B hB
  · have he : k = (108 : Fin 2886) := Fin.ext h108
    subst k
    rw [keyMomentRowsAt108]
    exact keyMoment108 B hB
  · have he : k = (109 : Fin 2886) := Fin.ext h109
    subst k
    rw [keyMomentRowsAt109]
    exact keyMoment109 B hB
  · have he : k = (110 : Fin 2886) := Fin.ext h110
    subst k
    rw [keyMomentRowsAt110]
    exact keyMoment110 B hB
  · have he : k = (111 : Fin 2886) := Fin.ext h111
    subst k
    rw [keyMomentRowsAt111]
    exact keyMoment111 B hB
  · have he : k = (112 : Fin 2886) := Fin.ext h112
    subst k
    rw [keyMomentRowsAt112]
    exact keyMoment112 B hB
  · have he : k = (113 : Fin 2886) := Fin.ext h113
    subst k
    rw [keyMomentRowsAt113]
    exact keyMoment113 B hB
  · have he : k = (114 : Fin 2886) := Fin.ext h114
    subst k
    rw [keyMomentRowsAt114]
    exact keyMoment114 B hB
  · have he : k = (115 : Fin 2886) := Fin.ext h115
    subst k
    rw [keyMomentRowsAt115]
    exact keyMoment115 B hB
  · have he : k = (116 : Fin 2886) := Fin.ext h116
    subst k
    rw [keyMomentRowsAt116]
    exact keyMoment116 B hB
  · have he : k = (117 : Fin 2886) := Fin.ext h117
    subst k
    rw [keyMomentRowsAt117]
    exact keyMoment117 B hB
  · have he : k = (118 : Fin 2886) := Fin.ext h118
    subst k
    rw [keyMomentRowsAt118]
    exact keyMoment118 B hB
  · have he : k = (119 : Fin 2886) := Fin.ext h119
    subst k
    rw [keyMomentRowsAt119]
    exact keyMoment119 B hB
  · have he : k = (120 : Fin 2886) := Fin.ext h120
    subst k
    rw [keyMomentRowsAt120]
    exact keyMoment120 B hB
  · have he : k = (121 : Fin 2886) := Fin.ext h121
    subst k
    rw [keyMomentRowsAt121]
    exact keyMoment121 B hB
  · have he : k = (122 : Fin 2886) := Fin.ext h122
    subst k
    rw [keyMomentRowsAt122]
    exact keyMoment122 B hB
  · have he : k = (123 : Fin 2886) := Fin.ext h123
    subst k
    rw [keyMomentRowsAt123]
    exact keyMoment123 B hB
  · have he : k = (124 : Fin 2886) := Fin.ext h124
    subst k
    rw [keyMomentRowsAt124]
    exact keyMoment124 B hB
  · have he : k = (125 : Fin 2886) := Fin.ext h125
    subst k
    rw [keyMomentRowsAt125]
    exact keyMoment125 B hB
  · have he : k = (126 : Fin 2886) := Fin.ext h126
    subst k
    rw [keyMomentRowsAt126]
    exact keyMoment126 B hB
  · have he : k = (127 : Fin 2886) := Fin.ext h127
    subst k
    rw [keyMomentRowsAt127]
    exact keyMoment127 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound3_e_oai
