-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:04:22.734683+00:00
-- url     : https://prove2.me/submissions/7aff767d-0412-4cc9-8f65-75de17e7d01d

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E113
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

theorem rename_labels {p n l k : ℕ} (hk : k ≤ 6) (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin n) ℤ) (label : Fin n → Fin k)
    (small : Fin n → Fin l) (e : Fin l ↪ Fin k) (h : label = e ∘ small) :
    mixedMoment B A label = mixedMoment B A small := by
  rw [h]
  exact mixedMoment_label_embedding hk B A e small

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical331
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42432 raw42432Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw42432 raw42432Labels = mixedMoment B raw42432step0 raw42432step0Labels := by
      have ha : raw42432step0 = (fun i j => raw42432 (permutation599 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42432step0 raw42432; decide +kernel
      have hl : raw42432step0Labels = raw42432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42432 raw42432Labels permutation599 permutation4
    mixedMoment B raw42432step0 raw42432step0Labels = mixedMoment B raw42432step1 raw42432step1Labels := by
      have ha : raw42432step1 = raw42432step0 := by apply Matrix.ext; unfold raw42432step1 raw42432step0; decide +kernel
      have hl : raw42432step0Labels = labelEmbedding1 ∘ raw42432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42432step0 raw42432step0Labels raw42432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

theorem canonical42433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42433 raw42433Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42433 raw42433Labels = mixedMoment B raw42433step0 raw42433step0Labels := by
      have ha : raw42433step0 = (fun i j => raw42433 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42433step0 raw42433; decide +kernel
      have hl : raw42433step0Labels = raw42433Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42433 raw42433Labels permutation668 permutation5
    mixedMoment B raw42433step0 raw42433step0Labels = mixedMoment B raw42433step1 raw42433step1Labels := by
      have ha : raw42433step1 = raw42433step0 := by apply Matrix.ext; unfold raw42433step1 raw42433step0; decide +kernel
      have hl : raw42433step0Labels = labelEmbedding9 ∘ raw42433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42433step0 raw42433step0Labels raw42433step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical42434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42434 raw42434Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42434 raw42434Labels = mixedMoment B raw42434step0 raw42434step0Labels := by
      have ha : raw42434step0 = raw42434 := by apply Matrix.ext; unfold raw42434step0 raw42434; decide +kernel
      have hl : raw42434Labels = labelEmbedding1 ∘ raw42434step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42434 raw42434Labels raw42434step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

theorem canonical42435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42435 raw42435Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42435 raw42435Labels = mixedMoment B raw42435step0 raw42435step0Labels := by
      have ha : raw42435step0 = (fun i j => raw42435 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42435step0 raw42435; decide +kernel
      have hl : raw42435step0Labels = raw42435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42435 raw42435Labels permutation682 permutation3
    mixedMoment B raw42435step0 raw42435step0Labels = mixedMoment B raw42435step1 raw42435step1Labels := by
      have ha : raw42435step1 = -raw42435step0 := by apply Matrix.ext; change ∀ i j, raw42435step1 i j = -(raw42435step0 i j); unfold raw42435step1 raw42435step0; decide +kernel
      have hl : raw42435step1Labels = raw42435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42435step1 raw42435step1Labels = mixedMoment B raw42435step2 raw42435step2Labels := by
      have ha : raw42435step2 = raw42435step1 := by apply Matrix.ext; unfold raw42435step2 raw42435step1; decide +kernel
      have hl : raw42435step1Labels = labelEmbedding7 ∘ raw42435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42435step1 raw42435step1Labels raw42435step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

theorem canonical42436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42436 raw42436Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42436 raw42436Labels = mixedMoment B raw42436step0 raw42436step0Labels := by
      have ha : raw42436step0 = raw42436 := by apply Matrix.ext; unfold raw42436step0 raw42436; decide +kernel
      have hl : raw42436Labels = labelEmbedding1 ∘ raw42436step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42436 raw42436Labels raw42436step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

theorem canonical42437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42437 raw42437Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42437 raw42437Labels = mixedMoment B raw42437step0 raw42437step0Labels := by
      have ha : raw42437step0 = raw42437 := by apply Matrix.ext; unfold raw42437step0 raw42437; decide +kernel
      have hl : raw42437Labels = labelEmbedding8 ∘ raw42437step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42437 raw42437Labels raw42437step0Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

theorem canonical42438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42438 raw42438Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw42438 raw42438Labels = mixedMoment B raw42438step0 raw42438step0Labels := by
      have ha : raw42438step0 = (fun i j => raw42438 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42438step0 raw42438; decide +kernel
      have hl : raw42438step0Labels = raw42438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42438 raw42438Labels permutation526 permutation4
    mixedMoment B raw42438step0 raw42438step0Labels = mixedMoment B raw42438step1 raw42438step1Labels := by
      have ha : raw42438step1 = raw42438step0 := by apply Matrix.ext; unfold raw42438step1 raw42438step0; decide +kernel
      have hl : raw42438step0Labels = labelEmbedding1 ∘ raw42438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42438step0 raw42438step0Labels raw42438step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical42439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42439 raw42439Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw42439 raw42439Labels = mixedMoment B raw42439step0 raw42439step0Labels := by
      have ha : raw42439step0 = (fun i j => raw42439 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42439step0 raw42439; decide +kernel
      have hl : raw42439step0Labels = raw42439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42439 raw42439Labels permutation526 permutation4
    mixedMoment B raw42439step0 raw42439step0Labels = mixedMoment B raw42439step1 raw42439step1Labels := by
      have ha : raw42439step1 = raw42439step0 := by apply Matrix.ext; unfold raw42439step1 raw42439step0; decide +kernel
      have hl : raw42439step0Labels = labelEmbedding10 ∘ raw42439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42439step0 raw42439step0Labels raw42439step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical42440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42440 raw42440Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw42440 raw42440Labels = mixedMoment B raw42440step0 raw42440step0Labels := by
      have hz : ∀ j, raw42440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42440step0 = (fun i j => raw42440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42440step0 raw42440; decide +kernel
      have hl : raw42440step0Labels = raw42440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42440 raw42440Labels permutation434 hz
    mixedMoment B raw42440step0 raw42440step0Labels = mixedMoment B raw42440step1 raw42440step1Labels := by
      have ha : raw42440step1 = (fun i j => raw42440step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42440step1 raw42440step0; decide +kernel
      have hl : raw42440step1Labels = raw42440step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42440step0 raw42440step0Labels permutation128 permutation4
    mixedMoment B raw42440step1 raw42440step1Labels = mixedMoment B raw42440step2 raw42440step2Labels := by
      have ha : raw42440step2 = raw42440step1 := by apply Matrix.ext; unfold raw42440step2 raw42440step1; decide +kernel
      have hl : raw42440step1Labels = labelEmbedding1 ∘ raw42440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42440step1 raw42440step1Labels raw42440step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical42441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42441 raw42441Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42441 raw42441Labels = mixedMoment B raw42441step0 raw42441step0Labels := by
      have hz : ∀ j, raw42441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42441step0 = (fun i j => raw42441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42441step0 raw42441; decide +kernel
      have hl : raw42441step0Labels = raw42441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42441 raw42441Labels permutation434 hz
    mixedMoment B raw42441step0 raw42441step0Labels = mixedMoment B raw42441step1 raw42441step1Labels := by
      have ha : raw42441step1 = (fun i j => raw42441step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42441step1 raw42441step0; decide +kernel
      have hl : raw42441step1Labels = raw42441step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42441step0 raw42441step0Labels permutation133 permutation5
    mixedMoment B raw42441step1 raw42441step1Labels = mixedMoment B raw42441step2 raw42441step2Labels := by
      have ha : raw42441step2 = raw42441step1 := by apply Matrix.ext; unfold raw42441step2 raw42441step1; decide +kernel
      have hl : raw42441step1Labels = labelEmbedding9 ∘ raw42441step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42441step1 raw42441step1Labels raw42441step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42442 raw42442Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw42442 raw42442Labels = mixedMoment B raw42442step0 raw42442step0Labels := by
      have hz : ∀ j, raw42442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42442step0 = (fun i j => raw42442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42442step0 raw42442; decide +kernel
      have hl : raw42442step0Labels = raw42442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42442 raw42442Labels permutation434 hz
    mixedMoment B raw42442step0 raw42442step0Labels = mixedMoment B raw42442step1 raw42442step1Labels := by
      have ha : raw42442step1 = (fun i j => raw42442step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42442step1 raw42442step0; decide +kernel
      have hl : raw42442step1Labels = raw42442step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42442step0 raw42442step0Labels permutation104 permutation4
    mixedMoment B raw42442step1 raw42442step1Labels = mixedMoment B raw42442step2 raw42442step2Labels := by
      have ha : raw42442step2 = raw42442step1 := by apply Matrix.ext; unfold raw42442step2 raw42442step1; decide +kernel
      have hl : raw42442step1Labels = labelEmbedding1 ∘ raw42442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42442step1 raw42442step1Labels raw42442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

theorem canonical42443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42443 raw42443Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw42443 raw42443Labels = mixedMoment B raw42443step0 raw42443step0Labels := by
      have hz : ∀ j, raw42443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42443step0 = (fun i j => raw42443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42443step0 raw42443; decide +kernel
      have hl : raw42443step0Labels = raw42443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42443 raw42443Labels permutation434 hz
    mixedMoment B raw42443step0 raw42443step0Labels = mixedMoment B raw42443step1 raw42443step1Labels := by
      have ha : raw42443step1 = (fun i j => raw42443step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42443step1 raw42443step0; decide +kernel
      have hl : raw42443step1Labels = raw42443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42443step0 raw42443step0Labels permutation143 permutation7
    mixedMoment B raw42443step1 raw42443step1Labels = mixedMoment B raw42443step2 raw42443step2Labels := by
      have ha : raw42443step2 = raw42443step1 := by apply Matrix.ext; unfold raw42443step2 raw42443step1; decide +kernel
      have hl : raw42443step1Labels = labelEmbedding6 ∘ raw42443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42443step1 raw42443step1Labels raw42443step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

theorem canonical42444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42444 raw42444Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw42444 raw42444Labels = mixedMoment B raw42444step0 raw42444step0Labels := by
      have ha : raw42444step0 = (fun i j => raw42444 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42444step0 raw42444; decide +kernel
      have hl : raw42444step0Labels = raw42444Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42444 raw42444Labels permutation158 permutation2
    mixedMoment B raw42444step0 raw42444step0Labels = mixedMoment B raw42444step1 raw42444step1Labels := by
      have ha : raw42444step1 = raw42444step0 := by apply Matrix.ext; unfold raw42444step1 raw42444step0; decide +kernel
      have hl : raw42444step0Labels = labelEmbedding1 ∘ raw42444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42444step0 raw42444step0Labels raw42444step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

theorem canonical42445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42445 raw42445Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42445 raw42445Labels = mixedMoment B raw42445step0 raw42445step0Labels := by
      have ha : raw42445step0 = (fun i j => raw42445 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42445step0 raw42445; decide +kernel
      have hl : raw42445step0Labels = raw42445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42445 raw42445Labels permutation158 permutation2
    mixedMoment B raw42445step0 raw42445step0Labels = mixedMoment B raw42445step1 raw42445step1Labels := by
      have ha : raw42445step1 = raw42445step0 := by apply Matrix.ext; unfold raw42445step1 raw42445step0; decide +kernel
      have hl : raw42445step0Labels = labelEmbedding8 ∘ raw42445step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42445step0 raw42445step0Labels raw42445step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

theorem canonical42446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42446 raw42446Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw42446 raw42446Labels = mixedMoment B raw42446step0 raw42446step0Labels := by
      have ha : raw42446step0 = (fun i j => raw42446 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42446step0 raw42446; decide +kernel
      have hl : raw42446step0Labels = raw42446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42446 raw42446Labels permutation682 permutation2
    mixedMoment B raw42446step0 raw42446step0Labels = mixedMoment B raw42446step1 raw42446step1Labels := by
      have ha : raw42446step1 = -raw42446step0 := by apply Matrix.ext; change ∀ i j, raw42446step1 i j = -(raw42446step0 i j); unfold raw42446step1 raw42446step0; decide +kernel
      have hl : raw42446step1Labels = raw42446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42446step1 raw42446step1Labels = mixedMoment B raw42446step2 raw42446step2Labels := by
      have ha : raw42446step2 = raw42446step1 := by apply Matrix.ext; unfold raw42446step2 raw42446step1; decide +kernel
      have hl : raw42446step1Labels = labelEmbedding1 ∘ raw42446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42446step1 raw42446step1Labels raw42446step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

theorem canonical42447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42447 raw42447Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw42447 raw42447Labels = mixedMoment B raw42447step0 raw42447step0Labels := by
      have ha : raw42447step0 = (fun i j => raw42447 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42447step0 raw42447; decide +kernel
      have hl : raw42447step0Labels = raw42447Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42447 raw42447Labels permutation634 permutation7
    mixedMoment B raw42447step0 raw42447step0Labels = mixedMoment B raw42447step1 raw42447step1Labels := by
      have ha : raw42447step1 = raw42447step0 := by apply Matrix.ext; unfold raw42447step1 raw42447step0; decide +kernel
      have hl : raw42447step0Labels = labelEmbedding6 ∘ raw42447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42447step0 raw42447step0Labels raw42447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

theorem canonical42448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42448 raw42448Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw42448 raw42448Labels = mixedMoment B raw42448step0 raw42448step0Labels := by
      have ha : raw42448step0 = (fun i j => raw42448 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42448step0 raw42448; decide +kernel
      have hl : raw42448step0Labels = raw42448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42448 raw42448Labels permutation682 permutation2
    mixedMoment B raw42448step0 raw42448step0Labels = mixedMoment B raw42448step1 raw42448step1Labels := by
      have ha : raw42448step1 = -raw42448step0 := by apply Matrix.ext; change ∀ i j, raw42448step1 i j = -(raw42448step0 i j); unfold raw42448step1 raw42448step0; decide +kernel
      have hl : raw42448step1Labels = raw42448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42448step1 raw42448step1Labels = mixedMoment B raw42448step2 raw42448step2Labels := by
      have ha : raw42448step2 = raw42448step1 := by apply Matrix.ext; unfold raw42448step2 raw42448step1; decide +kernel
      have hl : raw42448step1Labels = labelEmbedding1 ∘ raw42448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42448step1 raw42448step1Labels raw42448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical42449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42449 raw42449Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw42449 raw42449Labels = mixedMoment B raw42449step0 raw42449step0Labels := by
      have ha : raw42449step0 = (fun i j => raw42449 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42449step0 raw42449; decide +kernel
      have hl : raw42449step0Labels = raw42449Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42449 raw42449Labels permutation644 permutation7
    mixedMoment B raw42449step0 raw42449step0Labels = mixedMoment B raw42449step1 raw42449step1Labels := by
      have ha : raw42449step1 = raw42449step0 := by apply Matrix.ext; unfold raw42449step1 raw42449step0; decide +kernel
      have hl : raw42449step0Labels = labelEmbedding6 ∘ raw42449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42449step0 raw42449step0Labels raw42449step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical42450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42450 raw42450Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw42450 raw42450Labels = mixedMoment B raw42450step0 raw42450step0Labels := by
      have ha : raw42450step0 = (fun i j => raw42450 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42450step0 raw42450; decide +kernel
      have hl : raw42450step0Labels = raw42450Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42450 raw42450Labels permutation157 permutation2
    mixedMoment B raw42450step0 raw42450step0Labels = mixedMoment B raw42450step1 raw42450step1Labels := by
      have ha : raw42450step1 = raw42450step0 := by apply Matrix.ext; unfold raw42450step1 raw42450step0; decide +kernel
      have hl : raw42450step0Labels = labelEmbedding1 ∘ raw42450step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42450step0 raw42450step0Labels raw42450step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

theorem canonical42451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42451 raw42451Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42451 raw42451Labels = mixedMoment B raw42451step0 raw42451step0Labels := by
      have ha : raw42451step0 = (fun i j => raw42451 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42451step0 raw42451; decide +kernel
      have hl : raw42451step0Labels = raw42451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42451 raw42451Labels permutation157 permutation2
    mixedMoment B raw42451step0 raw42451step0Labels = mixedMoment B raw42451step1 raw42451step1Labels := by
      have ha : raw42451step1 = raw42451step0 := by apply Matrix.ext; unfold raw42451step1 raw42451step0; decide +kernel
      have hl : raw42451step0Labels = labelEmbedding8 ∘ raw42451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42451step0 raw42451step0Labels raw42451step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

theorem canonical42452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42452 raw42452Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw42452 raw42452Labels = mixedMoment B raw42452step0 raw42452step0Labels := by
      have hz : ∀ j, raw42452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42452step0 = (fun i j => raw42452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42452step0 raw42452; decide +kernel
      have hl : raw42452step0Labels = raw42452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42452 raw42452Labels permutation434 hz
    mixedMoment B raw42452step0 raw42452step0Labels = mixedMoment B raw42452step1 raw42452step1Labels := by
      have hz : ∀ j, raw42452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42452step1 = (fun i j => raw42452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42452step1 raw42452step0; decide +kernel
      have hl : raw42452step1Labels = raw42452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42452step0 raw42452step0Labels permutation80 hz
    mixedMoment B raw42452step1 raw42452step1Labels = mixedMoment B raw42452step2 raw42452step2Labels := by
      have ha : raw42452step2 = (fun i j => raw42452step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42452step2 raw42452step1; decide +kernel
      have hl : raw42452step2Labels = raw42452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42452step1 raw42452step1Labels permutation26 permutation4
    mixedMoment B raw42452step2 raw42452step2Labels = mixedMoment B raw42452step3 raw42452step3Labels := by
      have ha : raw42452step3 = raw42452step2 := by apply Matrix.ext; unfold raw42452step3 raw42452step2; decide +kernel
      have hl : raw42452step2Labels = labelEmbedding1 ∘ raw42452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42452step2 raw42452step2Labels raw42452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

theorem canonical42453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42453 raw42453Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42453 raw42453Labels = mixedMoment B raw42453step0 raw42453step0Labels := by
      have hz : ∀ j, raw42453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42453step0 = (fun i j => raw42453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42453step0 raw42453; decide +kernel
      have hl : raw42453step0Labels = raw42453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42453 raw42453Labels permutation434 hz
    mixedMoment B raw42453step0 raw42453step0Labels = mixedMoment B raw42453step1 raw42453step1Labels := by
      have hz : ∀ j, raw42453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42453step1 = (fun i j => raw42453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42453step1 raw42453step0; decide +kernel
      have hl : raw42453step1Labels = raw42453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42453step0 raw42453step0Labels permutation80 hz
    mixedMoment B raw42453step1 raw42453step1Labels = mixedMoment B raw42453step2 raw42453step2Labels := by
      have ha : raw42453step2 = (fun i j => raw42453step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42453step2 raw42453step1; decide +kernel
      have hl : raw42453step2Labels = raw42453step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42453step1 raw42453step1Labels permutation23 permutation6
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical42454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42454 raw42454Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw42454 raw42454Labels = mixedMoment B raw42454step0 raw42454step0Labels := by
      have hz : ∀ j, raw42454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42454step0 = (fun i j => raw42454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42454step0 raw42454; decide +kernel
      have hl : raw42454step0Labels = raw42454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42454 raw42454Labels permutation434 hz
    mixedMoment B raw42454step0 raw42454step0Labels = mixedMoment B raw42454step1 raw42454step1Labels := by
      have hz : ∀ j, raw42454step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42454step1 = (fun i j => raw42454step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42454step1 raw42454step0; decide +kernel
      have hl : raw42454step1Labels = raw42454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42454step0 raw42454step0Labels permutation80 hz
    mixedMoment B raw42454step1 raw42454step1Labels = mixedMoment B raw42454step2 raw42454step2Labels := by
      have ha : raw42454step2 = (fun i j => raw42454step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42454step2 raw42454step1; decide +kernel
      have hl : raw42454step2Labels = raw42454step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42454step1 raw42454step1Labels permutation20 permutation4
    mixedMoment B raw42454step2 raw42454step2Labels = mixedMoment B raw42454step3 raw42454step3Labels := by
      have ha : raw42454step3 = raw42454step2 := by apply Matrix.ext; unfold raw42454step3 raw42454step2; decide +kernel
      have hl : raw42454step2Labels = labelEmbedding1 ∘ raw42454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42454step2 raw42454step2Labels raw42454step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

theorem canonical42455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42455 raw42455Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw42455 raw42455Labels = mixedMoment B raw42455step0 raw42455step0Labels := by
      have hz : ∀ j, raw42455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42455step0 = (fun i j => raw42455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42455step0 raw42455; decide +kernel
      have hl : raw42455step0Labels = raw42455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42455 raw42455Labels permutation434 hz
    mixedMoment B raw42455step0 raw42455step0Labels = mixedMoment B raw42455step1 raw42455step1Labels := by
      have hz : ∀ j, raw42455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42455step1 = (fun i j => raw42455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42455step1 raw42455step0; decide +kernel
      have hl : raw42455step1Labels = raw42455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42455step0 raw42455step0Labels permutation80 hz
    mixedMoment B raw42455step1 raw42455step1Labels = mixedMoment B raw42455step2 raw42455step2Labels := by
      have ha : raw42455step2 = (fun i j => raw42455step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42455step2 raw42455step1; decide +kernel
      have hl : raw42455step2Labels = raw42455step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42455step1 raw42455step1Labels permutation28 permutation6
    _ = mixedMoment B node4611 node4611Labels := by rfl

theorem canonical42456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42456 raw42456Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42456 raw42456Labels = mixedMoment B raw42456step0 raw42456step0Labels := by
      have hz : ∀ j, raw42456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42456step0 = (fun i j => raw42456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42456step0 raw42456; decide +kernel
      have hl : raw42456step0Labels = raw42456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42456 raw42456Labels permutation346 hz
    mixedMoment B raw42456step0 raw42456step0Labels = mixedMoment B raw42456step1 raw42456step1Labels := by
      have ha : raw42456step1 = (fun i j => raw42456step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42456step1 raw42456step0; decide +kernel
      have hl : raw42456step1Labels = raw42456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42456step0 raw42456step0Labels permutation110 permutation4
    mixedMoment B raw42456step1 raw42456step1Labels = mixedMoment B raw42456step2 raw42456step2Labels := by
      have ha : raw42456step2 = -raw42456step1 := by apply Matrix.ext; change ∀ i j, raw42456step2 i j = -(raw42456step1 i j); unfold raw42456step2 raw42456step1; decide +kernel
      have hl : raw42456step2Labels = raw42456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42456step2 raw42456step2Labels = mixedMoment B raw42456step3 raw42456step3Labels := by
      have ha : raw42456step3 = raw42456step2 := by apply Matrix.ext; unfold raw42456step3 raw42456step2; decide +kernel
      have hl : raw42456step2Labels = labelEmbedding1 ∘ raw42456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42456step2 raw42456step2Labels raw42456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

theorem canonical42457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42457 raw42457Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42457 raw42457Labels = mixedMoment B raw42457step0 raw42457step0Labels := by
      have hz : ∀ j, raw42457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42457step0 = (fun i j => raw42457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42457step0 raw42457; decide +kernel
      have hl : raw42457step0Labels = raw42457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42457 raw42457Labels permutation346 hz
    mixedMoment B raw42457step0 raw42457step0Labels = mixedMoment B raw42457step1 raw42457step1Labels := by
      have ha : raw42457step1 = (fun i j => raw42457step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42457step1 raw42457step0; decide +kernel
      have hl : raw42457step1Labels = raw42457step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42457step0 raw42457step0Labels permutation115 permutation6
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42458 raw42458Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw42458 raw42458Labels = mixedMoment B raw42458step0 raw42458step0Labels := by
      have hz : ∀ j, raw42458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42458step0 = (fun i j => raw42458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42458step0 raw42458; decide +kernel
      have hl : raw42458step0Labels = raw42458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42458 raw42458Labels permutation346 hz
    mixedMoment B raw42458step0 raw42458step0Labels = mixedMoment B raw42458step1 raw42458step1Labels := by
      have ha : raw42458step1 = (fun i j => raw42458step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42458step1 raw42458step0; decide +kernel
      have hl : raw42458step1Labels = raw42458step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42458step0 raw42458step0Labels permutation134 permutation4
    mixedMoment B raw42458step1 raw42458step1Labels = mixedMoment B raw42458step2 raw42458step2Labels := by
      have ha : raw42458step2 = -raw42458step1 := by apply Matrix.ext; change ∀ i j, raw42458step2 i j = -(raw42458step1 i j); unfold raw42458step2 raw42458step1; decide +kernel
      have hl : raw42458step2Labels = raw42458step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42458step2 raw42458step2Labels = mixedMoment B raw42458step3 raw42458step3Labels := by
      have ha : raw42458step3 = raw42458step2 := by apply Matrix.ext; unfold raw42458step3 raw42458step2; decide +kernel
      have hl : raw42458step2Labels = labelEmbedding1 ∘ raw42458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42458step2 raw42458step2Labels raw42458step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

theorem canonical42459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42459 raw42459Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw42459 raw42459Labels = mixedMoment B raw42459step0 raw42459step0Labels := by
      have hz : ∀ j, raw42459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42459step0 = (fun i j => raw42459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42459step0 raw42459; decide +kernel
      have hl : raw42459step0Labels = raw42459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42459 raw42459Labels permutation346 hz
    mixedMoment B raw42459step0 raw42459step0Labels = mixedMoment B raw42459step1 raw42459step1Labels := by
      have ha : raw42459step1 = (fun i j => raw42459step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42459step1 raw42459step0; decide +kernel
      have hl : raw42459step1Labels = raw42459step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42459step0 raw42459step0Labels permutation137 permutation6
    _ = mixedMoment B node4607 node4607Labels := by rfl

theorem canonical42460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42460 raw42460Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw42460 raw42460Labels = mixedMoment B raw42460step0 raw42460step0Labels := by
      have hz : ∀ j, raw42460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42460step0 = (fun i j => raw42460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42460step0 raw42460; decide +kernel
      have hl : raw42460step0Labels = raw42460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42460 raw42460Labels permutation346 hz
    mixedMoment B raw42460step0 raw42460step0Labels = mixedMoment B raw42460step1 raw42460step1Labels := by
      have ha : raw42460step1 = (fun i j => raw42460step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42460step1 raw42460step0; decide +kernel
      have hl : raw42460step1Labels = raw42460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42460step0 raw42460step0Labels permutation151 permutation2
    mixedMoment B raw42460step1 raw42460step1Labels = mixedMoment B raw42460step2 raw42460step2Labels := by
      have ha : raw42460step2 = -raw42460step1 := by apply Matrix.ext; change ∀ i j, raw42460step2 i j = -(raw42460step1 i j); unfold raw42460step2 raw42460step1; decide +kernel
      have hl : raw42460step2Labels = raw42460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42460step2 raw42460step2Labels = mixedMoment B raw42460step3 raw42460step3Labels := by
      have ha : raw42460step3 = raw42460step2 := by apply Matrix.ext; unfold raw42460step3 raw42460step2; decide +kernel
      have hl : raw42460step2Labels = labelEmbedding1 ∘ raw42460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42460step2 raw42460step2Labels raw42460step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

theorem canonical42461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42461 raw42461Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw42461 raw42461Labels = mixedMoment B raw42461step0 raw42461step0Labels := by
      have hz : ∀ j, raw42461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42461step0 = (fun i j => raw42461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42461step0 raw42461; decide +kernel
      have hl : raw42461step0Labels = raw42461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42461 raw42461Labels permutation346 hz
    mixedMoment B raw42461step0 raw42461step0Labels = mixedMoment B raw42461step1 raw42461step1Labels := by
      have ha : raw42461step1 = (fun i j => raw42461step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42461step1 raw42461step0; decide +kernel
      have hl : raw42461step1Labels = raw42461step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42461step0 raw42461step0Labels permutation138 permutation6
    _ = mixedMoment B node4592 node4592Labels := by rfl

theorem canonical42462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42462 raw42462Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw42462 raw42462Labels = mixedMoment B raw42462step0 raw42462step0Labels := by
      have hz : ∀ j, raw42462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42462step0 = (fun i j => raw42462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42462step0 raw42462; decide +kernel
      have hl : raw42462step0Labels = raw42462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42462 raw42462Labels permutation346 hz
    mixedMoment B raw42462step0 raw42462step0Labels = mixedMoment B raw42462step1 raw42462step1Labels := by
      have ha : raw42462step1 = (fun i j => raw42462step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42462step1 raw42462step0; decide +kernel
      have hl : raw42462step1Labels = raw42462step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42462step0 raw42462step0Labels permutation132 permutation4
    mixedMoment B raw42462step1 raw42462step1Labels = mixedMoment B raw42462step2 raw42462step2Labels := by
      have ha : raw42462step2 = raw42462step1 := by apply Matrix.ext; unfold raw42462step2 raw42462step1; decide +kernel
      have hl : raw42462step1Labels = labelEmbedding1 ∘ raw42462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42462step1 raw42462step1Labels raw42462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

theorem canonical42463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42463 raw42463Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw42463 raw42463Labels = mixedMoment B raw42463step0 raw42463step0Labels := by
      have hz : ∀ j, raw42463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42463step0 = (fun i j => raw42463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42463step0 raw42463; decide +kernel
      have hl : raw42463step0Labels = raw42463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42463 raw42463Labels permutation346 hz
    mixedMoment B raw42463step0 raw42463step0Labels = mixedMoment B raw42463step1 raw42463step1Labels := by
      have ha : raw42463step1 = (fun i j => raw42463step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42463step1 raw42463step0; decide +kernel
      have hl : raw42463step1Labels = raw42463step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42463step0 raw42463step0Labels permutation94 permutation6
    _ = mixedMoment B node5140 node5140Labels := by rfl

theorem canonical42464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42464 raw42464Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42464 raw42464Labels = mixedMoment B raw42464step0 raw42464step0Labels := by
      have hz : ∀ j, raw42464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42464step0 = (fun i j => raw42464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42464step0 raw42464; decide +kernel
      have hl : raw42464step0Labels = raw42464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42464 raw42464Labels permutation346 hz
    mixedMoment B raw42464step0 raw42464step0Labels = mixedMoment B raw42464step1 raw42464step1Labels := by
      have ha : raw42464step1 = (fun i j => raw42464step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42464step1 raw42464step0; decide +kernel
      have hl : raw42464step1Labels = raw42464step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42464step0 raw42464step0Labels permutation86 permutation4
    mixedMoment B raw42464step1 raw42464step1Labels = mixedMoment B raw42464step2 raw42464step2Labels := by
      have ha : raw42464step2 = -raw42464step1 := by apply Matrix.ext; change ∀ i j, raw42464step2 i j = -(raw42464step1 i j); unfold raw42464step2 raw42464step1; decide +kernel
      have hl : raw42464step2Labels = raw42464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42464step2 raw42464step2Labels = mixedMoment B raw42464step3 raw42464step3Labels := by
      have ha : raw42464step3 = raw42464step2 := by apply Matrix.ext; unfold raw42464step3 raw42464step2; decide +kernel
      have hl : raw42464step2Labels = labelEmbedding1 ∘ raw42464step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42464step2 raw42464step2Labels raw42464step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

theorem canonical42465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42465 raw42465Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42465 raw42465Labels = mixedMoment B raw42465step0 raw42465step0Labels := by
      have hz : ∀ j, raw42465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42465step0 = (fun i j => raw42465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42465step0 raw42465; decide +kernel
      have hl : raw42465step0Labels = raw42465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42465 raw42465Labels permutation346 hz
    mixedMoment B raw42465step0 raw42465step0Labels = mixedMoment B raw42465step1 raw42465step1Labels := by
      have ha : raw42465step1 = (fun i j => raw42465step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42465step1 raw42465step0; decide +kernel
      have hl : raw42465step1Labels = raw42465step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42465step0 raw42465step0Labels permutation89 permutation6
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical42466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42466 raw42466Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw42466 raw42466Labels = mixedMoment B raw42466step0 raw42466step0Labels := by
      have hz : ∀ j, raw42466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42466step0 = (fun i j => raw42466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42466step0 raw42466; decide +kernel
      have hl : raw42466step0Labels = raw42466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42466 raw42466Labels permutation346 hz
    mixedMoment B raw42466step0 raw42466step0Labels = mixedMoment B raw42466step1 raw42466step1Labels := by
      have ha : raw42466step1 = (fun i j => raw42466step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42466step1 raw42466step0; decide +kernel
      have hl : raw42466step1Labels = raw42466step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42466step0 raw42466step0Labels permutation128 permutation4
    mixedMoment B raw42466step1 raw42466step1Labels = mixedMoment B raw42466step2 raw42466step2Labels := by
      have ha : raw42466step2 = raw42466step1 := by apply Matrix.ext; unfold raw42466step2 raw42466step1; decide +kernel
      have hl : raw42466step1Labels = labelEmbedding1 ∘ raw42466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42466step1 raw42466step1Labels raw42466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

theorem canonical42467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42467 raw42467Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw42467 raw42467Labels = mixedMoment B raw42467step0 raw42467step0Labels := by
      have hz : ∀ j, raw42467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42467step0 = (fun i j => raw42467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42467step0 raw42467; decide +kernel
      have hl : raw42467step0Labels = raw42467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42467 raw42467Labels permutation346 hz
    mixedMoment B raw42467step0 raw42467step0Labels = mixedMoment B raw42467step1 raw42467step1Labels := by
      have ha : raw42467step1 = (fun i j => raw42467step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42467step1 raw42467step0; decide +kernel
      have hl : raw42467step1Labels = raw42467step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42467step0 raw42467step0Labels permutation128 permutation4
    mixedMoment B raw42467step1 raw42467step1Labels = mixedMoment B raw42467step2 raw42467step2Labels := by
      have ha : raw42467step2 = raw42467step1 := by apply Matrix.ext; unfold raw42467step2 raw42467step1; decide +kernel
      have hl : raw42467step1Labels = labelEmbedding10 ∘ raw42467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42467step1 raw42467step1Labels raw42467step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

theorem canonical42468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42468 raw42468Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw42468 raw42468Labels = mixedMoment B raw42468step0 raw42468step0Labels := by
      have ha : raw42468step0 = (fun i j => raw42468 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42468step0 raw42468; decide +kernel
      have hl : raw42468step0Labels = raw42468Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42468 raw42468Labels permutation682 permutation2
    mixedMoment B raw42468step0 raw42468step0Labels = mixedMoment B raw42468step1 raw42468step1Labels := by
      have ha : raw42468step1 = -raw42468step0 := by apply Matrix.ext; change ∀ i j, raw42468step1 i j = -(raw42468step0 i j); unfold raw42468step1 raw42468step0; decide +kernel
      have hl : raw42468step1Labels = raw42468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42468step1 raw42468step1Labels = mixedMoment B raw42468step2 raw42468step2Labels := by
      have ha : raw42468step2 = raw42468step1 := by apply Matrix.ext; unfold raw42468step2 raw42468step1; decide +kernel
      have hl : raw42468step1Labels = labelEmbedding1 ∘ raw42468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42468step1 raw42468step1Labels raw42468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

theorem canonical42469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42469 raw42469Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw42469 raw42469Labels = mixedMoment B raw42469step0 raw42469step0Labels := by
      have ha : raw42469step0 = (fun i j => raw42469 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42469step0 raw42469; decide +kernel
      have hl : raw42469step0Labels = raw42469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42469 raw42469Labels permutation674 permutation7
    mixedMoment B raw42469step0 raw42469step0Labels = mixedMoment B raw42469step1 raw42469step1Labels := by
      have ha : raw42469step1 = raw42469step0 := by apply Matrix.ext; unfold raw42469step1 raw42469step0; decide +kernel
      have hl : raw42469step0Labels = labelEmbedding6 ∘ raw42469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42469step0 raw42469step0Labels raw42469step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

theorem canonical42470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42470 raw42470Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw42470 raw42470Labels = mixedMoment B raw42470step0 raw42470step0Labels := by
      have ha : raw42470step0 = (fun i j => raw42470 (permutation459 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42470step0 raw42470; decide +kernel
      have hl : raw42470step0Labels = raw42470Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42470 raw42470Labels permutation459 permutation4
    mixedMoment B raw42470step0 raw42470step0Labels = mixedMoment B raw42470step1 raw42470step1Labels := by
      have ha : raw42470step1 = -raw42470step0 := by apply Matrix.ext; change ∀ i j, raw42470step1 i j = -(raw42470step0 i j); unfold raw42470step1 raw42470step0; decide +kernel
      have hl : raw42470step1Labels = raw42470step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42470step1 raw42470step1Labels = mixedMoment B raw42470step2 raw42470step2Labels := by
      have ha : raw42470step2 = raw42470step1 := by apply Matrix.ext; unfold raw42470step2 raw42470step1; decide +kernel
      have hl : raw42470step1Labels = labelEmbedding1 ∘ raw42470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42470step1 raw42470step1Labels raw42470step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

theorem canonical42471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42471 raw42471Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw42471 raw42471Labels = mixedMoment B raw42471step0 raw42471step0Labels := by
      have ha : raw42471step0 = (fun i j => raw42471 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42471step0 raw42471; decide +kernel
      have hl : raw42471step0Labels = raw42471Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42471 raw42471Labels permutation492 permutation6
    _ = mixedMoment B node5138 node5138Labels := by rfl

theorem canonical42472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42472 raw42472Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw42472 raw42472Labels = mixedMoment B raw42472step0 raw42472step0Labels := by
      have ha : raw42472step0 = (fun i j => raw42472 (permutation454 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42472step0 raw42472; decide +kernel
      have hl : raw42472step0Labels = raw42472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42472 raw42472Labels permutation454 permutation4
    mixedMoment B raw42472step0 raw42472step0Labels = mixedMoment B raw42472step1 raw42472step1Labels := by
      have ha : raw42472step1 = -raw42472step0 := by apply Matrix.ext; change ∀ i j, raw42472step1 i j = -(raw42472step0 i j); unfold raw42472step1 raw42472step0; decide +kernel
      have hl : raw42472step1Labels = raw42472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42472step1 raw42472step1Labels = mixedMoment B raw42472step2 raw42472step2Labels := by
      have ha : raw42472step2 = raw42472step1 := by apply Matrix.ext; unfold raw42472step2 raw42472step1; decide +kernel
      have hl : raw42472step1Labels = labelEmbedding1 ∘ raw42472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42472step1 raw42472step1Labels raw42472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

theorem canonical42473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42473 raw42473Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42473 raw42473Labels = mixedMoment B raw42473step0 raw42473step0Labels := by
      have ha : raw42473step0 = (fun i j => raw42473 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42473step0 raw42473; decide +kernel
      have hl : raw42473step0Labels = raw42473Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42473 raw42473Labels permutation463 permutation6
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical42474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42474 raw42474Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw42474 raw42474Labels = mixedMoment B raw42474step0 raw42474step0Labels := by
      have ha : raw42474step0 = (fun i j => raw42474 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42474step0 raw42474; decide +kernel
      have hl : raw42474step0Labels = raw42474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42474 raw42474Labels permutation156 permutation2
    mixedMoment B raw42474step0 raw42474step0Labels = mixedMoment B raw42474step1 raw42474step1Labels := by
      have ha : raw42474step1 = raw42474step0 := by apply Matrix.ext; unfold raw42474step1 raw42474step0; decide +kernel
      have hl : raw42474step0Labels = labelEmbedding1 ∘ raw42474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42474step0 raw42474step0Labels raw42474step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

theorem canonical42475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42475 raw42475Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw42475 raw42475Labels = mixedMoment B raw42475step0 raw42475step0Labels := by
      have ha : raw42475step0 = (fun i j => raw42475 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42475step0 raw42475; decide +kernel
      have hl : raw42475step0Labels = raw42475Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42475 raw42475Labels permutation194 permutation7
    mixedMoment B raw42475step0 raw42475step0Labels = mixedMoment B raw42475step1 raw42475step1Labels := by
      have ha : raw42475step1 = -raw42475step0 := by apply Matrix.ext; change ∀ i j, raw42475step1 i j = -(raw42475step0 i j); unfold raw42475step1 raw42475step0; decide +kernel
      have hl : raw42475step1Labels = raw42475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42475step1 raw42475step1Labels = mixedMoment B raw42475step2 raw42475step2Labels := by
      have ha : raw42475step2 = raw42475step1 := by apply Matrix.ext; unfold raw42475step2 raw42475step1; decide +kernel
      have hl : raw42475step1Labels = labelEmbedding6 ∘ raw42475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42475step1 raw42475step1Labels raw42475step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

theorem canonical42476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42476 raw42476Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw42476 raw42476Labels = mixedMoment B raw42476step0 raw42476step0Labels := by
      have ha : raw42476step0 = (fun i j => raw42476 (permutation460 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42476step0 raw42476; decide +kernel
      have hl : raw42476step0Labels = raw42476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42476 raw42476Labels permutation460 permutation4
    mixedMoment B raw42476step0 raw42476step0Labels = mixedMoment B raw42476step1 raw42476step1Labels := by
      have ha : raw42476step1 = -raw42476step0 := by apply Matrix.ext; change ∀ i j, raw42476step1 i j = -(raw42476step0 i j); unfold raw42476step1 raw42476step0; decide +kernel
      have hl : raw42476step1Labels = raw42476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42476step1 raw42476step1Labels = mixedMoment B raw42476step2 raw42476step2Labels := by
      have ha : raw42476step2 = raw42476step1 := by apply Matrix.ext; unfold raw42476step2 raw42476step1; decide +kernel
      have hl : raw42476step1Labels = labelEmbedding1 ∘ raw42476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42476step1 raw42476step1Labels raw42476step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

theorem canonical42477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42477 raw42477Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw42477 raw42477Labels = mixedMoment B raw42477step0 raw42477step0Labels := by
      have ha : raw42477step0 = (fun i j => raw42477 (permutation493 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42477step0 raw42477; decide +kernel
      have hl : raw42477step0Labels = raw42477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42477 raw42477Labels permutation493 permutation6
    _ = mixedMoment B node5129 node5129Labels := by rfl

theorem canonical42478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42478 raw42478Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw42478 raw42478Labels = mixedMoment B raw42478step0 raw42478step0Labels := by
      have ha : raw42478step0 = (fun i j => raw42478 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42478step0 raw42478; decide +kernel
      have hl : raw42478step0Labels = raw42478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42478 raw42478Labels permutation156 permutation2
    mixedMoment B raw42478step0 raw42478step0Labels = mixedMoment B raw42478step1 raw42478step1Labels := by
      have ha : raw42478step1 = raw42478step0 := by apply Matrix.ext; unfold raw42478step1 raw42478step0; decide +kernel
      have hl : raw42478step0Labels = labelEmbedding1 ∘ raw42478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42478step0 raw42478step0Labels raw42478step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

theorem canonical42479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42479 raw42479Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw42479 raw42479Labels = mixedMoment B raw42479step0 raw42479step0Labels := by
      have ha : raw42479step0 = (fun i j => raw42479 (permutation361 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42479step0 raw42479; decide +kernel
      have hl : raw42479step0Labels = raw42479Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42479 raw42479Labels permutation361 permutation6
    mixedMoment B raw42479step0 raw42479step0Labels = mixedMoment B raw42479step1 raw42479step1Labels := by
      have ha : raw42479step1 = -raw42479step0 := by apply Matrix.ext; change ∀ i j, raw42479step1 i j = -(raw42479step0 i j); unfold raw42479step1 raw42479step0; decide +kernel
      have hl : raw42479step1Labels = raw42479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5377 node5377Labels := by rfl

theorem canonical42480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42480 raw42480Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw42480 raw42480Labels = mixedMoment B raw42480step0 raw42480step0Labels := by
      have hz : ∀ j, raw42480 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42480step0 = (fun i j => raw42480 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42480step0 raw42480; decide +kernel
      have hl : raw42480step0Labels = raw42480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42480 raw42480Labels permutation520 hz
    mixedMoment B raw42480step0 raw42480step0Labels = mixedMoment B raw42480step1 raw42480step1Labels := by
      have hz : ∀ j, raw42480step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42480step1 = (fun i j => raw42480step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42480step1 raw42480step0; decide +kernel
      have hl : raw42480step1Labels = raw42480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42480step0 raw42480step0Labels permutation104 hz
    mixedMoment B raw42480step1 raw42480step1Labels = mixedMoment B raw42480step2 raw42480step2Labels := by
      have ha : raw42480step2 = (fun i j => raw42480step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42480step2 raw42480step1; decide +kernel
      have hl : raw42480step2Labels = raw42480step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42480step1 raw42480step1Labels permutation22 permutation4
    mixedMoment B raw42480step2 raw42480step2Labels = mixedMoment B raw42480step3 raw42480step3Labels := by
      have ha : raw42480step3 = -raw42480step2 := by apply Matrix.ext; change ∀ i j, raw42480step3 i j = -(raw42480step2 i j); unfold raw42480step3 raw42480step2; decide +kernel
      have hl : raw42480step3Labels = raw42480step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42480step3 raw42480step3Labels = mixedMoment B raw42480step4 raw42480step4Labels := by
      have ha : raw42480step4 = raw42480step3 := by apply Matrix.ext; unfold raw42480step4 raw42480step3; decide +kernel
      have hl : raw42480step3Labels = labelEmbedding1 ∘ raw42480step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42480step3 raw42480step3Labels raw42480step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2255 node2255Labels := by rfl

theorem canonical42481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42481 raw42481Labels = mixedMoment B node4892 node4892Labels := by
  calc
    mixedMoment B raw42481 raw42481Labels = mixedMoment B raw42481step0 raw42481step0Labels := by
      have hz : ∀ j, raw42481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42481step0 = (fun i j => raw42481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42481step0 raw42481; decide +kernel
      have hl : raw42481step0Labels = raw42481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42481 raw42481Labels permutation520 hz
    mixedMoment B raw42481step0 raw42481step0Labels = mixedMoment B raw42481step1 raw42481step1Labels := by
      have hz : ∀ j, raw42481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42481step1 = (fun i j => raw42481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42481step1 raw42481step0; decide +kernel
      have hl : raw42481step1Labels = raw42481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42481step0 raw42481step0Labels permutation104 hz
    mixedMoment B raw42481step1 raw42481step1Labels = mixedMoment B raw42481step2 raw42481step2Labels := by
      have ha : raw42481step2 = (fun i j => raw42481step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42481step2 raw42481step1; decide +kernel
      have hl : raw42481step2Labels = raw42481step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42481step1 raw42481step1Labels permutation22 permutation4
    mixedMoment B raw42481step2 raw42481step2Labels = mixedMoment B raw42481step3 raw42481step3Labels := by
      have ha : raw42481step3 = -raw42481step2 := by apply Matrix.ext; change ∀ i j, raw42481step3 i j = -(raw42481step2 i j); unfold raw42481step3 raw42481step2; decide +kernel
      have hl : raw42481step3Labels = raw42481step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42481step3 raw42481step3Labels = mixedMoment B raw42481step4 raw42481step4Labels := by
      have ha : raw42481step4 = raw42481step3 := by apply Matrix.ext; unfold raw42481step4 raw42481step3; decide +kernel
      have hl : raw42481step3Labels = labelEmbedding10 ∘ raw42481step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42481step3 raw42481step3Labels raw42481step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4892 node4892Labels := by rfl

theorem canonical42482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42482 raw42482Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw42482 raw42482Labels = mixedMoment B raw42482step0 raw42482step0Labels := by
      have hz : ∀ j, raw42482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42482step0 = (fun i j => raw42482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42482step0 raw42482; decide +kernel
      have hl : raw42482step0Labels = raw42482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42482 raw42482Labels permutation434 hz
    mixedMoment B raw42482step0 raw42482step0Labels = mixedMoment B raw42482step1 raw42482step1Labels := by
      have ha : raw42482step1 = (fun i j => raw42482step0 (permutation94 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42482step1 raw42482step0; decide +kernel
      have hl : raw42482step1Labels = raw42482step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42482step0 raw42482step0Labels permutation94 permutation4
    mixedMoment B raw42482step1 raw42482step1Labels = mixedMoment B raw42482step2 raw42482step2Labels := by
      have ha : raw42482step2 = -raw42482step1 := by apply Matrix.ext; change ∀ i j, raw42482step2 i j = -(raw42482step1 i j); unfold raw42482step2 raw42482step1; decide +kernel
      have hl : raw42482step2Labels = raw42482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42482step2 raw42482step2Labels = mixedMoment B raw42482step3 raw42482step3Labels := by
      have ha : raw42482step3 = raw42482step2 := by apply Matrix.ext; unfold raw42482step3 raw42482step2; decide +kernel
      have hl : raw42482step2Labels = labelEmbedding1 ∘ raw42482step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42482step2 raw42482step2Labels raw42482step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

theorem canonical42483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42483 raw42483Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw42483 raw42483Labels = mixedMoment B raw42483step0 raw42483step0Labels := by
      have hz : ∀ j, raw42483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42483step0 = (fun i j => raw42483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42483step0 raw42483; decide +kernel
      have hl : raw42483step0Labels = raw42483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42483 raw42483Labels permutation434 hz
    mixedMoment B raw42483step0 raw42483step0Labels = mixedMoment B raw42483step1 raw42483step1Labels := by
      have ha : raw42483step1 = (fun i j => raw42483step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42483step1 raw42483step0; decide +kernel
      have hl : raw42483step1Labels = raw42483step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42483step0 raw42483step0Labels permutation95 permutation6
    _ = mixedMoment B node4836 node4836Labels := by rfl

theorem canonical42484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42484 raw42484Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw42484 raw42484Labels = mixedMoment B raw42484step0 raw42484step0Labels := by
      have hz : ∀ j, raw42484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42484step0 = (fun i j => raw42484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42484step0 raw42484; decide +kernel
      have hl : raw42484step0Labels = raw42484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42484 raw42484Labels permutation434 hz
    mixedMoment B raw42484step0 raw42484step0Labels = mixedMoment B raw42484step1 raw42484step1Labels := by
      have ha : raw42484step1 = (fun i j => raw42484step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42484step1 raw42484step0; decide +kernel
      have hl : raw42484step1Labels = raw42484step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42484step0 raw42484step0Labels permutation86 permutation4
    mixedMoment B raw42484step1 raw42484step1Labels = mixedMoment B raw42484step2 raw42484step2Labels := by
      have ha : raw42484step2 = -raw42484step1 := by apply Matrix.ext; change ∀ i j, raw42484step2 i j = -(raw42484step1 i j); unfold raw42484step2 raw42484step1; decide +kernel
      have hl : raw42484step2Labels = raw42484step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42484step2 raw42484step2Labels = mixedMoment B raw42484step3 raw42484step3Labels := by
      have ha : raw42484step3 = raw42484step2 := by apply Matrix.ext; unfold raw42484step3 raw42484step2; decide +kernel
      have hl : raw42484step2Labels = labelEmbedding1 ∘ raw42484step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42484step2 raw42484step2Labels raw42484step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

theorem canonical42485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42485 raw42485Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw42485 raw42485Labels = mixedMoment B raw42485step0 raw42485step0Labels := by
      have hz : ∀ j, raw42485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42485step0 = (fun i j => raw42485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42485step0 raw42485; decide +kernel
      have hl : raw42485step0Labels = raw42485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42485 raw42485Labels permutation434 hz
    mixedMoment B raw42485step0 raw42485step0Labels = mixedMoment B raw42485step1 raw42485step1Labels := by
      have ha : raw42485step1 = (fun i j => raw42485step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42485step1 raw42485step0; decide +kernel
      have hl : raw42485step1Labels = raw42485step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42485step0 raw42485step0Labels permutation86 permutation4
    mixedMoment B raw42485step1 raw42485step1Labels = mixedMoment B raw42485step2 raw42485step2Labels := by
      have ha : raw42485step2 = -raw42485step1 := by apply Matrix.ext; change ∀ i j, raw42485step2 i j = -(raw42485step1 i j); unfold raw42485step2 raw42485step1; decide +kernel
      have hl : raw42485step2Labels = raw42485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42485step2 raw42485step2Labels = mixedMoment B raw42485step3 raw42485step3Labels := by
      have ha : raw42485step3 = raw42485step2 := by apply Matrix.ext; unfold raw42485step3 raw42485step2; decide +kernel
      have hl : raw42485step2Labels = labelEmbedding10 ∘ raw42485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42485step2 raw42485step2Labels raw42485step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

theorem canonical42486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42486 raw42486Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw42486 raw42486Labels = mixedMoment B raw42486step0 raw42486step0Labels := by
      have hz : ∀ j, raw42486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42486step0 = (fun i j => raw42486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42486step0 raw42486; decide +kernel
      have hl : raw42486step0Labels = raw42486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42486 raw42486Labels permutation434 hz
    mixedMoment B raw42486step0 raw42486step0Labels = mixedMoment B raw42486step1 raw42486step1Labels := by
      have ha : raw42486step1 = (fun i j => raw42486step0 (permutation87 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42486step1 raw42486step0; decide +kernel
      have hl : raw42486step1Labels = raw42486step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42486step0 raw42486step0Labels permutation87 permutation4
    mixedMoment B raw42486step1 raw42486step1Labels = mixedMoment B raw42486step2 raw42486step2Labels := by
      have ha : raw42486step2 = -raw42486step1 := by apply Matrix.ext; change ∀ i j, raw42486step2 i j = -(raw42486step1 i j); unfold raw42486step2 raw42486step1; decide +kernel
      have hl : raw42486step2Labels = raw42486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42486step2 raw42486step2Labels = mixedMoment B raw42486step3 raw42486step3Labels := by
      have ha : raw42486step3 = raw42486step2 := by apply Matrix.ext; unfold raw42486step3 raw42486step2; decide +kernel
      have hl : raw42486step2Labels = labelEmbedding1 ∘ raw42486step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42486step2 raw42486step2Labels raw42486step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

theorem canonical42487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42487 raw42487Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw42487 raw42487Labels = mixedMoment B raw42487step0 raw42487step0Labels := by
      have hz : ∀ j, raw42487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42487step0 = (fun i j => raw42487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42487step0 raw42487; decide +kernel
      have hl : raw42487step0Labels = raw42487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42487 raw42487Labels permutation434 hz
    mixedMoment B raw42487step0 raw42487step0Labels = mixedMoment B raw42487step1 raw42487step1Labels := by
      have ha : raw42487step1 = (fun i j => raw42487step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42487step1 raw42487step0; decide +kernel
      have hl : raw42487step1Labels = raw42487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42487step0 raw42487step0Labels permutation101 permutation6
    _ = mixedMoment B node4867 node4867Labels := by rfl

theorem canonical42488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42488 raw42488Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw42488 raw42488Labels = mixedMoment B raw42488step0 raw42488step0Labels := by
      have hz : ∀ j, raw42488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42488step0 = (fun i j => raw42488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42488step0 raw42488; decide +kernel
      have hl : raw42488step0Labels = raw42488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42488 raw42488Labels permutation434 hz
    mixedMoment B raw42488step0 raw42488step0Labels = mixedMoment B raw42488step1 raw42488step1Labels := by
      have ha : raw42488step1 = (fun i j => raw42488step0 (permutation100 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42488step1 raw42488step0; decide +kernel
      have hl : raw42488step1Labels = raw42488step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42488step0 raw42488step0Labels permutation100 permutation4
    mixedMoment B raw42488step1 raw42488step1Labels = mixedMoment B raw42488step2 raw42488step2Labels := by
      have ha : raw42488step2 = -raw42488step1 := by apply Matrix.ext; change ∀ i j, raw42488step2 i j = -(raw42488step1 i j); unfold raw42488step2 raw42488step1; decide +kernel
      have hl : raw42488step2Labels = raw42488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42488step2 raw42488step2Labels = mixedMoment B raw42488step3 raw42488step3Labels := by
      have ha : raw42488step3 = raw42488step2 := by apply Matrix.ext; unfold raw42488step3 raw42488step2; decide +kernel
      have hl : raw42488step2Labels = labelEmbedding1 ∘ raw42488step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42488step2 raw42488step2Labels raw42488step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

theorem canonical42489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42489 raw42489Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw42489 raw42489Labels = mixedMoment B raw42489step0 raw42489step0Labels := by
      have hz : ∀ j, raw42489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42489step0 = (fun i j => raw42489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42489step0 raw42489; decide +kernel
      have hl : raw42489step0Labels = raw42489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42489 raw42489Labels permutation434 hz
    mixedMoment B raw42489step0 raw42489step0Labels = mixedMoment B raw42489step1 raw42489step1Labels := by
      have ha : raw42489step1 = (fun i j => raw42489step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42489step1 raw42489step0; decide +kernel
      have hl : raw42489step1Labels = raw42489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42489step0 raw42489step0Labels permutation100 permutation6
    _ = mixedMoment B node4683 node4683Labels := by rfl

theorem canonical42490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42490 raw42490Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw42490 raw42490Labels = mixedMoment B raw42490step0 raw42490step0Labels := by
      have ha : raw42490step0 = (fun i j => raw42490 (permutation403 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42490step0 raw42490; decide +kernel
      have hl : raw42490step0Labels = raw42490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42490 raw42490Labels permutation403 permutation4
    mixedMoment B raw42490step0 raw42490step0Labels = mixedMoment B raw42490step1 raw42490step1Labels := by
      have ha : raw42490step1 = -raw42490step0 := by apply Matrix.ext; change ∀ i j, raw42490step1 i j = -(raw42490step0 i j); unfold raw42490step1 raw42490step0; decide +kernel
      have hl : raw42490step1Labels = raw42490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42490step1 raw42490step1Labels = mixedMoment B raw42490step2 raw42490step2Labels := by
      have ha : raw42490step2 = raw42490step1 := by apply Matrix.ext; unfold raw42490step2 raw42490step1; decide +kernel
      have hl : raw42490step1Labels = labelEmbedding1 ∘ raw42490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42490step1 raw42490step1Labels raw42490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

theorem canonical42491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42491 raw42491Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw42491 raw42491Labels = mixedMoment B raw42491step0 raw42491step0Labels := by
      have ha : raw42491step0 = (fun i j => raw42491 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42491step0 raw42491; decide +kernel
      have hl : raw42491step0Labels = raw42491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42491 raw42491Labels permutation412 permutation6
    _ = mixedMoment B node4816 node4816Labels := by rfl

theorem canonical42492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42492 raw42492Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw42492 raw42492Labels = mixedMoment B raw42492step0 raw42492step0Labels := by
      have ha : raw42492step0 = (fun i j => raw42492 (permutation371 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42492step0 raw42492; decide +kernel
      have hl : raw42492step0Labels = raw42492Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42492 raw42492Labels permutation371 permutation4
    mixedMoment B raw42492step0 raw42492step0Labels = mixedMoment B raw42492step1 raw42492step1Labels := by
      have ha : raw42492step1 = -raw42492step0 := by apply Matrix.ext; change ∀ i j, raw42492step1 i j = -(raw42492step0 i j); unfold raw42492step1 raw42492step0; decide +kernel
      have hl : raw42492step1Labels = raw42492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42492step1 raw42492step1Labels = mixedMoment B raw42492step2 raw42492step2Labels := by
      have ha : raw42492step2 = raw42492step1 := by apply Matrix.ext; unfold raw42492step2 raw42492step1; decide +kernel
      have hl : raw42492step1Labels = labelEmbedding1 ∘ raw42492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42492step1 raw42492step1Labels raw42492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

theorem canonical42493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42493 raw42493Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw42493 raw42493Labels = mixedMoment B raw42493step0 raw42493step0Labels := by
      have ha : raw42493step0 = (fun i j => raw42493 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42493step0 raw42493; decide +kernel
      have hl : raw42493step0Labels = raw42493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42493 raw42493Labels permutation431 permutation6
    _ = mixedMoment B node4852 node4852Labels := by rfl

theorem canonical42494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42494 raw42494Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw42494 raw42494Labels = mixedMoment B raw42494step0 raw42494step0Labels := by
      have ha : raw42494step0 = (fun i j => raw42494 (permutation419 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42494step0 raw42494; decide +kernel
      have hl : raw42494step0Labels = raw42494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42494 raw42494Labels permutation419 permutation4
    mixedMoment B raw42494step0 raw42494step0Labels = mixedMoment B raw42494step1 raw42494step1Labels := by
      have ha : raw42494step1 = -raw42494step0 := by apply Matrix.ext; change ∀ i j, raw42494step1 i j = -(raw42494step0 i j); unfold raw42494step1 raw42494step0; decide +kernel
      have hl : raw42494step1Labels = raw42494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42494step1 raw42494step1Labels = mixedMoment B raw42494step2 raw42494step2Labels := by
      have ha : raw42494step2 = raw42494step1 := by apply Matrix.ext; unfold raw42494step2 raw42494step1; decide +kernel
      have hl : raw42494step1Labels = labelEmbedding1 ∘ raw42494step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42494step1 raw42494step1Labels raw42494step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

theorem canonical42495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42495 raw42495Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw42495 raw42495Labels = mixedMoment B raw42495step0 raw42495step0Labels := by
      have ha : raw42495step0 = (fun i j => raw42495 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42495step0 raw42495; decide +kernel
      have hl : raw42495step0Labels = raw42495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42495 raw42495Labels permutation421 permutation6
    _ = mixedMoment B node4680 node4680Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2560 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2560) =
      Integer.Sparse.eval keyMomentRow2560 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3037) := by
    have ha : gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge = raw42432 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42432Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42432 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge = raw42433 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42433Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42433 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2560).leftCharge (GramAssembly.key 2560).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2560, Integer.Sparse.eval]
  ring

theorem keyMoment2561 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2561) =
      Integer.Sparse.eval keyMomentRow2561 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3847) := by
    have ha : gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge = raw42434 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42434Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42434 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5406) := by
    have ha : gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge = raw42435 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42435Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42435 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2561).leftCharge (GramAssembly.key 2561).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2561, Integer.Sparse.eval]
  ring

theorem keyMoment2562 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2562) =
      Integer.Sparse.eval keyMomentRow2562 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3846) := by
    have ha : gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge = raw42436 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42436Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42436 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5429) := by
    have ha : gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge = raw42437 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42437Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42437 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2562).leftCharge (GramAssembly.key 2562).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2562, Integer.Sparse.eval]
  ring

theorem keyMoment2563 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2563) =
      Integer.Sparse.eval keyMomentRow2563 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2676) := by
    have ha : gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge = raw42438 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42438Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42438 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5231) := by
    have ha : gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge = raw42439 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42439Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42439 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2563).leftCharge (GramAssembly.key 2563).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2563, Integer.Sparse.eval]
  ring

theorem keyMoment2564 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2564) =
      Integer.Sparse.eval keyMomentRow2564 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge = raw42440 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42440Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42440 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge = raw42441 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42441Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42441 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2564).leftCharge (GramAssembly.key 2564).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2564, Integer.Sparse.eval]
  ring

theorem keyMoment2565 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2565) =
      Integer.Sparse.eval keyMomentRow2565 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2681) := by
    have ha : gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge = raw42442 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42442Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42442 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5151) := by
    have ha : gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge = raw42443 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42443Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42443 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2565).leftCharge (GramAssembly.key 2565).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2565, Integer.Sparse.eval]
  ring

theorem keyMoment2566 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2566) =
      Integer.Sparse.eval keyMomentRow2566 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3839) := by
    have ha : gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge = raw42444 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42444Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42444 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5425) := by
    have ha : gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge = raw42445 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42445Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42445 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2566).leftCharge (GramAssembly.key 2566).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2566, Integer.Sparse.eval]
  ring

theorem keyMoment2567 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2567) =
      Integer.Sparse.eval keyMomentRow2567 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3557) := by
    have ha : gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge = raw42446 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42446Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42446 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5144) := by
    have ha : gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge = raw42447 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42447Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42447 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2567).leftCharge (GramAssembly.key 2567).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2567, Integer.Sparse.eval]
  ring

theorem keyMoment2568 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2568) =
      Integer.Sparse.eval keyMomentRow2568 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge = raw42448 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42448Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42448 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge = raw42449 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42449Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42449 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2568).leftCharge (GramAssembly.key 2568).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2568, Integer.Sparse.eval]
  ring

theorem keyMoment2569 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2569) =
      Integer.Sparse.eval keyMomentRow2569 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3848) := by
    have ha : gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge = raw42450 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42450Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42450 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5430) := by
    have ha : gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge = raw42451 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42451Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42451 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2569).leftCharge (GramAssembly.key 2569).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2569, Integer.Sparse.eval]
  ring

theorem keyMoment2570 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2570) =
      Integer.Sparse.eval keyMomentRow2570 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3052) := by
    have ha : gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge = raw42452 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42452Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42452 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge = raw42453 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42453Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42453 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2570).leftCharge (GramAssembly.key 2570).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2570, Integer.Sparse.eval]
  ring

theorem keyMoment2571 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2571) =
      Integer.Sparse.eval keyMomentRow2571 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2683) := by
    have ha : gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge = raw42454 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42454Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42454 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4611) := by
    have ha : gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge = raw42455 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42455Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42455 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2571).leftCharge (GramAssembly.key 2571).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2571, Integer.Sparse.eval]
  ring

theorem keyMoment2572 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2572) =
      Integer.Sparse.eval keyMomentRow2572 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3541) := by
    have ha : gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge = raw42456 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42456Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42456 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge = raw42457 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42457Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42457 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2572).leftCharge (GramAssembly.key 2572).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2572, Integer.Sparse.eval]
  ring

theorem keyMoment2573 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2573) =
      Integer.Sparse.eval keyMomentRow2573 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3296) := by
    have ha : gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge = raw42458 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42458Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42458 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4607) := by
    have ha : gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge = raw42459 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42459Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42459 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2573).leftCharge (GramAssembly.key 2573).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2573, Integer.Sparse.eval]
  ring

theorem keyMoment2574 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2574) =
      Integer.Sparse.eval keyMomentRow2574 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3295) := by
    have ha : gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge = raw42460 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42460Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42460 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4592) := by
    have ha : gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge = raw42461 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42461Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42461 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2574).leftCharge (GramAssembly.key 2574).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2574, Integer.Sparse.eval]
  ring

theorem keyMoment2575 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2575) =
      Integer.Sparse.eval keyMomentRow2575 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2670) := by
    have ha : gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge = raw42462 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42462Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42462 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5140) := by
    have ha : gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge = raw42463 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42463Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42463 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2575).leftCharge (GramAssembly.key 2575).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2575, Integer.Sparse.eval]
  ring

theorem keyMoment2576 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2576) =
      Integer.Sparse.eval keyMomentRow2576 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3540) := by
    have ha : gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge = raw42464 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42464Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42464 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge = raw42465 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42465Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42465 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2576).leftCharge (GramAssembly.key 2576).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2576, Integer.Sparse.eval]
  ring

theorem keyMoment2577 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2577) =
      Integer.Sparse.eval keyMomentRow2577 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2682) := by
    have ha : gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge = raw42466 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42466Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42466 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5236) := by
    have ha : gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge = raw42467 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42467Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42467 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2577).leftCharge (GramAssembly.key 2577).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2577, Integer.Sparse.eval]
  ring

theorem keyMoment2578 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2578) =
      Integer.Sparse.eval keyMomentRow2578 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3288) := by
    have ha : gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge = raw42468 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42468Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42468 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4589) := by
    have ha : gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge = raw42469 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42469Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42469 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2578).leftCharge (GramAssembly.key 2578).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2578, Integer.Sparse.eval]
  ring

theorem keyMoment2579 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2579) =
      Integer.Sparse.eval keyMomentRow2579 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3517) := by
    have ha : gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge = raw42470 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42470Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42470 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5138) := by
    have ha : gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge = raw42471 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42471Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42471 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2579).leftCharge (GramAssembly.key 2579).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2579, Integer.Sparse.eval]
  ring

theorem keyMoment2580 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2580) =
      Integer.Sparse.eval keyMomentRow2580 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3539) := by
    have ha : gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge = raw42472 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42472Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42472 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge = raw42473 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42473Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42473 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2580).leftCharge (GramAssembly.key 2580).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2580, Integer.Sparse.eval]
  ring

theorem keyMoment2581 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2581) =
      Integer.Sparse.eval keyMomentRow2581 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3842) := by
    have ha : gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge = raw42474 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42474Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42474 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5419) := by
    have ha : gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge = raw42475 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42475Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42475 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2581).leftCharge (GramAssembly.key 2581).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2581, Integer.Sparse.eval]
  ring

theorem keyMoment2582 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2582) =
      Integer.Sparse.eval keyMomentRow2582 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3516) := by
    have ha : gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge = raw42476 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42476Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42476 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5129) := by
    have ha : gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge = raw42477 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42477Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42477 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2582).leftCharge (GramAssembly.key 2582).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2582, Integer.Sparse.eval]
  ring

theorem keyMoment2583 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2583) =
      Integer.Sparse.eval keyMomentRow2583 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3835) := by
    have ha : gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge = raw42478 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42478Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42478 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5377) := by
    have ha : gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge = raw42479 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42479Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42479 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2583).leftCharge (GramAssembly.key 2583).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2583, Integer.Sparse.eval]
  ring

theorem keyMoment2584 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2584) =
      Integer.Sparse.eval keyMomentRow2584 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2255) := by
    have ha : gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge = raw42480 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42480Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42480 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4892) := by
    have ha : gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge = raw42481 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42481Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42481 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2584).leftCharge (GramAssembly.key 2584).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2584, Integer.Sparse.eval]
  ring

theorem keyMoment2585 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2585) =
      Integer.Sparse.eval keyMomentRow2585 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2197) := by
    have ha : gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge = raw42482 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42482Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42482 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4836) := by
    have ha : gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge = raw42483 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42483Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42483 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2585).leftCharge (GramAssembly.key 2585).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2585, Integer.Sparse.eval]
  ring

theorem keyMoment2586 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2586) =
      Integer.Sparse.eval keyMomentRow2586 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2253) := by
    have ha : gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge = raw42484 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42484Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42484 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4891) := by
    have ha : gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge = raw42485 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42485Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42485 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2586).leftCharge (GramAssembly.key 2586).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2586, Integer.Sparse.eval]
  ring

theorem keyMoment2587 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2587) =
      Integer.Sparse.eval keyMomentRow2587 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2251) := by
    have ha : gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge = raw42486 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42486Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42486 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4867) := by
    have ha : gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge = raw42487 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42487Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42487 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2587).leftCharge (GramAssembly.key 2587).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2587, Integer.Sparse.eval]
  ring

theorem keyMoment2588 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2588) =
      Integer.Sparse.eval keyMomentRow2588 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2146) := by
    have ha : gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge = raw42488 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42488Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42488 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4683) := by
    have ha : gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge = raw42489 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42489Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42489 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2588).leftCharge (GramAssembly.key 2588).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2588, Integer.Sparse.eval]
  ring

theorem keyMoment2589 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2589) =
      Integer.Sparse.eval keyMomentRow2589 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2196) := by
    have ha : gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge = raw42490 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42490Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42490 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4816) := by
    have ha : gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge = raw42491 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42491Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42491 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2589).leftCharge (GramAssembly.key 2589).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2589, Integer.Sparse.eval]
  ring

theorem keyMoment2590 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2590) =
      Integer.Sparse.eval keyMomentRow2590 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2250) := by
    have ha : gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge = raw42492 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42492Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42492 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4852) := by
    have ha : gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge = raw42493 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42493Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42493 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2590).leftCharge (GramAssembly.key 2590).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2590, Integer.Sparse.eval]
  ring

theorem keyMoment2591 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2591) =
      Integer.Sparse.eval keyMomentRow2591 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2145) := by
    have ha : gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge = raw42494 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42494Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42494 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4680) := by
    have ha : gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge = raw42495 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42495Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42495 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2591).leftCharge (GramAssembly.key 2591).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2591, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk80
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2560 : keyMomentRows (2560 : Fin 2886) =
    keyMomentRow2560 := by decide +kernel

theorem keyMomentRowsAt2561 : keyMomentRows (2561 : Fin 2886) =
    keyMomentRow2561 := by decide +kernel

theorem keyMomentRowsAt2562 : keyMomentRows (2562 : Fin 2886) =
    keyMomentRow2562 := by decide +kernel

theorem keyMomentRowsAt2563 : keyMomentRows (2563 : Fin 2886) =
    keyMomentRow2563 := by decide +kernel

theorem keyMomentRowsAt2564 : keyMomentRows (2564 : Fin 2886) =
    keyMomentRow2564 := by decide +kernel

theorem keyMomentRowsAt2565 : keyMomentRows (2565 : Fin 2886) =
    keyMomentRow2565 := by decide +kernel

theorem keyMomentRowsAt2566 : keyMomentRows (2566 : Fin 2886) =
    keyMomentRow2566 := by decide +kernel

theorem keyMomentRowsAt2567 : keyMomentRows (2567 : Fin 2886) =
    keyMomentRow2567 := by decide +kernel

theorem keyMomentRowsAt2568 : keyMomentRows (2568 : Fin 2886) =
    keyMomentRow2568 := by decide +kernel

theorem keyMomentRowsAt2569 : keyMomentRows (2569 : Fin 2886) =
    keyMomentRow2569 := by decide +kernel

theorem keyMomentRowsAt2570 : keyMomentRows (2570 : Fin 2886) =
    keyMomentRow2570 := by decide +kernel

theorem keyMomentRowsAt2571 : keyMomentRows (2571 : Fin 2886) =
    keyMomentRow2571 := by decide +kernel

theorem keyMomentRowsAt2572 : keyMomentRows (2572 : Fin 2886) =
    keyMomentRow2572 := by decide +kernel

theorem keyMomentRowsAt2573 : keyMomentRows (2573 : Fin 2886) =
    keyMomentRow2573 := by decide +kernel

theorem keyMomentRowsAt2574 : keyMomentRows (2574 : Fin 2886) =
    keyMomentRow2574 := by decide +kernel

theorem keyMomentRowsAt2575 : keyMomentRows (2575 : Fin 2886) =
    keyMomentRow2575 := by decide +kernel

theorem keyMomentRowsAt2576 : keyMomentRows (2576 : Fin 2886) =
    keyMomentRow2576 := by decide +kernel

theorem keyMomentRowsAt2577 : keyMomentRows (2577 : Fin 2886) =
    keyMomentRow2577 := by decide +kernel

theorem keyMomentRowsAt2578 : keyMomentRows (2578 : Fin 2886) =
    keyMomentRow2578 := by decide +kernel

theorem keyMomentRowsAt2579 : keyMomentRows (2579 : Fin 2886) =
    keyMomentRow2579 := by decide +kernel

theorem keyMomentRowsAt2580 : keyMomentRows (2580 : Fin 2886) =
    keyMomentRow2580 := by decide +kernel

theorem keyMomentRowsAt2581 : keyMomentRows (2581 : Fin 2886) =
    keyMomentRow2581 := by decide +kernel

theorem keyMomentRowsAt2582 : keyMomentRows (2582 : Fin 2886) =
    keyMomentRow2582 := by decide +kernel

theorem keyMomentRowsAt2583 : keyMomentRows (2583 : Fin 2886) =
    keyMomentRow2583 := by decide +kernel

theorem keyMomentRowsAt2584 : keyMomentRows (2584 : Fin 2886) =
    keyMomentRow2584 := by decide +kernel

theorem keyMomentRowsAt2585 : keyMomentRows (2585 : Fin 2886) =
    keyMomentRow2585 := by decide +kernel

theorem keyMomentRowsAt2586 : keyMomentRows (2586 : Fin 2886) =
    keyMomentRow2586 := by decide +kernel

theorem keyMomentRowsAt2587 : keyMomentRows (2587 : Fin 2886) =
    keyMomentRow2587 := by decide +kernel

theorem keyMomentRowsAt2588 : keyMomentRows (2588 : Fin 2886) =
    keyMomentRow2588 := by decide +kernel

theorem keyMomentRowsAt2589 : keyMomentRows (2589 : Fin 2886) =
    keyMomentRow2589 := by decide +kernel

theorem keyMomentRowsAt2590 : keyMomentRows (2590 : Fin 2886) =
    keyMomentRow2590 := by decide +kernel

theorem keyMomentRowsAt2591 : keyMomentRows (2591 : Fin 2886) =
    keyMomentRow2591 := by decide +kernel

theorem keyMomentChunkSound80_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 80) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2560 ∨ k.val = 2561 ∨ k.val = 2562 ∨ k.val = 2563 ∨ k.val = 2564 ∨ k.val = 2565 ∨ k.val = 2566 ∨ k.val = 2567 ∨ k.val = 2568 ∨ k.val = 2569 ∨ k.val = 2570 ∨ k.val = 2571 ∨ k.val = 2572 ∨ k.val = 2573 ∨ k.val = 2574 ∨ k.val = 2575 ∨ k.val = 2576 ∨ k.val = 2577 ∨ k.val = 2578 ∨ k.val = 2579 ∨ k.val = 2580 ∨ k.val = 2581 ∨ k.val = 2582 ∨ k.val = 2583 ∨ k.val = 2584 ∨ k.val = 2585 ∨ k.val = 2586 ∨ k.val = 2587 ∨ k.val = 2588 ∨ k.val = 2589 ∨ k.val = 2590 ∨ k.val = 2591 := by omega
  rcases heq with h2560 | h2561 | h2562 | h2563 | h2564 | h2565 | h2566 | h2567 | h2568 | h2569 | h2570 | h2571 | h2572 | h2573 | h2574 | h2575 | h2576 | h2577 | h2578 | h2579 | h2580 | h2581 | h2582 | h2583 | h2584 | h2585 | h2586 | h2587 | h2588 | h2589 | h2590 | h2591
  · have he : k = (2560 : Fin 2886) := Fin.ext h2560
    subst k
    rw [keyMomentRowsAt2560]
    exact keyMoment2560 B hB
  · have he : k = (2561 : Fin 2886) := Fin.ext h2561
    subst k
    rw [keyMomentRowsAt2561]
    exact keyMoment2561 B hB
  · have he : k = (2562 : Fin 2886) := Fin.ext h2562
    subst k
    rw [keyMomentRowsAt2562]
    exact keyMoment2562 B hB
  · have he : k = (2563 : Fin 2886) := Fin.ext h2563
    subst k
    rw [keyMomentRowsAt2563]
    exact keyMoment2563 B hB
  · have he : k = (2564 : Fin 2886) := Fin.ext h2564
    subst k
    rw [keyMomentRowsAt2564]
    exact keyMoment2564 B hB
  · have he : k = (2565 : Fin 2886) := Fin.ext h2565
    subst k
    rw [keyMomentRowsAt2565]
    exact keyMoment2565 B hB
  · have he : k = (2566 : Fin 2886) := Fin.ext h2566
    subst k
    rw [keyMomentRowsAt2566]
    exact keyMoment2566 B hB
  · have he : k = (2567 : Fin 2886) := Fin.ext h2567
    subst k
    rw [keyMomentRowsAt2567]
    exact keyMoment2567 B hB
  · have he : k = (2568 : Fin 2886) := Fin.ext h2568
    subst k
    rw [keyMomentRowsAt2568]
    exact keyMoment2568 B hB
  · have he : k = (2569 : Fin 2886) := Fin.ext h2569
    subst k
    rw [keyMomentRowsAt2569]
    exact keyMoment2569 B hB
  · have he : k = (2570 : Fin 2886) := Fin.ext h2570
    subst k
    rw [keyMomentRowsAt2570]
    exact keyMoment2570 B hB
  · have he : k = (2571 : Fin 2886) := Fin.ext h2571
    subst k
    rw [keyMomentRowsAt2571]
    exact keyMoment2571 B hB
  · have he : k = (2572 : Fin 2886) := Fin.ext h2572
    subst k
    rw [keyMomentRowsAt2572]
    exact keyMoment2572 B hB
  · have he : k = (2573 : Fin 2886) := Fin.ext h2573
    subst k
    rw [keyMomentRowsAt2573]
    exact keyMoment2573 B hB
  · have he : k = (2574 : Fin 2886) := Fin.ext h2574
    subst k
    rw [keyMomentRowsAt2574]
    exact keyMoment2574 B hB
  · have he : k = (2575 : Fin 2886) := Fin.ext h2575
    subst k
    rw [keyMomentRowsAt2575]
    exact keyMoment2575 B hB
  · have he : k = (2576 : Fin 2886) := Fin.ext h2576
    subst k
    rw [keyMomentRowsAt2576]
    exact keyMoment2576 B hB
  · have he : k = (2577 : Fin 2886) := Fin.ext h2577
    subst k
    rw [keyMomentRowsAt2577]
    exact keyMoment2577 B hB
  · have he : k = (2578 : Fin 2886) := Fin.ext h2578
    subst k
    rw [keyMomentRowsAt2578]
    exact keyMoment2578 B hB
  · have he : k = (2579 : Fin 2886) := Fin.ext h2579
    subst k
    rw [keyMomentRowsAt2579]
    exact keyMoment2579 B hB
  · have he : k = (2580 : Fin 2886) := Fin.ext h2580
    subst k
    rw [keyMomentRowsAt2580]
    exact keyMoment2580 B hB
  · have he : k = (2581 : Fin 2886) := Fin.ext h2581
    subst k
    rw [keyMomentRowsAt2581]
    exact keyMoment2581 B hB
  · have he : k = (2582 : Fin 2886) := Fin.ext h2582
    subst k
    rw [keyMomentRowsAt2582]
    exact keyMoment2582 B hB
  · have he : k = (2583 : Fin 2886) := Fin.ext h2583
    subst k
    rw [keyMomentRowsAt2583]
    exact keyMoment2583 B hB
  · have he : k = (2584 : Fin 2886) := Fin.ext h2584
    subst k
    rw [keyMomentRowsAt2584]
    exact keyMoment2584 B hB
  · have he : k = (2585 : Fin 2886) := Fin.ext h2585
    subst k
    rw [keyMomentRowsAt2585]
    exact keyMoment2585 B hB
  · have he : k = (2586 : Fin 2886) := Fin.ext h2586
    subst k
    rw [keyMomentRowsAt2586]
    exact keyMoment2586 B hB
  · have he : k = (2587 : Fin 2886) := Fin.ext h2587
    subst k
    rw [keyMomentRowsAt2587]
    exact keyMoment2587 B hB
  · have he : k = (2588 : Fin 2886) := Fin.ext h2588
    subst k
    rw [keyMomentRowsAt2588]
    exact keyMoment2588 B hB
  · have he : k = (2589 : Fin 2886) := Fin.ext h2589
    subst k
    rw [keyMomentRowsAt2589]
    exact keyMoment2589 B hB
  · have he : k = (2590 : Fin 2886) := Fin.ext h2590
    subst k
    rw [keyMomentRowsAt2590]
    exact keyMoment2590 B hB
  · have he : k = (2591 : Fin 2886) := Fin.ext h2591
    subst k
    rw [keyMomentRowsAt2591]
    exact keyMoment2591 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound80_e_oai
