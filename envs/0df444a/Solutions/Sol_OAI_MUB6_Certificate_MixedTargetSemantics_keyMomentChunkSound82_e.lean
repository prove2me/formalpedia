-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:04:58.588118+00:00
-- url     : https://prove2.me/submissions/37061126-3b64-408c-910d-f0bf325636bf

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical332
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42560 raw42560Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw42560 raw42560Labels = mixedMoment B raw42560step0 raw42560step0Labels := by
      have hz : ∀ j, raw42560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42560step0 = (fun i j => raw42560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42560step0 raw42560; decide +kernel
      have hl : raw42560step0Labels = raw42560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42560 raw42560Labels permutation346 hz
    mixedMoment B raw42560step0 raw42560step0Labels = mixedMoment B raw42560step1 raw42560step1Labels := by
      have ha : raw42560step1 = (fun i j => raw42560step0 (permutation86 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42560step1 raw42560step0; decide +kernel
      have hl : raw42560step1Labels = raw42560step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42560step0 raw42560step0Labels permutation86 permutation4
    mixedMoment B raw42560step1 raw42560step1Labels = mixedMoment B raw42560step2 raw42560step2Labels := by
      have ha : raw42560step2 = -raw42560step1 := by apply Matrix.ext; change ∀ i j, raw42560step2 i j = -(raw42560step1 i j); unfold raw42560step2 raw42560step1; decide +kernel
      have hl : raw42560step2Labels = raw42560step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42560step2 raw42560step2Labels = mixedMoment B raw42560step3 raw42560step3Labels := by
      have ha : raw42560step3 = raw42560step2 := by apply Matrix.ext; unfold raw42560step3 raw42560step2; decide +kernel
      have hl : raw42560step2Labels = labelEmbedding1 ∘ raw42560step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42560step2 raw42560step2Labels raw42560step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

theorem canonical42561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42561 raw42561Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw42561 raw42561Labels = mixedMoment B raw42561step0 raw42561step0Labels := by
      have hz : ∀ j, raw42561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42561step0 = (fun i j => raw42561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42561step0 raw42561; decide +kernel
      have hl : raw42561step0Labels = raw42561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42561 raw42561Labels permutation346 hz
    mixedMoment B raw42561step0 raw42561step0Labels = mixedMoment B raw42561step1 raw42561step1Labels := by
      have ha : raw42561step1 = (fun i j => raw42561step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42561step1 raw42561step0; decide +kernel
      have hl : raw42561step1Labels = raw42561step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42561step0 raw42561step0Labels permutation95 permutation6
    _ = mixedMoment B node4459 node4459Labels := by rfl

theorem canonical42562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42562 raw42562Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw42562 raw42562Labels = mixedMoment B raw42562step0 raw42562step0Labels := by
      have hz : ∀ j, raw42562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42562step0 = (fun i j => raw42562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42562step0 raw42562; decide +kernel
      have hl : raw42562step0Labels = raw42562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42562 raw42562Labels permutation346 hz
    mixedMoment B raw42562step0 raw42562step0Labels = mixedMoment B raw42562step1 raw42562step1Labels := by
      have ha : raw42562step1 = (fun i j => raw42562step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42562step1 raw42562step0; decide +kernel
      have hl : raw42562step1Labels = raw42562step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42562step0 raw42562step0Labels permutation129 permutation4
    mixedMoment B raw42562step1 raw42562step1Labels = mixedMoment B raw42562step2 raw42562step2Labels := by
      have ha : raw42562step2 = raw42562step1 := by apply Matrix.ext; unfold raw42562step2 raw42562step1; decide +kernel
      have hl : raw42562step1Labels = labelEmbedding1 ∘ raw42562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42562step1 raw42562step1Labels raw42562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

theorem canonical42563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42563 raw42563Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw42563 raw42563Labels = mixedMoment B raw42563step0 raw42563step0Labels := by
      have hz : ∀ j, raw42563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42563step0 = (fun i j => raw42563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42563step0 raw42563; decide +kernel
      have hl : raw42563step0Labels = raw42563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42563 raw42563Labels permutation346 hz
    mixedMoment B raw42563step0 raw42563step0Labels = mixedMoment B raw42563step1 raw42563step1Labels := by
      have ha : raw42563step1 = (fun i j => raw42563step0 (permutation94 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42563step1 raw42563step0; decide +kernel
      have hl : raw42563step1Labels = raw42563step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42563step0 raw42563step0Labels permutation94 permutation6
    _ = mixedMoment B node4945 node4945Labels := by rfl

theorem canonical42564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42564 raw42564Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw42564 raw42564Labels = mixedMoment B raw42564step0 raw42564step0Labels := by
      have ha : raw42564step0 = (fun i j => raw42564 (permutation606 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42564step0 raw42564; decide +kernel
      have hl : raw42564step0Labels = raw42564Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42564 raw42564Labels permutation606 permutation4
    mixedMoment B raw42564step0 raw42564step0Labels = mixedMoment B raw42564step1 raw42564step1Labels := by
      have ha : raw42564step1 = -raw42564step0 := by apply Matrix.ext; change ∀ i j, raw42564step1 i j = -(raw42564step0 i j); unfold raw42564step1 raw42564step0; decide +kernel
      have hl : raw42564step1Labels = raw42564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42564step1 raw42564step1Labels = mixedMoment B raw42564step2 raw42564step2Labels := by
      have ha : raw42564step2 = raw42564step1 := by apply Matrix.ext; unfold raw42564step2 raw42564step1; decide +kernel
      have hl : raw42564step1Labels = labelEmbedding1 ∘ raw42564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42564step1 raw42564step1Labels raw42564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

theorem canonical42565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42565 raw42565Labels = mixedMoment B node4152 node4152Labels := by
  calc
    mixedMoment B raw42565 raw42565Labels = mixedMoment B raw42565step0 raw42565step0Labels := by
      have ha : raw42565step0 = (fun i j => raw42565 (permutation674 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42565step0 raw42565; decide +kernel
      have hl : raw42565step0Labels = raw42565Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42565 raw42565Labels permutation674 permutation6
    _ = mixedMoment B node4152 node4152Labels := by rfl

theorem canonical42566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42566 raw42566Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw42566 raw42566Labels = mixedMoment B raw42566step0 raw42566step0Labels := by
      have ha : raw42566step0 = (fun i j => raw42566 (permutation489 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42566step0 raw42566; decide +kernel
      have hl : raw42566step0Labels = raw42566Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42566 raw42566Labels permutation489 permutation4
    mixedMoment B raw42566step0 raw42566step0Labels = mixedMoment B raw42566step1 raw42566step1Labels := by
      have ha : raw42566step1 = -raw42566step0 := by apply Matrix.ext; change ∀ i j, raw42566step1 i j = -(raw42566step0 i j); unfold raw42566step1 raw42566step0; decide +kernel
      have hl : raw42566step1Labels = raw42566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42566step1 raw42566step1Labels = mixedMoment B raw42566step2 raw42566step2Labels := by
      have ha : raw42566step2 = raw42566step1 := by apply Matrix.ext; unfold raw42566step2 raw42566step1; decide +kernel
      have hl : raw42566step1Labels = labelEmbedding1 ∘ raw42566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42566step1 raw42566step1Labels raw42566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

theorem canonical42567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42567 raw42567Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw42567 raw42567Labels = mixedMoment B raw42567step0 raw42567step0Labels := by
      have ha : raw42567step0 = (fun i j => raw42567 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42567step0 raw42567; decide +kernel
      have hl : raw42567step0Labels = raw42567Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42567 raw42567Labels permutation492 permutation6
    _ = mixedMoment B node4345 node4345Labels := by rfl

theorem canonical42568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42568 raw42568Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw42568 raw42568Labels = mixedMoment B raw42568step0 raw42568step0Labels := by
      have ha : raw42568step0 = (fun i j => raw42568 (permutation454 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42568step0 raw42568; decide +kernel
      have hl : raw42568step0Labels = raw42568Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42568 raw42568Labels permutation454 permutation4
    mixedMoment B raw42568step0 raw42568step0Labels = mixedMoment B raw42568step1 raw42568step1Labels := by
      have ha : raw42568step1 = -raw42568step0 := by apply Matrix.ext; change ∀ i j, raw42568step1 i j = -(raw42568step0 i j); unfold raw42568step1 raw42568step0; decide +kernel
      have hl : raw42568step1Labels = raw42568step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42568step1 raw42568step1Labels = mixedMoment B raw42568step2 raw42568step2Labels := by
      have ha : raw42568step2 = raw42568step1 := by apply Matrix.ext; unfold raw42568step2 raw42568step1; decide +kernel
      have hl : raw42568step1Labels = labelEmbedding1 ∘ raw42568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42568step1 raw42568step1Labels raw42568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

theorem canonical42569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42569 raw42569Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw42569 raw42569Labels = mixedMoment B raw42569step0 raw42569step0Labels := by
      have ha : raw42569step0 = (fun i j => raw42569 (permutation502 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42569step0 raw42569; decide +kernel
      have hl : raw42569step0Labels = raw42569Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42569 raw42569Labels permutation502 permutation6
    _ = mixedMoment B node4439 node4439Labels := by rfl

theorem canonical42570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42570 raw42570Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw42570 raw42570Labels = mixedMoment B raw42570step0 raw42570step0Labels := by
      have ha : raw42570step0 = (fun i j => raw42570 (permutation489 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42570step0 raw42570; decide +kernel
      have hl : raw42570step0Labels = raw42570Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42570 raw42570Labels permutation489 permutation4
    mixedMoment B raw42570step0 raw42570step0Labels = mixedMoment B raw42570step1 raw42570step1Labels := by
      have ha : raw42570step1 = -raw42570step0 := by apply Matrix.ext; change ∀ i j, raw42570step1 i j = -(raw42570step0 i j); unfold raw42570step1 raw42570step0; decide +kernel
      have hl : raw42570step1Labels = raw42570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42570step1 raw42570step1Labels = mixedMoment B raw42570step2 raw42570step2Labels := by
      have ha : raw42570step2 = raw42570step1 := by apply Matrix.ext; unfold raw42570step2 raw42570step1; decide +kernel
      have hl : raw42570step1Labels = labelEmbedding1 ∘ raw42570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42570step1 raw42570step1Labels raw42570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

theorem canonical42571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42571 raw42571Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw42571 raw42571Labels = mixedMoment B raw42571step0 raw42571step0Labels := by
      have ha : raw42571step0 = (fun i j => raw42571 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42571step0 raw42571; decide +kernel
      have hl : raw42571step0Labels = raw42571Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42571 raw42571Labels permutation492 permutation6
    _ = mixedMoment B node4942 node4942Labels := by rfl

theorem canonical42572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42572 raw42572Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw42572 raw42572Labels = mixedMoment B raw42572step0 raw42572step0Labels := by
      have ha : raw42572step0 = (fun i j => raw42572 (permutation490 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42572step0 raw42572; decide +kernel
      have hl : raw42572step0Labels = raw42572Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42572 raw42572Labels permutation490 permutation4
    mixedMoment B raw42572step0 raw42572step0Labels = mixedMoment B raw42572step1 raw42572step1Labels := by
      have ha : raw42572step1 = -raw42572step0 := by apply Matrix.ext; change ∀ i j, raw42572step1 i j = -(raw42572step0 i j); unfold raw42572step1 raw42572step0; decide +kernel
      have hl : raw42572step1Labels = raw42572step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42572step1 raw42572step1Labels = mixedMoment B raw42572step2 raw42572step2Labels := by
      have ha : raw42572step2 = raw42572step1 := by apply Matrix.ext; unfold raw42572step2 raw42572step1; decide +kernel
      have hl : raw42572step1Labels = labelEmbedding1 ∘ raw42572step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42572step1 raw42572step1Labels raw42572step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

theorem canonical42573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42573 raw42573Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw42573 raw42573Labels = mixedMoment B raw42573step0 raw42573step0Labels := by
      have ha : raw42573step0 = (fun i j => raw42573 (permutation501 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42573step0 raw42573; decide +kernel
      have hl : raw42573step0Labels = raw42573Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42573 raw42573Labels permutation501 permutation6
    _ = mixedMoment B node4328 node4328Labels := by rfl

theorem canonical42574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42574 raw42574Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw42574 raw42574Labels = mixedMoment B raw42574step0 raw42574step0Labels := by
      have ha : raw42574step0 = (fun i j => raw42574 (permutation490 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42574step0 raw42574; decide +kernel
      have hl : raw42574step0Labels = raw42574Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42574 raw42574Labels permutation490 permutation4
    mixedMoment B raw42574step0 raw42574step0Labels = mixedMoment B raw42574step1 raw42574step1Labels := by
      have ha : raw42574step1 = -raw42574step0 := by apply Matrix.ext; change ∀ i j, raw42574step1 i j = -(raw42574step0 i j); unfold raw42574step1 raw42574step0; decide +kernel
      have hl : raw42574step1Labels = raw42574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42574step1 raw42574step1Labels = mixedMoment B raw42574step2 raw42574step2Labels := by
      have ha : raw42574step2 = raw42574step1 := by apply Matrix.ext; unfold raw42574step2 raw42574step1; decide +kernel
      have hl : raw42574step1Labels = labelEmbedding1 ∘ raw42574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42574step1 raw42574step1Labels raw42574step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

theorem canonical42575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42575 raw42575Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw42575 raw42575Labels = mixedMoment B raw42575step0 raw42575step0Labels := by
      have ha : raw42575step0 = (fun i j => raw42575 (permutation501 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42575step0 raw42575; decide +kernel
      have hl : raw42575step0Labels = raw42575Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42575 raw42575Labels permutation501 permutation6
    _ = mixedMoment B node4931 node4931Labels := by rfl

theorem canonical42576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42576 raw42576Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw42576 raw42576Labels = mixedMoment B raw42576step0 raw42576step0Labels := by
      have hz : ∀ j, raw42576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42576step0 = (fun i j => raw42576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42576step0 raw42576; decide +kernel
      have hl : raw42576step0Labels = raw42576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42576 raw42576Labels permutation434 hz
    mixedMoment B raw42576step0 raw42576step0Labels = mixedMoment B raw42576step1 raw42576step1Labels := by
      have ha : raw42576step1 = (fun i j => raw42576step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42576step1 raw42576step0; decide +kernel
      have hl : raw42576step1Labels = raw42576step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42576step0 raw42576step0Labels permutation92 permutation4
    mixedMoment B raw42576step1 raw42576step1Labels = mixedMoment B raw42576step2 raw42576step2Labels := by
      have ha : raw42576step2 = -raw42576step1 := by apply Matrix.ext; change ∀ i j, raw42576step2 i j = -(raw42576step1 i j); unfold raw42576step2 raw42576step1; decide +kernel
      have hl : raw42576step2Labels = raw42576step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42576step2 raw42576step2Labels = mixedMoment B raw42576step3 raw42576step3Labels := by
      have ha : raw42576step3 = raw42576step2 := by apply Matrix.ext; unfold raw42576step3 raw42576step2; decide +kernel
      have hl : raw42576step2Labels = labelEmbedding1 ∘ raw42576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42576step2 raw42576step2Labels raw42576step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

theorem canonical42577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42577 raw42577Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw42577 raw42577Labels = mixedMoment B raw42577step0 raw42577step0Labels := by
      have hz : ∀ j, raw42577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42577step0 = (fun i j => raw42577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42577step0 raw42577; decide +kernel
      have hl : raw42577step0Labels = raw42577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42577 raw42577Labels permutation434 hz
    mixedMoment B raw42577step0 raw42577step0Labels = mixedMoment B raw42577step1 raw42577step1Labels := by
      have ha : raw42577step1 = (fun i j => raw42577step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42577step1 raw42577step0; decide +kernel
      have hl : raw42577step1Labels = raw42577step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42577step0 raw42577step0Labels permutation96 permutation6
    _ = mixedMoment B node4821 node4821Labels := by rfl

theorem canonical42578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42578 raw42578Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw42578 raw42578Labels = mixedMoment B raw42578step0 raw42578step0Labels := by
      have hz : ∀ j, raw42578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42578step0 = (fun i j => raw42578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42578step0 raw42578; decide +kernel
      have hl : raw42578step0Labels = raw42578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42578 raw42578Labels permutation434 hz
    mixedMoment B raw42578step0 raw42578step0Labels = mixedMoment B raw42578step1 raw42578step1Labels := by
      have ha : raw42578step1 = (fun i j => raw42578step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42578step1 raw42578step0; decide +kernel
      have hl : raw42578step1Labels = raw42578step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42578step0 raw42578step0Labels permutation85 permutation4
    mixedMoment B raw42578step1 raw42578step1Labels = mixedMoment B raw42578step2 raw42578step2Labels := by
      have ha : raw42578step2 = -raw42578step1 := by apply Matrix.ext; change ∀ i j, raw42578step2 i j = -(raw42578step1 i j); unfold raw42578step2 raw42578step1; decide +kernel
      have hl : raw42578step2Labels = raw42578step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42578step2 raw42578step2Labels = mixedMoment B raw42578step3 raw42578step3Labels := by
      have ha : raw42578step3 = raw42578step2 := by apply Matrix.ext; unfold raw42578step3 raw42578step2; decide +kernel
      have hl : raw42578step2Labels = labelEmbedding1 ∘ raw42578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42578step2 raw42578step2Labels raw42578step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

theorem canonical42579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42579 raw42579Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw42579 raw42579Labels = mixedMoment B raw42579step0 raw42579step0Labels := by
      have hz : ∀ j, raw42579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42579step0 = (fun i j => raw42579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42579step0 raw42579; decide +kernel
      have hl : raw42579step0Labels = raw42579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42579 raw42579Labels permutation434 hz
    mixedMoment B raw42579step0 raw42579step0Labels = mixedMoment B raw42579step1 raw42579step1Labels := by
      have ha : raw42579step1 = (fun i j => raw42579step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42579step1 raw42579step0; decide +kernel
      have hl : raw42579step1Labels = raw42579step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42579step0 raw42579step0Labels permutation102 permutation6
    _ = mixedMoment B node4856 node4856Labels := by rfl

theorem canonical42580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42580 raw42580Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw42580 raw42580Labels = mixedMoment B raw42580step0 raw42580step0Labels := by
      have hz : ∀ j, raw42580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42580step0 = (fun i j => raw42580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42580step0 raw42580; decide +kernel
      have hl : raw42580step0Labels = raw42580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42580 raw42580Labels permutation434 hz
    mixedMoment B raw42580step0 raw42580step0Labels = mixedMoment B raw42580step1 raw42580step1Labels := by
      have ha : raw42580step1 = (fun i j => raw42580step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42580step1 raw42580step0; decide +kernel
      have hl : raw42580step1Labels = raw42580step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42580step0 raw42580step0Labels permutation98 permutation4
    mixedMoment B raw42580step1 raw42580step1Labels = mixedMoment B raw42580step2 raw42580step2Labels := by
      have ha : raw42580step2 = -raw42580step1 := by apply Matrix.ext; change ∀ i j, raw42580step2 i j = -(raw42580step1 i j); unfold raw42580step2 raw42580step1; decide +kernel
      have hl : raw42580step2Labels = raw42580step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42580step2 raw42580step2Labels = mixedMoment B raw42580step3 raw42580step3Labels := by
      have ha : raw42580step3 = raw42580step2 := by apply Matrix.ext; unfold raw42580step3 raw42580step2; decide +kernel
      have hl : raw42580step2Labels = labelEmbedding1 ∘ raw42580step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42580step2 raw42580step2Labels raw42580step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

theorem canonical42581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42581 raw42581Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw42581 raw42581Labels = mixedMoment B raw42581step0 raw42581step0Labels := by
      have hz : ∀ j, raw42581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42581step0 = (fun i j => raw42581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42581step0 raw42581; decide +kernel
      have hl : raw42581step0Labels = raw42581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42581 raw42581Labels permutation434 hz
    mixedMoment B raw42581step0 raw42581step0Labels = mixedMoment B raw42581step1 raw42581step1Labels := by
      have ha : raw42581step1 = (fun i j => raw42581step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42581step1 raw42581step0; decide +kernel
      have hl : raw42581step1Labels = raw42581step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42581step0 raw42581step0Labels permutation102 permutation6
    _ = mixedMoment B node4690 node4690Labels := by rfl

theorem canonical42582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42582 raw42582Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw42582 raw42582Labels = mixedMoment B raw42582step0 raw42582step0Labels := by
      have ha : raw42582step0 = (fun i j => raw42582 (permutation418 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42582step0 raw42582; decide +kernel
      have hl : raw42582step0Labels = raw42582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42582 raw42582Labels permutation418 permutation4
    mixedMoment B raw42582step0 raw42582step0Labels = mixedMoment B raw42582step1 raw42582step1Labels := by
      have ha : raw42582step1 = -raw42582step0 := by apply Matrix.ext; change ∀ i j, raw42582step1 i j = -(raw42582step0 i j); unfold raw42582step1 raw42582step0; decide +kernel
      have hl : raw42582step1Labels = raw42582step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42582step1 raw42582step1Labels = mixedMoment B raw42582step2 raw42582step2Labels := by
      have ha : raw42582step2 = raw42582step1 := by apply Matrix.ext; unfold raw42582step2 raw42582step1; decide +kernel
      have hl : raw42582step1Labels = labelEmbedding1 ∘ raw42582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42582step1 raw42582step1Labels raw42582step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

theorem canonical42583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42583 raw42583Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw42583 raw42583Labels = mixedMoment B raw42583step0 raw42583step0Labels := by
      have ha : raw42583step0 = (fun i j => raw42583 (permutation432 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42583step0 raw42583; decide +kernel
      have hl : raw42583step0Labels = raw42583Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42583 raw42583Labels permutation432 permutation6
    _ = mixedMoment B node4668 node4668Labels := by rfl

theorem canonical42584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42584 raw42584Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw42584 raw42584Labels = mixedMoment B raw42584step0 raw42584step0Labels := by
      have ha : raw42584step0 = (fun i j => raw42584 (permutation389 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42584step0 raw42584; decide +kernel
      have hl : raw42584step0Labels = raw42584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42584 raw42584Labels permutation389 permutation4
    mixedMoment B raw42584step0 raw42584step0Labels = mixedMoment B raw42584step1 raw42584step1Labels := by
      have ha : raw42584step1 = -raw42584step0 := by apply Matrix.ext; change ∀ i j, raw42584step1 i j = -(raw42584step0 i j); unfold raw42584step1 raw42584step0; decide +kernel
      have hl : raw42584step1Labels = raw42584step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42584step1 raw42584step1Labels = mixedMoment B raw42584step2 raw42584step2Labels := by
      have ha : raw42584step2 = raw42584step1 := by apply Matrix.ext; unfold raw42584step2 raw42584step1; decide +kernel
      have hl : raw42584step1Labels = labelEmbedding1 ∘ raw42584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42584step1 raw42584step1Labels raw42584step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

theorem canonical42585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42585 raw42585Labels = mixedMoment B node4768 node4768Labels := by
  calc
    mixedMoment B raw42585 raw42585Labels = mixedMoment B raw42585step0 raw42585step0Labels := by
      have ha : raw42585step0 = (fun i j => raw42585 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42585step0 raw42585; decide +kernel
      have hl : raw42585step0Labels = raw42585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42585 raw42585Labels permutation393 permutation6
    _ = mixedMoment B node4768 node4768Labels := by rfl

theorem canonical42586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42586 raw42586Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw42586 raw42586Labels = mixedMoment B raw42586step0 raw42586step0Labels := by
      have ha : raw42586step0 = (fun i j => raw42586 (permutation383 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42586step0 raw42586; decide +kernel
      have hl : raw42586step0Labels = raw42586Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42586 raw42586Labels permutation383 permutation4
    mixedMoment B raw42586step0 raw42586step0Labels = mixedMoment B raw42586step1 raw42586step1Labels := by
      have ha : raw42586step1 = -raw42586step0 := by apply Matrix.ext; change ∀ i j, raw42586step1 i j = -(raw42586step0 i j); unfold raw42586step1 raw42586step0; decide +kernel
      have hl : raw42586step1Labels = raw42586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42586step1 raw42586step1Labels = mixedMoment B raw42586step2 raw42586step2Labels := by
      have ha : raw42586step2 = raw42586step1 := by apply Matrix.ext; unfold raw42586step2 raw42586step1; decide +kernel
      have hl : raw42586step1Labels = labelEmbedding1 ∘ raw42586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42586step1 raw42586step1Labels raw42586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

theorem canonical42587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42587 raw42587Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw42587 raw42587Labels = mixedMoment B raw42587step0 raw42587step0Labels := by
      have ha : raw42587step0 = (fun i j => raw42587 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42587step0 raw42587; decide +kernel
      have hl : raw42587step0Labels = raw42587Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42587 raw42587Labels permutation393 permutation6
    _ = mixedMoment B node4795 node4795Labels := by rfl

theorem canonical42588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42588 raw42588Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw42588 raw42588Labels = mixedMoment B raw42588step0 raw42588step0Labels := by
      have ha : raw42588step0 = (fun i j => raw42588 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42588step0 raw42588; decide +kernel
      have hl : raw42588step0Labels = raw42588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42588 raw42588Labels permutation158 permutation2
    mixedMoment B raw42588step0 raw42588step0Labels = mixedMoment B raw42588step1 raw42588step1Labels := by
      have ha : raw42588step1 = raw42588step0 := by apply Matrix.ext; unfold raw42588step1 raw42588step0; decide +kernel
      have hl : raw42588step0Labels = labelEmbedding1 ∘ raw42588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42588step0 raw42588step0Labels raw42588step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical42589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42589 raw42589Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw42589 raw42589Labels = mixedMoment B raw42589step0 raw42589step0Labels := by
      have ha : raw42589step0 = (fun i j => raw42589 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42589step0 raw42589; decide +kernel
      have hl : raw42589step0Labels = raw42589Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42589 raw42589Labels permutation173 permutation7
    mixedMoment B raw42589step0 raw42589step0Labels = mixedMoment B raw42589step1 raw42589step1Labels := by
      have ha : raw42589step1 = -raw42589step0 := by apply Matrix.ext; change ∀ i j, raw42589step1 i j = -(raw42589step0 i j); unfold raw42589step1 raw42589step0; decide +kernel
      have hl : raw42589step1Labels = raw42589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42589step1 raw42589step1Labels = mixedMoment B raw42589step2 raw42589step2Labels := by
      have ha : raw42589step2 = raw42589step1 := by apply Matrix.ext; unfold raw42589step2 raw42589step1; decide +kernel
      have hl : raw42589step1Labels = labelEmbedding6 ∘ raw42589step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42589step1 raw42589step1Labels raw42589step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical42590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42590 raw42590Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw42590 raw42590Labels = mixedMoment B raw42590step0 raw42590step0Labels := by
      have ha : raw42590step0 = (fun i j => raw42590 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42590step0 raw42590; decide +kernel
      have hl : raw42590step0Labels = raw42590Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42590 raw42590Labels permutation158 permutation2
    mixedMoment B raw42590step0 raw42590step0Labels = mixedMoment B raw42590step1 raw42590step1Labels := by
      have ha : raw42590step1 = raw42590step0 := by apply Matrix.ext; unfold raw42590step1 raw42590step0; decide +kernel
      have hl : raw42590step0Labels = labelEmbedding1 ∘ raw42590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42590step0 raw42590step0Labels raw42590step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical42591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42591 raw42591Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw42591 raw42591Labels = mixedMoment B raw42591step0 raw42591step0Labels := by
      have ha : raw42591step0 = (fun i j => raw42591 (permutation167 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42591step0 raw42591; decide +kernel
      have hl : raw42591step0Labels = raw42591Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42591 raw42591Labels permutation167 permutation7
    mixedMoment B raw42591step0 raw42591step0Labels = mixedMoment B raw42591step1 raw42591step1Labels := by
      have ha : raw42591step1 = -raw42591step0 := by apply Matrix.ext; change ∀ i j, raw42591step1 i j = -(raw42591step0 i j); unfold raw42591step1 raw42591step0; decide +kernel
      have hl : raw42591step1Labels = raw42591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42591step1 raw42591step1Labels = mixedMoment B raw42591step2 raw42591step2Labels := by
      have ha : raw42591step2 = raw42591step1 := by apply Matrix.ext; unfold raw42591step2 raw42591step1; decide +kernel
      have hl : raw42591step1Labels = labelEmbedding6 ∘ raw42591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42591step1 raw42591step1Labels raw42591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical42592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42592 raw42592Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw42592 raw42592Labels = mixedMoment B raw42592step0 raw42592step0Labels := by
      have ha : raw42592step0 = (fun i j => raw42592 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42592step0 raw42592; decide +kernel
      have hl : raw42592step0Labels = raw42592Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42592 raw42592Labels permutation158 permutation2
    mixedMoment B raw42592step0 raw42592step0Labels = mixedMoment B raw42592step1 raw42592step1Labels := by
      have ha : raw42592step1 = raw42592step0 := by apply Matrix.ext; unfold raw42592step1 raw42592step0; decide +kernel
      have hl : raw42592step0Labels = labelEmbedding1 ∘ raw42592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42592step0 raw42592step0Labels raw42592step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

theorem canonical42593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42593 raw42593Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw42593 raw42593Labels = mixedMoment B raw42593step0 raw42593step0Labels := by
      have ha : raw42593step0 = (fun i j => raw42593 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42593step0 raw42593; decide +kernel
      have hl : raw42593step0Labels = raw42593Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42593 raw42593Labels permutation166 permutation7
    mixedMoment B raw42593step0 raw42593step0Labels = mixedMoment B raw42593step1 raw42593step1Labels := by
      have ha : raw42593step1 = -raw42593step0 := by apply Matrix.ext; change ∀ i j, raw42593step1 i j = -(raw42593step0 i j); unfold raw42593step1 raw42593step0; decide +kernel
      have hl : raw42593step1Labels = raw42593step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42593step1 raw42593step1Labels = mixedMoment B raw42593step2 raw42593step2Labels := by
      have ha : raw42593step2 = raw42593step1 := by apply Matrix.ext; unfold raw42593step2 raw42593step1; decide +kernel
      have hl : raw42593step1Labels = labelEmbedding6 ∘ raw42593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42593step1 raw42593step1Labels raw42593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5339 node5339Labels := by rfl

theorem canonical42594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42594 raw42594Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw42594 raw42594Labels = mixedMoment B raw42594step0 raw42594step0Labels := by
      have hz : ∀ j, raw42594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42594step0 = (fun i j => raw42594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42594step0 raw42594; decide +kernel
      have hl : raw42594step0Labels = raw42594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42594 raw42594Labels permutation434 hz
    mixedMoment B raw42594step0 raw42594step0Labels = mixedMoment B raw42594step1 raw42594step1Labels := by
      have ha : raw42594step1 = raw42594step0 := by apply Matrix.ext; unfold raw42594step1 raw42594step0; decide +kernel
      have hl : raw42594step0Labels = labelEmbedding1 ∘ raw42594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42594step0 raw42594step0Labels raw42594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3772 node3772Labels := by rfl

theorem canonical42595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42595 raw42595Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw42595 raw42595Labels = mixedMoment B raw42595step0 raw42595step0Labels := by
      have hz : ∀ j, raw42595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42595step0 = (fun i j => raw42595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42595step0 raw42595; decide +kernel
      have hl : raw42595step0Labels = raw42595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42595 raw42595Labels permutation434 hz
    mixedMoment B raw42595step0 raw42595step0Labels = mixedMoment B raw42595step1 raw42595step1Labels := by
      have ha : raw42595step1 = (fun i j => raw42595step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42595step1 raw42595step0; decide +kernel
      have hl : raw42595step1Labels = raw42595step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42595step0 raw42595step0Labels permutation96 permutation6
    _ = mixedMoment B node5361 node5361Labels := by rfl

theorem canonical42596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42596 raw42596Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw42596 raw42596Labels = mixedMoment B raw42596step0 raw42596step0Labels := by
      have hz : ∀ j, raw42596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42596step0 = (fun i j => raw42596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42596step0 raw42596; decide +kernel
      have hl : raw42596step0Labels = raw42596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42596 raw42596Labels permutation434 hz
    mixedMoment B raw42596step0 raw42596step0Labels = mixedMoment B raw42596step1 raw42596step1Labels := by
      have ha : raw42596step1 = (fun i j => raw42596step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42596step1 raw42596step0; decide +kernel
      have hl : raw42596step1Labels = raw42596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42596step0 raw42596step0Labels permutation151 permutation2
    mixedMoment B raw42596step1 raw42596step1Labels = mixedMoment B raw42596step2 raw42596step2Labels := by
      have ha : raw42596step2 = -raw42596step1 := by apply Matrix.ext; change ∀ i j, raw42596step2 i j = -(raw42596step1 i j); unfold raw42596step2 raw42596step1; decide +kernel
      have hl : raw42596step2Labels = raw42596step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42596step2 raw42596step2Labels = mixedMoment B raw42596step3 raw42596step3Labels := by
      have ha : raw42596step3 = raw42596step2 := by apply Matrix.ext; unfold raw42596step3 raw42596step2; decide +kernel
      have hl : raw42596step2Labels = labelEmbedding1 ∘ raw42596step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42596step2 raw42596step2Labels raw42596step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

theorem canonical42597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42597 raw42597Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw42597 raw42597Labels = mixedMoment B raw42597step0 raw42597step0Labels := by
      have hz : ∀ j, raw42597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42597step0 = (fun i j => raw42597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42597step0 raw42597; decide +kernel
      have hl : raw42597step0Labels = raw42597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42597 raw42597Labels permutation434 hz
    mixedMoment B raw42597step0 raw42597step0Labels = mixedMoment B raw42597step1 raw42597step1Labels := by
      have ha : raw42597step1 = (fun i j => raw42597step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42597step1 raw42597step0; decide +kernel
      have hl : raw42597step1Labels = raw42597step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42597step0 raw42597step0Labels permutation145 permutation7
    mixedMoment B raw42597step1 raw42597step1Labels = mixedMoment B raw42597step2 raw42597step2Labels := by
      have ha : raw42597step2 = raw42597step1 := by apply Matrix.ext; unfold raw42597step2 raw42597step1; decide +kernel
      have hl : raw42597step1Labels = labelEmbedding6 ∘ raw42597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42597step1 raw42597step1Labels raw42597step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4966 node4966Labels := by rfl

theorem canonical42598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42598 raw42598Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw42598 raw42598Labels = mixedMoment B raw42598step0 raw42598step0Labels := by
      have ha : raw42598step0 = (fun i j => raw42598 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42598step0 raw42598; decide +kernel
      have hl : raw42598step0Labels = raw42598Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42598 raw42598Labels permutation682 permutation2
    mixedMoment B raw42598step0 raw42598step0Labels = mixedMoment B raw42598step1 raw42598step1Labels := by
      have ha : raw42598step1 = -raw42598step0 := by apply Matrix.ext; change ∀ i j, raw42598step1 i j = -(raw42598step0 i j); unfold raw42598step1 raw42598step0; decide +kernel
      have hl : raw42598step1Labels = raw42598step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42598step1 raw42598step1Labels = mixedMoment B raw42598step2 raw42598step2Labels := by
      have ha : raw42598step2 = raw42598step1 := by apply Matrix.ext; unfold raw42598step2 raw42598step1; decide +kernel
      have hl : raw42598step1Labels = labelEmbedding1 ∘ raw42598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42598step1 raw42598step1Labels raw42598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

theorem canonical42599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42599 raw42599Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw42599 raw42599Labels = mixedMoment B raw42599step0 raw42599step0Labels := by
      have ha : raw42599step0 = (fun i j => raw42599 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42599step0 raw42599; decide +kernel
      have hl : raw42599step0Labels = raw42599Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42599 raw42599Labels permutation646 permutation7
    mixedMoment B raw42599step0 raw42599step0Labels = mixedMoment B raw42599step1 raw42599step1Labels := by
      have ha : raw42599step1 = raw42599step0 := by apply Matrix.ext; unfold raw42599step1 raw42599step0; decide +kernel
      have hl : raw42599step0Labels = labelEmbedding6 ∘ raw42599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42599step0 raw42599step0Labels raw42599step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4955 node4955Labels := by rfl

theorem canonical42600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42600 raw42600Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw42600 raw42600Labels = mixedMoment B raw42600step0 raw42600step0Labels := by
      have ha : raw42600step0 = (fun i j => raw42600 (permutation389 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42600step0 raw42600; decide +kernel
      have hl : raw42600step0Labels = raw42600Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42600 raw42600Labels permutation389 permutation4
    mixedMoment B raw42600step0 raw42600step0Labels = mixedMoment B raw42600step1 raw42600step1Labels := by
      have ha : raw42600step1 = -raw42600step0 := by apply Matrix.ext; change ∀ i j, raw42600step1 i j = -(raw42600step0 i j); unfold raw42600step1 raw42600step0; decide +kernel
      have hl : raw42600step1Labels = raw42600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42600step1 raw42600step1Labels = mixedMoment B raw42600step2 raw42600step2Labels := by
      have ha : raw42600step2 = raw42600step1 := by apply Matrix.ext; unfold raw42600step2 raw42600step1; decide +kernel
      have hl : raw42600step1Labels = labelEmbedding1 ∘ raw42600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42600step1 raw42600step1Labels raw42600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

theorem canonical42601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42601 raw42601Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw42601 raw42601Labels = mixedMoment B raw42601step0 raw42601step0Labels := by
      have ha : raw42601step0 = (fun i j => raw42601 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42601step0 raw42601; decide +kernel
      have hl : raw42601step0Labels = raw42601Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42601 raw42601Labels permutation393 permutation6
    _ = mixedMoment B node5338 node5338Labels := by rfl

theorem canonical42602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42602 raw42602Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw42602 raw42602Labels = mixedMoment B raw42602step0 raw42602step0Labels := by
      have ha : raw42602step0 = (fun i j => raw42602 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42602step0 raw42602; decide +kernel
      have hl : raw42602step0Labels = raw42602Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42602 raw42602Labels permutation155 permutation2
    mixedMoment B raw42602step0 raw42602step0Labels = mixedMoment B raw42602step1 raw42602step1Labels := by
      have ha : raw42602step1 = raw42602step0 := by apply Matrix.ext; unfold raw42602step1 raw42602step0; decide +kernel
      have hl : raw42602step0Labels = labelEmbedding1 ∘ raw42602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42602step0 raw42602step0Labels raw42602step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

theorem canonical42603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42603 raw42603Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw42603 raw42603Labels = mixedMoment B raw42603step0 raw42603step0Labels := by
      have ha : raw42603step0 = (fun i j => raw42603 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42603step0 raw42603; decide +kernel
      have hl : raw42603step0Labels = raw42603Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42603 raw42603Labels permutation393 permutation6
    _ = mixedMoment B node5348 node5348Labels := by rfl

theorem canonical42604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42604 raw42604Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw42604 raw42604Labels = mixedMoment B raw42604step0 raw42604step0Labels := by
      have ha : raw42604step0 = raw42604 := by apply Matrix.ext; unfold raw42604step0 raw42604; decide +kernel
      have hl : raw42604Labels = labelEmbedding1 ∘ raw42604step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42604 raw42604Labels raw42604step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

theorem canonical42605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42605 raw42605Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw42605 raw42605Labels = mixedMoment B raw42605step0 raw42605step0Labels := by
      have ha : raw42605step0 = (fun i j => raw42605 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42605step0 raw42605; decide +kernel
      have hl : raw42605step0Labels = raw42605Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42605 raw42605Labels permutation170 permutation7
    mixedMoment B raw42605step0 raw42605step0Labels = mixedMoment B raw42605step1 raw42605step1Labels := by
      have ha : raw42605step1 = -raw42605step0 := by apply Matrix.ext; change ∀ i j, raw42605step1 i j = -(raw42605step0 i j); unfold raw42605step1 raw42605step0; decide +kernel
      have hl : raw42605step1Labels = raw42605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42605step1 raw42605step1Labels = mixedMoment B raw42605step2 raw42605step2Labels := by
      have ha : raw42605step2 = raw42605step1 := by apply Matrix.ext; unfold raw42605step2 raw42605step1; decide +kernel
      have hl : raw42605step1Labels = labelEmbedding6 ∘ raw42605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42605step1 raw42605step1Labels raw42605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

theorem canonical42606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42606 raw42606Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw42606 raw42606Labels = mixedMoment B raw42606step0 raw42606step0Labels := by
      have ha : raw42606step0 = (fun i j => raw42606 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42606step0 raw42606; decide +kernel
      have hl : raw42606step0Labels = raw42606Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42606 raw42606Labels permutation682 permutation2
    mixedMoment B raw42606step0 raw42606step0Labels = mixedMoment B raw42606step1 raw42606step1Labels := by
      have ha : raw42606step1 = -raw42606step0 := by apply Matrix.ext; change ∀ i j, raw42606step1 i j = -(raw42606step0 i j); unfold raw42606step1 raw42606step0; decide +kernel
      have hl : raw42606step1Labels = raw42606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42606step1 raw42606step1Labels = mixedMoment B raw42606step2 raw42606step2Labels := by
      have ha : raw42606step2 = raw42606step1 := by apply Matrix.ext; unfold raw42606step2 raw42606step1; decide +kernel
      have hl : raw42606step1Labels = labelEmbedding1 ∘ raw42606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42606step1 raw42606step1Labels raw42606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

theorem canonical42607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42607 raw42607Labels = mixedMoment B node5112 node5112Labels := by
  calc
    mixedMoment B raw42607 raw42607Labels = mixedMoment B raw42607step0 raw42607step0Labels := by
      have ha : raw42607step0 = (fun i j => raw42607 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42607step0 raw42607; decide +kernel
      have hl : raw42607step0Labels = raw42607Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42607 raw42607Labels permutation640 permutation7
    mixedMoment B raw42607step0 raw42607step0Labels = mixedMoment B raw42607step1 raw42607step1Labels := by
      have ha : raw42607step1 = raw42607step0 := by apply Matrix.ext; unfold raw42607step1 raw42607step0; decide +kernel
      have hl : raw42607step0Labels = labelEmbedding6 ∘ raw42607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42607step0 raw42607step0Labels raw42607step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5112 node5112Labels := by rfl

theorem canonical42608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42608 raw42608Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw42608 raw42608Labels = mixedMoment B raw42608step0 raw42608step0Labels := by
      have hz : ∀ j, raw42608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42608step0 = (fun i j => raw42608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42608step0 raw42608; decide +kernel
      have hl : raw42608step0Labels = raw42608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42608 raw42608Labels permutation434 hz
    mixedMoment B raw42608step0 raw42608step0Labels = mixedMoment B raw42608step1 raw42608step1Labels := by
      have ha : raw42608step1 = (fun i j => raw42608step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42608step1 raw42608step0; decide +kernel
      have hl : raw42608step1Labels = raw42608step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42608step0 raw42608step0Labels permutation116 permutation4
    mixedMoment B raw42608step1 raw42608step1Labels = mixedMoment B raw42608step2 raw42608step2Labels := by
      have ha : raw42608step2 = -raw42608step1 := by apply Matrix.ext; change ∀ i j, raw42608step2 i j = -(raw42608step1 i j); unfold raw42608step2 raw42608step1; decide +kernel
      have hl : raw42608step2Labels = raw42608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42608step2 raw42608step2Labels = mixedMoment B raw42608step3 raw42608step3Labels := by
      have ha : raw42608step3 = raw42608step2 := by apply Matrix.ext; unfold raw42608step3 raw42608step2; decide +kernel
      have hl : raw42608step2Labels = labelEmbedding1 ∘ raw42608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42608step2 raw42608step2Labels raw42608step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

theorem canonical42609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42609 raw42609Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw42609 raw42609Labels = mixedMoment B raw42609step0 raw42609step0Labels := by
      have hz : ∀ j, raw42609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42609step0 = (fun i j => raw42609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42609step0 raw42609; decide +kernel
      have hl : raw42609step0Labels = raw42609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42609 raw42609Labels permutation434 hz
    mixedMoment B raw42609step0 raw42609step0Labels = mixedMoment B raw42609step1 raw42609step1Labels := by
      have ha : raw42609step1 = (fun i j => raw42609step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42609step1 raw42609step0; decide +kernel
      have hl : raw42609step1Labels = raw42609step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42609step0 raw42609step0Labels permutation120 permutation6
    _ = mixedMoment B node5090 node5090Labels := by rfl

theorem canonical42610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42610 raw42610Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw42610 raw42610Labels = mixedMoment B raw42610step0 raw42610step0Labels := by
      have hz : ∀ j, raw42610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42610step0 = (fun i j => raw42610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42610step0 raw42610; decide +kernel
      have hl : raw42610step0Labels = raw42610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42610 raw42610Labels permutation434 hz
    mixedMoment B raw42610step0 raw42610step0Labels = mixedMoment B raw42610step1 raw42610step1Labels := by
      have ha : raw42610step1 = (fun i j => raw42610step0 (permutation140 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42610step1 raw42610step0; decide +kernel
      have hl : raw42610step1Labels = raw42610step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42610step0 raw42610step0Labels permutation140 permutation4
    mixedMoment B raw42610step1 raw42610step1Labels = mixedMoment B raw42610step2 raw42610step2Labels := by
      have ha : raw42610step2 = -raw42610step1 := by apply Matrix.ext; change ∀ i j, raw42610step2 i j = -(raw42610step1 i j); unfold raw42610step2 raw42610step1; decide +kernel
      have hl : raw42610step2Labels = raw42610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42610step2 raw42610step2Labels = mixedMoment B raw42610step3 raw42610step3Labels := by
      have ha : raw42610step3 = raw42610step2 := by apply Matrix.ext; unfold raw42610step3 raw42610step2; decide +kernel
      have hl : raw42610step2Labels = labelEmbedding1 ∘ raw42610step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42610step2 raw42610step2Labels raw42610step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

theorem canonical42611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42611 raw42611Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw42611 raw42611Labels = mixedMoment B raw42611step0 raw42611step0Labels := by
      have hz : ∀ j, raw42611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42611step0 = (fun i j => raw42611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42611step0 raw42611; decide +kernel
      have hl : raw42611step0Labels = raw42611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42611 raw42611Labels permutation434 hz
    mixedMoment B raw42611step0 raw42611step0Labels = mixedMoment B raw42611step1 raw42611step1Labels := by
      have ha : raw42611step1 = (fun i j => raw42611step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42611step1 raw42611step0; decide +kernel
      have hl : raw42611step1Labels = raw42611step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42611step0 raw42611step0Labels permutation144 permutation6
    _ = mixedMoment B node4556 node4556Labels := by rfl

theorem canonical42612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42612 raw42612Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw42612 raw42612Labels = mixedMoment B raw42612step0 raw42612step0Labels := by
      have ha : raw42612step0 = (fun i j => raw42612 (permutation628 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42612step0 raw42612; decide +kernel
      have hl : raw42612step0Labels = raw42612Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42612 raw42612Labels permutation628 permutation4
    mixedMoment B raw42612step0 raw42612step0Labels = mixedMoment B raw42612step1 raw42612step1Labels := by
      have ha : raw42612step1 = -raw42612step0 := by apply Matrix.ext; change ∀ i j, raw42612step1 i j = -(raw42612step0 i j); unfold raw42612step1 raw42612step0; decide +kernel
      have hl : raw42612step1Labels = raw42612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42612step1 raw42612step1Labels = mixedMoment B raw42612step2 raw42612step2Labels := by
      have ha : raw42612step2 = raw42612step1 := by apply Matrix.ext; unfold raw42612step2 raw42612step1; decide +kernel
      have hl : raw42612step1Labels = labelEmbedding1 ∘ raw42612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42612step1 raw42612step1Labels raw42612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

theorem canonical42613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42613 raw42613Labels = mixedMoment B node4533 node4533Labels := by
  calc
    mixedMoment B raw42613 raw42613Labels = mixedMoment B raw42613step0 raw42613step0Labels := by
      have ha : raw42613step0 = (fun i j => raw42613 (permutation645 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42613step0 raw42613; decide +kernel
      have hl : raw42613step0Labels = raw42613Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42613 raw42613Labels permutation645 permutation6
    _ = mixedMoment B node4533 node4533Labels := by rfl

theorem canonical42614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42614 raw42614Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw42614 raw42614Labels = mixedMoment B raw42614step0 raw42614step0Labels := by
      have ha : raw42614step0 = (fun i j => raw42614 (permutation475 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42614step0 raw42614; decide +kernel
      have hl : raw42614step0Labels = raw42614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42614 raw42614Labels permutation475 permutation4
    mixedMoment B raw42614step0 raw42614step0Labels = mixedMoment B raw42614step1 raw42614step1Labels := by
      have ha : raw42614step1 = -raw42614step0 := by apply Matrix.ext; change ∀ i j, raw42614step1 i j = -(raw42614step0 i j); unfold raw42614step1 raw42614step0; decide +kernel
      have hl : raw42614step1Labels = raw42614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42614step1 raw42614step1Labels = mixedMoment B raw42614step2 raw42614step2Labels := by
      have ha : raw42614step2 = raw42614step1 := by apply Matrix.ext; unfold raw42614step2 raw42614step1; decide +kernel
      have hl : raw42614step1Labels = labelEmbedding1 ∘ raw42614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42614step1 raw42614step1Labels raw42614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

theorem canonical42615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42615 raw42615Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw42615 raw42615Labels = mixedMoment B raw42615step0 raw42615step0Labels := by
      have ha : raw42615step0 = (fun i j => raw42615 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42615step0 raw42615; decide +kernel
      have hl : raw42615step0Labels = raw42615Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42615 raw42615Labels permutation479 permutation6
    _ = mixedMoment B node5040 node5040Labels := by rfl

theorem canonical42616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42616 raw42616Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw42616 raw42616Labels = mixedMoment B raw42616step0 raw42616step0Labels := by
      have ha : raw42616step0 = (fun i j => raw42616 (permutation468 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42616step0 raw42616; decide +kernel
      have hl : raw42616step0Labels = raw42616Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42616 raw42616Labels permutation468 permutation4
    mixedMoment B raw42616step0 raw42616step0Labels = mixedMoment B raw42616step1 raw42616step1Labels := by
      have ha : raw42616step1 = -raw42616step0 := by apply Matrix.ext; change ∀ i j, raw42616step1 i j = -(raw42616step0 i j); unfold raw42616step1 raw42616step0; decide +kernel
      have hl : raw42616step1Labels = raw42616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42616step1 raw42616step1Labels = mixedMoment B raw42616step2 raw42616step2Labels := by
      have ha : raw42616step2 = raw42616step1 := by apply Matrix.ext; unfold raw42616step2 raw42616step1; decide +kernel
      have hl : raw42616step1Labels = labelEmbedding1 ∘ raw42616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42616step1 raw42616step1Labels raw42616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

theorem canonical42617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42617 raw42617Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw42617 raw42617Labels = mixedMoment B raw42617step0 raw42617step0Labels := by
      have ha : raw42617step0 = (fun i j => raw42617 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42617step0 raw42617; decide +kernel
      have hl : raw42617step0Labels = raw42617Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42617 raw42617Labels permutation479 permutation6
    _ = mixedMoment B node5067 node5067Labels := by rfl

theorem canonical42618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42618 raw42618Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw42618 raw42618Labels = mixedMoment B raw42618step0 raw42618step0Labels := by
      have ha : raw42618step0 = (fun i j => raw42618 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42618step0 raw42618; decide +kernel
      have hl : raw42618step0Labels = raw42618Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42618 raw42618Labels permutation156 permutation2
    mixedMoment B raw42618step0 raw42618step0Labels = mixedMoment B raw42618step1 raw42618step1Labels := by
      have ha : raw42618step1 = raw42618step0 := by apply Matrix.ext; unfold raw42618step1 raw42618step0; decide +kernel
      have hl : raw42618step0Labels = labelEmbedding1 ∘ raw42618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42618step0 raw42618step0Labels raw42618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

theorem canonical42619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42619 raw42619Labels = mixedMoment B node5340 node5340Labels := by
  calc
    mixedMoment B raw42619 raw42619Labels = mixedMoment B raw42619step0 raw42619step0Labels := by
      have ha : raw42619step0 = (fun i j => raw42619 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42619step0 raw42619; decide +kernel
      have hl : raw42619step0Labels = raw42619Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42619 raw42619Labels permutation170 permutation7
    mixedMoment B raw42619step0 raw42619step0Labels = mixedMoment B raw42619step1 raw42619step1Labels := by
      have ha : raw42619step1 = -raw42619step0 := by apply Matrix.ext; change ∀ i j, raw42619step1 i j = -(raw42619step0 i j); unfold raw42619step1 raw42619step0; decide +kernel
      have hl : raw42619step1Labels = raw42619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42619step1 raw42619step1Labels = mixedMoment B raw42619step2 raw42619step2Labels := by
      have ha : raw42619step2 = raw42619step1 := by apply Matrix.ext; unfold raw42619step2 raw42619step1; decide +kernel
      have hl : raw42619step1Labels = labelEmbedding6 ∘ raw42619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42619step1 raw42619step1Labels raw42619step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5340 node5340Labels := by rfl

theorem canonical42620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42620 raw42620Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw42620 raw42620Labels = mixedMoment B raw42620step0 raw42620step0Labels := by
      have hz : ∀ j, raw42620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42620step0 = (fun i j => raw42620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42620step0 raw42620; decide +kernel
      have hl : raw42620step0Labels = raw42620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42620 raw42620Labels permutation434 hz
    mixedMoment B raw42620step0 raw42620step0Labels = mixedMoment B raw42620step1 raw42620step1Labels := by
      have hz : ∀ j, raw42620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42620step1 = (fun i j => raw42620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42620step1 raw42620step0; decide +kernel
      have hl : raw42620step1Labels = raw42620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42620step0 raw42620step0Labels permutation80 hz
    mixedMoment B raw42620step1 raw42620step1Labels = mixedMoment B raw42620step2 raw42620step2Labels := by
      have ha : raw42620step2 = (fun i j => raw42620step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42620step2 raw42620step1; decide +kernel
      have hl : raw42620step2Labels = raw42620step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42620step1 raw42620step1Labels permutation20 permutation4
    mixedMoment B raw42620step2 raw42620step2Labels = mixedMoment B raw42620step3 raw42620step3Labels := by
      have ha : raw42620step3 = -raw42620step2 := by apply Matrix.ext; change ∀ i j, raw42620step3 i j = -(raw42620step2 i j); unfold raw42620step3 raw42620step2; decide +kernel
      have hl : raw42620step3Labels = raw42620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42620step3 raw42620step3Labels = mixedMoment B raw42620step4 raw42620step4Labels := by
      have ha : raw42620step4 = raw42620step3 := by apply Matrix.ext; unfold raw42620step4 raw42620step3; decide +kernel
      have hl : raw42620step3Labels = labelEmbedding1 ∘ raw42620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42620step3 raw42620step3Labels raw42620step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1740 node1740Labels := by rfl

theorem canonical42621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42621 raw42621Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw42621 raw42621Labels = mixedMoment B raw42621step0 raw42621step0Labels := by
      have hz : ∀ j, raw42621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42621step0 = (fun i j => raw42621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42621step0 raw42621; decide +kernel
      have hl : raw42621step0Labels = raw42621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42621 raw42621Labels permutation434 hz
    mixedMoment B raw42621step0 raw42621step0Labels = mixedMoment B raw42621step1 raw42621step1Labels := by
      have hz : ∀ j, raw42621step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42621step1 = (fun i j => raw42621step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42621step1 raw42621step0; decide +kernel
      have hl : raw42621step1Labels = raw42621step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42621step0 raw42621step0Labels permutation80 hz
    mixedMoment B raw42621step1 raw42621step1Labels = mixedMoment B raw42621step2 raw42621step2Labels := by
      have ha : raw42621step2 = (fun i j => raw42621step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42621step2 raw42621step1; decide +kernel
      have hl : raw42621step2Labels = raw42621step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42621step1 raw42621step1Labels permutation24 permutation6
    _ = mixedMoment B node4480 node4480Labels := by rfl

theorem canonical42622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42622 raw42622Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw42622 raw42622Labels = mixedMoment B raw42622step0 raw42622step0Labels := by
      have hz : ∀ j, raw42622 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42622step0 = (fun i j => raw42622 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42622step0 raw42622; decide +kernel
      have hl : raw42622step0Labels = raw42622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42622 raw42622Labels permutation434 hz
    mixedMoment B raw42622step0 raw42622step0Labels = mixedMoment B raw42622step1 raw42622step1Labels := by
      have hz : ∀ j, raw42622step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42622step1 = (fun i j => raw42622step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42622step1 raw42622step0; decide +kernel
      have hl : raw42622step1Labels = raw42622step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42622step0 raw42622step0Labels permutation80 hz
    mixedMoment B raw42622step1 raw42622step1Labels = mixedMoment B raw42622step2 raw42622step2Labels := by
      have ha : raw42622step2 = (fun i j => raw42622step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42622step2 raw42622step1; decide +kernel
      have hl : raw42622step2Labels = raw42622step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42622step1 raw42622step1Labels permutation26 permutation4
    mixedMoment B raw42622step2 raw42622step2Labels = mixedMoment B raw42622step3 raw42622step3Labels := by
      have ha : raw42622step3 = -raw42622step2 := by apply Matrix.ext; change ∀ i j, raw42622step3 i j = -(raw42622step2 i j); unfold raw42622step3 raw42622step2; decide +kernel
      have hl : raw42622step3Labels = raw42622step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42622step3 raw42622step3Labels = mixedMoment B raw42622step4 raw42622step4Labels := by
      have ha : raw42622step4 = raw42622step3 := by apply Matrix.ext; unfold raw42622step4 raw42622step3; decide +kernel
      have hl : raw42622step3Labels = labelEmbedding1 ∘ raw42622step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42622step3 raw42622step3Labels raw42622step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

theorem canonical42623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42623 raw42623Labels = mixedMoment B node4188 node4188Labels := by
  calc
    mixedMoment B raw42623 raw42623Labels = mixedMoment B raw42623step0 raw42623step0Labels := by
      have hz : ∀ j, raw42623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42623step0 = (fun i j => raw42623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42623step0 raw42623; decide +kernel
      have hl : raw42623step0Labels = raw42623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42623 raw42623Labels permutation434 hz
    mixedMoment B raw42623step0 raw42623step0Labels = mixedMoment B raw42623step1 raw42623step1Labels := by
      have hz : ∀ j, raw42623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42623step1 = (fun i j => raw42623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42623step1 raw42623step0; decide +kernel
      have hl : raw42623step1Labels = raw42623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42623step0 raw42623step0Labels permutation80 hz
    mixedMoment B raw42623step1 raw42623step1Labels = mixedMoment B raw42623step2 raw42623step2Labels := by
      have ha : raw42623step2 = (fun i j => raw42623step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42623step2 raw42623step1; decide +kernel
      have hl : raw42623step2Labels = raw42623step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42623step1 raw42623step1Labels permutation30 permutation6
    _ = mixedMoment B node4188 node4188Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2624 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2624) =
      Integer.Sparse.eval keyMomentRow2624 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1714) := by
    have ha : gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge = raw42560 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42560Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42560 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4459) := by
    have ha : gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge = raw42561 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42561Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42561 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2624).leftCharge (GramAssembly.key 2624).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2624, Integer.Sparse.eval] <;> ring

theorem keyMoment2625 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2625) =
      Integer.Sparse.eval keyMomentRow2625 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2658) := by
    have ha : gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge = raw42562 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42562Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42562 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4945) := by
    have ha : gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge = raw42563 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42563Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42563 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2625).leftCharge (GramAssembly.key 2625).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2625, Integer.Sparse.eval] <;> ring

theorem keyMoment2626 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2626) =
      Integer.Sparse.eval keyMomentRow2626 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1510) := by
    have ha : gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge = raw42564 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42564Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42564 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4152) := by
    have ha : gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge = raw42565 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42565Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42565 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2626).leftCharge (GramAssembly.key 2626).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2626, Integer.Sparse.eval] <;> ring

theorem keyMoment2627 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2627) =
      Integer.Sparse.eval keyMomentRow2627 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1668) := by
    have ha : gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge = raw42566 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42566Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42566 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4345) := by
    have ha : gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge = raw42567 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42567Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42567 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2627).leftCharge (GramAssembly.key 2627).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2627, Integer.Sparse.eval] <;> ring

theorem keyMoment2628 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2628) =
      Integer.Sparse.eval keyMomentRow2628 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1713) := by
    have ha : gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge = raw42568 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42568Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42568 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4439) := by
    have ha : gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge = raw42569 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42569Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42569 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2628).leftCharge (GramAssembly.key 2628).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2628, Integer.Sparse.eval] <;> ring

theorem keyMoment2629 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2629) =
      Integer.Sparse.eval keyMomentRow2629 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3407) := by
    have ha : gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge = raw42570 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42570Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42570 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4942) := by
    have ha : gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge = raw42571 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42571Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42571 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2629).leftCharge (GramAssembly.key 2629).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2629, Integer.Sparse.eval] <;> ring

theorem keyMoment2630 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2630) =
      Integer.Sparse.eval keyMomentRow2630 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1667) := by
    have ha : gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge = raw42572 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42572Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42572 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4328) := by
    have ha : gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge = raw42573 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42573Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42573 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2630).leftCharge (GramAssembly.key 2630).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2630, Integer.Sparse.eval] <;> ring

theorem keyMoment2631 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2631) =
      Integer.Sparse.eval keyMomentRow2631 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3406) := by
    have ha : gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge = raw42574 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42574Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42574 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4931) := by
    have ha : gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge = raw42575 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42575Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42575 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2631).leftCharge (GramAssembly.key 2631).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2631, Integer.Sparse.eval] <;> ring

theorem keyMoment2632 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2632) =
      Integer.Sparse.eval keyMomentRow2632 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2217) := by
    have ha : gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge = raw42576 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42576Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42576 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4821) := by
    have ha : gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge = raw42577 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42577Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42577 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2632).leftCharge (GramAssembly.key 2632).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2632, Integer.Sparse.eval] <;> ring

theorem keyMoment2633 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2633) =
      Integer.Sparse.eval keyMomentRow2633 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2274) := by
    have ha : gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge = raw42578 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42578Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42578 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4856) := by
    have ha : gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge = raw42579 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42579Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42579 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2633).leftCharge (GramAssembly.key 2633).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2633, Integer.Sparse.eval] <;> ring

theorem keyMoment2634 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2634) =
      Integer.Sparse.eval keyMomentRow2634 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2158) := by
    have ha : gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge = raw42580 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42580Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42580 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4690) := by
    have ha : gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge = raw42581 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42581Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42581 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2634).leftCharge (GramAssembly.key 2634).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2634, Integer.Sparse.eval] <;> ring

theorem keyMoment2635 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2635) =
      Integer.Sparse.eval keyMomentRow2635 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2154) := by
    have ha : gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge = raw42582 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42582Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42582 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4668) := by
    have ha : gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge = raw42583 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42583Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42583 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2635).leftCharge (GramAssembly.key 2635).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2635, Integer.Sparse.eval] <;> ring

theorem keyMoment2636 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2636) =
      Integer.Sparse.eval keyMomentRow2636 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2178) := by
    have ha : gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge = raw42584 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42584Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42584 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4768) := by
    have ha : gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge = raw42585 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42585Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42585 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2636).leftCharge (GramAssembly.key 2636).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2636, Integer.Sparse.eval] <;> ring

theorem keyMoment2637 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2637) =
      Integer.Sparse.eval keyMomentRow2637 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2213) := by
    have ha : gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge = raw42586 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42586Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42586 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4795) := by
    have ha : gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge = raw42587 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42587Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42587 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2637).leftCharge (GramAssembly.key 2637).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2637, Integer.Sparse.eval] <;> ring

theorem keyMoment2638 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2638) =
      Integer.Sparse.eval keyMomentRow2638 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3762) := by
    have ha : gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge = raw42588 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42588Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42588 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5360) := by
    have ha : gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge = raw42589 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42589Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42589 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2638).leftCharge (GramAssembly.key 2638).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2638, Integer.Sparse.eval] <;> ring

theorem keyMoment2639 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2639) =
      Integer.Sparse.eval keyMomentRow2639 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3761) := by
    have ha : gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge = raw42590 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42590Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42590 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5353) := by
    have ha : gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge = raw42591 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42591Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42591 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2639).leftCharge (GramAssembly.key 2639).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2639, Integer.Sparse.eval] <;> ring

theorem keyMoment2640 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2640) =
      Integer.Sparse.eval keyMomentRow2640 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3760) := by
    have ha : gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge = raw42592 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42592Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42592 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5339) := by
    have ha : gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge = raw42593 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42593Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42593 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2640).leftCharge (GramAssembly.key 2640).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2640, Integer.Sparse.eval] <;> ring

theorem keyMoment2641 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2641) =
      Integer.Sparse.eval keyMomentRow2641 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3772) := by
    have ha : gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge = raw42594 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42594Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42594 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5361) := by
    have ha : gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge = raw42595 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42595Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42595 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2641).leftCharge (GramAssembly.key 2641).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2641, Integer.Sparse.eval] <;> ring

theorem keyMoment2642 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2642) =
      Integer.Sparse.eval keyMomentRow2642 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3555) := by
    have ha : gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge = raw42596 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42596Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42596 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4966) := by
    have ha : gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge = raw42597 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42597Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42597 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2642).leftCharge (GramAssembly.key 2642).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2642, Integer.Sparse.eval] <;> ring

theorem keyMoment2643 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2643) =
      Integer.Sparse.eval keyMomentRow2643 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3508) := by
    have ha : gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge = raw42598 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42598Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42598 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4955) := by
    have ha : gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge = raw42599 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42599Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42599 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2643).leftCharge (GramAssembly.key 2643).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2643, Integer.Sparse.eval] <;> ring

theorem keyMoment2644 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2644) =
      Integer.Sparse.eval keyMomentRow2644 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3755) := by
    have ha : gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge = raw42600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42600 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5338) := by
    have ha : gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge = raw42601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42601 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2644).leftCharge (GramAssembly.key 2644).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2644, Integer.Sparse.eval] <;> ring

theorem keyMoment2645 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2645) =
      Integer.Sparse.eval keyMomentRow2645 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3768) := by
    have ha : gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge = raw42602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42602 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5348) := by
    have ha : gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge = raw42603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42603 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2645).leftCharge (GramAssembly.key 2645).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2645, Integer.Sparse.eval] <;> ring

theorem keyMoment2646 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2646) =
      Integer.Sparse.eval keyMomentRow2646 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3759) := by
    have ha : gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge = raw42604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42604 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5359) := by
    have ha : gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge = raw42605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42605 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2646).leftCharge (GramAssembly.key 2646).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2646, Integer.Sparse.eval] <;> ring

theorem keyMoment2647 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2647) =
      Integer.Sparse.eval keyMomentRow2647 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3556) := by
    have ha : gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge = raw42606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42606 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5112) := by
    have ha : gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge = raw42607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42607 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2647).leftCharge (GramAssembly.key 2647).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2647, Integer.Sparse.eval] <;> ring

theorem keyMoment2648 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2648) =
      Integer.Sparse.eval keyMomentRow2648 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3480) := by
    have ha : gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge = raw42608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42608 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5090) := by
    have ha : gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge = raw42609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42609 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2648).leftCharge (GramAssembly.key 2648).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2648, Integer.Sparse.eval] <;> ring

theorem keyMoment2649 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2649) =
      Integer.Sparse.eval keyMomentRow2649 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3271) := by
    have ha : gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge = raw42610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42610 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4556) := by
    have ha : gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge = raw42611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42611 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2649).leftCharge (GramAssembly.key 2649).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2649, Integer.Sparse.eval] <;> ring

theorem keyMoment2650 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2650) =
      Integer.Sparse.eval keyMomentRow2650 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3267) := by
    have ha : gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge = raw42612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42612 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4533) := by
    have ha : gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge = raw42613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42613 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2650).leftCharge (GramAssembly.key 2650).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2650, Integer.Sparse.eval] <;> ring

theorem keyMoment2651 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2651) =
      Integer.Sparse.eval keyMomentRow2651 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3454) := by
    have ha : gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge = raw42614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42614 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5040) := by
    have ha : gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge = raw42615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42615 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2651).leftCharge (GramAssembly.key 2651).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2651, Integer.Sparse.eval] <;> ring

theorem keyMoment2652 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2652) =
      Integer.Sparse.eval keyMomentRow2652 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3476) := by
    have ha : gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge = raw42616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42616 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5067) := by
    have ha : gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge = raw42617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42617 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2652).leftCharge (GramAssembly.key 2652).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2652, Integer.Sparse.eval] <;> ring

theorem keyMoment2653 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2653) =
      Integer.Sparse.eval keyMomentRow2653 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3763) := by
    have ha : gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge = raw42618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42618 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5340) := by
    have ha : gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge = raw42619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42619 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2653).leftCharge (GramAssembly.key 2653).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2653, Integer.Sparse.eval] <;> ring

theorem keyMoment2654 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2654) =
      Integer.Sparse.eval keyMomentRow2654 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1740) := by
    have ha : gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge = raw42620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42620 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4480) := by
    have ha : gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge = raw42621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42621 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2654).leftCharge (GramAssembly.key 2654).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2654, Integer.Sparse.eval] <;> ring

theorem keyMoment2655 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2655) =
      Integer.Sparse.eval keyMomentRow2655 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1526) := by
    have ha : gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge = raw42622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42622 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4188) := by
    have ha : gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge = raw42623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42623 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2655).leftCharge (GramAssembly.key 2655).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2655, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk82
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2624 : keyMomentRows (2624 : Fin 2886) =
    keyMomentRow2624 := by decide +kernel

theorem keyMomentRowsAt2625 : keyMomentRows (2625 : Fin 2886) =
    keyMomentRow2625 := by decide +kernel

theorem keyMomentRowsAt2626 : keyMomentRows (2626 : Fin 2886) =
    keyMomentRow2626 := by decide +kernel

theorem keyMomentRowsAt2627 : keyMomentRows (2627 : Fin 2886) =
    keyMomentRow2627 := by decide +kernel

theorem keyMomentRowsAt2628 : keyMomentRows (2628 : Fin 2886) =
    keyMomentRow2628 := by decide +kernel

theorem keyMomentRowsAt2629 : keyMomentRows (2629 : Fin 2886) =
    keyMomentRow2629 := by decide +kernel

theorem keyMomentRowsAt2630 : keyMomentRows (2630 : Fin 2886) =
    keyMomentRow2630 := by decide +kernel

theorem keyMomentRowsAt2631 : keyMomentRows (2631 : Fin 2886) =
    keyMomentRow2631 := by decide +kernel

theorem keyMomentRowsAt2632 : keyMomentRows (2632 : Fin 2886) =
    keyMomentRow2632 := by decide +kernel

theorem keyMomentRowsAt2633 : keyMomentRows (2633 : Fin 2886) =
    keyMomentRow2633 := by decide +kernel

theorem keyMomentRowsAt2634 : keyMomentRows (2634 : Fin 2886) =
    keyMomentRow2634 := by decide +kernel

theorem keyMomentRowsAt2635 : keyMomentRows (2635 : Fin 2886) =
    keyMomentRow2635 := by decide +kernel

theorem keyMomentRowsAt2636 : keyMomentRows (2636 : Fin 2886) =
    keyMomentRow2636 := by decide +kernel

theorem keyMomentRowsAt2637 : keyMomentRows (2637 : Fin 2886) =
    keyMomentRow2637 := by decide +kernel

theorem keyMomentRowsAt2638 : keyMomentRows (2638 : Fin 2886) =
    keyMomentRow2638 := by decide +kernel

theorem keyMomentRowsAt2639 : keyMomentRows (2639 : Fin 2886) =
    keyMomentRow2639 := by decide +kernel

theorem keyMomentRowsAt2640 : keyMomentRows (2640 : Fin 2886) =
    keyMomentRow2640 := by decide +kernel

theorem keyMomentRowsAt2641 : keyMomentRows (2641 : Fin 2886) =
    keyMomentRow2641 := by decide +kernel

theorem keyMomentRowsAt2642 : keyMomentRows (2642 : Fin 2886) =
    keyMomentRow2642 := by decide +kernel

theorem keyMomentRowsAt2643 : keyMomentRows (2643 : Fin 2886) =
    keyMomentRow2643 := by decide +kernel

theorem keyMomentRowsAt2644 : keyMomentRows (2644 : Fin 2886) =
    keyMomentRow2644 := by decide +kernel

theorem keyMomentRowsAt2645 : keyMomentRows (2645 : Fin 2886) =
    keyMomentRow2645 := by decide +kernel

theorem keyMomentRowsAt2646 : keyMomentRows (2646 : Fin 2886) =
    keyMomentRow2646 := by decide +kernel

theorem keyMomentRowsAt2647 : keyMomentRows (2647 : Fin 2886) =
    keyMomentRow2647 := by decide +kernel

theorem keyMomentRowsAt2648 : keyMomentRows (2648 : Fin 2886) =
    keyMomentRow2648 := by decide +kernel

theorem keyMomentRowsAt2649 : keyMomentRows (2649 : Fin 2886) =
    keyMomentRow2649 := by decide +kernel

theorem keyMomentRowsAt2650 : keyMomentRows (2650 : Fin 2886) =
    keyMomentRow2650 := by decide +kernel

theorem keyMomentRowsAt2651 : keyMomentRows (2651 : Fin 2886) =
    keyMomentRow2651 := by decide +kernel

theorem keyMomentRowsAt2652 : keyMomentRows (2652 : Fin 2886) =
    keyMomentRow2652 := by decide +kernel

theorem keyMomentRowsAt2653 : keyMomentRows (2653 : Fin 2886) =
    keyMomentRow2653 := by decide +kernel

theorem keyMomentRowsAt2654 : keyMomentRows (2654 : Fin 2886) =
    keyMomentRow2654 := by decide +kernel

theorem keyMomentRowsAt2655 : keyMomentRows (2655 : Fin 2886) =
    keyMomentRow2655 := by decide +kernel

theorem keyMomentChunkSound82_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 82) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2624 ∨ k.val = 2625 ∨ k.val = 2626 ∨ k.val = 2627 ∨ k.val = 2628 ∨ k.val = 2629 ∨ k.val = 2630 ∨ k.val = 2631 ∨ k.val = 2632 ∨ k.val = 2633 ∨ k.val = 2634 ∨ k.val = 2635 ∨ k.val = 2636 ∨ k.val = 2637 ∨ k.val = 2638 ∨ k.val = 2639 ∨ k.val = 2640 ∨ k.val = 2641 ∨ k.val = 2642 ∨ k.val = 2643 ∨ k.val = 2644 ∨ k.val = 2645 ∨ k.val = 2646 ∨ k.val = 2647 ∨ k.val = 2648 ∨ k.val = 2649 ∨ k.val = 2650 ∨ k.val = 2651 ∨ k.val = 2652 ∨ k.val = 2653 ∨ k.val = 2654 ∨ k.val = 2655 := by omega
  rcases heq with h2624 | h2625 | h2626 | h2627 | h2628 | h2629 | h2630 | h2631 | h2632 | h2633 | h2634 | h2635 | h2636 | h2637 | h2638 | h2639 | h2640 | h2641 | h2642 | h2643 | h2644 | h2645 | h2646 | h2647 | h2648 | h2649 | h2650 | h2651 | h2652 | h2653 | h2654 | h2655
  · have he : k = (2624 : Fin 2886) := Fin.ext h2624
    subst k
    rw [keyMomentRowsAt2624]
    exact keyMoment2624 B hB
  · have he : k = (2625 : Fin 2886) := Fin.ext h2625
    subst k
    rw [keyMomentRowsAt2625]
    exact keyMoment2625 B hB
  · have he : k = (2626 : Fin 2886) := Fin.ext h2626
    subst k
    rw [keyMomentRowsAt2626]
    exact keyMoment2626 B hB
  · have he : k = (2627 : Fin 2886) := Fin.ext h2627
    subst k
    rw [keyMomentRowsAt2627]
    exact keyMoment2627 B hB
  · have he : k = (2628 : Fin 2886) := Fin.ext h2628
    subst k
    rw [keyMomentRowsAt2628]
    exact keyMoment2628 B hB
  · have he : k = (2629 : Fin 2886) := Fin.ext h2629
    subst k
    rw [keyMomentRowsAt2629]
    exact keyMoment2629 B hB
  · have he : k = (2630 : Fin 2886) := Fin.ext h2630
    subst k
    rw [keyMomentRowsAt2630]
    exact keyMoment2630 B hB
  · have he : k = (2631 : Fin 2886) := Fin.ext h2631
    subst k
    rw [keyMomentRowsAt2631]
    exact keyMoment2631 B hB
  · have he : k = (2632 : Fin 2886) := Fin.ext h2632
    subst k
    rw [keyMomentRowsAt2632]
    exact keyMoment2632 B hB
  · have he : k = (2633 : Fin 2886) := Fin.ext h2633
    subst k
    rw [keyMomentRowsAt2633]
    exact keyMoment2633 B hB
  · have he : k = (2634 : Fin 2886) := Fin.ext h2634
    subst k
    rw [keyMomentRowsAt2634]
    exact keyMoment2634 B hB
  · have he : k = (2635 : Fin 2886) := Fin.ext h2635
    subst k
    rw [keyMomentRowsAt2635]
    exact keyMoment2635 B hB
  · have he : k = (2636 : Fin 2886) := Fin.ext h2636
    subst k
    rw [keyMomentRowsAt2636]
    exact keyMoment2636 B hB
  · have he : k = (2637 : Fin 2886) := Fin.ext h2637
    subst k
    rw [keyMomentRowsAt2637]
    exact keyMoment2637 B hB
  · have he : k = (2638 : Fin 2886) := Fin.ext h2638
    subst k
    rw [keyMomentRowsAt2638]
    exact keyMoment2638 B hB
  · have he : k = (2639 : Fin 2886) := Fin.ext h2639
    subst k
    rw [keyMomentRowsAt2639]
    exact keyMoment2639 B hB
  · have he : k = (2640 : Fin 2886) := Fin.ext h2640
    subst k
    rw [keyMomentRowsAt2640]
    exact keyMoment2640 B hB
  · have he : k = (2641 : Fin 2886) := Fin.ext h2641
    subst k
    rw [keyMomentRowsAt2641]
    exact keyMoment2641 B hB
  · have he : k = (2642 : Fin 2886) := Fin.ext h2642
    subst k
    rw [keyMomentRowsAt2642]
    exact keyMoment2642 B hB
  · have he : k = (2643 : Fin 2886) := Fin.ext h2643
    subst k
    rw [keyMomentRowsAt2643]
    exact keyMoment2643 B hB
  · have he : k = (2644 : Fin 2886) := Fin.ext h2644
    subst k
    rw [keyMomentRowsAt2644]
    exact keyMoment2644 B hB
  · have he : k = (2645 : Fin 2886) := Fin.ext h2645
    subst k
    rw [keyMomentRowsAt2645]
    exact keyMoment2645 B hB
  · have he : k = (2646 : Fin 2886) := Fin.ext h2646
    subst k
    rw [keyMomentRowsAt2646]
    exact keyMoment2646 B hB
  · have he : k = (2647 : Fin 2886) := Fin.ext h2647
    subst k
    rw [keyMomentRowsAt2647]
    exact keyMoment2647 B hB
  · have he : k = (2648 : Fin 2886) := Fin.ext h2648
    subst k
    rw [keyMomentRowsAt2648]
    exact keyMoment2648 B hB
  · have he : k = (2649 : Fin 2886) := Fin.ext h2649
    subst k
    rw [keyMomentRowsAt2649]
    exact keyMoment2649 B hB
  · have he : k = (2650 : Fin 2886) := Fin.ext h2650
    subst k
    rw [keyMomentRowsAt2650]
    exact keyMoment2650 B hB
  · have he : k = (2651 : Fin 2886) := Fin.ext h2651
    subst k
    rw [keyMomentRowsAt2651]
    exact keyMoment2651 B hB
  · have he : k = (2652 : Fin 2886) := Fin.ext h2652
    subst k
    rw [keyMomentRowsAt2652]
    exact keyMoment2652 B hB
  · have he : k = (2653 : Fin 2886) := Fin.ext h2653
    subst k
    rw [keyMomentRowsAt2653]
    exact keyMoment2653 B hB
  · have he : k = (2654 : Fin 2886) := Fin.ext h2654
    subst k
    rw [keyMomentRowsAt2654]
    exact keyMoment2654 B hB
  · have he : k = (2655 : Fin 2886) := Fin.ext h2655
    subst k
    rw [keyMomentRowsAt2655]
    exact keyMoment2655 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound82_e_oai
