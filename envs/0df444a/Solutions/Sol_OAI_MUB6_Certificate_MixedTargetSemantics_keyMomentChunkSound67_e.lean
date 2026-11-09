-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:19.548591+00:00
-- url     : https://prove2.me/submissions/4a368f98-3e0c-4eef-a83b-8ee0be2a095d

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical325
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41600 raw41600Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw41600 raw41600Labels = mixedMoment B raw41600step0 raw41600step0Labels := by
      have hz : ∀ j, raw41600 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41600step0 = (fun i j => raw41600 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41600step0 raw41600; decide +kernel
      have hl : raw41600step0Labels = raw41600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41600 raw41600Labels permutation265 hz
    mixedMoment B raw41600step0 raw41600step0Labels = mixedMoment B raw41600step1 raw41600step1Labels := by
      have ha : raw41600step1 = (fun i j => raw41600step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41600step1 raw41600step0; decide +kernel
      have hl : raw41600step1Labels = raw41600step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41600step0 raw41600step0Labels permutation37 permutation2
    mixedMoment B raw41600step1 raw41600step1Labels = mixedMoment B raw41600step2 raw41600step2Labels := by
      have ha : raw41600step2 = raw41600step1 := by apply Matrix.ext; unfold raw41600step2 raw41600step1; decide +kernel
      have hl : raw41600step1Labels = labelEmbedding1 ∘ raw41600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41600step1 raw41600step1Labels raw41600step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

theorem canonical41601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41601 raw41601Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw41601 raw41601Labels = mixedMoment B raw41601step0 raw41601step0Labels := by
      have hz : ∀ j, raw41601 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41601step0 = (fun i j => raw41601 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41601step0 raw41601; decide +kernel
      have hl : raw41601step0Labels = raw41601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41601 raw41601Labels permutation265 hz
    mixedMoment B raw41601step0 raw41601step0Labels = mixedMoment B raw41601step1 raw41601step1Labels := by
      have ha : raw41601step1 = (fun i j => raw41601step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41601step1 raw41601step0; decide +kernel
      have hl : raw41601step1Labels = raw41601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41601step0 raw41601step0Labels permutation32 permutation3
    mixedMoment B raw41601step1 raw41601step1Labels = mixedMoment B raw41601step2 raw41601step2Labels := by
      have ha : raw41601step2 = raw41601step1 := by apply Matrix.ext; unfold raw41601step2 raw41601step1; decide +kernel
      have hl : raw41601step1Labels = labelEmbedding7 ∘ raw41601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41601step1 raw41601step1Labels raw41601step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical41602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41602 raw41602Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw41602 raw41602Labels = mixedMoment B raw41602step0 raw41602step0Labels := by
      have ha : raw41602step0 = (fun i j => raw41602 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41602step0 raw41602; decide +kernel
      have hl : raw41602step0Labels = raw41602Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41602 raw41602Labels permutation157 permutation2
    mixedMoment B raw41602step0 raw41602step0Labels = mixedMoment B raw41602step1 raw41602step1Labels := by
      have ha : raw41602step1 = raw41602step0 := by apply Matrix.ext; unfold raw41602step1 raw41602step0; decide +kernel
      have hl : raw41602step0Labels = labelEmbedding1 ∘ raw41602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41602step0 raw41602step0Labels raw41602step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

theorem canonical41603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41603 raw41603Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw41603 raw41603Labels = mixedMoment B raw41603step0 raw41603step0Labels := by
      have ha : raw41603step0 = (fun i j => raw41603 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41603step0 raw41603; decide +kernel
      have hl : raw41603step0Labels = raw41603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41603 raw41603Labels permutation152 permutation3
    mixedMoment B raw41603step0 raw41603step0Labels = mixedMoment B raw41603step1 raw41603step1Labels := by
      have ha : raw41603step1 = raw41603step0 := by apply Matrix.ext; unfold raw41603step1 raw41603step0; decide +kernel
      have hl : raw41603step0Labels = labelEmbedding7 ∘ raw41603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41603step0 raw41603step0Labels raw41603step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical41604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41604 raw41604Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw41604 raw41604Labels = mixedMoment B raw41604step0 raw41604step0Labels := by
      have hz : ∀ j, raw41604 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41604step0 = (fun i j => raw41604 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41604step0 raw41604; decide +kernel
      have hl : raw41604step0Labels = raw41604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41604 raw41604Labels permutation520 hz
    mixedMoment B raw41604step0 raw41604step0Labels = mixedMoment B raw41604step1 raw41604step1Labels := by
      have hz : ∀ j, raw41604step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41604step1 = (fun i j => raw41604step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41604step1 raw41604step0; decide +kernel
      have hl : raw41604step1Labels = raw41604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41604step0 raw41604step0Labels permutation104 hz
    mixedMoment B raw41604step1 raw41604step1Labels = mixedMoment B raw41604step2 raw41604step2Labels := by
      have hz : ∀ j, raw41604step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41604step2 = (fun i j => raw41604step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41604step2 raw41604step1; decide +kernel
      have hl : raw41604step2Labels = raw41604step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41604step1 raw41604step1Labels permutation20 hz
    mixedMoment B raw41604step2 raw41604step2Labels = mixedMoment B raw41604step3 raw41604step3Labels := by
      have ha : raw41604step3 = raw41604step2 := by apply Matrix.ext; unfold raw41604step3 raw41604step2; decide +kernel
      have hl : raw41604step2Labels = labelEmbedding1 ∘ raw41604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41604step2 raw41604step2Labels raw41604step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

theorem canonical41605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41605 raw41605Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw41605 raw41605Labels = mixedMoment B raw41605step0 raw41605step0Labels := by
      have hz : ∀ j, raw41605 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41605step0 = (fun i j => raw41605 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41605step0 raw41605; decide +kernel
      have hl : raw41605step0Labels = raw41605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41605 raw41605Labels permutation520 hz
    mixedMoment B raw41605step0 raw41605step0Labels = mixedMoment B raw41605step1 raw41605step1Labels := by
      have hz : ∀ j, raw41605step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41605step1 = (fun i j => raw41605step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41605step1 raw41605step0; decide +kernel
      have hl : raw41605step1Labels = raw41605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41605step0 raw41605step0Labels permutation104 hz
    mixedMoment B raw41605step1 raw41605step1Labels = mixedMoment B raw41605step2 raw41605step2Labels := by
      have hz : ∀ j, raw41605step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41605step2 = (fun i j => raw41605step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41605step2 raw41605step1; decide +kernel
      have hl : raw41605step2Labels = raw41605step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41605step1 raw41605step1Labels permutation20 hz
    mixedMoment B raw41605step2 raw41605step2Labels = mixedMoment B raw41605step3 raw41605step3Labels := by
      have ha : raw41605step3 = (fun i j => raw41605step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41605step3 raw41605step2; decide +kernel
      have hl : raw41605step3Labels = raw41605step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41605step2 raw41605step2Labels permutation7 permutation3
    mixedMoment B raw41605step3 raw41605step3Labels = mixedMoment B raw41605step4 raw41605step4Labels := by
      have ha : raw41605step4 = -raw41605step3 := by apply Matrix.ext; change ∀ i j, raw41605step4 i j = -(raw41605step3 i j); unfold raw41605step4 raw41605step3; decide +kernel
      have hl : raw41605step4Labels = raw41605step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41605step4 raw41605step4Labels = mixedMoment B raw41605step5 raw41605step5Labels := by
      have ha : raw41605step5 = raw41605step4 := by apply Matrix.ext; unfold raw41605step5 raw41605step4; decide +kernel
      have hl : raw41605step4Labels = labelEmbedding7 ∘ raw41605step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41605step4 raw41605step4Labels raw41605step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical41606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41606 raw41606Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw41606 raw41606Labels = mixedMoment B raw41606step0 raw41606step0Labels := by
      have hz : ∀ j, raw41606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41606step0 = (fun i j => raw41606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41606step0 raw41606; decide +kernel
      have hl : raw41606step0Labels = raw41606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41606 raw41606Labels permutation434 hz
    mixedMoment B raw41606step0 raw41606step0Labels = mixedMoment B raw41606step1 raw41606step1Labels := by
      have hz : ∀ j, raw41606step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41606step1 = (fun i j => raw41606step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41606step1 raw41606step0; decide +kernel
      have hl : raw41606step1Labels = raw41606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41606step0 raw41606step0Labels permutation80 hz
    mixedMoment B raw41606step1 raw41606step1Labels = mixedMoment B raw41606step2 raw41606step2Labels := by
      have ha : raw41606step2 = raw41606step1 := by apply Matrix.ext; unfold raw41606step2 raw41606step1; decide +kernel
      have hl : raw41606step1Labels = labelEmbedding1 ∘ raw41606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41606step1 raw41606step1Labels raw41606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

theorem canonical41607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41607 raw41607Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41607 raw41607Labels = mixedMoment B raw41607step0 raw41607step0Labels := by
      have hz : ∀ j, raw41607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41607step0 = (fun i j => raw41607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41607step0 raw41607; decide +kernel
      have hl : raw41607step0Labels = raw41607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41607 raw41607Labels permutation434 hz
    mixedMoment B raw41607step0 raw41607step0Labels = mixedMoment B raw41607step1 raw41607step1Labels := by
      have hz : ∀ j, raw41607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41607step1 = (fun i j => raw41607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41607step1 raw41607step0; decide +kernel
      have hl : raw41607step1Labels = raw41607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41607step0 raw41607step0Labels permutation80 hz
    mixedMoment B raw41607step1 raw41607step1Labels = mixedMoment B raw41607step2 raw41607step2Labels := by
      have ha : raw41607step2 = (fun i j => raw41607step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41607step2 raw41607step1; decide +kernel
      have hl : raw41607step2Labels = raw41607step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41607step1 raw41607step1Labels permutation30 permutation5
    mixedMoment B raw41607step2 raw41607step2Labels = mixedMoment B raw41607step3 raw41607step3Labels := by
      have ha : raw41607step3 = raw41607step2 := by apply Matrix.ext; unfold raw41607step3 raw41607step2; decide +kernel
      have hl : raw41607step2Labels = labelEmbedding9 ∘ raw41607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41607step2 raw41607step2Labels raw41607step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

theorem canonical41608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41608 raw41608Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw41608 raw41608Labels = mixedMoment B raw41608step0 raw41608step0Labels := by
      have hz : ∀ j, raw41608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41608step0 = (fun i j => raw41608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41608step0 raw41608; decide +kernel
      have hl : raw41608step0Labels = raw41608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41608 raw41608Labels permutation434 hz
    mixedMoment B raw41608step0 raw41608step0Labels = mixedMoment B raw41608step1 raw41608step1Labels := by
      have hz : ∀ j, raw41608step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41608step1 = (fun i j => raw41608step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41608step1 raw41608step0; decide +kernel
      have hl : raw41608step1Labels = raw41608step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41608step0 raw41608step0Labels permutation80 hz
    mixedMoment B raw41608step1 raw41608step1Labels = mixedMoment B raw41608step2 raw41608step2Labels := by
      have ha : raw41608step2 = raw41608step1 := by apply Matrix.ext; unfold raw41608step2 raw41608step1; decide +kernel
      have hl : raw41608step1Labels = labelEmbedding1 ∘ raw41608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41608step1 raw41608step1Labels raw41608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical41609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41609 raw41609Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw41609 raw41609Labels = mixedMoment B raw41609step0 raw41609step0Labels := by
      have hz : ∀ j, raw41609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41609step0 = (fun i j => raw41609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41609step0 raw41609; decide +kernel
      have hl : raw41609step0Labels = raw41609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41609 raw41609Labels permutation434 hz
    mixedMoment B raw41609step0 raw41609step0Labels = mixedMoment B raw41609step1 raw41609step1Labels := by
      have hz : ∀ j, raw41609step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41609step1 = (fun i j => raw41609step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41609step1 raw41609step0; decide +kernel
      have hl : raw41609step1Labels = raw41609step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41609step0 raw41609step0Labels permutation80 hz
    mixedMoment B raw41609step1 raw41609step1Labels = mixedMoment B raw41609step2 raw41609step2Labels := by
      have ha : raw41609step2 = raw41609step1 := by apply Matrix.ext; unfold raw41609step2 raw41609step1; decide +kernel
      have hl : raw41609step1Labels = labelEmbedding8 ∘ raw41609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41609step1 raw41609step1Labels raw41609step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical41610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41610 raw41610Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw41610 raw41610Labels = mixedMoment B raw41610step0 raw41610step0Labels := by
      have hz : ∀ j, raw41610 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41610step0 = (fun i j => raw41610 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41610step0 raw41610; decide +kernel
      have hl : raw41610step0Labels = raw41610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41610 raw41610Labels permutation434 hz
    mixedMoment B raw41610step0 raw41610step0Labels = mixedMoment B raw41610step1 raw41610step1Labels := by
      have hz : ∀ j, raw41610step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41610step1 = (fun i j => raw41610step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41610step1 raw41610step0; decide +kernel
      have hl : raw41610step1Labels = raw41610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41610step0 raw41610step0Labels permutation80 hz
    mixedMoment B raw41610step1 raw41610step1Labels = mixedMoment B raw41610step2 raw41610step2Labels := by
      have ha : raw41610step2 = raw41610step1 := by apply Matrix.ext; unfold raw41610step2 raw41610step1; decide +kernel
      have hl : raw41610step1Labels = labelEmbedding1 ∘ raw41610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41610step1 raw41610step1Labels raw41610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical41611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41611 raw41611Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw41611 raw41611Labels = mixedMoment B raw41611step0 raw41611step0Labels := by
      have hz : ∀ j, raw41611 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41611step0 = (fun i j => raw41611 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41611step0 raw41611; decide +kernel
      have hl : raw41611step0Labels = raw41611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41611 raw41611Labels permutation434 hz
    mixedMoment B raw41611step0 raw41611step0Labels = mixedMoment B raw41611step1 raw41611step1Labels := by
      have hz : ∀ j, raw41611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41611step1 = (fun i j => raw41611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41611step1 raw41611step0; decide +kernel
      have hl : raw41611step1Labels = raw41611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41611step0 raw41611step0Labels permutation80 hz
    mixedMoment B raw41611step1 raw41611step1Labels = mixedMoment B raw41611step2 raw41611step2Labels := by
      have ha : raw41611step2 = raw41611step1 := by apply Matrix.ext; unfold raw41611step2 raw41611step1; decide +kernel
      have hl : raw41611step1Labels = labelEmbedding8 ∘ raw41611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41611step1 raw41611step1Labels raw41611step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical41612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41612 raw41612Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw41612 raw41612Labels = mixedMoment B raw41612step0 raw41612step0Labels := by
      have hz : ∀ j, raw41612 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41612step0 = (fun i j => raw41612 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41612step0 raw41612; decide +kernel
      have hl : raw41612step0Labels = raw41612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41612 raw41612Labels permutation434 hz
    mixedMoment B raw41612step0 raw41612step0Labels = mixedMoment B raw41612step1 raw41612step1Labels := by
      have hz : ∀ j, raw41612step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41612step1 = (fun i j => raw41612step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41612step1 raw41612step0; decide +kernel
      have hl : raw41612step1Labels = raw41612step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41612step0 raw41612step0Labels permutation80 hz
    mixedMoment B raw41612step1 raw41612step1Labels = mixedMoment B raw41612step2 raw41612step2Labels := by
      have ha : raw41612step2 = raw41612step1 := by apply Matrix.ext; unfold raw41612step2 raw41612step1; decide +kernel
      have hl : raw41612step1Labels = labelEmbedding1 ∘ raw41612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41612step1 raw41612step1Labels raw41612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2771 node2771Labels := by rfl

theorem canonical41613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41613 raw41613Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw41613 raw41613Labels = mixedMoment B raw41613step0 raw41613step0Labels := by
      have hz : ∀ j, raw41613 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41613step0 = (fun i j => raw41613 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41613step0 raw41613; decide +kernel
      have hl : raw41613step0Labels = raw41613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41613 raw41613Labels permutation434 hz
    mixedMoment B raw41613step0 raw41613step0Labels = mixedMoment B raw41613step1 raw41613step1Labels := by
      have hz : ∀ j, raw41613step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41613step1 = (fun i j => raw41613step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41613step1 raw41613step0; decide +kernel
      have hl : raw41613step1Labels = raw41613step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41613step0 raw41613step0Labels permutation80 hz
    mixedMoment B raw41613step1 raw41613step1Labels = mixedMoment B raw41613step2 raw41613step2Labels := by
      have ha : raw41613step2 = raw41613step1 := by apply Matrix.ext; unfold raw41613step2 raw41613step1; decide +kernel
      have hl : raw41613step1Labels = labelEmbedding8 ∘ raw41613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41613step1 raw41613step1Labels raw41613step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

theorem canonical41614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41614 raw41614Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw41614 raw41614Labels = mixedMoment B raw41614step0 raw41614step0Labels := by
      have hz : ∀ j, raw41614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41614step0 = (fun i j => raw41614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41614step0 raw41614; decide +kernel
      have hl : raw41614step0Labels = raw41614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41614 raw41614Labels permutation346 hz
    mixedMoment B raw41614step0 raw41614step0Labels = mixedMoment B raw41614step1 raw41614step1Labels := by
      have ha : raw41614step1 = (fun i j => raw41614step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41614step1 raw41614step0; decide +kernel
      have hl : raw41614step1Labels = raw41614step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41614step0 raw41614step0Labels permutation38 permutation2
    mixedMoment B raw41614step1 raw41614step1Labels = mixedMoment B raw41614step2 raw41614step2Labels := by
      have ha : raw41614step2 = raw41614step1 := by apply Matrix.ext; unfold raw41614step2 raw41614step1; decide +kernel
      have hl : raw41614step1Labels = labelEmbedding1 ∘ raw41614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41614step1 raw41614step1Labels raw41614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical41615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41615 raw41615Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw41615 raw41615Labels = mixedMoment B raw41615step0 raw41615step0Labels := by
      have hz : ∀ j, raw41615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41615step0 = (fun i j => raw41615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41615step0 raw41615; decide +kernel
      have hl : raw41615step0Labels = raw41615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41615 raw41615Labels permutation346 hz
    mixedMoment B raw41615step0 raw41615step0Labels = mixedMoment B raw41615step1 raw41615step1Labels := by
      have ha : raw41615step1 = (fun i j => raw41615step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41615step1 raw41615step0; decide +kernel
      have hl : raw41615step1Labels = raw41615step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41615step0 raw41615step0Labels permutation38 permutation2
    mixedMoment B raw41615step1 raw41615step1Labels = mixedMoment B raw41615step2 raw41615step2Labels := by
      have ha : raw41615step2 = raw41615step1 := by apply Matrix.ext; unfold raw41615step2 raw41615step1; decide +kernel
      have hl : raw41615step1Labels = labelEmbedding8 ∘ raw41615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41615step1 raw41615step1Labels raw41615step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical41616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41616 raw41616Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw41616 raw41616Labels = mixedMoment B raw41616step0 raw41616step0Labels := by
      have hz : ∀ j, raw41616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41616step0 = (fun i j => raw41616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41616step0 raw41616; decide +kernel
      have hl : raw41616step0Labels = raw41616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41616 raw41616Labels permutation346 hz
    mixedMoment B raw41616step0 raw41616step0Labels = mixedMoment B raw41616step1 raw41616step1Labels := by
      have ha : raw41616step1 = (fun i j => raw41616step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41616step1 raw41616step0; decide +kernel
      have hl : raw41616step1Labels = raw41616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41616step0 raw41616step0Labels permutation38 permutation2
    mixedMoment B raw41616step1 raw41616step1Labels = mixedMoment B raw41616step2 raw41616step2Labels := by
      have ha : raw41616step2 = raw41616step1 := by apply Matrix.ext; unfold raw41616step2 raw41616step1; decide +kernel
      have hl : raw41616step1Labels = labelEmbedding1 ∘ raw41616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41616step1 raw41616step1Labels raw41616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical41617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41617 raw41617Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw41617 raw41617Labels = mixedMoment B raw41617step0 raw41617step0Labels := by
      have hz : ∀ j, raw41617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41617step0 = (fun i j => raw41617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41617step0 raw41617; decide +kernel
      have hl : raw41617step0Labels = raw41617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41617 raw41617Labels permutation346 hz
    mixedMoment B raw41617step0 raw41617step0Labels = mixedMoment B raw41617step1 raw41617step1Labels := by
      have ha : raw41617step1 = (fun i j => raw41617step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41617step1 raw41617step0; decide +kernel
      have hl : raw41617step1Labels = raw41617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41617step0 raw41617step0Labels permutation38 permutation2
    mixedMoment B raw41617step1 raw41617step1Labels = mixedMoment B raw41617step2 raw41617step2Labels := by
      have ha : raw41617step2 = raw41617step1 := by apply Matrix.ext; unfold raw41617step2 raw41617step1; decide +kernel
      have hl : raw41617step1Labels = labelEmbedding8 ∘ raw41617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41617step1 raw41617step1Labels raw41617step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical41618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41618 raw41618Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw41618 raw41618Labels = mixedMoment B raw41618step0 raw41618step0Labels := by
      have hz : ∀ j, raw41618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41618step0 = (fun i j => raw41618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41618step0 raw41618; decide +kernel
      have hl : raw41618step0Labels = raw41618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41618 raw41618Labels permutation346 hz
    mixedMoment B raw41618step0 raw41618step0Labels = mixedMoment B raw41618step1 raw41618step1Labels := by
      have ha : raw41618step1 = (fun i j => raw41618step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41618step1 raw41618step0; decide +kernel
      have hl : raw41618step1Labels = raw41618step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41618step0 raw41618step0Labels permutation38 permutation2
    mixedMoment B raw41618step1 raw41618step1Labels = mixedMoment B raw41618step2 raw41618step2Labels := by
      have ha : raw41618step2 = raw41618step1 := by apply Matrix.ext; unfold raw41618step2 raw41618step1; decide +kernel
      have hl : raw41618step1Labels = labelEmbedding1 ∘ raw41618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41618step1 raw41618step1Labels raw41618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

theorem canonical41619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41619 raw41619Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw41619 raw41619Labels = mixedMoment B raw41619step0 raw41619step0Labels := by
      have hz : ∀ j, raw41619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41619step0 = (fun i j => raw41619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41619step0 raw41619; decide +kernel
      have hl : raw41619step0Labels = raw41619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41619 raw41619Labels permutation346 hz
    mixedMoment B raw41619step0 raw41619step0Labels = mixedMoment B raw41619step1 raw41619step1Labels := by
      have ha : raw41619step1 = (fun i j => raw41619step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41619step1 raw41619step0; decide +kernel
      have hl : raw41619step1Labels = raw41619step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41619step0 raw41619step0Labels permutation38 permutation2
    mixedMoment B raw41619step1 raw41619step1Labels = mixedMoment B raw41619step2 raw41619step2Labels := by
      have ha : raw41619step2 = raw41619step1 := by apply Matrix.ext; unfold raw41619step2 raw41619step1; decide +kernel
      have hl : raw41619step1Labels = labelEmbedding8 ∘ raw41619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41619step1 raw41619step1Labels raw41619step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

theorem canonical41620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41620 raw41620Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw41620 raw41620Labels = mixedMoment B raw41620step0 raw41620step0Labels := by
      have hz : ∀ j, raw41620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41620step0 = (fun i j => raw41620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41620step0 raw41620; decide +kernel
      have hl : raw41620step0Labels = raw41620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41620 raw41620Labels permutation346 hz
    mixedMoment B raw41620step0 raw41620step0Labels = mixedMoment B raw41620step1 raw41620step1Labels := by
      have ha : raw41620step1 = (fun i j => raw41620step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41620step1 raw41620step0; decide +kernel
      have hl : raw41620step1Labels = raw41620step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41620step0 raw41620step0Labels permutation38 permutation2
    mixedMoment B raw41620step1 raw41620step1Labels = mixedMoment B raw41620step2 raw41620step2Labels := by
      have ha : raw41620step2 = raw41620step1 := by apply Matrix.ext; unfold raw41620step2 raw41620step1; decide +kernel
      have hl : raw41620step1Labels = labelEmbedding1 ∘ raw41620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41620step1 raw41620step1Labels raw41620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical41621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41621 raw41621Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw41621 raw41621Labels = mixedMoment B raw41621step0 raw41621step0Labels := by
      have hz : ∀ j, raw41621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41621step0 = (fun i j => raw41621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41621step0 raw41621; decide +kernel
      have hl : raw41621step0Labels = raw41621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41621 raw41621Labels permutation346 hz
    mixedMoment B raw41621step0 raw41621step0Labels = mixedMoment B raw41621step1 raw41621step1Labels := by
      have ha : raw41621step1 = (fun i j => raw41621step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41621step1 raw41621step0; decide +kernel
      have hl : raw41621step1Labels = raw41621step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41621step0 raw41621step0Labels permutation38 permutation2
    mixedMoment B raw41621step1 raw41621step1Labels = mixedMoment B raw41621step2 raw41621step2Labels := by
      have ha : raw41621step2 = raw41621step1 := by apply Matrix.ext; unfold raw41621step2 raw41621step1; decide +kernel
      have hl : raw41621step1Labels = labelEmbedding8 ∘ raw41621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41621step1 raw41621step1Labels raw41621step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical41622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41622 raw41622Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw41622 raw41622Labels = mixedMoment B raw41622step0 raw41622step0Labels := by
      have hz : ∀ j, raw41622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41622step0 = (fun i j => raw41622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41622step0 raw41622; decide +kernel
      have hl : raw41622step0Labels = raw41622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41622 raw41622Labels permutation346 hz
    mixedMoment B raw41622step0 raw41622step0Labels = mixedMoment B raw41622step1 raw41622step1Labels := by
      have ha : raw41622step1 = (fun i j => raw41622step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41622step1 raw41622step0; decide +kernel
      have hl : raw41622step1Labels = raw41622step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41622step0 raw41622step0Labels permutation144 permutation4
    mixedMoment B raw41622step1 raw41622step1Labels = mixedMoment B raw41622step2 raw41622step2Labels := by
      have ha : raw41622step2 = raw41622step1 := by apply Matrix.ext; unfold raw41622step2 raw41622step1; decide +kernel
      have hl : raw41622step1Labels = labelEmbedding1 ∘ raw41622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41622step1 raw41622step1Labels raw41622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

theorem canonical41623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41623 raw41623Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw41623 raw41623Labels = mixedMoment B raw41623step0 raw41623step0Labels := by
      have hz : ∀ j, raw41623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41623step0 = (fun i j => raw41623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41623step0 raw41623; decide +kernel
      have hl : raw41623step0Labels = raw41623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41623 raw41623Labels permutation346 hz
    mixedMoment B raw41623step0 raw41623step0Labels = mixedMoment B raw41623step1 raw41623step1Labels := by
      have ha : raw41623step1 = (fun i j => raw41623step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41623step1 raw41623step0; decide +kernel
      have hl : raw41623step1Labels = raw41623step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41623step0 raw41623step0Labels permutation144 permutation4
    mixedMoment B raw41623step1 raw41623step1Labels = mixedMoment B raw41623step2 raw41623step2Labels := by
      have ha : raw41623step2 = raw41623step1 := by apply Matrix.ext; unfold raw41623step2 raw41623step1; decide +kernel
      have hl : raw41623step1Labels = labelEmbedding10 ∘ raw41623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41623step1 raw41623step1Labels raw41623step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

theorem canonical41624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41624 raw41624Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw41624 raw41624Labels = mixedMoment B raw41624step0 raw41624step0Labels := by
      have hz : ∀ j, raw41624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41624step0 = (fun i j => raw41624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41624step0 raw41624; decide +kernel
      have hl : raw41624step0Labels = raw41624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41624 raw41624Labels permutation346 hz
    mixedMoment B raw41624step0 raw41624step0Labels = mixedMoment B raw41624step1 raw41624step1Labels := by
      have ha : raw41624step1 = (fun i j => raw41624step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41624step1 raw41624step0; decide +kernel
      have hl : raw41624step1Labels = raw41624step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41624step0 raw41624step0Labels permutation37 permutation2
    mixedMoment B raw41624step1 raw41624step1Labels = mixedMoment B raw41624step2 raw41624step2Labels := by
      have ha : raw41624step2 = raw41624step1 := by apply Matrix.ext; unfold raw41624step2 raw41624step1; decide +kernel
      have hl : raw41624step1Labels = labelEmbedding1 ∘ raw41624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41624step1 raw41624step1Labels raw41624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical41625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41625 raw41625Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw41625 raw41625Labels = mixedMoment B raw41625step0 raw41625step0Labels := by
      have hz : ∀ j, raw41625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41625step0 = (fun i j => raw41625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41625step0 raw41625; decide +kernel
      have hl : raw41625step0Labels = raw41625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41625 raw41625Labels permutation346 hz
    mixedMoment B raw41625step0 raw41625step0Labels = mixedMoment B raw41625step1 raw41625step1Labels := by
      have ha : raw41625step1 = (fun i j => raw41625step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41625step1 raw41625step0; decide +kernel
      have hl : raw41625step1Labels = raw41625step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41625step0 raw41625step0Labels permutation37 permutation2
    mixedMoment B raw41625step1 raw41625step1Labels = mixedMoment B raw41625step2 raw41625step2Labels := by
      have ha : raw41625step2 = raw41625step1 := by apply Matrix.ext; unfold raw41625step2 raw41625step1; decide +kernel
      have hl : raw41625step1Labels = labelEmbedding8 ∘ raw41625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41625step1 raw41625step1Labels raw41625step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical41626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41626 raw41626Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw41626 raw41626Labels = mixedMoment B raw41626step0 raw41626step0Labels := by
      have hz : ∀ j, raw41626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41626step0 = (fun i j => raw41626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41626step0 raw41626; decide +kernel
      have hl : raw41626step0Labels = raw41626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41626 raw41626Labels permutation346 hz
    mixedMoment B raw41626step0 raw41626step0Labels = mixedMoment B raw41626step1 raw41626step1Labels := by
      have ha : raw41626step1 = raw41626step0 := by apply Matrix.ext; unfold raw41626step1 raw41626step0; decide +kernel
      have hl : raw41626step0Labels = labelEmbedding1 ∘ raw41626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41626step0 raw41626step0Labels raw41626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

theorem canonical41627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41627 raw41627Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw41627 raw41627Labels = mixedMoment B raw41627step0 raw41627step0Labels := by
      have hz : ∀ j, raw41627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41627step0 = (fun i j => raw41627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41627step0 raw41627; decide +kernel
      have hl : raw41627step0Labels = raw41627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41627 raw41627Labels permutation346 hz
    mixedMoment B raw41627step0 raw41627step0Labels = mixedMoment B raw41627step1 raw41627step1Labels := by
      have ha : raw41627step1 = raw41627step0 := by apply Matrix.ext; unfold raw41627step1 raw41627step0; decide +kernel
      have hl : raw41627step0Labels = labelEmbedding8 ∘ raw41627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41627step0 raw41627step0Labels raw41627step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical41628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41628 raw41628Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw41628 raw41628Labels = mixedMoment B raw41628step0 raw41628step0Labels := by
      have ha : raw41628step0 = (fun i j => raw41628 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41628step0 raw41628; decide +kernel
      have hl : raw41628step0Labels = raw41628Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41628 raw41628Labels permutation182 permutation2
    mixedMoment B raw41628step0 raw41628step0Labels = mixedMoment B raw41628step1 raw41628step1Labels := by
      have ha : raw41628step1 = raw41628step0 := by apply Matrix.ext; unfold raw41628step1 raw41628step0; decide +kernel
      have hl : raw41628step0Labels = labelEmbedding1 ∘ raw41628step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41628step0 raw41628step0Labels raw41628step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical41629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41629 raw41629Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw41629 raw41629Labels = mixedMoment B raw41629step0 raw41629step0Labels := by
      have ha : raw41629step0 = (fun i j => raw41629 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41629step0 raw41629; decide +kernel
      have hl : raw41629step0Labels = raw41629Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41629 raw41629Labels permutation182 permutation2
    mixedMoment B raw41629step0 raw41629step0Labels = mixedMoment B raw41629step1 raw41629step1Labels := by
      have ha : raw41629step1 = raw41629step0 := by apply Matrix.ext; unfold raw41629step1 raw41629step0; decide +kernel
      have hl : raw41629step0Labels = labelEmbedding8 ∘ raw41629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41629step0 raw41629step0Labels raw41629step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

theorem canonical41630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41630 raw41630Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw41630 raw41630Labels = mixedMoment B raw41630step0 raw41630step0Labels := by
      have ha : raw41630step0 = (fun i j => raw41630 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41630step0 raw41630; decide +kernel
      have hl : raw41630step0Labels = raw41630Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41630 raw41630Labels permutation180 permutation2
    mixedMoment B raw41630step0 raw41630step0Labels = mixedMoment B raw41630step1 raw41630step1Labels := by
      have ha : raw41630step1 = raw41630step0 := by apply Matrix.ext; unfold raw41630step1 raw41630step0; decide +kernel
      have hl : raw41630step0Labels = labelEmbedding1 ∘ raw41630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41630step0 raw41630step0Labels raw41630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

theorem canonical41631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41631 raw41631Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw41631 raw41631Labels = mixedMoment B raw41631step0 raw41631step0Labels := by
      have ha : raw41631step0 = (fun i j => raw41631 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41631step0 raw41631; decide +kernel
      have hl : raw41631step0Labels = raw41631Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41631 raw41631Labels permutation180 permutation2
    mixedMoment B raw41631step0 raw41631step0Labels = mixedMoment B raw41631step1 raw41631step1Labels := by
      have ha : raw41631step1 = raw41631step0 := by apply Matrix.ext; unfold raw41631step1 raw41631step0; decide +kernel
      have hl : raw41631step0Labels = labelEmbedding8 ∘ raw41631step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41631step0 raw41631step0Labels raw41631step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

theorem canonical41632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41632 raw41632Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw41632 raw41632Labels = mixedMoment B raw41632step0 raw41632step0Labels := by
      have ha : raw41632step0 = (fun i j => raw41632 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41632step0 raw41632; decide +kernel
      have hl : raw41632step0Labels = raw41632Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41632 raw41632Labels permutation179 permutation2
    mixedMoment B raw41632step0 raw41632step0Labels = mixedMoment B raw41632step1 raw41632step1Labels := by
      have ha : raw41632step1 = raw41632step0 := by apply Matrix.ext; unfold raw41632step1 raw41632step0; decide +kernel
      have hl : raw41632step0Labels = labelEmbedding1 ∘ raw41632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41632step0 raw41632step0Labels raw41632step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical41633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41633 raw41633Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw41633 raw41633Labels = mixedMoment B raw41633step0 raw41633step0Labels := by
      have ha : raw41633step0 = (fun i j => raw41633 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41633step0 raw41633; decide +kernel
      have hl : raw41633step0Labels = raw41633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41633 raw41633Labels permutation179 permutation2
    mixedMoment B raw41633step0 raw41633step0Labels = mixedMoment B raw41633step1 raw41633step1Labels := by
      have ha : raw41633step1 = raw41633step0 := by apply Matrix.ext; unfold raw41633step1 raw41633step0; decide +kernel
      have hl : raw41633step0Labels = labelEmbedding8 ∘ raw41633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41633step0 raw41633step0Labels raw41633step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical41634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41634 raw41634Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw41634 raw41634Labels = mixedMoment B raw41634step0 raw41634step0Labels := by
      have ha : raw41634step0 = (fun i j => raw41634 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41634step0 raw41634; decide +kernel
      have hl : raw41634step0Labels = raw41634Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41634 raw41634Labels permutation180 permutation2
    mixedMoment B raw41634step0 raw41634step0Labels = mixedMoment B raw41634step1 raw41634step1Labels := by
      have ha : raw41634step1 = raw41634step0 := by apply Matrix.ext; unfold raw41634step1 raw41634step0; decide +kernel
      have hl : raw41634step0Labels = labelEmbedding1 ∘ raw41634step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41634step0 raw41634step0Labels raw41634step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical41635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41635 raw41635Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw41635 raw41635Labels = mixedMoment B raw41635step0 raw41635step0Labels := by
      have ha : raw41635step0 = (fun i j => raw41635 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41635step0 raw41635; decide +kernel
      have hl : raw41635step0Labels = raw41635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41635 raw41635Labels permutation180 permutation2
    mixedMoment B raw41635step0 raw41635step0Labels = mixedMoment B raw41635step1 raw41635step1Labels := by
      have ha : raw41635step1 = raw41635step0 := by apply Matrix.ext; unfold raw41635step1 raw41635step0; decide +kernel
      have hl : raw41635step0Labels = labelEmbedding8 ∘ raw41635step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41635step0 raw41635step0Labels raw41635step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical41636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41636 raw41636Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw41636 raw41636Labels = mixedMoment B raw41636step0 raw41636step0Labels := by
      have hz : ∀ j, raw41636 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41636step0 = (fun i j => raw41636 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41636step0 raw41636; decide +kernel
      have hl : raw41636step0Labels = raw41636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41636 raw41636Labels permutation520 hz
    mixedMoment B raw41636step0 raw41636step0Labels = mixedMoment B raw41636step1 raw41636step1Labels := by
      have hz : ∀ j, raw41636step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41636step1 = (fun i j => raw41636step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41636step1 raw41636step0; decide +kernel
      have hl : raw41636step1Labels = raw41636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41636step0 raw41636step0Labels permutation104 hz
    mixedMoment B raw41636step1 raw41636step1Labels = mixedMoment B raw41636step2 raw41636step2Labels := by
      have ha : raw41636step2 = raw41636step1 := by apply Matrix.ext; unfold raw41636step2 raw41636step1; decide +kernel
      have hl : raw41636step1Labels = labelEmbedding1 ∘ raw41636step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41636step1 raw41636step1Labels raw41636step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

theorem canonical41637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41637 raw41637Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw41637 raw41637Labels = mixedMoment B raw41637step0 raw41637step0Labels := by
      have hz : ∀ j, raw41637 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41637step0 = (fun i j => raw41637 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41637step0 raw41637; decide +kernel
      have hl : raw41637step0Labels = raw41637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41637 raw41637Labels permutation520 hz
    mixedMoment B raw41637step0 raw41637step0Labels = mixedMoment B raw41637step1 raw41637step1Labels := by
      have hz : ∀ j, raw41637step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41637step1 = (fun i j => raw41637step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41637step1 raw41637step0; decide +kernel
      have hl : raw41637step1Labels = raw41637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41637step0 raw41637step0Labels permutation104 hz
    mixedMoment B raw41637step1 raw41637step1Labels = mixedMoment B raw41637step2 raw41637step2Labels := by
      have ha : raw41637step2 = (fun i j => raw41637step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41637step2 raw41637step1; decide +kernel
      have hl : raw41637step2Labels = raw41637step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41637step1 raw41637step1Labels permutation29 permutation3
    mixedMoment B raw41637step2 raw41637step2Labels = mixedMoment B raw41637step3 raw41637step3Labels := by
      have ha : raw41637step3 = -raw41637step2 := by apply Matrix.ext; change ∀ i j, raw41637step3 i j = -(raw41637step2 i j); unfold raw41637step3 raw41637step2; decide +kernel
      have hl : raw41637step3Labels = raw41637step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41637step3 raw41637step3Labels = mixedMoment B raw41637step4 raw41637step4Labels := by
      have ha : raw41637step4 = raw41637step3 := by apply Matrix.ext; unfold raw41637step4 raw41637step3; decide +kernel
      have hl : raw41637step3Labels = labelEmbedding7 ∘ raw41637step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41637step3 raw41637step3Labels raw41637step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

theorem canonical41638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41638 raw41638Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw41638 raw41638Labels = mixedMoment B raw41638step0 raw41638step0Labels := by
      have hz : ∀ j, raw41638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41638step0 = (fun i j => raw41638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41638step0 raw41638; decide +kernel
      have hl : raw41638step0Labels = raw41638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41638 raw41638Labels permutation434 hz
    mixedMoment B raw41638step0 raw41638step0Labels = mixedMoment B raw41638step1 raw41638step1Labels := by
      have ha : raw41638step1 = raw41638step0 := by apply Matrix.ext; unfold raw41638step1 raw41638step0; decide +kernel
      have hl : raw41638step0Labels = labelEmbedding1 ∘ raw41638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41638step0 raw41638step0Labels raw41638step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

theorem canonical41639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41639 raw41639Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41639 raw41639Labels = mixedMoment B raw41639step0 raw41639step0Labels := by
      have hz : ∀ j, raw41639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41639step0 = (fun i j => raw41639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41639step0 raw41639; decide +kernel
      have hl : raw41639step0Labels = raw41639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41639 raw41639Labels permutation434 hz
    mixedMoment B raw41639step0 raw41639step0Labels = mixedMoment B raw41639step1 raw41639step1Labels := by
      have ha : raw41639step1 = (fun i j => raw41639step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41639step1 raw41639step0; decide +kernel
      have hl : raw41639step1Labels = raw41639step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41639step0 raw41639step0Labels permutation149 permutation5
    mixedMoment B raw41639step1 raw41639step1Labels = mixedMoment B raw41639step2 raw41639step2Labels := by
      have ha : raw41639step2 = raw41639step1 := by apply Matrix.ext; unfold raw41639step2 raw41639step1; decide +kernel
      have hl : raw41639step1Labels = labelEmbedding9 ∘ raw41639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41639step1 raw41639step1Labels raw41639step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

theorem canonical41640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41640 raw41640Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw41640 raw41640Labels = mixedMoment B raw41640step0 raw41640step0Labels := by
      have hz : ∀ j, raw41640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41640step0 = (fun i j => raw41640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41640step0 raw41640; decide +kernel
      have hl : raw41640step0Labels = raw41640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41640 raw41640Labels permutation434 hz
    mixedMoment B raw41640step0 raw41640step0Labels = mixedMoment B raw41640step1 raw41640step1Labels := by
      have ha : raw41640step1 = raw41640step0 := by apply Matrix.ext; unfold raw41640step1 raw41640step0; decide +kernel
      have hl : raw41640step0Labels = labelEmbedding1 ∘ raw41640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41640step0 raw41640step0Labels raw41640step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

theorem canonical41641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41641 raw41641Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw41641 raw41641Labels = mixedMoment B raw41641step0 raw41641step0Labels := by
      have hz : ∀ j, raw41641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41641step0 = (fun i j => raw41641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41641step0 raw41641; decide +kernel
      have hl : raw41641step0Labels = raw41641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41641 raw41641Labels permutation434 hz
    mixedMoment B raw41641step0 raw41641step0Labels = mixedMoment B raw41641step1 raw41641step1Labels := by
      have ha : raw41641step1 = raw41641step0 := by apply Matrix.ext; unfold raw41641step1 raw41641step0; decide +kernel
      have hl : raw41641step0Labels = labelEmbedding8 ∘ raw41641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41641step0 raw41641step0Labels raw41641step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

theorem canonical41642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41642 raw41642Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw41642 raw41642Labels = mixedMoment B raw41642step0 raw41642step0Labels := by
      have hz : ∀ j, raw41642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41642step0 = (fun i j => raw41642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41642step0 raw41642; decide +kernel
      have hl : raw41642step0Labels = raw41642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41642 raw41642Labels permutation434 hz
    mixedMoment B raw41642step0 raw41642step0Labels = mixedMoment B raw41642step1 raw41642step1Labels := by
      have ha : raw41642step1 = raw41642step0 := by apply Matrix.ext; unfold raw41642step1 raw41642step0; decide +kernel
      have hl : raw41642step0Labels = labelEmbedding1 ∘ raw41642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41642step0 raw41642step0Labels raw41642step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

theorem canonical41643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41643 raw41643Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw41643 raw41643Labels = mixedMoment B raw41643step0 raw41643step0Labels := by
      have hz : ∀ j, raw41643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41643step0 = (fun i j => raw41643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41643step0 raw41643; decide +kernel
      have hl : raw41643step0Labels = raw41643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41643 raw41643Labels permutation434 hz
    mixedMoment B raw41643step0 raw41643step0Labels = mixedMoment B raw41643step1 raw41643step1Labels := by
      have ha : raw41643step1 = raw41643step0 := by apply Matrix.ext; unfold raw41643step1 raw41643step0; decide +kernel
      have hl : raw41643step0Labels = labelEmbedding8 ∘ raw41643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41643step0 raw41643step0Labels raw41643step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical41644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41644 raw41644Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw41644 raw41644Labels = mixedMoment B raw41644step0 raw41644step0Labels := by
      have hz : ∀ j, raw41644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41644step0 = (fun i j => raw41644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41644step0 raw41644; decide +kernel
      have hl : raw41644step0Labels = raw41644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41644 raw41644Labels permutation434 hz
    mixedMoment B raw41644step0 raw41644step0Labels = mixedMoment B raw41644step1 raw41644step1Labels := by
      have ha : raw41644step1 = raw41644step0 := by apply Matrix.ext; unfold raw41644step1 raw41644step0; decide +kernel
      have hl : raw41644step0Labels = labelEmbedding1 ∘ raw41644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41644step0 raw41644step0Labels raw41644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

theorem canonical41645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41645 raw41645Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw41645 raw41645Labels = mixedMoment B raw41645step0 raw41645step0Labels := by
      have hz : ∀ j, raw41645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41645step0 = (fun i j => raw41645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41645step0 raw41645; decide +kernel
      have hl : raw41645step0Labels = raw41645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41645 raw41645Labels permutation434 hz
    mixedMoment B raw41645step0 raw41645step0Labels = mixedMoment B raw41645step1 raw41645step1Labels := by
      have ha : raw41645step1 = raw41645step0 := by apply Matrix.ext; unfold raw41645step1 raw41645step0; decide +kernel
      have hl : raw41645step0Labels = labelEmbedding8 ∘ raw41645step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41645step0 raw41645step0Labels raw41645step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

theorem canonical41646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41646 raw41646Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw41646 raw41646Labels = mixedMoment B raw41646step0 raw41646step0Labels := by
      have ha : raw41646step0 = (fun i j => raw41646 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41646step0 raw41646; decide +kernel
      have hl : raw41646step0Labels = raw41646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41646 raw41646Labels permutation200 permutation2
    mixedMoment B raw41646step0 raw41646step0Labels = mixedMoment B raw41646step1 raw41646step1Labels := by
      have ha : raw41646step1 = raw41646step0 := by apply Matrix.ext; unfold raw41646step1 raw41646step0; decide +kernel
      have hl : raw41646step0Labels = labelEmbedding1 ∘ raw41646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41646step0 raw41646step0Labels raw41646step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

theorem canonical41647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41647 raw41647Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw41647 raw41647Labels = mixedMoment B raw41647step0 raw41647step0Labels := by
      have ha : raw41647step0 = (fun i j => raw41647 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41647step0 raw41647; decide +kernel
      have hl : raw41647step0Labels = raw41647Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41647 raw41647Labels permutation200 permutation2
    mixedMoment B raw41647step0 raw41647step0Labels = mixedMoment B raw41647step1 raw41647step1Labels := by
      have ha : raw41647step1 = raw41647step0 := by apply Matrix.ext; unfold raw41647step1 raw41647step0; decide +kernel
      have hl : raw41647step0Labels = labelEmbedding8 ∘ raw41647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41647step0 raw41647step0Labels raw41647step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

theorem canonical41648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41648 raw41648Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw41648 raw41648Labels = mixedMoment B raw41648step0 raw41648step0Labels := by
      have ha : raw41648step0 = (fun i j => raw41648 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41648step0 raw41648; decide +kernel
      have hl : raw41648step0Labels = raw41648Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41648 raw41648Labels permutation200 permutation2
    mixedMoment B raw41648step0 raw41648step0Labels = mixedMoment B raw41648step1 raw41648step1Labels := by
      have ha : raw41648step1 = raw41648step0 := by apply Matrix.ext; unfold raw41648step1 raw41648step0; decide +kernel
      have hl : raw41648step0Labels = labelEmbedding1 ∘ raw41648step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41648step0 raw41648step0Labels raw41648step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

theorem canonical41649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41649 raw41649Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw41649 raw41649Labels = mixedMoment B raw41649step0 raw41649step0Labels := by
      have ha : raw41649step0 = (fun i j => raw41649 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41649step0 raw41649; decide +kernel
      have hl : raw41649step0Labels = raw41649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41649 raw41649Labels permutation200 permutation2
    mixedMoment B raw41649step0 raw41649step0Labels = mixedMoment B raw41649step1 raw41649step1Labels := by
      have ha : raw41649step1 = raw41649step0 := by apply Matrix.ext; unfold raw41649step1 raw41649step0; decide +kernel
      have hl : raw41649step0Labels = labelEmbedding8 ∘ raw41649step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41649step0 raw41649step0Labels raw41649step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

theorem canonical41650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41650 raw41650Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw41650 raw41650Labels = mixedMoment B raw41650step0 raw41650step0Labels := by
      have ha : raw41650step0 = (fun i j => raw41650 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41650step0 raw41650; decide +kernel
      have hl : raw41650step0Labels = raw41650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41650 raw41650Labels permutation200 permutation2
    mixedMoment B raw41650step0 raw41650step0Labels = mixedMoment B raw41650step1 raw41650step1Labels := by
      have ha : raw41650step1 = raw41650step0 := by apply Matrix.ext; unfold raw41650step1 raw41650step0; decide +kernel
      have hl : raw41650step0Labels = labelEmbedding1 ∘ raw41650step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41650step0 raw41650step0Labels raw41650step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

theorem canonical41651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41651 raw41651Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw41651 raw41651Labels = mixedMoment B raw41651step0 raw41651step0Labels := by
      have ha : raw41651step0 = (fun i j => raw41651 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41651step0 raw41651; decide +kernel
      have hl : raw41651step0Labels = raw41651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41651 raw41651Labels permutation200 permutation2
    mixedMoment B raw41651step0 raw41651step0Labels = mixedMoment B raw41651step1 raw41651step1Labels := by
      have ha : raw41651step1 = raw41651step0 := by apply Matrix.ext; unfold raw41651step1 raw41651step0; decide +kernel
      have hl : raw41651step0Labels = labelEmbedding8 ∘ raw41651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41651step0 raw41651step0Labels raw41651step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

theorem canonical41652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41652 raw41652Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw41652 raw41652Labels = mixedMoment B raw41652step0 raw41652step0Labels := by
      have ha : raw41652step0 = (fun i j => raw41652 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41652step0 raw41652; decide +kernel
      have hl : raw41652step0Labels = raw41652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41652 raw41652Labels permutation156 permutation2
    mixedMoment B raw41652step0 raw41652step0Labels = mixedMoment B raw41652step1 raw41652step1Labels := by
      have ha : raw41652step1 = raw41652step0 := by apply Matrix.ext; unfold raw41652step1 raw41652step0; decide +kernel
      have hl : raw41652step0Labels = labelEmbedding1 ∘ raw41652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41652step0 raw41652step0Labels raw41652step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2747 node2747Labels := by rfl

theorem canonical41653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41653 raw41653Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw41653 raw41653Labels = mixedMoment B raw41653step0 raw41653step0Labels := by
      have ha : raw41653step0 = (fun i j => raw41653 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41653step0 raw41653; decide +kernel
      have hl : raw41653step0Labels = raw41653Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41653 raw41653Labels permutation156 permutation2
    mixedMoment B raw41653step0 raw41653step0Labels = mixedMoment B raw41653step1 raw41653step1Labels := by
      have ha : raw41653step1 = raw41653step0 := by apply Matrix.ext; unfold raw41653step1 raw41653step0; decide +kernel
      have hl : raw41653step0Labels = labelEmbedding8 ∘ raw41653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41653step0 raw41653step0Labels raw41653step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

theorem canonical41654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41654 raw41654Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw41654 raw41654Labels = mixedMoment B raw41654step0 raw41654step0Labels := by
      have ha : raw41654step0 = (fun i j => raw41654 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41654step0 raw41654; decide +kernel
      have hl : raw41654step0Labels = raw41654Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41654 raw41654Labels permutation157 permutation2
    mixedMoment B raw41654step0 raw41654step0Labels = mixedMoment B raw41654step1 raw41654step1Labels := by
      have ha : raw41654step1 = raw41654step0 := by apply Matrix.ext; unfold raw41654step1 raw41654step0; decide +kernel
      have hl : raw41654step0Labels = labelEmbedding1 ∘ raw41654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41654step0 raw41654step0Labels raw41654step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

theorem canonical41655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41655 raw41655Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw41655 raw41655Labels = mixedMoment B raw41655step0 raw41655step0Labels := by
      have ha : raw41655step0 = (fun i j => raw41655 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41655step0 raw41655; decide +kernel
      have hl : raw41655step0Labels = raw41655Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41655 raw41655Labels permutation157 permutation2
    mixedMoment B raw41655step0 raw41655step0Labels = mixedMoment B raw41655step1 raw41655step1Labels := by
      have ha : raw41655step1 = raw41655step0 := by apply Matrix.ext; unfold raw41655step1 raw41655step0; decide +kernel
      have hl : raw41655step0Labels = labelEmbedding8 ∘ raw41655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41655step0 raw41655step0Labels raw41655step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

theorem canonical41656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41656 raw41656Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41656 raw41656Labels = mixedMoment B raw41656step0 raw41656step0Labels := by
      have hz : ∀ j, raw41656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41656step0 = (fun i j => raw41656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41656step0 raw41656; decide +kernel
      have hl : raw41656step0Labels = raw41656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41656 raw41656Labels permutation434 hz
    mixedMoment B raw41656step0 raw41656step0Labels = mixedMoment B raw41656step1 raw41656step1Labels := by
      have hz : ∀ j, raw41656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41656step1 = (fun i j => raw41656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41656step1 raw41656step0; decide +kernel
      have hl : raw41656step1Labels = raw41656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41656step0 raw41656step0Labels permutation80 hz
    mixedMoment B raw41656step1 raw41656step1Labels = mixedMoment B raw41656step2 raw41656step2Labels := by
      have ha : raw41656step2 = raw41656step1 := by apply Matrix.ext; unfold raw41656step2 raw41656step1; decide +kernel
      have hl : raw41656step1Labels = labelEmbedding1 ∘ raw41656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41656step1 raw41656step1Labels raw41656step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

theorem canonical41657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41657 raw41657Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41657 raw41657Labels = mixedMoment B raw41657step0 raw41657step0Labels := by
      have hz : ∀ j, raw41657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41657step0 = (fun i j => raw41657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41657step0 raw41657; decide +kernel
      have hl : raw41657step0Labels = raw41657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41657 raw41657Labels permutation434 hz
    mixedMoment B raw41657step0 raw41657step0Labels = mixedMoment B raw41657step1 raw41657step1Labels := by
      have hz : ∀ j, raw41657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41657step1 = (fun i j => raw41657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41657step1 raw41657step0; decide +kernel
      have hl : raw41657step1Labels = raw41657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41657step0 raw41657step0Labels permutation80 hz
    mixedMoment B raw41657step1 raw41657step1Labels = mixedMoment B raw41657step2 raw41657step2Labels := by
      have ha : raw41657step2 = raw41657step1 := by apply Matrix.ext; unfold raw41657step2 raw41657step1; decide +kernel
      have hl : raw41657step1Labels = labelEmbedding8 ∘ raw41657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41657step1 raw41657step1Labels raw41657step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

theorem canonical41658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41658 raw41658Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw41658 raw41658Labels = mixedMoment B raw41658step0 raw41658step0Labels := by
      have hz : ∀ j, raw41658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41658step0 = (fun i j => raw41658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41658step0 raw41658; decide +kernel
      have hl : raw41658step0Labels = raw41658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41658 raw41658Labels permutation434 hz
    mixedMoment B raw41658step0 raw41658step0Labels = mixedMoment B raw41658step1 raw41658step1Labels := by
      have hz : ∀ j, raw41658step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41658step1 = (fun i j => raw41658step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41658step1 raw41658step0; decide +kernel
      have hl : raw41658step1Labels = raw41658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41658step0 raw41658step0Labels permutation80 hz
    mixedMoment B raw41658step1 raw41658step1Labels = mixedMoment B raw41658step2 raw41658step2Labels := by
      have ha : raw41658step2 = raw41658step1 := by apply Matrix.ext; unfold raw41658step2 raw41658step1; decide +kernel
      have hl : raw41658step1Labels = labelEmbedding1 ∘ raw41658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41658step1 raw41658step1Labels raw41658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

theorem canonical41659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41659 raw41659Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw41659 raw41659Labels = mixedMoment B raw41659step0 raw41659step0Labels := by
      have hz : ∀ j, raw41659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41659step0 = (fun i j => raw41659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41659step0 raw41659; decide +kernel
      have hl : raw41659step0Labels = raw41659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41659 raw41659Labels permutation434 hz
    mixedMoment B raw41659step0 raw41659step0Labels = mixedMoment B raw41659step1 raw41659step1Labels := by
      have hz : ∀ j, raw41659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41659step1 = (fun i j => raw41659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41659step1 raw41659step0; decide +kernel
      have hl : raw41659step1Labels = raw41659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41659step0 raw41659step0Labels permutation80 hz
    mixedMoment B raw41659step1 raw41659step1Labels = mixedMoment B raw41659step2 raw41659step2Labels := by
      have ha : raw41659step2 = (fun i j => raw41659step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41659step2 raw41659step1; decide +kernel
      have hl : raw41659step2Labels = raw41659step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41659step1 raw41659step1Labels permutation29 permutation7
    mixedMoment B raw41659step2 raw41659step2Labels = mixedMoment B raw41659step3 raw41659step3Labels := by
      have ha : raw41659step3 = raw41659step2 := by apply Matrix.ext; unfold raw41659step3 raw41659step2; decide +kernel
      have hl : raw41659step2Labels = labelEmbedding6 ∘ raw41659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41659step2 raw41659step2Labels raw41659step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

theorem canonical41660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41660 raw41660Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw41660 raw41660Labels = mixedMoment B raw41660step0 raw41660step0Labels := by
      have hz : ∀ j, raw41660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41660step0 = (fun i j => raw41660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41660step0 raw41660; decide +kernel
      have hl : raw41660step0Labels = raw41660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41660 raw41660Labels permutation346 hz
    mixedMoment B raw41660step0 raw41660step0Labels = mixedMoment B raw41660step1 raw41660step1Labels := by
      have ha : raw41660step1 = (fun i j => raw41660step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41660step1 raw41660step0; decide +kernel
      have hl : raw41660step1Labels = raw41660step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41660step0 raw41660step0Labels permutation38 permutation2
    mixedMoment B raw41660step1 raw41660step1Labels = mixedMoment B raw41660step2 raw41660step2Labels := by
      have ha : raw41660step2 = raw41660step1 := by apply Matrix.ext; unfold raw41660step2 raw41660step1; decide +kernel
      have hl : raw41660step1Labels = labelEmbedding1 ∘ raw41660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41660step1 raw41660step1Labels raw41660step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

theorem canonical41661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41661 raw41661Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw41661 raw41661Labels = mixedMoment B raw41661step0 raw41661step0Labels := by
      have hz : ∀ j, raw41661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41661step0 = (fun i j => raw41661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41661step0 raw41661; decide +kernel
      have hl : raw41661step0Labels = raw41661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41661 raw41661Labels permutation346 hz
    mixedMoment B raw41661step0 raw41661step0Labels = mixedMoment B raw41661step1 raw41661step1Labels := by
      have ha : raw41661step1 = (fun i j => raw41661step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41661step1 raw41661step0; decide +kernel
      have hl : raw41661step1Labels = raw41661step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41661step0 raw41661step0Labels permutation38 permutation2
    mixedMoment B raw41661step1 raw41661step1Labels = mixedMoment B raw41661step2 raw41661step2Labels := by
      have ha : raw41661step2 = raw41661step1 := by apply Matrix.ext; unfold raw41661step2 raw41661step1; decide +kernel
      have hl : raw41661step1Labels = labelEmbedding8 ∘ raw41661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41661step1 raw41661step1Labels raw41661step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

theorem canonical41662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41662 raw41662Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw41662 raw41662Labels = mixedMoment B raw41662step0 raw41662step0Labels := by
      have hz : ∀ j, raw41662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41662step0 = (fun i j => raw41662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41662step0 raw41662; decide +kernel
      have hl : raw41662step0Labels = raw41662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41662 raw41662Labels permutation346 hz
    mixedMoment B raw41662step0 raw41662step0Labels = mixedMoment B raw41662step1 raw41662step1Labels := by
      have ha : raw41662step1 = (fun i j => raw41662step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41662step1 raw41662step0; decide +kernel
      have hl : raw41662step1Labels = raw41662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41662step0 raw41662step0Labels permutation38 permutation2
    mixedMoment B raw41662step1 raw41662step1Labels = mixedMoment B raw41662step2 raw41662step2Labels := by
      have ha : raw41662step2 = raw41662step1 := by apply Matrix.ext; unfold raw41662step2 raw41662step1; decide +kernel
      have hl : raw41662step1Labels = labelEmbedding1 ∘ raw41662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41662step1 raw41662step1Labels raw41662step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

theorem canonical41663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41663 raw41663Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw41663 raw41663Labels = mixedMoment B raw41663step0 raw41663step0Labels := by
      have hz : ∀ j, raw41663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41663step0 = (fun i j => raw41663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41663step0 raw41663; decide +kernel
      have hl : raw41663step0Labels = raw41663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41663 raw41663Labels permutation346 hz
    mixedMoment B raw41663step0 raw41663step0Labels = mixedMoment B raw41663step1 raw41663step1Labels := by
      have ha : raw41663step1 = (fun i j => raw41663step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41663step1 raw41663step0; decide +kernel
      have hl : raw41663step1Labels = raw41663step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41663step0 raw41663step0Labels permutation139 permutation7
    mixedMoment B raw41663step1 raw41663step1Labels = mixedMoment B raw41663step2 raw41663step2Labels := by
      have ha : raw41663step2 = raw41663step1 := by apply Matrix.ext; unfold raw41663step2 raw41663step1; decide +kernel
      have hl : raw41663step1Labels = labelEmbedding6 ∘ raw41663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41663step1 raw41663step1Labels raw41663step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2144 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2144) =
      Integer.Sparse.eval keyMomentRow2144 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3051) := by
    have ha : gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge = raw41600 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41600Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41600 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge = raw41601 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41601Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41601 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2144).leftCharge (GramAssembly.key 2144).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2144, Integer.Sparse.eval]
  ring

theorem keyMoment2145 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2145) =
      Integer.Sparse.eval keyMomentRow2145 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3074) := by
    have ha : gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge = raw41602 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41602Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41602 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge = raw41603 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41603Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41603 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2145).leftCharge (GramAssembly.key 2145).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2145, Integer.Sparse.eval]
  ring

theorem keyMoment2146 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2146) =
      Integer.Sparse.eval keyMomentRow2146 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2778) := by
    have ha : gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge = raw41604 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41604Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41604 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4899) := by
    have ha : gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge = raw41605 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41605Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41605 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2146).leftCharge (GramAssembly.key 2146).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2146, Integer.Sparse.eval]
  ring

theorem keyMoment2147 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2147) =
      Integer.Sparse.eval keyMomentRow2147 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2777) := by
    have ha : gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge = raw41606 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41606Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41606 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5276) := by
    have ha : gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge = raw41607 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41607Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41607 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2147).leftCharge (GramAssembly.key 2147).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2147, Integer.Sparse.eval]
  ring

theorem keyMoment2148 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2148) =
      Integer.Sparse.eval keyMomentRow2148 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2776) := by
    have ha : gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge = raw41608 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41608Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41608 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5302) := by
    have ha : gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge = raw41609 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41609Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41609 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2148).leftCharge (GramAssembly.key 2148).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2148, Integer.Sparse.eval]
  ring

theorem keyMoment2149 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2149) =
      Integer.Sparse.eval keyMomentRow2149 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge = raw41610 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41610Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41610 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge = raw41611 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41611Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41611 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2149).leftCharge (GramAssembly.key 2149).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2149, Integer.Sparse.eval]
  ring

theorem keyMoment2150 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2150) =
      Integer.Sparse.eval keyMomentRow2150 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2771) := by
    have ha : gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge = raw41612 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41612Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41612 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5297) := by
    have ha : gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge = raw41613 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41613Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41613 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2150).leftCharge (GramAssembly.key 2150).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2150, Integer.Sparse.eval]
  ring

theorem keyMoment2151 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2151) =
      Integer.Sparse.eval keyMomentRow2151 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge = raw41614 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41614Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41614 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge = raw41615 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41615Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41615 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2151).leftCharge (GramAssembly.key 2151).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2151, Integer.Sparse.eval]
  ring

theorem keyMoment2152 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2152) =
      Integer.Sparse.eval keyMomentRow2152 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge = raw41616 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41616Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41616 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge = raw41617 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41617Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41617 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2152).leftCharge (GramAssembly.key 2152).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2152, Integer.Sparse.eval]
  ring

theorem keyMoment2153 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2153) =
      Integer.Sparse.eval keyMomentRow2153 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2729) := by
    have ha : gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge = raw41618 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41618Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41618 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5264) := by
    have ha : gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge = raw41619 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41619Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41619 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2153).leftCharge (GramAssembly.key 2153).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2153, Integer.Sparse.eval]
  ring

theorem keyMoment2154 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2154) =
      Integer.Sparse.eval keyMomentRow2154 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2677) := by
    have ha : gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge = raw41620 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41620Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41620 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5232) := by
    have ha : gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge = raw41621 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41621Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41621 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2154).leftCharge (GramAssembly.key 2154).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2154, Integer.Sparse.eval]
  ring

theorem keyMoment2155 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2155) =
      Integer.Sparse.eval keyMomentRow2155 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2748) := by
    have ha : gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge = raw41622 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41622Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41622 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5279) := by
    have ha : gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge = raw41623 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41623Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41623 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2155).leftCharge (GramAssembly.key 2155).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2155, Integer.Sparse.eval]
  ring

theorem keyMoment2156 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2156) =
      Integer.Sparse.eval keyMomentRow2156 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge = raw41624 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41624Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41624 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge = raw41625 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41625Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41625 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2156).leftCharge (GramAssembly.key 2156).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2156, Integer.Sparse.eval]
  ring

theorem keyMoment2157 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2157) =
      Integer.Sparse.eval keyMomentRow2157 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2775) := by
    have ha : gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge = raw41626 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41626Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41626 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5301) := by
    have ha : gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge = raw41627 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41627Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41627 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2157).leftCharge (GramAssembly.key 2157).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2157, Integer.Sparse.eval]
  ring

theorem keyMoment2158 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2158) =
      Integer.Sparse.eval keyMomentRow2158 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2697) := by
    have ha : gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge = raw41628 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41628Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41628 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5243) := by
    have ha : gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge = raw41629 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41629Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41629 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2158).leftCharge (GramAssembly.key 2158).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2158, Integer.Sparse.eval]
  ring

theorem keyMoment2159 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2159) =
      Integer.Sparse.eval keyMomentRow2159 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2728) := by
    have ha : gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge = raw41630 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41630Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41630 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5263) := by
    have ha : gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge = raw41631 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41631Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41631 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2159).leftCharge (GramAssembly.key 2159).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2159, Integer.Sparse.eval]
  ring

theorem keyMoment2160 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2160) =
      Integer.Sparse.eval keyMomentRow2160 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge = raw41632 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41632Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41632 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge = raw41633 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41633Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41633 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2160).leftCharge (GramAssembly.key 2160).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2160, Integer.Sparse.eval]
  ring

theorem keyMoment2161 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2161) =
      Integer.Sparse.eval keyMomentRow2161 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2676) := by
    have ha : gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge = raw41634 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41634Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41634 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5231) := by
    have ha : gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge = raw41635 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41635Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41635 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2161).leftCharge (GramAssembly.key 2161).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2161, Integer.Sparse.eval]
  ring

theorem keyMoment2162 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2162) =
      Integer.Sparse.eval keyMomentRow2162 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2755) := by
    have ha : gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge = raw41636 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41636Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41636 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4890) := by
    have ha : gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge = raw41637 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41637Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41637 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2162).leftCharge (GramAssembly.key 2162).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2162, Integer.Sparse.eval]
  ring

theorem keyMoment2163 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2163) =
      Integer.Sparse.eval keyMomentRow2163 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2754) := by
    have ha : gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge = raw41638 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41638Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41638 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5270) := by
    have ha : gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge = raw41639 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41639Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41639 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2163).leftCharge (GramAssembly.key 2163).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2163, Integer.Sparse.eval]
  ring

theorem keyMoment2164 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2164) =
      Integer.Sparse.eval keyMomentRow2164 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2753) := by
    have ha : gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge = raw41640 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41640Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41640 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5284) := by
    have ha : gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge = raw41641 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41641Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41641 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2164).leftCharge (GramAssembly.key 2164).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2164, Integer.Sparse.eval]
  ring

theorem keyMoment2165 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2165) =
      Integer.Sparse.eval keyMomentRow2165 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2751) := by
    have ha : gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge = raw41642 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41642Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41642 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge = raw41643 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41643Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41643 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2165).leftCharge (GramAssembly.key 2165).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2165, Integer.Sparse.eval]
  ring

theorem keyMoment2166 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2166) =
      Integer.Sparse.eval keyMomentRow2166 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2748) := by
    have ha : gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge = raw41644 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41644Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41644 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5279) := by
    have ha : gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge = raw41645 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41645Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41645 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2166).leftCharge (GramAssembly.key 2166).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2166, Integer.Sparse.eval]
  ring

theorem keyMoment2167 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2167) =
      Integer.Sparse.eval keyMomentRow2167 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2710) := by
    have ha : gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge = raw41646 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41646Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41646 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5251) := by
    have ha : gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge = raw41647 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41647Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41647 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2167).leftCharge (GramAssembly.key 2167).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2167, Integer.Sparse.eval]
  ring

theorem keyMoment2168 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2168) =
      Integer.Sparse.eval keyMomentRow2168 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2708) := by
    have ha : gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge = raw41648 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41648Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41648 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5249) := by
    have ha : gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge = raw41649 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41649Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41649 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2168).leftCharge (GramAssembly.key 2168).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2168, Integer.Sparse.eval]
  ring

theorem keyMoment2169 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2169) =
      Integer.Sparse.eval keyMomentRow2169 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2661) := by
    have ha : gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge = raw41650 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41650Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41650 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5219) := by
    have ha : gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge = raw41651 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41651Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41651 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2169).leftCharge (GramAssembly.key 2169).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2169, Integer.Sparse.eval]
  ring

theorem keyMoment2170 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2170) =
      Integer.Sparse.eval keyMomentRow2170 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2747) := by
    have ha : gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge = raw41652 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41652Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41652 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5278) := by
    have ha : gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge = raw41653 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41653Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41653 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2170).leftCharge (GramAssembly.key 2170).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2170, Integer.Sparse.eval]
  ring

theorem keyMoment2171 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2171) =
      Integer.Sparse.eval keyMomentRow2171 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2750) := by
    have ha : gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge = raw41654 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41654Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41654 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5281) := by
    have ha : gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge = raw41655 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41655Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41655 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2171).leftCharge (GramAssembly.key 2171).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2171, Integer.Sparse.eval]
  ring

theorem keyMoment2172 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2172) =
      Integer.Sparse.eval keyMomentRow2172 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2769) := by
    have ha : gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge = raw41656 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41656Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41656 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5295) := by
    have ha : gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge = raw41657 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41657Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41657 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2172).leftCharge (GramAssembly.key 2172).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2172, Integer.Sparse.eval]
  ring

theorem keyMoment2173 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2173) =
      Integer.Sparse.eval keyMomentRow2173 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2761) := by
    have ha : gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge = raw41658 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41658Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41658 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5175) := by
    have ha : gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge = raw41659 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41659Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41659 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2173).leftCharge (GramAssembly.key 2173).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2173, Integer.Sparse.eval]
  ring

theorem keyMoment2174 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2174) =
      Integer.Sparse.eval keyMomentRow2174 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2724) := by
    have ha : gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge = raw41660 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41660Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41660 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5260) := by
    have ha : gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge = raw41661 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41661Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41661 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2174).leftCharge (GramAssembly.key 2174).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2174, Integer.Sparse.eval]
  ring

theorem keyMoment2175 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2175) =
      Integer.Sparse.eval keyMomentRow2175 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2719) := by
    have ha : gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge = raw41662 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41662Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41662 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5161) := by
    have ha : gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge = raw41663 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41663Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41663 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2175).leftCharge (GramAssembly.key 2175).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2175, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk67
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2144 : keyMomentRows (2144 : Fin 2886) =
    keyMomentRow2144 := by decide +kernel

theorem keyMomentRowsAt2145 : keyMomentRows (2145 : Fin 2886) =
    keyMomentRow2145 := by decide +kernel

theorem keyMomentRowsAt2146 : keyMomentRows (2146 : Fin 2886) =
    keyMomentRow2146 := by decide +kernel

theorem keyMomentRowsAt2147 : keyMomentRows (2147 : Fin 2886) =
    keyMomentRow2147 := by decide +kernel

theorem keyMomentRowsAt2148 : keyMomentRows (2148 : Fin 2886) =
    keyMomentRow2148 := by decide +kernel

theorem keyMomentRowsAt2149 : keyMomentRows (2149 : Fin 2886) =
    keyMomentRow2149 := by decide +kernel

theorem keyMomentRowsAt2150 : keyMomentRows (2150 : Fin 2886) =
    keyMomentRow2150 := by decide +kernel

theorem keyMomentRowsAt2151 : keyMomentRows (2151 : Fin 2886) =
    keyMomentRow2151 := by decide +kernel

theorem keyMomentRowsAt2152 : keyMomentRows (2152 : Fin 2886) =
    keyMomentRow2152 := by decide +kernel

theorem keyMomentRowsAt2153 : keyMomentRows (2153 : Fin 2886) =
    keyMomentRow2153 := by decide +kernel

theorem keyMomentRowsAt2154 : keyMomentRows (2154 : Fin 2886) =
    keyMomentRow2154 := by decide +kernel

theorem keyMomentRowsAt2155 : keyMomentRows (2155 : Fin 2886) =
    keyMomentRow2155 := by decide +kernel

theorem keyMomentRowsAt2156 : keyMomentRows (2156 : Fin 2886) =
    keyMomentRow2156 := by decide +kernel

theorem keyMomentRowsAt2157 : keyMomentRows (2157 : Fin 2886) =
    keyMomentRow2157 := by decide +kernel

theorem keyMomentRowsAt2158 : keyMomentRows (2158 : Fin 2886) =
    keyMomentRow2158 := by decide +kernel

theorem keyMomentRowsAt2159 : keyMomentRows (2159 : Fin 2886) =
    keyMomentRow2159 := by decide +kernel

theorem keyMomentRowsAt2160 : keyMomentRows (2160 : Fin 2886) =
    keyMomentRow2160 := by decide +kernel

theorem keyMomentRowsAt2161 : keyMomentRows (2161 : Fin 2886) =
    keyMomentRow2161 := by decide +kernel

theorem keyMomentRowsAt2162 : keyMomentRows (2162 : Fin 2886) =
    keyMomentRow2162 := by decide +kernel

theorem keyMomentRowsAt2163 : keyMomentRows (2163 : Fin 2886) =
    keyMomentRow2163 := by decide +kernel

theorem keyMomentRowsAt2164 : keyMomentRows (2164 : Fin 2886) =
    keyMomentRow2164 := by decide +kernel

theorem keyMomentRowsAt2165 : keyMomentRows (2165 : Fin 2886) =
    keyMomentRow2165 := by decide +kernel

theorem keyMomentRowsAt2166 : keyMomentRows (2166 : Fin 2886) =
    keyMomentRow2166 := by decide +kernel

theorem keyMomentRowsAt2167 : keyMomentRows (2167 : Fin 2886) =
    keyMomentRow2167 := by decide +kernel

theorem keyMomentRowsAt2168 : keyMomentRows (2168 : Fin 2886) =
    keyMomentRow2168 := by decide +kernel

theorem keyMomentRowsAt2169 : keyMomentRows (2169 : Fin 2886) =
    keyMomentRow2169 := by decide +kernel

theorem keyMomentRowsAt2170 : keyMomentRows (2170 : Fin 2886) =
    keyMomentRow2170 := by decide +kernel

theorem keyMomentRowsAt2171 : keyMomentRows (2171 : Fin 2886) =
    keyMomentRow2171 := by decide +kernel

theorem keyMomentRowsAt2172 : keyMomentRows (2172 : Fin 2886) =
    keyMomentRow2172 := by decide +kernel

theorem keyMomentRowsAt2173 : keyMomentRows (2173 : Fin 2886) =
    keyMomentRow2173 := by decide +kernel

theorem keyMomentRowsAt2174 : keyMomentRows (2174 : Fin 2886) =
    keyMomentRow2174 := by decide +kernel

theorem keyMomentRowsAt2175 : keyMomentRows (2175 : Fin 2886) =
    keyMomentRow2175 := by decide +kernel

theorem keyMomentChunkSound67_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 67) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2144 ∨ k.val = 2145 ∨ k.val = 2146 ∨ k.val = 2147 ∨ k.val = 2148 ∨ k.val = 2149 ∨ k.val = 2150 ∨ k.val = 2151 ∨ k.val = 2152 ∨ k.val = 2153 ∨ k.val = 2154 ∨ k.val = 2155 ∨ k.val = 2156 ∨ k.val = 2157 ∨ k.val = 2158 ∨ k.val = 2159 ∨ k.val = 2160 ∨ k.val = 2161 ∨ k.val = 2162 ∨ k.val = 2163 ∨ k.val = 2164 ∨ k.val = 2165 ∨ k.val = 2166 ∨ k.val = 2167 ∨ k.val = 2168 ∨ k.val = 2169 ∨ k.val = 2170 ∨ k.val = 2171 ∨ k.val = 2172 ∨ k.val = 2173 ∨ k.val = 2174 ∨ k.val = 2175 := by omega
  rcases heq with h2144 | h2145 | h2146 | h2147 | h2148 | h2149 | h2150 | h2151 | h2152 | h2153 | h2154 | h2155 | h2156 | h2157 | h2158 | h2159 | h2160 | h2161 | h2162 | h2163 | h2164 | h2165 | h2166 | h2167 | h2168 | h2169 | h2170 | h2171 | h2172 | h2173 | h2174 | h2175
  · have he : k = (2144 : Fin 2886) := Fin.ext h2144
    subst k
    rw [keyMomentRowsAt2144]
    exact keyMoment2144 B hB
  · have he : k = (2145 : Fin 2886) := Fin.ext h2145
    subst k
    rw [keyMomentRowsAt2145]
    exact keyMoment2145 B hB
  · have he : k = (2146 : Fin 2886) := Fin.ext h2146
    subst k
    rw [keyMomentRowsAt2146]
    exact keyMoment2146 B hB
  · have he : k = (2147 : Fin 2886) := Fin.ext h2147
    subst k
    rw [keyMomentRowsAt2147]
    exact keyMoment2147 B hB
  · have he : k = (2148 : Fin 2886) := Fin.ext h2148
    subst k
    rw [keyMomentRowsAt2148]
    exact keyMoment2148 B hB
  · have he : k = (2149 : Fin 2886) := Fin.ext h2149
    subst k
    rw [keyMomentRowsAt2149]
    exact keyMoment2149 B hB
  · have he : k = (2150 : Fin 2886) := Fin.ext h2150
    subst k
    rw [keyMomentRowsAt2150]
    exact keyMoment2150 B hB
  · have he : k = (2151 : Fin 2886) := Fin.ext h2151
    subst k
    rw [keyMomentRowsAt2151]
    exact keyMoment2151 B hB
  · have he : k = (2152 : Fin 2886) := Fin.ext h2152
    subst k
    rw [keyMomentRowsAt2152]
    exact keyMoment2152 B hB
  · have he : k = (2153 : Fin 2886) := Fin.ext h2153
    subst k
    rw [keyMomentRowsAt2153]
    exact keyMoment2153 B hB
  · have he : k = (2154 : Fin 2886) := Fin.ext h2154
    subst k
    rw [keyMomentRowsAt2154]
    exact keyMoment2154 B hB
  · have he : k = (2155 : Fin 2886) := Fin.ext h2155
    subst k
    rw [keyMomentRowsAt2155]
    exact keyMoment2155 B hB
  · have he : k = (2156 : Fin 2886) := Fin.ext h2156
    subst k
    rw [keyMomentRowsAt2156]
    exact keyMoment2156 B hB
  · have he : k = (2157 : Fin 2886) := Fin.ext h2157
    subst k
    rw [keyMomentRowsAt2157]
    exact keyMoment2157 B hB
  · have he : k = (2158 : Fin 2886) := Fin.ext h2158
    subst k
    rw [keyMomentRowsAt2158]
    exact keyMoment2158 B hB
  · have he : k = (2159 : Fin 2886) := Fin.ext h2159
    subst k
    rw [keyMomentRowsAt2159]
    exact keyMoment2159 B hB
  · have he : k = (2160 : Fin 2886) := Fin.ext h2160
    subst k
    rw [keyMomentRowsAt2160]
    exact keyMoment2160 B hB
  · have he : k = (2161 : Fin 2886) := Fin.ext h2161
    subst k
    rw [keyMomentRowsAt2161]
    exact keyMoment2161 B hB
  · have he : k = (2162 : Fin 2886) := Fin.ext h2162
    subst k
    rw [keyMomentRowsAt2162]
    exact keyMoment2162 B hB
  · have he : k = (2163 : Fin 2886) := Fin.ext h2163
    subst k
    rw [keyMomentRowsAt2163]
    exact keyMoment2163 B hB
  · have he : k = (2164 : Fin 2886) := Fin.ext h2164
    subst k
    rw [keyMomentRowsAt2164]
    exact keyMoment2164 B hB
  · have he : k = (2165 : Fin 2886) := Fin.ext h2165
    subst k
    rw [keyMomentRowsAt2165]
    exact keyMoment2165 B hB
  · have he : k = (2166 : Fin 2886) := Fin.ext h2166
    subst k
    rw [keyMomentRowsAt2166]
    exact keyMoment2166 B hB
  · have he : k = (2167 : Fin 2886) := Fin.ext h2167
    subst k
    rw [keyMomentRowsAt2167]
    exact keyMoment2167 B hB
  · have he : k = (2168 : Fin 2886) := Fin.ext h2168
    subst k
    rw [keyMomentRowsAt2168]
    exact keyMoment2168 B hB
  · have he : k = (2169 : Fin 2886) := Fin.ext h2169
    subst k
    rw [keyMomentRowsAt2169]
    exact keyMoment2169 B hB
  · have he : k = (2170 : Fin 2886) := Fin.ext h2170
    subst k
    rw [keyMomentRowsAt2170]
    exact keyMoment2170 B hB
  · have he : k = (2171 : Fin 2886) := Fin.ext h2171
    subst k
    rw [keyMomentRowsAt2171]
    exact keyMoment2171 B hB
  · have he : k = (2172 : Fin 2886) := Fin.ext h2172
    subst k
    rw [keyMomentRowsAt2172]
    exact keyMoment2172 B hB
  · have he : k = (2173 : Fin 2886) := Fin.ext h2173
    subst k
    rw [keyMomentRowsAt2173]
    exact keyMoment2173 B hB
  · have he : k = (2174 : Fin 2886) := Fin.ext h2174
    subst k
    rw [keyMomentRowsAt2174]
    exact keyMoment2174 B hB
  · have he : k = (2175 : Fin 2886) := Fin.ext h2175
    subst k
    rw [keyMomentRowsAt2175]
    exact keyMoment2175 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound67_e_oai
