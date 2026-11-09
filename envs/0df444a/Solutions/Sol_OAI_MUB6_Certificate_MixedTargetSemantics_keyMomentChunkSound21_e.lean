-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T04:48:22.863914+00:00
-- url     : https://prove2.me/submissions/7f56c5a3-98ee-4d55-b583-1066cc4416ab

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

theorem mixedMoment_zero_first_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (hA : ∀ i, A i 0 = 0) :
    mixedMoment B A label = mixedMoment B (fun i j => A i j.succ) (fun j => label j.succ) := by
  apply average_congr
  intro r
  apply average_congr
  intro ρ
  apply average_congr
  intro τ
  unfold mixedIntegrand
  rw [Fin.prod_univ_succ]
  have hz : (fun i => A i 0) = 0 := funext hA
  rw [hz, rowFourier_zero, one_mul]

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

theorem delete_zero_factor {p n l : ℕ} (B : Fin 7 → Basis)
    (A : Matrix (Fin p) (Fin (n + 1)) ℤ) (label : Fin (n + 1) → Fin l)
    (σ : Equiv.Perm (Fin (n + 1))) (hz : ∀ i, A i (σ 0) = 0) :
    mixedMoment B A label =
      mixedMoment B (fun i j => A i (σ j.succ)) (fun j => label (σ j.succ)) := by
  rw [← mixedMoment_factor_permutation B A label σ]
  exact mixedMoment_zero_first_factor B _ _ hz

end MUB6.Certificate.MixedSemantics

end

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical313
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical40120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40120 raw40120Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw40120 raw40120Labels = mixedMoment B raw40120step0 raw40120step0Labels := by
      have ha : raw40120step0 = (fun i j => raw40120 (permutation665 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40120step0 raw40120; decide +kernel
      have hl : raw40120step0Labels = raw40120Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40120 raw40120Labels permutation665 permutation7
    _ = mixedMoment B node373 node373Labels := by rfl

theorem canonical40121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40121 raw40121Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw40121 raw40121Labels = mixedMoment B raw40121step0 raw40121step0Labels := by
      have hz : ∀ j, raw40121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40121step0 = (fun i j => raw40121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40121step0 raw40121; decide +kernel
      have hl : raw40121step0Labels = raw40121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40121 raw40121Labels permutation434 hz
    mixedMoment B raw40121step0 raw40121step0Labels = mixedMoment B raw40121step1 raw40121step1Labels := by
      have ha : raw40121step1 = (fun i j => raw40121step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40121step1 raw40121step0; decide +kernel
      have hl : raw40121step1Labels = raw40121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40121step0 raw40121step0Labels permutation146 permutation2
    mixedMoment B raw40121step1 raw40121step1Labels = mixedMoment B raw40121step2 raw40121step2Labels := by
      have ha : raw40121step2 = -raw40121step1 := by apply Matrix.ext; change ∀ i j, raw40121step2 i j = -(raw40121step1 i j); unfold raw40121step2 raw40121step1; decide +kernel
      have hl : raw40121step2Labels = raw40121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node494 node494Labels := by rfl

theorem canonical40122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40122 raw40122Labels = mixedMoment B node373 node373Labels := by
  calc
    mixedMoment B raw40122 raw40122Labels = mixedMoment B raw40122step0 raw40122step0Labels := by
      have ha : raw40122step0 = (fun i j => raw40122 (permutation399 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40122step0 raw40122; decide +kernel
      have hl : raw40122step0Labels = raw40122Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40122 raw40122Labels permutation399 permutation6
    mixedMoment B raw40122step0 raw40122step0Labels = mixedMoment B raw40122step1 raw40122step1Labels := by
      have ha : raw40122step1 = -raw40122step0 := by apply Matrix.ext; change ∀ i j, raw40122step1 i j = -(raw40122step0 i j); unfold raw40122step1 raw40122step0; decide +kernel
      have hl : raw40122step1Labels = raw40122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node373 node373Labels := by rfl

theorem canonical40123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40123 raw40123Labels = mixedMoment B node374 node374Labels := by
  calc
    mixedMoment B raw40123 raw40123Labels = mixedMoment B raw40123step0 raw40123step0Labels := by
      have hz : ∀ j, raw40123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40123step0 = (fun i j => raw40123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40123step0 raw40123; decide +kernel
      have hl : raw40123step0Labels = raw40123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40123 raw40123Labels permutation434 hz
    mixedMoment B raw40123step0 raw40123step0Labels = mixedMoment B raw40123step1 raw40123step1Labels := by
      have ha : raw40123step1 = (fun i j => raw40123step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40123step1 raw40123step0; decide +kernel
      have hl : raw40123step1Labels = raw40123step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40123step0 raw40123step0Labels permutation92 permutation6
    mixedMoment B raw40123step1 raw40123step1Labels = mixedMoment B raw40123step2 raw40123step2Labels := by
      have ha : raw40123step2 = -raw40123step1 := by apply Matrix.ext; change ∀ i j, raw40123step2 i j = -(raw40123step1 i j); unfold raw40123step2 raw40123step1; decide +kernel
      have hl : raw40123step2Labels = raw40123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node374 node374Labels := by rfl

theorem canonical40124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40124 raw40124Labels = mixedMoment B node5509 node5509Labels := by
  calc
    mixedMoment B raw40124 raw40124Labels = mixedMoment B raw40124step0 raw40124step0Labels := by
      have hz : ∀ j, raw40124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40124step0 = (fun i j => raw40124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40124step0 raw40124; decide +kernel
      have hl : raw40124step0Labels = raw40124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40124 raw40124Labels permutation434 hz
    mixedMoment B raw40124step0 raw40124step0Labels = mixedMoment B raw40124step1 raw40124step1Labels := by
      have ha : raw40124step1 = (fun i j => raw40124step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40124step1 raw40124step0; decide +kernel
      have hl : raw40124step1Labels = raw40124step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40124step0 raw40124step0Labels permutation150 permutation5
    _ = mixedMoment B node5509 node5509Labels := by rfl

theorem canonical40125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40125 raw40125Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw40125 raw40125Labels = mixedMoment B raw40125step0 raw40125step0Labels := by
      have ha : raw40125step0 = (fun i j => raw40125 (permutation514 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40125step0 raw40125; decide +kernel
      have hl : raw40125step0Labels = raw40125Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40125 raw40125Labels permutation514 permutation4
    _ = mixedMoment B node488 node488Labels := by rfl

theorem canonical40126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40126 raw40126Labels = mixedMoment B node5 node5Labels := by
  calc
    mixedMoment B raw40126 raw40126Labels = mixedMoment B raw40126step0 raw40126step0Labels := by
      have hz : ∀ j, raw40126 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40126step0 = (fun i j => raw40126 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40126step0 raw40126; decide +kernel
      have hl : raw40126step0Labels = raw40126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40126 raw40126Labels permutation520 hz
    mixedMoment B raw40126step0 raw40126step0Labels = mixedMoment B raw40126step1 raw40126step1Labels := by
      have hz : ∀ j, raw40126step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40126step1 = (fun i j => raw40126step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40126step1 raw40126step0; decide +kernel
      have hl : raw40126step1Labels = raw40126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40126step0 raw40126step0Labels permutation104 hz
    mixedMoment B raw40126step1 raw40126step1Labels = mixedMoment B raw40126step2 raw40126step2Labels := by
      have hz : ∀ j, raw40126step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40126step2 = (fun i j => raw40126step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40126step2 raw40126step1; decide +kernel
      have hl : raw40126step2Labels = raw40126step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40126step1 raw40126step1Labels permutation20 hz
    mixedMoment B raw40126step2 raw40126step2Labels = mixedMoment B raw40126step3 raw40126step3Labels := by
      have hz : ∀ i, raw40126step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40126step3 = (fun i j => raw40126step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40126step3 raw40126step2; decide +kernel
      have hl : raw40126step3Labels = (fun j => raw40126step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40126step2 raw40126step2Labels permutation6 hz
    mixedMoment B raw40126step3 raw40126step3Labels = mixedMoment B raw40126step4 raw40126step4Labels := by
      have ha : raw40126step4 = (fun i j => raw40126step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw40126step4 raw40126step3; decide +kernel
      have hl : raw40126step4Labels = raw40126step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40126step3 raw40126step3Labels permutation6 permutation0
    mixedMoment B raw40126step4 raw40126step4Labels = mixedMoment B raw40126step5 raw40126step5Labels := by
      have ha : raw40126step5 = -raw40126step4 := by apply Matrix.ext; change ∀ i j, raw40126step5 i j = -(raw40126step4 i j); unfold raw40126step5 raw40126step4; decide +kernel
      have hl : raw40126step5Labels = raw40126step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5 node5Labels := by rfl

theorem canonical40127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40127 raw40127Labels = mixedMoment B node529 node529Labels := by
  calc
    mixedMoment B raw40127 raw40127Labels = mixedMoment B raw40127step0 raw40127step0Labels := by
      have hz : ∀ j, raw40127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40127step0 = (fun i j => raw40127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40127step0 raw40127; decide +kernel
      have hl : raw40127step0Labels = raw40127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40127 raw40127Labels permutation434 hz
    mixedMoment B raw40127step0 raw40127step0Labels = mixedMoment B raw40127step1 raw40127step1Labels := by
      have hz : ∀ j, raw40127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40127step1 = (fun i j => raw40127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40127step1 raw40127step0; decide +kernel
      have hl : raw40127step1Labels = raw40127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40127step0 raw40127step0Labels permutation80 hz
    mixedMoment B raw40127step1 raw40127step1Labels = mixedMoment B raw40127step2 raw40127step2Labels := by
      have ha : raw40127step2 = (fun i j => raw40127step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40127step2 raw40127step1; decide +kernel
      have hl : raw40127step2Labels = raw40127step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40127step1 raw40127step1Labels permutation30 permutation3
    mixedMoment B raw40127step2 raw40127step2Labels = mixedMoment B raw40127step3 raw40127step3Labels := by
      have ha : raw40127step3 = -raw40127step2 := by apply Matrix.ext; change ∀ i j, raw40127step3 i j = -(raw40127step2 i j); unfold raw40127step3 raw40127step2; decide +kernel
      have hl : raw40127step3Labels = raw40127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node529 node529Labels := by rfl

theorem canonical40128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40128 raw40128Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw40128 raw40128Labels = mixedMoment B raw40128step0 raw40128step0Labels := by
      have hz : ∀ j, raw40128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40128step0 = (fun i j => raw40128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40128step0 raw40128; decide +kernel
      have hl : raw40128step0Labels = raw40128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40128 raw40128Labels permutation434 hz
    mixedMoment B raw40128step0 raw40128step0Labels = mixedMoment B raw40128step1 raw40128step1Labels := by
      have hz : ∀ j, raw40128step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40128step1 = (fun i j => raw40128step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40128step1 raw40128step0; decide +kernel
      have hl : raw40128step1Labels = raw40128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40128step0 raw40128step0Labels permutation80 hz
    mixedMoment B raw40128step1 raw40128step1Labels = mixedMoment B raw40128step2 raw40128step2Labels := by
      have ha : raw40128step2 = (fun i j => raw40128step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40128step2 raw40128step1; decide +kernel
      have hl : raw40128step2Labels = raw40128step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40128step1 raw40128step1Labels permutation20 permutation6
    mixedMoment B raw40128step2 raw40128step2Labels = mixedMoment B raw40128step3 raw40128step3Labels := by
      have ha : raw40128step3 = -raw40128step2 := by apply Matrix.ext; change ∀ i j, raw40128step3 i j = -(raw40128step2 i j); unfold raw40128step3 raw40128step2; decide +kernel
      have hl : raw40128step3Labels = raw40128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

theorem canonical40129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40129 raw40129Labels = mixedMoment B node262 node262Labels := by
  calc
    mixedMoment B raw40129 raw40129Labels = mixedMoment B raw40129step0 raw40129step0Labels := by
      have hz : ∀ j, raw40129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40129step0 = (fun i j => raw40129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40129step0 raw40129; decide +kernel
      have hl : raw40129step0Labels = raw40129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40129 raw40129Labels permutation434 hz
    mixedMoment B raw40129step0 raw40129step0Labels = mixedMoment B raw40129step1 raw40129step1Labels := by
      have hz : ∀ j, raw40129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40129step1 = (fun i j => raw40129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40129step1 raw40129step0; decide +kernel
      have hl : raw40129step1Labels = raw40129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40129step0 raw40129step0Labels permutation80 hz
    mixedMoment B raw40129step1 raw40129step1Labels = mixedMoment B raw40129step2 raw40129step2Labels := by
      have ha : raw40129step2 = (fun i j => raw40129step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40129step2 raw40129step1; decide +kernel
      have hl : raw40129step2Labels = raw40129step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40129step1 raw40129step1Labels permutation20 permutation6
    mixedMoment B raw40129step2 raw40129step2Labels = mixedMoment B raw40129step3 raw40129step3Labels := by
      have ha : raw40129step3 = -raw40129step2 := by apply Matrix.ext; change ∀ i j, raw40129step3 i j = -(raw40129step2 i j); unfold raw40129step3 raw40129step2; decide +kernel
      have hl : raw40129step3Labels = raw40129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node262 node262Labels := by rfl

theorem canonical40130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40130 raw40130Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw40130 raw40130Labels = mixedMoment B raw40130step0 raw40130step0Labels := by
      have hz : ∀ j, raw40130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40130step0 = (fun i j => raw40130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40130step0 raw40130; decide +kernel
      have hl : raw40130step0Labels = raw40130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40130 raw40130Labels permutation434 hz
    mixedMoment B raw40130step0 raw40130step0Labels = mixedMoment B raw40130step1 raw40130step1Labels := by
      have hz : ∀ j, raw40130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40130step1 = (fun i j => raw40130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40130step1 raw40130step0; decide +kernel
      have hl : raw40130step1Labels = raw40130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40130step0 raw40130step0Labels permutation80 hz
    mixedMoment B raw40130step1 raw40130step1Labels = mixedMoment B raw40130step2 raw40130step2Labels := by
      have ha : raw40130step2 = (fun i j => raw40130step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40130step2 raw40130step1; decide +kernel
      have hl : raw40130step2Labels = raw40130step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40130step1 raw40130step1Labels permutation26 permutation4
    _ = mixedMoment B node416 node416Labels := by rfl

theorem canonical40131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40131 raw40131Labels = mixedMoment B node7 node7Labels := by
  calc
    mixedMoment B raw40131 raw40131Labels = mixedMoment B raw40131step0 raw40131step0Labels := by
      have hz : ∀ j, raw40131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40131step0 = (fun i j => raw40131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40131step0 raw40131; decide +kernel
      have hl : raw40131step0Labels = raw40131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40131 raw40131Labels permutation434 hz
    mixedMoment B raw40131step0 raw40131step0Labels = mixedMoment B raw40131step1 raw40131step1Labels := by
      have hz : ∀ j, raw40131step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40131step1 = (fun i j => raw40131step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40131step1 raw40131step0; decide +kernel
      have hl : raw40131step1Labels = raw40131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40131step0 raw40131step0Labels permutation80 hz
    mixedMoment B raw40131step1 raw40131step1Labels = mixedMoment B raw40131step2 raw40131step2Labels := by
      have hz : ∀ i, raw40131step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw40131step2 = (fun i j => raw40131step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw40131step2 raw40131step1; decide +kernel
      have hl : raw40131step2Labels = (fun j => raw40131step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw40131step1 raw40131step1Labels permutation6 hz
    _ = mixedMoment B node7 node7Labels := by rfl

theorem canonical40132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40132 raw40132Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw40132 raw40132Labels = mixedMoment B raw40132step0 raw40132step0Labels := by
      have hz : ∀ j, raw40132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40132step0 = (fun i j => raw40132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40132step0 raw40132; decide +kernel
      have hl : raw40132step0Labels = raw40132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40132 raw40132Labels permutation346 hz
    mixedMoment B raw40132step0 raw40132step0Labels = mixedMoment B raw40132step1 raw40132step1Labels := by
      have ha : raw40132step1 = (fun i j => raw40132step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40132step1 raw40132step0; decide +kernel
      have hl : raw40132step1Labels = raw40132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40132step0 raw40132step0Labels permutation144 permutation2
    mixedMoment B raw40132step1 raw40132step1Labels = mixedMoment B raw40132step2 raw40132step2Labels := by
      have ha : raw40132step2 = -raw40132step1 := by apply Matrix.ext; change ∀ i j, raw40132step2 i j = -(raw40132step1 i j); unfold raw40132step2 raw40132step1; decide +kernel
      have hl : raw40132step2Labels = raw40132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node504 node504Labels := by rfl

theorem canonical40133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40133 raw40133Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw40133 raw40133Labels = mixedMoment B raw40133step0 raw40133step0Labels := by
      have hz : ∀ j, raw40133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40133step0 = (fun i j => raw40133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40133step0 raw40133; decide +kernel
      have hl : raw40133step0Labels = raw40133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40133 raw40133Labels permutation346 hz
    mixedMoment B raw40133step0 raw40133step0Labels = mixedMoment B raw40133step1 raw40133step1Labels := by
      have ha : raw40133step1 = (fun i j => raw40133step0 (permutation128 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40133step1 raw40133step0; decide +kernel
      have hl : raw40133step1Labels = raw40133step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40133step0 raw40133step0Labels permutation128 permutation7
    _ = mixedMoment B node397 node397Labels := by rfl

theorem canonical40134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40134 raw40134Labels = mixedMoment B node532 node532Labels := by
  calc
    mixedMoment B raw40134 raw40134Labels = mixedMoment B raw40134step0 raw40134step0Labels := by
      have hz : ∀ j, raw40134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40134step0 = (fun i j => raw40134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40134step0 raw40134; decide +kernel
      have hl : raw40134step0Labels = raw40134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40134 raw40134Labels permutation346 hz
    mixedMoment B raw40134step0 raw40134step0Labels = mixedMoment B raw40134step1 raw40134step1Labels := by
      have ha : raw40134step1 = (fun i j => raw40134step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40134step1 raw40134step0; decide +kernel
      have hl : raw40134step1Labels = raw40134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40134step0 raw40134step0Labels permutation32 permutation3
    _ = mixedMoment B node532 node532Labels := by rfl

theorem canonical40135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40135 raw40135Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw40135 raw40135Labels = mixedMoment B raw40135step0 raw40135step0Labels := by
      have hz : ∀ j, raw40135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40135step0 = (fun i j => raw40135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40135step0 raw40135; decide +kernel
      have hl : raw40135step0Labels = raw40135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40135 raw40135Labels permutation346 hz
    mixedMoment B raw40135step0 raw40135step0Labels = mixedMoment B raw40135step1 raw40135step1Labels := by
      have ha : raw40135step1 = (fun i j => raw40135step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40135step1 raw40135step0; decide +kernel
      have hl : raw40135step1Labels = raw40135step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40135step0 raw40135step0Labels permutation98 permutation4
    _ = mixedMoment B node494 node494Labels := by rfl

theorem canonical40136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40136 raw40136Labels = mixedMoment B node531 node531Labels := by
  calc
    mixedMoment B raw40136 raw40136Labels = mixedMoment B raw40136step0 raw40136step0Labels := by
      have ha : raw40136step0 = (fun i j => raw40136 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40136step0 raw40136; decide +kernel
      have hl : raw40136step0Labels = raw40136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40136 raw40136Labels permutation583 permutation2
    mixedMoment B raw40136step0 raw40136step0Labels = mixedMoment B raw40136step1 raw40136step1Labels := by
      have ha : raw40136step1 = -raw40136step0 := by apply Matrix.ext; change ∀ i j, raw40136step1 i j = -(raw40136step0 i j); unfold raw40136step1 raw40136step0; decide +kernel
      have hl : raw40136step1Labels = raw40136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node531 node531Labels := by rfl

theorem canonical40137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40137 raw40137Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw40137 raw40137Labels = mixedMoment B raw40137step0 raw40137step0Labels := by
      have ha : raw40137step0 = (fun i j => raw40137 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40137step0 raw40137; decide +kernel
      have hl : raw40137step0Labels = raw40137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40137 raw40137Labels permutation662 permutation3
    mixedMoment B raw40137step0 raw40137step0Labels = mixedMoment B raw40137step1 raw40137step1Labels := by
      have ha : raw40137step1 = -raw40137step0 := by apply Matrix.ext; change ∀ i j, raw40137step1 i j = -(raw40137step0 i j); unfold raw40137step1 raw40137step0; decide +kernel
      have hl : raw40137step1Labels = raw40137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node259 node259Labels := by rfl

theorem canonical40138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40138 raw40138Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40138 raw40138Labels = mixedMoment B raw40138step0 raw40138step0Labels := by
      have ha : raw40138step0 = (fun i j => raw40138 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40138step0 raw40138; decide +kernel
      have hl : raw40138step0Labels = raw40138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40138 raw40138Labels permutation686 permutation3
    mixedMoment B raw40138step0 raw40138step0Labels = mixedMoment B raw40138step1 raw40138step1Labels := by
      have ha : raw40138step1 = -raw40138step0 := by apply Matrix.ext; change ∀ i j, raw40138step1 i j = -(raw40138step0 i j); unfold raw40138step1 raw40138step0; decide +kernel
      have hl : raw40138step1Labels = raw40138step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node520 node520Labels := by rfl

theorem canonical40139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40139 raw40139Labels = mixedMoment B node327 node327Labels := by
  calc
    mixedMoment B raw40139 raw40139Labels = mixedMoment B raw40139step0 raw40139step0Labels := by
      have ha : raw40139step0 = (fun i j => raw40139 (permutation647 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40139step0 raw40139; decide +kernel
      have hl : raw40139step0Labels = raw40139Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40139 raw40139Labels permutation647 permutation7
    _ = mixedMoment B node327 node327Labels := by rfl

theorem canonical40140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40140 raw40140Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw40140 raw40140Labels = mixedMoment B raw40140step0 raw40140step0Labels := by
      have ha : raw40140step0 = (fun i j => raw40140 (permutation669 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40140step0 raw40140; decide +kernel
      have hl : raw40140step0Labels = raw40140Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40140 raw40140Labels permutation669 permutation7
    _ = mixedMoment B node376 node376Labels := by rfl

theorem canonical40141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40141 raw40141Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40141 raw40141Labels = mixedMoment B raw40141step0 raw40141step0Labels := by
      have ha : raw40141step0 = (fun i j => raw40141 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40141step0 raw40141; decide +kernel
      have hl : raw40141step0Labels = raw40141Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40141 raw40141Labels permutation659 permutation7
    _ = mixedMoment B node479 node479Labels := by rfl

theorem canonical40142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40142 raw40142Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw40142 raw40142Labels = mixedMoment B raw40142step0 raw40142step0Labels := by
      have hz : ∀ j, raw40142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40142step0 = (fun i j => raw40142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40142step0 raw40142; decide +kernel
      have hl : raw40142step0Labels = raw40142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40142 raw40142Labels permutation434 hz
    mixedMoment B raw40142step0 raw40142step0Labels = mixedMoment B raw40142step1 raw40142step1Labels := by
      have ha : raw40142step1 = (fun i j => raw40142step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw40142step1 raw40142step0; decide +kernel
      have hl : raw40142step1Labels = raw40142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40142step0 raw40142step0Labels permutation146 permutation7
    _ = mixedMoment B node378 node378Labels := by rfl

theorem canonical40143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40143 raw40143Labels = mixedMoment B node319 node319Labels := by
  calc
    mixedMoment B raw40143 raw40143Labels = mixedMoment B raw40143step0 raw40143step0Labels := by
      have ha : raw40143step0 = (fun i j => raw40143 (permutation375 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40143step0 raw40143; decide +kernel
      have hl : raw40143step0Labels = raw40143Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40143 raw40143Labels permutation375 permutation6
    mixedMoment B raw40143step0 raw40143step0Labels = mixedMoment B raw40143step1 raw40143step1Labels := by
      have ha : raw40143step1 = -raw40143step0 := by apply Matrix.ext; change ∀ i j, raw40143step1 i j = -(raw40143step0 i j); unfold raw40143step1 raw40143step0; decide +kernel
      have hl : raw40143step1Labels = raw40143step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node319 node319Labels := by rfl

theorem canonical40144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40144 raw40144Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw40144 raw40144Labels = mixedMoment B raw40144step0 raw40144step0Labels := by
      have hz : ∀ j, raw40144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40144step0 = (fun i j => raw40144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40144step0 raw40144; decide +kernel
      have hl : raw40144step0Labels = raw40144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40144 raw40144Labels permutation434 hz
    mixedMoment B raw40144step0 raw40144step0Labels = mixedMoment B raw40144step1 raw40144step1Labels := by
      have ha : raw40144step1 = (fun i j => raw40144step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40144step1 raw40144step0; decide +kernel
      have hl : raw40144step1Labels = raw40144step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40144step0 raw40144step0Labels permutation80 permutation4
    mixedMoment B raw40144step1 raw40144step1Labels = mixedMoment B raw40144step2 raw40144step2Labels := by
      have ha : raw40144step2 = -raw40144step1 := by apply Matrix.ext; change ∀ i j, raw40144step2 i j = -(raw40144step1 i j); unfold raw40144step2 raw40144step1; decide +kernel
      have hl : raw40144step2Labels = raw40144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

theorem canonical40145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40145 raw40145Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw40145 raw40145Labels = mixedMoment B raw40145step0 raw40145step0Labels := by
      have ha : raw40145step0 = (fun i j => raw40145 (permutation356 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40145step0 raw40145; decide +kernel
      have hl : raw40145step0Labels = raw40145Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40145 raw40145Labels permutation356 permutation4
    mixedMoment B raw40145step0 raw40145step0Labels = mixedMoment B raw40145step1 raw40145step1Labels := by
      have ha : raw40145step1 = -raw40145step0 := by apply Matrix.ext; change ∀ i j, raw40145step1 i j = -(raw40145step0 i j); unfold raw40145step1 raw40145step0; decide +kernel
      have hl : raw40145step1Labels = raw40145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

theorem canonical40146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40146 raw40146Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw40146 raw40146Labels = mixedMoment B raw40146step0 raw40146step0Labels := by
      have ha : raw40146step0 = (fun i j => raw40146 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw40146step0 raw40146; decide +kernel
      have hl : raw40146step0Labels = raw40146Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40146 raw40146Labels permutation674 permutation5
    _ = mixedMoment B node520 node520Labels := by rfl

theorem canonical40147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40147 raw40147Labels = mixedMoment B node506 node506Labels := by
  calc
    mixedMoment B raw40147 raw40147Labels = mixedMoment B raw40147step0 raw40147step0Labels := by
      have hz : ∀ j, raw40147 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40147step0 = (fun i j => raw40147 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40147step0 raw40147; decide +kernel
      have hl : raw40147step0Labels = raw40147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40147 raw40147Labels permutation520 hz
    mixedMoment B raw40147step0 raw40147step0Labels = mixedMoment B raw40147step1 raw40147step1Labels := by
      have hz : ∀ j, raw40147step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40147step1 = (fun i j => raw40147step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40147step1 raw40147step0; decide +kernel
      have hl : raw40147step1Labels = raw40147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40147step0 raw40147step0Labels permutation104 hz
    mixedMoment B raw40147step1 raw40147step1Labels = mixedMoment B raw40147step2 raw40147step2Labels := by
      have ha : raw40147step2 = (fun i j => raw40147step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40147step2 raw40147step1; decide +kernel
      have hl : raw40147step2Labels = raw40147step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40147step1 raw40147step1Labels permutation31 permutation3
    mixedMoment B raw40147step2 raw40147step2Labels = mixedMoment B raw40147step3 raw40147step3Labels := by
      have ha : raw40147step3 = -raw40147step2 := by apply Matrix.ext; change ∀ i j, raw40147step3 i j = -(raw40147step2 i j); unfold raw40147step3 raw40147step2; decide +kernel
      have hl : raw40147step3Labels = raw40147step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node506 node506Labels := by rfl

theorem canonical40148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40148 raw40148Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw40148 raw40148Labels = mixedMoment B raw40148step0 raw40148step0Labels := by
      have hz : ∀ j, raw40148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40148step0 = (fun i j => raw40148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40148step0 raw40148; decide +kernel
      have hl : raw40148step0Labels = raw40148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40148 raw40148Labels permutation434 hz
    mixedMoment B raw40148step0 raw40148step0Labels = mixedMoment B raw40148step1 raw40148step1Labels := by
      have ha : raw40148step1 = (fun i j => raw40148step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw40148step1 raw40148step0; decide +kernel
      have hl : raw40148step1Labels = raw40148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40148step0 raw40148step0Labels permutation144 permutation2
    mixedMoment B raw40148step1 raw40148step1Labels = mixedMoment B raw40148step2 raw40148step2Labels := by
      have ha : raw40148step2 = -raw40148step1 := by apply Matrix.ext; change ∀ i j, raw40148step2 i j = -(raw40148step1 i j); unfold raw40148step2 raw40148step1; decide +kernel
      have hl : raw40148step2Labels = raw40148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node526 node526Labels := by rfl

theorem canonical40149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40149 raw40149Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw40149 raw40149Labels = mixedMoment B raw40149step0 raw40149step0Labels := by
      have hz : ∀ j, raw40149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40149step0 = (fun i j => raw40149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40149step0 raw40149; decide +kernel
      have hl : raw40149step0Labels = raw40149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40149 raw40149Labels permutation434 hz
    mixedMoment B raw40149step0 raw40149step0Labels = mixedMoment B raw40149step1 raw40149step1Labels := by
      have ha : raw40149step1 = (fun i j => raw40149step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40149step1 raw40149step0; decide +kernel
      have hl : raw40149step1Labels = raw40149step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40149step0 raw40149step0Labels permutation110 permutation6
    mixedMoment B raw40149step1 raw40149step1Labels = mixedMoment B raw40149step2 raw40149step2Labels := by
      have ha : raw40149step2 = -raw40149step1 := by apply Matrix.ext; change ∀ i j, raw40149step2 i j = -(raw40149step1 i j); unfold raw40149step2 raw40149step1; decide +kernel
      have hl : raw40149step2Labels = raw40149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node490 node490Labels := by rfl

theorem canonical40150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40150 raw40150Labels = mixedMoment B node224 node224Labels := by
  calc
    mixedMoment B raw40150 raw40150Labels = mixedMoment B raw40150step0 raw40150step0Labels := by
      have hz : ∀ j, raw40150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40150step0 = (fun i j => raw40150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40150step0 raw40150; decide +kernel
      have hl : raw40150step0Labels = raw40150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40150 raw40150Labels permutation434 hz
    mixedMoment B raw40150step0 raw40150step0Labels = mixedMoment B raw40150step1 raw40150step1Labels := by
      have ha : raw40150step1 = (fun i j => raw40150step0 (permutation110 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40150step1 raw40150step0; decide +kernel
      have hl : raw40150step1Labels = raw40150step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40150step0 raw40150step0Labels permutation110 permutation6
    mixedMoment B raw40150step1 raw40150step1Labels = mixedMoment B raw40150step2 raw40150step2Labels := by
      have ha : raw40150step2 = -raw40150step1 := by apply Matrix.ext; change ∀ i j, raw40150step2 i j = -(raw40150step1 i j); unfold raw40150step2 raw40150step1; decide +kernel
      have hl : raw40150step2Labels = raw40150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node224 node224Labels := by rfl

theorem canonical40151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40151 raw40151Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw40151 raw40151Labels = mixedMoment B raw40151step0 raw40151step0Labels := by
      have hz : ∀ j, raw40151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40151step0 = (fun i j => raw40151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40151step0 raw40151; decide +kernel
      have hl : raw40151step0Labels = raw40151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40151 raw40151Labels permutation434 hz
    mixedMoment B raw40151step0 raw40151step0Labels = mixedMoment B raw40151step1 raw40151step1Labels := by
      have ha : raw40151step1 = (fun i j => raw40151step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw40151step1 raw40151step0; decide +kernel
      have hl : raw40151step1Labels = raw40151step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40151step0 raw40151step0Labels permutation134 permutation4
    _ = mixedMoment B node387 node387Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment672 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 672) =
      Integer.Sparse.eval keyMomentRow672 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 672).leftCharge (GramAssembly.key 672).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 672).leftCharge (GramAssembly.key 672).rightCharge = raw40120 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40120Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40120 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 672).leftCharge (GramAssembly.key 672).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow672, Integer.Sparse.eval]

theorem keyMoment673 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 673) =
      Integer.Sparse.eval keyMomentRow673 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 673).leftCharge (GramAssembly.key 673).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 673).leftCharge (GramAssembly.key 673).rightCharge = raw40121 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40121Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40121 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 673).leftCharge (GramAssembly.key 673).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow673, Integer.Sparse.eval]

theorem keyMoment674 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 674) =
      Integer.Sparse.eval keyMomentRow674 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 674).leftCharge (GramAssembly.key 674).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 373) := by
    have ha : gramCharges (GramAssembly.key 674).leftCharge (GramAssembly.key 674).rightCharge = raw40122 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40122Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40122 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 674).leftCharge (GramAssembly.key 674).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow674, Integer.Sparse.eval]

theorem keyMoment675 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 675) =
      Integer.Sparse.eval keyMomentRow675 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 675).leftCharge (GramAssembly.key 675).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 374) := by
    have ha : gramCharges (GramAssembly.key 675).leftCharge (GramAssembly.key 675).rightCharge = raw40123 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40123Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40123 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 675).leftCharge (GramAssembly.key 675).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow675, Integer.Sparse.eval]

theorem keyMoment676 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 676) =
      Integer.Sparse.eval keyMomentRow676 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 676).leftCharge (GramAssembly.key 676).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inr 7) := by
    have ha : gramCharges (GramAssembly.key 676).leftCharge (GramAssembly.key 676).rightCharge = raw40124 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40124Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40124 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 676).leftCharge (GramAssembly.key 676).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow676, Integer.Sparse.eval]

theorem keyMoment677 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 677) =
      Integer.Sparse.eval keyMomentRow677 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 677).leftCharge (GramAssembly.key 677).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 488) := by
    have ha : gramCharges (GramAssembly.key 677).leftCharge (GramAssembly.key 677).rightCharge = raw40125 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40125Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40125 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 677).leftCharge (GramAssembly.key 677).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow677, Integer.Sparse.eval]

theorem keyMoment678 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 678) =
      Integer.Sparse.eval keyMomentRow678 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 678).leftCharge (GramAssembly.key 678).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 5) := by
    have ha : gramCharges (GramAssembly.key 678).leftCharge (GramAssembly.key 678).rightCharge = raw40126 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40126Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40126 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 678).leftCharge (GramAssembly.key 678).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow678, Integer.Sparse.eval]

theorem keyMoment679 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 679) =
      Integer.Sparse.eval keyMomentRow679 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 679).leftCharge (GramAssembly.key 679).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 529) := by
    have ha : gramCharges (GramAssembly.key 679).leftCharge (GramAssembly.key 679).rightCharge = raw40127 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40127Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40127 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 679).leftCharge (GramAssembly.key 679).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow679, Integer.Sparse.eval]

theorem keyMoment680 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 680) =
      Integer.Sparse.eval keyMomentRow680 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 680).leftCharge (GramAssembly.key 680).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 505) := by
    have ha : gramCharges (GramAssembly.key 680).leftCharge (GramAssembly.key 680).rightCharge = raw40128 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40128Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40128 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 680).leftCharge (GramAssembly.key 680).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow680, Integer.Sparse.eval]

theorem keyMoment681 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 681) =
      Integer.Sparse.eval keyMomentRow681 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 681).leftCharge (GramAssembly.key 681).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 262) := by
    have ha : gramCharges (GramAssembly.key 681).leftCharge (GramAssembly.key 681).rightCharge = raw40129 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40129Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40129 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 681).leftCharge (GramAssembly.key 681).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow681, Integer.Sparse.eval]

theorem keyMoment682 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 682) =
      Integer.Sparse.eval keyMomentRow682 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 682).leftCharge (GramAssembly.key 682).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 416) := by
    have ha : gramCharges (GramAssembly.key 682).leftCharge (GramAssembly.key 682).rightCharge = raw40130 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40130Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40130 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 682).leftCharge (GramAssembly.key 682).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow682, Integer.Sparse.eval]

theorem keyMoment683 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 683) =
      Integer.Sparse.eval keyMomentRow683 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 683).leftCharge (GramAssembly.key 683).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 7) := by
    have ha : gramCharges (GramAssembly.key 683).leftCharge (GramAssembly.key 683).rightCharge = raw40131 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40131Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40131 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 683).leftCharge (GramAssembly.key 683).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow683, Integer.Sparse.eval]

theorem keyMoment684 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 684) =
      Integer.Sparse.eval keyMomentRow684 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 684).leftCharge (GramAssembly.key 684).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 504) := by
    have ha : gramCharges (GramAssembly.key 684).leftCharge (GramAssembly.key 684).rightCharge = raw40132 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40132Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40132 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 684).leftCharge (GramAssembly.key 684).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow684, Integer.Sparse.eval]

theorem keyMoment685 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 685) =
      Integer.Sparse.eval keyMomentRow685 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 685).leftCharge (GramAssembly.key 685).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 397) := by
    have ha : gramCharges (GramAssembly.key 685).leftCharge (GramAssembly.key 685).rightCharge = raw40133 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40133Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40133 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 685).leftCharge (GramAssembly.key 685).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow685, Integer.Sparse.eval]

theorem keyMoment686 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 686) =
      Integer.Sparse.eval keyMomentRow686 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 686).leftCharge (GramAssembly.key 686).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 532) := by
    have ha : gramCharges (GramAssembly.key 686).leftCharge (GramAssembly.key 686).rightCharge = raw40134 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40134Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40134 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 686).leftCharge (GramAssembly.key 686).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow686, Integer.Sparse.eval]

theorem keyMoment687 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 687) =
      Integer.Sparse.eval keyMomentRow687 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 687).leftCharge (GramAssembly.key 687).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 494) := by
    have ha : gramCharges (GramAssembly.key 687).leftCharge (GramAssembly.key 687).rightCharge = raw40135 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40135Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40135 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 687).leftCharge (GramAssembly.key 687).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow687, Integer.Sparse.eval]

theorem keyMoment688 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 688) =
      Integer.Sparse.eval keyMomentRow688 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 688).leftCharge (GramAssembly.key 688).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 531) := by
    have ha : gramCharges (GramAssembly.key 688).leftCharge (GramAssembly.key 688).rightCharge = raw40136 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40136Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40136 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 688).leftCharge (GramAssembly.key 688).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow688, Integer.Sparse.eval]

theorem keyMoment689 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 689) =
      Integer.Sparse.eval keyMomentRow689 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 689).leftCharge (GramAssembly.key 689).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 259) := by
    have ha : gramCharges (GramAssembly.key 689).leftCharge (GramAssembly.key 689).rightCharge = raw40137 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40137Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40137 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 689).leftCharge (GramAssembly.key 689).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow689, Integer.Sparse.eval]

theorem keyMoment690 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 690) =
      Integer.Sparse.eval keyMomentRow690 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 690).leftCharge (GramAssembly.key 690).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 690).leftCharge (GramAssembly.key 690).rightCharge = raw40138 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40138Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40138 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 690).leftCharge (GramAssembly.key 690).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow690, Integer.Sparse.eval]

theorem keyMoment691 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 691) =
      Integer.Sparse.eval keyMomentRow691 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 691).leftCharge (GramAssembly.key 691).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 327) := by
    have ha : gramCharges (GramAssembly.key 691).leftCharge (GramAssembly.key 691).rightCharge = raw40139 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40139Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40139 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 691).leftCharge (GramAssembly.key 691).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow691, Integer.Sparse.eval]

theorem keyMoment692 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 692) =
      Integer.Sparse.eval keyMomentRow692 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 692).leftCharge (GramAssembly.key 692).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 376) := by
    have ha : gramCharges (GramAssembly.key 692).leftCharge (GramAssembly.key 692).rightCharge = raw40140 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40140Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40140 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 692).leftCharge (GramAssembly.key 692).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow692, Integer.Sparse.eval]

theorem keyMoment693 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 693) =
      Integer.Sparse.eval keyMomentRow693 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 693).leftCharge (GramAssembly.key 693).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 693).leftCharge (GramAssembly.key 693).rightCharge = raw40141 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40141Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40141 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 693).leftCharge (GramAssembly.key 693).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow693, Integer.Sparse.eval]

theorem keyMoment694 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 694) =
      Integer.Sparse.eval keyMomentRow694 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 694).leftCharge (GramAssembly.key 694).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 378) := by
    have ha : gramCharges (GramAssembly.key 694).leftCharge (GramAssembly.key 694).rightCharge = raw40142 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40142Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40142 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 694).leftCharge (GramAssembly.key 694).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow694, Integer.Sparse.eval]

theorem keyMoment695 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 695) =
      Integer.Sparse.eval keyMomentRow695 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 695).leftCharge (GramAssembly.key 695).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 319) := by
    have ha : gramCharges (GramAssembly.key 695).leftCharge (GramAssembly.key 695).rightCharge = raw40143 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40143Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40143 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 695).leftCharge (GramAssembly.key 695).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow695, Integer.Sparse.eval]

theorem keyMoment696 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 696) =
      Integer.Sparse.eval keyMomentRow696 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 696).leftCharge (GramAssembly.key 696).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 489) := by
    have ha : gramCharges (GramAssembly.key 696).leftCharge (GramAssembly.key 696).rightCharge = raw40144 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40144Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40144 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 696).leftCharge (GramAssembly.key 696).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow696, Integer.Sparse.eval]

theorem keyMoment697 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 697) =
      Integer.Sparse.eval keyMomentRow697 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 697).leftCharge (GramAssembly.key 697).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 479) := by
    have ha : gramCharges (GramAssembly.key 697).leftCharge (GramAssembly.key 697).rightCharge = raw40145 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40145Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40145 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 697).leftCharge (GramAssembly.key 697).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow697, Integer.Sparse.eval]

theorem keyMoment698 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 698) =
      Integer.Sparse.eval keyMomentRow698 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 698).leftCharge (GramAssembly.key 698).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 520) := by
    have ha : gramCharges (GramAssembly.key 698).leftCharge (GramAssembly.key 698).rightCharge = raw40146 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40146Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40146 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 698).leftCharge (GramAssembly.key 698).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow698, Integer.Sparse.eval]

theorem keyMoment699 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 699) =
      Integer.Sparse.eval keyMomentRow699 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 699).leftCharge (GramAssembly.key 699).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 506) := by
    have ha : gramCharges (GramAssembly.key 699).leftCharge (GramAssembly.key 699).rightCharge = raw40147 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40147Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40147 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 699).leftCharge (GramAssembly.key 699).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow699, Integer.Sparse.eval]

theorem keyMoment700 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 700) =
      Integer.Sparse.eval keyMomentRow700 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 700).leftCharge (GramAssembly.key 700).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 526) := by
    have ha : gramCharges (GramAssembly.key 700).leftCharge (GramAssembly.key 700).rightCharge = raw40148 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40148Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40148 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 700).leftCharge (GramAssembly.key 700).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow700, Integer.Sparse.eval]

theorem keyMoment701 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 701) =
      Integer.Sparse.eval keyMomentRow701 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 701).leftCharge (GramAssembly.key 701).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 490) := by
    have ha : gramCharges (GramAssembly.key 701).leftCharge (GramAssembly.key 701).rightCharge = raw40149 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40149Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40149 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 701).leftCharge (GramAssembly.key 701).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow701, Integer.Sparse.eval]

theorem keyMoment702 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 702) =
      Integer.Sparse.eval keyMomentRow702 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 702).leftCharge (GramAssembly.key 702).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 224) := by
    have ha : gramCharges (GramAssembly.key 702).leftCharge (GramAssembly.key 702).rightCharge = raw40150 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40150Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40150 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 702).leftCharge (GramAssembly.key 702).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow702, Integer.Sparse.eval]

theorem keyMoment703 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 703) =
      Integer.Sparse.eval keyMomentRow703 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 703).leftCharge (GramAssembly.key 703).rightCharge) (gramLabels 0 0) =
      originalVector B (Sum.inl 387) := by
    have ha : gramCharges (GramAssembly.key 703).leftCharge (GramAssembly.key 703).rightCharge = raw40151 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 0 0 = (Fin.castLEEmb (by decide : 1 ≤ 6)) ∘ raw40151Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical40151 B hB).trans rfl
  change 5 * mixedMoment B (gramCharges (GramAssembly.key 703).leftCharge (GramAssembly.key 703).rightCharge) (gramLabels 0 0) = _
  rw [hfirst]
  norm_num [keyMomentRow703, Integer.Sparse.eval]

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt672 : keyMomentRows (672 : Fin 2886) =
    keyMomentRow672 := by decide +kernel

theorem keyMomentRowsAt673 : keyMomentRows (673 : Fin 2886) =
    keyMomentRow673 := by decide +kernel

theorem keyMomentRowsAt674 : keyMomentRows (674 : Fin 2886) =
    keyMomentRow674 := by decide +kernel

theorem keyMomentRowsAt675 : keyMomentRows (675 : Fin 2886) =
    keyMomentRow675 := by decide +kernel

theorem keyMomentRowsAt676 : keyMomentRows (676 : Fin 2886) =
    keyMomentRow676 := by decide +kernel

theorem keyMomentRowsAt677 : keyMomentRows (677 : Fin 2886) =
    keyMomentRow677 := by decide +kernel

theorem keyMomentRowsAt678 : keyMomentRows (678 : Fin 2886) =
    keyMomentRow678 := by decide +kernel

theorem keyMomentRowsAt679 : keyMomentRows (679 : Fin 2886) =
    keyMomentRow679 := by decide +kernel

theorem keyMomentRowsAt680 : keyMomentRows (680 : Fin 2886) =
    keyMomentRow680 := by decide +kernel

theorem keyMomentRowsAt681 : keyMomentRows (681 : Fin 2886) =
    keyMomentRow681 := by decide +kernel

theorem keyMomentRowsAt682 : keyMomentRows (682 : Fin 2886) =
    keyMomentRow682 := by decide +kernel

theorem keyMomentRowsAt683 : keyMomentRows (683 : Fin 2886) =
    keyMomentRow683 := by decide +kernel

theorem keyMomentRowsAt684 : keyMomentRows (684 : Fin 2886) =
    keyMomentRow684 := by decide +kernel

theorem keyMomentRowsAt685 : keyMomentRows (685 : Fin 2886) =
    keyMomentRow685 := by decide +kernel

theorem keyMomentRowsAt686 : keyMomentRows (686 : Fin 2886) =
    keyMomentRow686 := by decide +kernel

theorem keyMomentRowsAt687 : keyMomentRows (687 : Fin 2886) =
    keyMomentRow687 := by decide +kernel

theorem keyMomentRowsAt688 : keyMomentRows (688 : Fin 2886) =
    keyMomentRow688 := by decide +kernel

theorem keyMomentRowsAt689 : keyMomentRows (689 : Fin 2886) =
    keyMomentRow689 := by decide +kernel

theorem keyMomentRowsAt690 : keyMomentRows (690 : Fin 2886) =
    keyMomentRow690 := by decide +kernel

theorem keyMomentRowsAt691 : keyMomentRows (691 : Fin 2886) =
    keyMomentRow691 := by decide +kernel

theorem keyMomentRowsAt692 : keyMomentRows (692 : Fin 2886) =
    keyMomentRow692 := by decide +kernel

theorem keyMomentRowsAt693 : keyMomentRows (693 : Fin 2886) =
    keyMomentRow693 := by decide +kernel

theorem keyMomentRowsAt694 : keyMomentRows (694 : Fin 2886) =
    keyMomentRow694 := by decide +kernel

theorem keyMomentRowsAt695 : keyMomentRows (695 : Fin 2886) =
    keyMomentRow695 := by decide +kernel

theorem keyMomentRowsAt696 : keyMomentRows (696 : Fin 2886) =
    keyMomentRow696 := by decide +kernel

theorem keyMomentRowsAt697 : keyMomentRows (697 : Fin 2886) =
    keyMomentRow697 := by decide +kernel

theorem keyMomentRowsAt698 : keyMomentRows (698 : Fin 2886) =
    keyMomentRow698 := by decide +kernel

theorem keyMomentRowsAt699 : keyMomentRows (699 : Fin 2886) =
    keyMomentRow699 := by decide +kernel

theorem keyMomentRowsAt700 : keyMomentRows (700 : Fin 2886) =
    keyMomentRow700 := by decide +kernel

theorem keyMomentRowsAt701 : keyMomentRows (701 : Fin 2886) =
    keyMomentRow701 := by decide +kernel

theorem keyMomentRowsAt702 : keyMomentRows (702 : Fin 2886) =
    keyMomentRow702 := by decide +kernel

theorem keyMomentRowsAt703 : keyMomentRows (703 : Fin 2886) =
    keyMomentRow703 := by decide +kernel

theorem keyMomentChunkSound21_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 21) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 672 ∨ k.val = 673 ∨ k.val = 674 ∨ k.val = 675 ∨ k.val = 676 ∨ k.val = 677 ∨ k.val = 678 ∨ k.val = 679 ∨ k.val = 680 ∨ k.val = 681 ∨ k.val = 682 ∨ k.val = 683 ∨ k.val = 684 ∨ k.val = 685 ∨ k.val = 686 ∨ k.val = 687 ∨ k.val = 688 ∨ k.val = 689 ∨ k.val = 690 ∨ k.val = 691 ∨ k.val = 692 ∨ k.val = 693 ∨ k.val = 694 ∨ k.val = 695 ∨ k.val = 696 ∨ k.val = 697 ∨ k.val = 698 ∨ k.val = 699 ∨ k.val = 700 ∨ k.val = 701 ∨ k.val = 702 ∨ k.val = 703 := by omega
  rcases heq with h672 | h673 | h674 | h675 | h676 | h677 | h678 | h679 | h680 | h681 | h682 | h683 | h684 | h685 | h686 | h687 | h688 | h689 | h690 | h691 | h692 | h693 | h694 | h695 | h696 | h697 | h698 | h699 | h700 | h701 | h702 | h703
  · have he : k = (672 : Fin 2886) := Fin.ext h672
    subst k
    rw [keyMomentRowsAt672]
    exact keyMoment672 B hB
  · have he : k = (673 : Fin 2886) := Fin.ext h673
    subst k
    rw [keyMomentRowsAt673]
    exact keyMoment673 B hB
  · have he : k = (674 : Fin 2886) := Fin.ext h674
    subst k
    rw [keyMomentRowsAt674]
    exact keyMoment674 B hB
  · have he : k = (675 : Fin 2886) := Fin.ext h675
    subst k
    rw [keyMomentRowsAt675]
    exact keyMoment675 B hB
  · have he : k = (676 : Fin 2886) := Fin.ext h676
    subst k
    rw [keyMomentRowsAt676]
    exact keyMoment676 B hB
  · have he : k = (677 : Fin 2886) := Fin.ext h677
    subst k
    rw [keyMomentRowsAt677]
    exact keyMoment677 B hB
  · have he : k = (678 : Fin 2886) := Fin.ext h678
    subst k
    rw [keyMomentRowsAt678]
    exact keyMoment678 B hB
  · have he : k = (679 : Fin 2886) := Fin.ext h679
    subst k
    rw [keyMomentRowsAt679]
    exact keyMoment679 B hB
  · have he : k = (680 : Fin 2886) := Fin.ext h680
    subst k
    rw [keyMomentRowsAt680]
    exact keyMoment680 B hB
  · have he : k = (681 : Fin 2886) := Fin.ext h681
    subst k
    rw [keyMomentRowsAt681]
    exact keyMoment681 B hB
  · have he : k = (682 : Fin 2886) := Fin.ext h682
    subst k
    rw [keyMomentRowsAt682]
    exact keyMoment682 B hB
  · have he : k = (683 : Fin 2886) := Fin.ext h683
    subst k
    rw [keyMomentRowsAt683]
    exact keyMoment683 B hB
  · have he : k = (684 : Fin 2886) := Fin.ext h684
    subst k
    rw [keyMomentRowsAt684]
    exact keyMoment684 B hB
  · have he : k = (685 : Fin 2886) := Fin.ext h685
    subst k
    rw [keyMomentRowsAt685]
    exact keyMoment685 B hB
  · have he : k = (686 : Fin 2886) := Fin.ext h686
    subst k
    rw [keyMomentRowsAt686]
    exact keyMoment686 B hB
  · have he : k = (687 : Fin 2886) := Fin.ext h687
    subst k
    rw [keyMomentRowsAt687]
    exact keyMoment687 B hB
  · have he : k = (688 : Fin 2886) := Fin.ext h688
    subst k
    rw [keyMomentRowsAt688]
    exact keyMoment688 B hB
  · have he : k = (689 : Fin 2886) := Fin.ext h689
    subst k
    rw [keyMomentRowsAt689]
    exact keyMoment689 B hB
  · have he : k = (690 : Fin 2886) := Fin.ext h690
    subst k
    rw [keyMomentRowsAt690]
    exact keyMoment690 B hB
  · have he : k = (691 : Fin 2886) := Fin.ext h691
    subst k
    rw [keyMomentRowsAt691]
    exact keyMoment691 B hB
  · have he : k = (692 : Fin 2886) := Fin.ext h692
    subst k
    rw [keyMomentRowsAt692]
    exact keyMoment692 B hB
  · have he : k = (693 : Fin 2886) := Fin.ext h693
    subst k
    rw [keyMomentRowsAt693]
    exact keyMoment693 B hB
  · have he : k = (694 : Fin 2886) := Fin.ext h694
    subst k
    rw [keyMomentRowsAt694]
    exact keyMoment694 B hB
  · have he : k = (695 : Fin 2886) := Fin.ext h695
    subst k
    rw [keyMomentRowsAt695]
    exact keyMoment695 B hB
  · have he : k = (696 : Fin 2886) := Fin.ext h696
    subst k
    rw [keyMomentRowsAt696]
    exact keyMoment696 B hB
  · have he : k = (697 : Fin 2886) := Fin.ext h697
    subst k
    rw [keyMomentRowsAt697]
    exact keyMoment697 B hB
  · have he : k = (698 : Fin 2886) := Fin.ext h698
    subst k
    rw [keyMomentRowsAt698]
    exact keyMoment698 B hB
  · have he : k = (699 : Fin 2886) := Fin.ext h699
    subst k
    rw [keyMomentRowsAt699]
    exact keyMoment699 B hB
  · have he : k = (700 : Fin 2886) := Fin.ext h700
    subst k
    rw [keyMomentRowsAt700]
    exact keyMoment700 B hB
  · have he : k = (701 : Fin 2886) := Fin.ext h701
    subst k
    rw [keyMomentRowsAt701]
    exact keyMoment701 B hB
  · have he : k = (702 : Fin 2886) := Fin.ext h702
    subst k
    rw [keyMomentRowsAt702]
    exact keyMoment702 B hB
  · have he : k = (703 : Fin 2886) := Fin.ext h703
    subst k
    rw [keyMomentRowsAt703]
    exact keyMoment703 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound21_e_oai
