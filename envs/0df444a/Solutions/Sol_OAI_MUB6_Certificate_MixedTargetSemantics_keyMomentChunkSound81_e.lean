-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:04:23.960213+00:00
-- url     : https://prove2.me/submissions/99c9d994-b2f7-48e1-9577-1bedc5f3bb0a

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

theorem canonical42496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42496 raw42496Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw42496 raw42496Labels = mixedMoment B raw42496step0 raw42496step0Labels := by
      have ha : raw42496step0 = (fun i j => raw42496 (permutation420 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42496step0 raw42496; decide +kernel
      have hl : raw42496step0Labels = raw42496Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42496 raw42496Labels permutation420 permutation4
    mixedMoment B raw42496step0 raw42496step0Labels = mixedMoment B raw42496step1 raw42496step1Labels := by
      have ha : raw42496step1 = -raw42496step0 := by apply Matrix.ext; change ∀ i j, raw42496step1 i j = -(raw42496step0 i j); unfold raw42496step1 raw42496step0; decide +kernel
      have hl : raw42496step1Labels = raw42496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42496step1 raw42496step1Labels = mixedMoment B raw42496step2 raw42496step2Labels := by
      have ha : raw42496step2 = raw42496step1 := by apply Matrix.ext; unfold raw42496step2 raw42496step1; decide +kernel
      have hl : raw42496step1Labels = labelEmbedding1 ∘ raw42496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42496step1 raw42496step1Labels raw42496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

theorem canonical42497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42497 raw42497Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw42497 raw42497Labels = mixedMoment B raw42497step0 raw42497step0Labels := by
      have ha : raw42497step0 = (fun i j => raw42497 (permutation430 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42497step0 raw42497; decide +kernel
      have hl : raw42497step0Labels = raw42497Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42497 raw42497Labels permutation430 permutation6
    _ = mixedMoment B node4665 node4665Labels := by rfl

theorem canonical42498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42498 raw42498Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw42498 raw42498Labels = mixedMoment B raw42498step0 raw42498step0Labels := by
      have ha : raw42498step0 = (fun i j => raw42498 (permutation391 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42498step0 raw42498; decide +kernel
      have hl : raw42498step0Labels = raw42498Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42498 raw42498Labels permutation391 permutation4
    mixedMoment B raw42498step0 raw42498step0Labels = mixedMoment B raw42498step1 raw42498step1Labels := by
      have ha : raw42498step1 = -raw42498step0 := by apply Matrix.ext; change ∀ i j, raw42498step1 i j = -(raw42498step0 i j); unfold raw42498step1 raw42498step0; decide +kernel
      have hl : raw42498step1Labels = raw42498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42498step1 raw42498step1Labels = mixedMoment B raw42498step2 raw42498step2Labels := by
      have ha : raw42498step2 = raw42498step1 := by apply Matrix.ext; unfold raw42498step2 raw42498step1; decide +kernel
      have hl : raw42498step1Labels = labelEmbedding1 ∘ raw42498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42498step1 raw42498step1Labels raw42498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

theorem canonical42499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42499 raw42499Labels = mixedMoment B node4762 node4762Labels := by
  calc
    mixedMoment B raw42499 raw42499Labels = mixedMoment B raw42499step0 raw42499step0Labels := by
      have ha : raw42499step0 = (fun i j => raw42499 (permutation391 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42499step0 raw42499; decide +kernel
      have hl : raw42499step0Labels = raw42499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42499 raw42499Labels permutation391 permutation6
    _ = mixedMoment B node4762 node4762Labels := by rfl

theorem canonical42500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42500 raw42500Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw42500 raw42500Labels = mixedMoment B raw42500step0 raw42500step0Labels := by
      have ha : raw42500step0 = (fun i j => raw42500 (permutation385 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42500step0 raw42500; decide +kernel
      have hl : raw42500step0Labels = raw42500Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42500 raw42500Labels permutation385 permutation4
    mixedMoment B raw42500step0 raw42500step0Labels = mixedMoment B raw42500step1 raw42500step1Labels := by
      have ha : raw42500step1 = -raw42500step0 := by apply Matrix.ext; change ∀ i j, raw42500step1 i j = -(raw42500step0 i j); unfold raw42500step1 raw42500step0; decide +kernel
      have hl : raw42500step1Labels = raw42500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42500step1 raw42500step1Labels = mixedMoment B raw42500step2 raw42500step2Labels := by
      have ha : raw42500step2 = raw42500step1 := by apply Matrix.ext; unfold raw42500step2 raw42500step1; decide +kernel
      have hl : raw42500step1Labels = labelEmbedding1 ∘ raw42500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42500step1 raw42500step1Labels raw42500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

theorem canonical42501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42501 raw42501Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw42501 raw42501Labels = mixedMoment B raw42501step0 raw42501step0Labels := by
      have ha : raw42501step0 = (fun i j => raw42501 (permutation392 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42501step0 raw42501; decide +kernel
      have hl : raw42501step0Labels = raw42501Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42501 raw42501Labels permutation392 permutation6
    _ = mixedMoment B node4803 node4803Labels := by rfl

theorem canonical42502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42502 raw42502Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw42502 raw42502Labels = mixedMoment B raw42502step0 raw42502step0Labels := by
      have ha : raw42502step0 = (fun i j => raw42502 (permutation367 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42502step0 raw42502; decide +kernel
      have hl : raw42502step0Labels = raw42502Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42502 raw42502Labels permutation367 permutation4
    mixedMoment B raw42502step0 raw42502step0Labels = mixedMoment B raw42502step1 raw42502step1Labels := by
      have ha : raw42502step1 = -raw42502step0 := by apply Matrix.ext; change ∀ i j, raw42502step1 i j = -(raw42502step0 i j); unfold raw42502step1 raw42502step0; decide +kernel
      have hl : raw42502step1Labels = raw42502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42502step1 raw42502step1Labels = mixedMoment B raw42502step2 raw42502step2Labels := by
      have ha : raw42502step2 = raw42502step1 := by apply Matrix.ext; unfold raw42502step2 raw42502step1; decide +kernel
      have hl : raw42502step1Labels = labelEmbedding1 ∘ raw42502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42502step1 raw42502step1Labels raw42502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

theorem canonical42503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42503 raw42503Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw42503 raw42503Labels = mixedMoment B raw42503step0 raw42503step0Labels := by
      have ha : raw42503step0 = (fun i j => raw42503 (permutation394 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42503step0 raw42503; decide +kernel
      have hl : raw42503step0Labels = raw42503Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42503 raw42503Labels permutation394 permutation6
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical42504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42504 raw42504Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw42504 raw42504Labels = mixedMoment B raw42504step0 raw42504step0Labels := by
      have hz : ∀ j, raw42504 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42504step0 = (fun i j => raw42504 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42504step0 raw42504; decide +kernel
      have hl : raw42504step0Labels = raw42504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42504 raw42504Labels permutation520 hz
    mixedMoment B raw42504step0 raw42504step0Labels = mixedMoment B raw42504step1 raw42504step1Labels := by
      have ha : raw42504step1 = (fun i j => raw42504step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42504step1 raw42504step0; decide +kernel
      have hl : raw42504step1Labels = raw42504step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42504step0 raw42504step0Labels permutation145 permutation2
    mixedMoment B raw42504step1 raw42504step1Labels = mixedMoment B raw42504step2 raw42504step2Labels := by
      have ha : raw42504step2 = -raw42504step1 := by apply Matrix.ext; change ∀ i j, raw42504step2 i j = -(raw42504step1 i j); unfold raw42504step2 raw42504step1; decide +kernel
      have hl : raw42504step2Labels = raw42504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42504step2 raw42504step2Labels = mixedMoment B raw42504step3 raw42504step3Labels := by
      have ha : raw42504step3 = raw42504step2 := by apply Matrix.ext; unfold raw42504step3 raw42504step2; decide +kernel
      have hl : raw42504step2Labels = labelEmbedding1 ∘ raw42504step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42504step2 raw42504step2Labels raw42504step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3222 node3222Labels := by rfl

theorem canonical42505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42505 raw42505Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw42505 raw42505Labels = mixedMoment B raw42505step0 raw42505step0Labels := by
      have hz : ∀ j, raw42505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42505step0 = (fun i j => raw42505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42505step0 raw42505; decide +kernel
      have hl : raw42505step0Labels = raw42505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42505 raw42505Labels permutation520 hz
    mixedMoment B raw42505step0 raw42505step0Labels = mixedMoment B raw42505step1 raw42505step1Labels := by
      have ha : raw42505step1 = (fun i j => raw42505step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42505step1 raw42505step0; decide +kernel
      have hl : raw42505step1Labels = raw42505step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42505step0 raw42505step0Labels permutation151 permutation3
    mixedMoment B raw42505step1 raw42505step1Labels = mixedMoment B raw42505step2 raw42505step2Labels := by
      have ha : raw42505step2 = -raw42505step1 := by apply Matrix.ext; change ∀ i j, raw42505step2 i j = -(raw42505step1 i j); unfold raw42505step2 raw42505step1; decide +kernel
      have hl : raw42505step2Labels = raw42505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42505step2 raw42505step2Labels = mixedMoment B raw42505step3 raw42505step3Labels := by
      have ha : raw42505step3 = raw42505step2 := by apply Matrix.ext; unfold raw42505step3 raw42505step2; decide +kernel
      have hl : raw42505step2Labels = labelEmbedding7 ∘ raw42505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42505step2 raw42505step2Labels raw42505step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

theorem canonical42506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42506 raw42506Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw42506 raw42506Labels = mixedMoment B raw42506step0 raw42506step0Labels := by
      have ha : raw42506step0 = (fun i j => raw42506 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42506step0 raw42506; decide +kernel
      have hl : raw42506step0Labels = raw42506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42506 raw42506Labels permutation594 permutation4
    mixedMoment B raw42506step0 raw42506step0Labels = mixedMoment B raw42506step1 raw42506step1Labels := by
      have ha : raw42506step1 = raw42506step0 := by apply Matrix.ext; unfold raw42506step1 raw42506step0; decide +kernel
      have hl : raw42506step0Labels = labelEmbedding1 ∘ raw42506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42506step0 raw42506step0Labels raw42506step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

theorem canonical42507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42507 raw42507Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw42507 raw42507Labels = mixedMoment B raw42507step0 raw42507step0Labels := by
      have ha : raw42507step0 = (fun i j => raw42507 (permutation672 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42507step0 raw42507; decide +kernel
      have hl : raw42507step0Labels = raw42507Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42507 raw42507Labels permutation672 permutation5
    mixedMoment B raw42507step0 raw42507step0Labels = mixedMoment B raw42507step1 raw42507step1Labels := by
      have ha : raw42507step1 = raw42507step0 := by apply Matrix.ext; unfold raw42507step1 raw42507step0; decide +kernel
      have hl : raw42507step0Labels = labelEmbedding9 ∘ raw42507step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42507step0 raw42507step0Labels raw42507step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

theorem canonical42508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42508 raw42508Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw42508 raw42508Labels = mixedMoment B raw42508step0 raw42508step0Labels := by
      have ha : raw42508step0 = (fun i j => raw42508 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42508step0 raw42508; decide +kernel
      have hl : raw42508step0Labels = raw42508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42508 raw42508Labels permutation158 permutation2
    mixedMoment B raw42508step0 raw42508step0Labels = mixedMoment B raw42508step1 raw42508step1Labels := by
      have ha : raw42508step1 = raw42508step0 := by apply Matrix.ext; unfold raw42508step1 raw42508step0; decide +kernel
      have hl : raw42508step0Labels = labelEmbedding1 ∘ raw42508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42508step0 raw42508step0Labels raw42508step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

theorem canonical42509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42509 raw42509Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw42509 raw42509Labels = mixedMoment B raw42509step0 raw42509step0Labels := by
      have ha : raw42509step0 = (fun i j => raw42509 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42509step0 raw42509; decide +kernel
      have hl : raw42509step0Labels = raw42509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42509 raw42509Labels permutation158 permutation2
    mixedMoment B raw42509step0 raw42509step0Labels = mixedMoment B raw42509step1 raw42509step1Labels := by
      have ha : raw42509step1 = raw42509step0 := by apply Matrix.ext; unfold raw42509step1 raw42509step0; decide +kernel
      have hl : raw42509step0Labels = labelEmbedding8 ∘ raw42509step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42509step0 raw42509step0Labels raw42509step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5407 node5407Labels := by rfl

theorem canonical42510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42510 raw42510Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw42510 raw42510Labels = mixedMoment B raw42510step0 raw42510step0Labels := by
      have ha : raw42510step0 = (fun i j => raw42510 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42510step0 raw42510; decide +kernel
      have hl : raw42510step0Labels = raw42510Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42510 raw42510Labels permutation158 permutation2
    mixedMoment B raw42510step0 raw42510step0Labels = mixedMoment B raw42510step1 raw42510step1Labels := by
      have ha : raw42510step1 = raw42510step0 := by apply Matrix.ext; unfold raw42510step1 raw42510step0; decide +kernel
      have hl : raw42510step0Labels = labelEmbedding1 ∘ raw42510step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42510step0 raw42510step0Labels raw42510step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

theorem canonical42511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42511 raw42511Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw42511 raw42511Labels = mixedMoment B raw42511step0 raw42511step0Labels := by
      have ha : raw42511step0 = (fun i j => raw42511 (permutation397 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42511step0 raw42511; decide +kernel
      have hl : raw42511step0Labels = raw42511Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42511 raw42511Labels permutation397 permutation6
    _ = mixedMoment B node5402 node5402Labels := by rfl

theorem canonical42512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42512 raw42512Labels = mixedMoment B node2654 node2654Labels := by
  calc
    mixedMoment B raw42512 raw42512Labels = mixedMoment B raw42512step0 raw42512step0Labels := by
      have ha : raw42512step0 = (fun i j => raw42512 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42512step0 raw42512; decide +kernel
      have hl : raw42512step0Labels = raw42512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42512 raw42512Labels permutation525 permutation4
    mixedMoment B raw42512step0 raw42512step0Labels = mixedMoment B raw42512step1 raw42512step1Labels := by
      have ha : raw42512step1 = raw42512step0 := by apply Matrix.ext; unfold raw42512step1 raw42512step0; decide +kernel
      have hl : raw42512step0Labels = labelEmbedding1 ∘ raw42512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42512step0 raw42512step0Labels raw42512step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2654 node2654Labels := by rfl

theorem canonical42513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42513 raw42513Labels = mixedMoment B node5216 node5216Labels := by
  calc
    mixedMoment B raw42513 raw42513Labels = mixedMoment B raw42513step0 raw42513step0Labels := by
      have ha : raw42513step0 = (fun i j => raw42513 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42513step0 raw42513; decide +kernel
      have hl : raw42513step0Labels = raw42513Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42513 raw42513Labels permutation525 permutation4
    mixedMoment B raw42513step0 raw42513step0Labels = mixedMoment B raw42513step1 raw42513step1Labels := by
      have ha : raw42513step1 = raw42513step0 := by apply Matrix.ext; unfold raw42513step1 raw42513step0; decide +kernel
      have hl : raw42513step0Labels = labelEmbedding10 ∘ raw42513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42513step0 raw42513step0Labels raw42513step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5216 node5216Labels := by rfl

theorem canonical42514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42514 raw42514Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw42514 raw42514Labels = mixedMoment B raw42514step0 raw42514step0Labels := by
      have hz : ∀ j, raw42514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42514step0 = (fun i j => raw42514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42514step0 raw42514; decide +kernel
      have hl : raw42514step0Labels = raw42514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42514 raw42514Labels permutation434 hz
    mixedMoment B raw42514step0 raw42514step0Labels = mixedMoment B raw42514step1 raw42514step1Labels := by
      have ha : raw42514step1 = (fun i j => raw42514step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42514step1 raw42514step0; decide +kernel
      have hl : raw42514step1Labels = raw42514step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42514step0 raw42514step0Labels permutation129 permutation4
    mixedMoment B raw42514step1 raw42514step1Labels = mixedMoment B raw42514step2 raw42514step2Labels := by
      have ha : raw42514step2 = raw42514step1 := by apply Matrix.ext; unfold raw42514step2 raw42514step1; decide +kernel
      have hl : raw42514step1Labels = labelEmbedding1 ∘ raw42514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42514step1 raw42514step1Labels raw42514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

theorem canonical42515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42515 raw42515Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw42515 raw42515Labels = mixedMoment B raw42515step0 raw42515step0Labels := by
      have hz : ∀ j, raw42515 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42515step0 = (fun i j => raw42515 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42515step0 raw42515; decide +kernel
      have hl : raw42515step0Labels = raw42515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42515 raw42515Labels permutation434 hz
    mixedMoment B raw42515step0 raw42515step0Labels = mixedMoment B raw42515step1 raw42515step1Labels := by
      have ha : raw42515step1 = (fun i j => raw42515step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42515step1 raw42515step0; decide +kernel
      have hl : raw42515step1Labels = raw42515step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42515step0 raw42515step0Labels permutation135 permutation5
    mixedMoment B raw42515step1 raw42515step1Labels = mixedMoment B raw42515step2 raw42515step2Labels := by
      have ha : raw42515step2 = raw42515step1 := by apply Matrix.ext; unfold raw42515step2 raw42515step1; decide +kernel
      have hl : raw42515step1Labels = labelEmbedding9 ∘ raw42515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42515step1 raw42515step1Labels raw42515step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

theorem canonical42516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42516 raw42516Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw42516 raw42516Labels = mixedMoment B raw42516step0 raw42516step0Labels := by
      have hz : ∀ j, raw42516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42516step0 = (fun i j => raw42516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42516step0 raw42516; decide +kernel
      have hl : raw42516step0Labels = raw42516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42516 raw42516Labels permutation434 hz
    mixedMoment B raw42516step0 raw42516step0Labels = mixedMoment B raw42516step1 raw42516step1Labels := by
      have ha : raw42516step1 = (fun i j => raw42516step0 (permutation105 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42516step1 raw42516step0; decide +kernel
      have hl : raw42516step1Labels = raw42516step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42516step0 raw42516step0Labels permutation105 permutation4
    mixedMoment B raw42516step1 raw42516step1Labels = mixedMoment B raw42516step2 raw42516step2Labels := by
      have ha : raw42516step2 = raw42516step1 := by apply Matrix.ext; unfold raw42516step2 raw42516step1; decide +kernel
      have hl : raw42516step1Labels = labelEmbedding1 ∘ raw42516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42516step1 raw42516step1Labels raw42516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

theorem canonical42517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42517 raw42517Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw42517 raw42517Labels = mixedMoment B raw42517step0 raw42517step0Labels := by
      have hz : ∀ j, raw42517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42517step0 = (fun i j => raw42517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42517step0 raw42517; decide +kernel
      have hl : raw42517step0Labels = raw42517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42517 raw42517Labels permutation434 hz
    mixedMoment B raw42517step0 raw42517step0Labels = mixedMoment B raw42517step1 raw42517step1Labels := by
      have ha : raw42517step1 = (fun i j => raw42517step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42517step1 raw42517step0; decide +kernel
      have hl : raw42517step1Labels = raw42517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42517step0 raw42517step0Labels permutation143 permutation7
    mixedMoment B raw42517step1 raw42517step1Labels = mixedMoment B raw42517step2 raw42517step2Labels := by
      have ha : raw42517step2 = raw42517step1 := by apply Matrix.ext; unfold raw42517step2 raw42517step1; decide +kernel
      have hl : raw42517step1Labels = labelEmbedding6 ∘ raw42517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42517step1 raw42517step1Labels raw42517step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4976 node4976Labels := by rfl

theorem canonical42518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42518 raw42518Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw42518 raw42518Labels = mixedMoment B raw42518step0 raw42518step0Labels := by
      have ha : raw42518step0 = (fun i j => raw42518 (permutation403 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42518step0 raw42518; decide +kernel
      have hl : raw42518step0Labels = raw42518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42518 raw42518Labels permutation403 permutation4
    mixedMoment B raw42518step0 raw42518step0Labels = mixedMoment B raw42518step1 raw42518step1Labels := by
      have ha : raw42518step1 = -raw42518step0 := by apply Matrix.ext; change ∀ i j, raw42518step1 i j = -(raw42518step0 i j); unfold raw42518step1 raw42518step0; decide +kernel
      have hl : raw42518step1Labels = raw42518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42518step1 raw42518step1Labels = mixedMoment B raw42518step2 raw42518step2Labels := by
      have ha : raw42518step2 = raw42518step1 := by apply Matrix.ext; unfold raw42518step2 raw42518step1; decide +kernel
      have hl : raw42518step1Labels = labelEmbedding1 ∘ raw42518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42518step1 raw42518step1Labels raw42518step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

theorem canonical42519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42519 raw42519Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw42519 raw42519Labels = mixedMoment B raw42519step0 raw42519step0Labels := by
      have ha : raw42519step0 = (fun i j => raw42519 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42519step0 raw42519; decide +kernel
      have hl : raw42519step0Labels = raw42519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42519 raw42519Labels permutation412 permutation6
    _ = mixedMoment B node5360 node5360Labels := by rfl

theorem canonical42520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42520 raw42520Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw42520 raw42520Labels = mixedMoment B raw42520step0 raw42520step0Labels := by
      have ha : raw42520step0 = (fun i j => raw42520 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42520step0 raw42520; decide +kernel
      have hl : raw42520step0Labels = raw42520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42520 raw42520Labels permutation682 permutation2
    mixedMoment B raw42520step0 raw42520step0Labels = mixedMoment B raw42520step1 raw42520step1Labels := by
      have ha : raw42520step1 = -raw42520step0 := by apply Matrix.ext; change ∀ i j, raw42520step1 i j = -(raw42520step0 i j); unfold raw42520step1 raw42520step0; decide +kernel
      have hl : raw42520step1Labels = raw42520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42520step1 raw42520step1Labels = mixedMoment B raw42520step2 raw42520step2Labels := by
      have ha : raw42520step2 = raw42520step1 := by apply Matrix.ext; unfold raw42520step2 raw42520step1; decide +kernel
      have hl : raw42520step1Labels = labelEmbedding1 ∘ raw42520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42520step1 raw42520step1Labels raw42520step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

theorem canonical42521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42521 raw42521Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw42521 raw42521Labels = mixedMoment B raw42521step0 raw42521step0Labels := by
      have ha : raw42521step0 = (fun i j => raw42521 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42521step0 raw42521; decide +kernel
      have hl : raw42521step0Labels = raw42521Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42521 raw42521Labels permutation646 permutation7
    mixedMoment B raw42521step0 raw42521step0Labels = mixedMoment B raw42521step1 raw42521step1Labels := by
      have ha : raw42521step1 = raw42521step0 := by apply Matrix.ext; unfold raw42521step1 raw42521step0; decide +kernel
      have hl : raw42521step0Labels = labelEmbedding6 ∘ raw42521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42521step0 raw42521step0Labels raw42521step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4963 node4963Labels := by rfl

theorem canonical42522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42522 raw42522Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw42522 raw42522Labels = mixedMoment B raw42522step0 raw42522step0Labels := by
      have ha : raw42522step0 = (fun i j => raw42522 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42522step0 raw42522; decide +kernel
      have hl : raw42522step0Labels = raw42522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42522 raw42522Labels permutation682 permutation2
    mixedMoment B raw42522step0 raw42522step0Labels = mixedMoment B raw42522step1 raw42522step1Labels := by
      have ha : raw42522step1 = -raw42522step0 := by apply Matrix.ext; change ∀ i j, raw42522step1 i j = -(raw42522step0 i j); unfold raw42522step1 raw42522step0; decide +kernel
      have hl : raw42522step1Labels = raw42522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42522step1 raw42522step1Labels = mixedMoment B raw42522step2 raw42522step2Labels := by
      have ha : raw42522step2 = raw42522step1 := by apply Matrix.ext; unfold raw42522step2 raw42522step1; decide +kernel
      have hl : raw42522step1Labels = labelEmbedding1 ∘ raw42522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42522step1 raw42522step1Labels raw42522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

theorem canonical42523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42523 raw42523Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw42523 raw42523Labels = mixedMoment B raw42523step0 raw42523step0Labels := by
      have ha : raw42523step0 = (fun i j => raw42523 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42523step0 raw42523; decide +kernel
      have hl : raw42523step0Labels = raw42523Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42523 raw42523Labels permutation644 permutation7
    mixedMoment B raw42523step0 raw42523step0Labels = mixedMoment B raw42523step1 raw42523step1Labels := by
      have ha : raw42523step1 = raw42523step0 := by apply Matrix.ext; unfold raw42523step1 raw42523step0; decide +kernel
      have hl : raw42523step0Labels = labelEmbedding6 ∘ raw42523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42523step0 raw42523step0Labels raw42523step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4957 node4957Labels := by rfl

theorem canonical42524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42524 raw42524Labels = mixedMoment B node2653 node2653Labels := by
  calc
    mixedMoment B raw42524 raw42524Labels = mixedMoment B raw42524step0 raw42524step0Labels := by
      have ha : raw42524step0 = (fun i j => raw42524 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42524step0 raw42524; decide +kernel
      have hl : raw42524step0Labels = raw42524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42524 raw42524Labels permutation594 permutation4
    mixedMoment B raw42524step0 raw42524step0Labels = mixedMoment B raw42524step1 raw42524step1Labels := by
      have ha : raw42524step1 = raw42524step0 := by apply Matrix.ext; unfold raw42524step1 raw42524step0; decide +kernel
      have hl : raw42524step0Labels = labelEmbedding1 ∘ raw42524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42524step0 raw42524step0Labels raw42524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2653 node2653Labels := by rfl

theorem canonical42525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42525 raw42525Labels = mixedMoment B node5215 node5215Labels := by
  calc
    mixedMoment B raw42525 raw42525Labels = mixedMoment B raw42525step0 raw42525step0Labels := by
      have ha : raw42525step0 = (fun i j => raw42525 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42525step0 raw42525; decide +kernel
      have hl : raw42525step0Labels = raw42525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42525 raw42525Labels permutation594 permutation4
    mixedMoment B raw42525step0 raw42525step0Labels = mixedMoment B raw42525step1 raw42525step1Labels := by
      have ha : raw42525step1 = raw42525step0 := by apply Matrix.ext; unfold raw42525step1 raw42525step0; decide +kernel
      have hl : raw42525step0Labels = labelEmbedding10 ∘ raw42525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42525step0 raw42525step0Labels raw42525step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5215 node5215Labels := by rfl

theorem canonical42526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42526 raw42526Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw42526 raw42526Labels = mixedMoment B raw42526step0 raw42526step0Labels := by
      have ha : raw42526step0 = (fun i j => raw42526 (permutation385 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42526step0 raw42526; decide +kernel
      have hl : raw42526step0Labels = raw42526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42526 raw42526Labels permutation385 permutation4
    mixedMoment B raw42526step0 raw42526step0Labels = mixedMoment B raw42526step1 raw42526step1Labels := by
      have ha : raw42526step1 = -raw42526step0 := by apply Matrix.ext; change ∀ i j, raw42526step1 i j = -(raw42526step0 i j); unfold raw42526step1 raw42526step0; decide +kernel
      have hl : raw42526step1Labels = raw42526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42526step1 raw42526step1Labels = mixedMoment B raw42526step2 raw42526step2Labels := by
      have ha : raw42526step2 = raw42526step1 := by apply Matrix.ext; unfold raw42526step2 raw42526step1; decide +kernel
      have hl : raw42526step1Labels = labelEmbedding1 ∘ raw42526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42526step1 raw42526step1Labels raw42526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

theorem canonical42527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42527 raw42527Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw42527 raw42527Labels = mixedMoment B raw42527step0 raw42527step0Labels := by
      have ha : raw42527step0 = (fun i j => raw42527 (permutation392 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42527step0 raw42527; decide +kernel
      have hl : raw42527step0Labels = raw42527Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42527 raw42527Labels permutation392 permutation6
    _ = mixedMoment B node5353 node5353Labels := by rfl

theorem canonical42528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42528 raw42528Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw42528 raw42528Labels = mixedMoment B raw42528step0 raw42528step0Labels := by
      have ha : raw42528step0 = (fun i j => raw42528 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42528step0 raw42528; decide +kernel
      have hl : raw42528step0Labels = raw42528Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42528 raw42528Labels permutation590 permutation4
    mixedMoment B raw42528step0 raw42528step0Labels = mixedMoment B raw42528step1 raw42528step1Labels := by
      have ha : raw42528step1 = raw42528step0 := by apply Matrix.ext; unfold raw42528step1 raw42528step0; decide +kernel
      have hl : raw42528step0Labels = labelEmbedding1 ∘ raw42528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42528step0 raw42528step0Labels raw42528step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

theorem canonical42529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42529 raw42529Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw42529 raw42529Labels = mixedMoment B raw42529step0 raw42529step0Labels := by
      have ha : raw42529step0 = (fun i j => raw42529 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42529step0 raw42529; decide +kernel
      have hl : raw42529step0Labels = raw42529Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42529 raw42529Labels permutation640 permutation3
    mixedMoment B raw42529step0 raw42529step0Labels = mixedMoment B raw42529step1 raw42529step1Labels := by
      have ha : raw42529step1 = -raw42529step0 := by apply Matrix.ext; change ∀ i j, raw42529step1 i j = -(raw42529step0 i j); unfold raw42529step1 raw42529step0; decide +kernel
      have hl : raw42529step1Labels = raw42529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42529step1 raw42529step1Labels = mixedMoment B raw42529step2 raw42529step2Labels := by
      have ha : raw42529step2 = raw42529step1 := by apply Matrix.ext; unfold raw42529step2 raw42529step1; decide +kernel
      have hl : raw42529step1Labels = labelEmbedding7 ∘ raw42529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42529step1 raw42529step1Labels raw42529step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

theorem canonical42530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42530 raw42530Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw42530 raw42530Labels = mixedMoment B raw42530step0 raw42530step0Labels := by
      have ha : raw42530step0 = (fun i j => raw42530 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42530step0 raw42530; decide +kernel
      have hl : raw42530step0Labels = raw42530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42530 raw42530Labels permutation590 permutation4
    mixedMoment B raw42530step0 raw42530step0Labels = mixedMoment B raw42530step1 raw42530step1Labels := by
      have ha : raw42530step1 = raw42530step0 := by apply Matrix.ext; unfold raw42530step1 raw42530step0; decide +kernel
      have hl : raw42530step0Labels = labelEmbedding1 ∘ raw42530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42530step0 raw42530step0Labels raw42530step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

theorem canonical42531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42531 raw42531Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw42531 raw42531Labels = mixedMoment B raw42531step0 raw42531step0Labels := by
      have ha : raw42531step0 = (fun i j => raw42531 (permutation606 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42531step0 raw42531; decide +kernel
      have hl : raw42531step0Labels = raw42531Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42531 raw42531Labels permutation606 permutation5
    mixedMoment B raw42531step0 raw42531step0Labels = mixedMoment B raw42531step1 raw42531step1Labels := by
      have ha : raw42531step1 = raw42531step0 := by apply Matrix.ext; unfold raw42531step1 raw42531step0; decide +kernel
      have hl : raw42531step0Labels = labelEmbedding9 ∘ raw42531step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42531step0 raw42531step0Labels raw42531step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

theorem canonical42532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42532 raw42532Labels = mixedMoment B node2655 node2655Labels := by
  calc
    mixedMoment B raw42532 raw42532Labels = mixedMoment B raw42532step0 raw42532step0Labels := by
      have ha : raw42532step0 = (fun i j => raw42532 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42532step0 raw42532; decide +kernel
      have hl : raw42532step0Labels = raw42532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42532 raw42532Labels permutation520 permutation4
    mixedMoment B raw42532step0 raw42532step0Labels = mixedMoment B raw42532step1 raw42532step1Labels := by
      have ha : raw42532step1 = raw42532step0 := by apply Matrix.ext; unfold raw42532step1 raw42532step0; decide +kernel
      have hl : raw42532step0Labels = labelEmbedding1 ∘ raw42532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42532step0 raw42532step0Labels raw42532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2655 node2655Labels := by rfl

theorem canonical42533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42533 raw42533Labels = mixedMoment B node5116 node5116Labels := by
  calc
    mixedMoment B raw42533 raw42533Labels = mixedMoment B raw42533step0 raw42533step0Labels := by
      have ha : raw42533step0 = (fun i j => raw42533 (permutation638 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42533step0 raw42533; decide +kernel
      have hl : raw42533step0Labels = raw42533Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42533 raw42533Labels permutation638 permutation7
    mixedMoment B raw42533step0 raw42533step0Labels = mixedMoment B raw42533step1 raw42533step1Labels := by
      have ha : raw42533step1 = raw42533step0 := by apply Matrix.ext; unfold raw42533step1 raw42533step0; decide +kernel
      have hl : raw42533step0Labels = labelEmbedding6 ∘ raw42533step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42533step0 raw42533step0Labels raw42533step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5116 node5116Labels := by rfl

theorem canonical42534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42534 raw42534Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw42534 raw42534Labels = mixedMoment B raw42534step0 raw42534step0Labels := by
      have hz : ∀ j, raw42534 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42534step0 = (fun i j => raw42534 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42534step0 raw42534; decide +kernel
      have hl : raw42534step0Labels = raw42534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42534 raw42534Labels permutation434 hz
    mixedMoment B raw42534step0 raw42534step0Labels = mixedMoment B raw42534step1 raw42534step1Labels := by
      have ha : raw42534step1 = (fun i j => raw42534step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42534step1 raw42534step0; decide +kernel
      have hl : raw42534step1Labels = raw42534step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42534step0 raw42534step0Labels permutation128 permutation4
    mixedMoment B raw42534step1 raw42534step1Labels = mixedMoment B raw42534step2 raw42534step2Labels := by
      have ha : raw42534step2 = raw42534step1 := by apply Matrix.ext; unfold raw42534step2 raw42534step1; decide +kernel
      have hl : raw42534step1Labels = labelEmbedding1 ∘ raw42534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42534step1 raw42534step1Labels raw42534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

theorem canonical42535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42535 raw42535Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw42535 raw42535Labels = mixedMoment B raw42535step0 raw42535step0Labels := by
      have hz : ∀ j, raw42535 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42535step0 = (fun i j => raw42535 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42535step0 raw42535; decide +kernel
      have hl : raw42535step0Labels = raw42535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42535 raw42535Labels permutation434 hz
    mixedMoment B raw42535step0 raw42535step0Labels = mixedMoment B raw42535step1 raw42535step1Labels := by
      have ha : raw42535step1 = (fun i j => raw42535step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42535step1 raw42535step0; decide +kernel
      have hl : raw42535step1Labels = raw42535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42535step0 raw42535step0Labels permutation119 permutation6
    _ = mixedMoment B node5103 node5103Labels := by rfl

theorem canonical42536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42536 raw42536Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw42536 raw42536Labels = mixedMoment B raw42536step0 raw42536step0Labels := by
      have hz : ∀ j, raw42536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42536step0 = (fun i j => raw42536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42536step0 raw42536; decide +kernel
      have hl : raw42536step0Labels = raw42536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42536 raw42536Labels permutation434 hz
    mixedMoment B raw42536step0 raw42536step0Labels = mixedMoment B raw42536step1 raw42536step1Labels := by
      have ha : raw42536step1 = (fun i j => raw42536step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42536step1 raw42536step0; decide +kernel
      have hl : raw42536step1Labels = raw42536step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42536step0 raw42536step0Labels permutation104 permutation4
    mixedMoment B raw42536step1 raw42536step1Labels = mixedMoment B raw42536step2 raw42536step2Labels := by
      have ha : raw42536step2 = raw42536step1 := by apply Matrix.ext; unfold raw42536step2 raw42536step1; decide +kernel
      have hl : raw42536step1Labels = labelEmbedding1 ∘ raw42536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42536step1 raw42536step1Labels raw42536step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

theorem canonical42537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42537 raw42537Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw42537 raw42537Labels = mixedMoment B raw42537step0 raw42537step0Labels := by
      have hz : ∀ j, raw42537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42537step0 = (fun i j => raw42537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42537step0 raw42537; decide +kernel
      have hl : raw42537step0Labels = raw42537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42537 raw42537Labels permutation434 hz
    mixedMoment B raw42537step0 raw42537step0Labels = mixedMoment B raw42537step1 raw42537step1Labels := by
      have ha : raw42537step1 = (fun i j => raw42537step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42537step1 raw42537step0; decide +kernel
      have hl : raw42537step1Labels = raw42537step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42537step0 raw42537step0Labels permutation142 permutation6
    _ = mixedMoment B node4548 node4548Labels := by rfl

theorem canonical42538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42538 raw42538Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw42538 raw42538Labels = mixedMoment B raw42538step0 raw42538step0Labels := by
      have ha : raw42538step0 = (fun i j => raw42538 (permutation543 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42538step0 raw42538; decide +kernel
      have hl : raw42538step0Labels = raw42538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42538 raw42538Labels permutation543 permutation4
    mixedMoment B raw42538step0 raw42538step0Labels = mixedMoment B raw42538step1 raw42538step1Labels := by
      have ha : raw42538step1 = -raw42538step0 := by apply Matrix.ext; change ∀ i j, raw42538step1 i j = -(raw42538step0 i j); unfold raw42538step1 raw42538step0; decide +kernel
      have hl : raw42538step1Labels = raw42538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42538step1 raw42538step1Labels = mixedMoment B raw42538step2 raw42538step2Labels := by
      have ha : raw42538step2 = raw42538step1 := by apply Matrix.ext; unfold raw42538step2 raw42538step1; decide +kernel
      have hl : raw42538step1Labels = labelEmbedding1 ∘ raw42538step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42538step1 raw42538step1Labels raw42538step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

theorem canonical42539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42539 raw42539Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw42539 raw42539Labels = mixedMoment B raw42539step0 raw42539step0Labels := by
      have ha : raw42539step0 = (fun i j => raw42539 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42539step0 raw42539; decide +kernel
      have hl : raw42539step0Labels = raw42539Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42539 raw42539Labels permutation550 permutation6
    _ = mixedMoment B node5086 node5086Labels := by rfl

theorem canonical42540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42540 raw42540Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw42540 raw42540Labels = mixedMoment B raw42540step0 raw42540step0Labels := by
      have ha : raw42540step0 = (fun i j => raw42540 (permutation629 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42540step0 raw42540; decide +kernel
      have hl : raw42540step0Labels = raw42540Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42540 raw42540Labels permutation629 permutation4
    mixedMoment B raw42540step0 raw42540step0Labels = mixedMoment B raw42540step1 raw42540step1Labels := by
      have ha : raw42540step1 = -raw42540step0 := by apply Matrix.ext; change ∀ i j, raw42540step1 i j = -(raw42540step0 i j); unfold raw42540step1 raw42540step0; decide +kernel
      have hl : raw42540step1Labels = raw42540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42540step1 raw42540step1Labels = mixedMoment B raw42540step2 raw42540step2Labels := by
      have ha : raw42540step2 = raw42540step1 := by apply Matrix.ext; unfold raw42540step2 raw42540step1; decide +kernel
      have hl : raw42540step1Labels = labelEmbedding1 ∘ raw42540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42540step1 raw42540step1Labels raw42540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

theorem canonical42541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42541 raw42541Labels = mixedMoment B node4545 node4545Labels := by
  calc
    mixedMoment B raw42541 raw42541Labels = mixedMoment B raw42541step0 raw42541step0Labels := by
      have ha : raw42541step0 = (fun i j => raw42541 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42541step0 raw42541; decide +kernel
      have hl : raw42541step0Labels = raw42541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42541 raw42541Labels permutation632 permutation6
    _ = mixedMoment B node4545 node4545Labels := by rfl

theorem canonical42542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42542 raw42542Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw42542 raw42542Labels = mixedMoment B raw42542step0 raw42542step0Labels := by
      have ha : raw42542step0 = (fun i j => raw42542 (permutation630 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42542step0 raw42542; decide +kernel
      have hl : raw42542step0Labels = raw42542Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42542 raw42542Labels permutation630 permutation4
    mixedMoment B raw42542step0 raw42542step0Labels = mixedMoment B raw42542step1 raw42542step1Labels := by
      have ha : raw42542step1 = -raw42542step0 := by apply Matrix.ext; change ∀ i j, raw42542step1 i j = -(raw42542step0 i j); unfold raw42542step1 raw42542step0; decide +kernel
      have hl : raw42542step1Labels = raw42542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42542step1 raw42542step1Labels = mixedMoment B raw42542step2 raw42542step2Labels := by
      have ha : raw42542step2 = raw42542step1 := by apply Matrix.ext; unfold raw42542step2 raw42542step1; decide +kernel
      have hl : raw42542step1Labels = labelEmbedding1 ∘ raw42542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42542step1 raw42542step1Labels raw42542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

theorem canonical42543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42543 raw42543Labels = mixedMoment B node4529 node4529Labels := by
  calc
    mixedMoment B raw42543 raw42543Labels = mixedMoment B raw42543step0 raw42543step0Labels := by
      have ha : raw42543step0 = (fun i j => raw42543 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42543step0 raw42543; decide +kernel
      have hl : raw42543step0Labels = raw42543Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42543 raw42543Labels permutation643 permutation6
    _ = mixedMoment B node4529 node4529Labels := by rfl

theorem canonical42544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42544 raw42544Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw42544 raw42544Labels = mixedMoment B raw42544step0 raw42544step0Labels := by
      have ha : raw42544step0 = (fun i j => raw42544 (permutation593 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42544step0 raw42544; decide +kernel
      have hl : raw42544step0Labels = raw42544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42544 raw42544Labels permutation593 permutation4
    mixedMoment B raw42544step0 raw42544step0Labels = mixedMoment B raw42544step1 raw42544step1Labels := by
      have ha : raw42544step1 = raw42544step0 := by apply Matrix.ext; unfold raw42544step1 raw42544step0; decide +kernel
      have hl : raw42544step0Labels = labelEmbedding1 ∘ raw42544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42544step0 raw42544step0Labels raw42544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

theorem canonical42545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42545 raw42545Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw42545 raw42545Labels = mixedMoment B raw42545step0 raw42545step0Labels := by
      have ha : raw42545step0 = (fun i j => raw42545 (permutation477 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42545step0 raw42545; decide +kernel
      have hl : raw42545step0Labels = raw42545Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42545 raw42545Labels permutation477 permutation6
    _ = mixedMoment B node5035 node5035Labels := by rfl

theorem canonical42546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42546 raw42546Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw42546 raw42546Labels = mixedMoment B raw42546step0 raw42546step0Labels := by
      have ha : raw42546step0 = (fun i j => raw42546 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42546step0 raw42546; decide +kernel
      have hl : raw42546step0Labels = raw42546Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42546 raw42546Labels permutation470 permutation4
    mixedMoment B raw42546step0 raw42546step0Labels = mixedMoment B raw42546step1 raw42546step1Labels := by
      have ha : raw42546step1 = -raw42546step0 := by apply Matrix.ext; change ∀ i j, raw42546step1 i j = -(raw42546step0 i j); unfold raw42546step1 raw42546step0; decide +kernel
      have hl : raw42546step1Labels = raw42546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42546step1 raw42546step1Labels = mixedMoment B raw42546step2 raw42546step2Labels := by
      have ha : raw42546step2 = raw42546step1 := by apply Matrix.ext; unfold raw42546step2 raw42546step1; decide +kernel
      have hl : raw42546step1Labels = labelEmbedding1 ∘ raw42546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42546step1 raw42546step1Labels raw42546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

theorem canonical42547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42547 raw42547Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw42547 raw42547Labels = mixedMoment B raw42547step0 raw42547step0Labels := by
      have ha : raw42547step0 = (fun i j => raw42547 (permutation478 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42547step0 raw42547; decide +kernel
      have hl : raw42547step0Labels = raw42547Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42547 raw42547Labels permutation478 permutation6
    _ = mixedMoment B node5074 node5074Labels := by rfl

theorem canonical42548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42548 raw42548Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw42548 raw42548Labels = mixedMoment B raw42548step0 raw42548step0Labels := by
      have ha : raw42548step0 = (fun i j => raw42548 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42548step0 raw42548; decide +kernel
      have hl : raw42548step0Labels = raw42548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42548 raw42548Labels permutation590 permutation4
    mixedMoment B raw42548step0 raw42548step0Labels = mixedMoment B raw42548step1 raw42548step1Labels := by
      have ha : raw42548step1 = raw42548step0 := by apply Matrix.ext; unfold raw42548step1 raw42548step0; decide +kernel
      have hl : raw42548step0Labels = labelEmbedding1 ∘ raw42548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42548step0 raw42548step0Labels raw42548step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

theorem canonical42549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42549 raw42549Labels = mixedMoment B node5217 node5217Labels := by
  calc
    mixedMoment B raw42549 raw42549Labels = mixedMoment B raw42549step0 raw42549step0Labels := by
      have ha : raw42549step0 = (fun i j => raw42549 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42549step0 raw42549; decide +kernel
      have hl : raw42549step0Labels = raw42549Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42549 raw42549Labels permutation590 permutation4
    mixedMoment B raw42549step0 raw42549step0Labels = mixedMoment B raw42549step1 raw42549step1Labels := by
      have ha : raw42549step1 = raw42549step0 := by apply Matrix.ext; unfold raw42549step1 raw42549step0; decide +kernel
      have hl : raw42549step0Labels = labelEmbedding10 ∘ raw42549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42549step0 raw42549step0Labels raw42549step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5217 node5217Labels := by rfl

theorem canonical42550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42550 raw42550Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw42550 raw42550Labels = mixedMoment B raw42550step0 raw42550step0Labels := by
      have hz : ∀ j, raw42550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42550step0 = (fun i j => raw42550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42550step0 raw42550; decide +kernel
      have hl : raw42550step0Labels = raw42550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42550 raw42550Labels permutation434 hz
    mixedMoment B raw42550step0 raw42550step0Labels = mixedMoment B raw42550step1 raw42550step1Labels := by
      have hz : ∀ j, raw42550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42550step1 = (fun i j => raw42550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42550step1 raw42550step0; decide +kernel
      have hl : raw42550step1Labels = raw42550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42550step0 raw42550step0Labels permutation80 hz
    mixedMoment B raw42550step1 raw42550step1Labels = mixedMoment B raw42550step2 raw42550step2Labels := by
      have ha : raw42550step2 = (fun i j => raw42550step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42550step2 raw42550step1; decide +kernel
      have hl : raw42550step2Labels = raw42550step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42550step1 raw42550step1Labels permutation22 permutation4
    mixedMoment B raw42550step2 raw42550step2Labels = mixedMoment B raw42550step3 raw42550step3Labels := by
      have ha : raw42550step3 = -raw42550step2 := by apply Matrix.ext; change ∀ i j, raw42550step3 i j = -(raw42550step2 i j); unfold raw42550step3 raw42550step2; decide +kernel
      have hl : raw42550step3Labels = raw42550step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42550step3 raw42550step3Labels = mixedMoment B raw42550step4 raw42550step4Labels := by
      have ha : raw42550step4 = raw42550step3 := by apply Matrix.ext; unfold raw42550step4 raw42550step3; decide +kernel
      have hl : raw42550step3Labels = labelEmbedding1 ∘ raw42550step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42550step3 raw42550step3Labels raw42550step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

theorem canonical42551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42551 raw42551Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw42551 raw42551Labels = mixedMoment B raw42551step0 raw42551step0Labels := by
      have hz : ∀ j, raw42551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42551step0 = (fun i j => raw42551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42551step0 raw42551; decide +kernel
      have hl : raw42551step0Labels = raw42551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42551 raw42551Labels permutation434 hz
    mixedMoment B raw42551step0 raw42551step0Labels = mixedMoment B raw42551step1 raw42551step1Labels := by
      have hz : ∀ j, raw42551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42551step1 = (fun i j => raw42551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42551step1 raw42551step0; decide +kernel
      have hl : raw42551step1Labels = raw42551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42551step0 raw42551step0Labels permutation80 hz
    mixedMoment B raw42551step1 raw42551step1Labels = mixedMoment B raw42551step2 raw42551step2Labels := by
      have ha : raw42551step2 = (fun i j => raw42551step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42551step2 raw42551step1; decide +kernel
      have hl : raw42551step2Labels = raw42551step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42551step1 raw42551step1Labels permutation23 permutation6
    _ = mixedMoment B node4500 node4500Labels := by rfl

theorem canonical42552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42552 raw42552Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw42552 raw42552Labels = mixedMoment B raw42552step0 raw42552step0Labels := by
      have hz : ∀ j, raw42552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42552step0 = (fun i j => raw42552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42552step0 raw42552; decide +kernel
      have hl : raw42552step0Labels = raw42552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42552 raw42552Labels permutation434 hz
    mixedMoment B raw42552step0 raw42552step0Labels = mixedMoment B raw42552step1 raw42552step1Labels := by
      have hz : ∀ j, raw42552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42552step1 = (fun i j => raw42552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42552step1 raw42552step0; decide +kernel
      have hl : raw42552step1Labels = raw42552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42552step0 raw42552step0Labels permutation80 hz
    mixedMoment B raw42552step1 raw42552step1Labels = mixedMoment B raw42552step2 raw42552step2Labels := by
      have ha : raw42552step2 = (fun i j => raw42552step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42552step2 raw42552step1; decide +kernel
      have hl : raw42552step2Labels = raw42552step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42552step1 raw42552step1Labels permutation28 permutation4
    mixedMoment B raw42552step2 raw42552step2Labels = mixedMoment B raw42552step3 raw42552step3Labels := by
      have ha : raw42552step3 = -raw42552step2 := by apply Matrix.ext; change ∀ i j, raw42552step3 i j = -(raw42552step2 i j); unfold raw42552step3 raw42552step2; decide +kernel
      have hl : raw42552step3Labels = raw42552step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42552step3 raw42552step3Labels = mixedMoment B raw42552step4 raw42552step4Labels := by
      have ha : raw42552step4 = raw42552step3 := by apply Matrix.ext; unfold raw42552step4 raw42552step3; decide +kernel
      have hl : raw42552step3Labels = labelEmbedding1 ∘ raw42552step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42552step3 raw42552step3Labels raw42552step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

theorem canonical42553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42553 raw42553Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw42553 raw42553Labels = mixedMoment B raw42553step0 raw42553step0Labels := by
      have hz : ∀ j, raw42553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42553step0 = (fun i j => raw42553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42553step0 raw42553; decide +kernel
      have hl : raw42553step0Labels = raw42553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42553 raw42553Labels permutation434 hz
    mixedMoment B raw42553step0 raw42553step0Labels = mixedMoment B raw42553step1 raw42553step1Labels := by
      have hz : ∀ j, raw42553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42553step1 = (fun i j => raw42553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42553step1 raw42553step0; decide +kernel
      have hl : raw42553step1Labels = raw42553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42553step0 raw42553step0Labels permutation80 hz
    mixedMoment B raw42553step1 raw42553step1Labels = mixedMoment B raw42553step2 raw42553step2Labels := by
      have ha : raw42553step2 = (fun i j => raw42553step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42553step2 raw42553step1; decide +kernel
      have hl : raw42553step2Labels = raw42553step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42553step1 raw42553step1Labels permutation28 permutation6
    _ = mixedMoment B node4179 node4179Labels := by rfl

theorem canonical42554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42554 raw42554Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw42554 raw42554Labels = mixedMoment B raw42554step0 raw42554step0Labels := by
      have hz : ∀ j, raw42554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42554step0 = (fun i j => raw42554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42554step0 raw42554; decide +kernel
      have hl : raw42554step0Labels = raw42554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42554 raw42554Labels permutation346 hz
    mixedMoment B raw42554step0 raw42554step0Labels = mixedMoment B raw42554step1 raw42554step1Labels := by
      have ha : raw42554step1 = (fun i j => raw42554step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42554step1 raw42554step0; decide +kernel
      have hl : raw42554step1Labels = raw42554step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42554step0 raw42554step0Labels permutation110 permutation4
    mixedMoment B raw42554step1 raw42554step1Labels = mixedMoment B raw42554step2 raw42554step2Labels := by
      have ha : raw42554step2 = -raw42554step1 := by apply Matrix.ext; change ∀ i j, raw42554step2 i j = -(raw42554step1 i j); unfold raw42554step2 raw42554step1; decide +kernel
      have hl : raw42554step2Labels = raw42554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42554step2 raw42554step2Labels = mixedMoment B raw42554step3 raw42554step3Labels := by
      have ha : raw42554step3 = raw42554step2 := by apply Matrix.ext; unfold raw42554step3 raw42554step2; decide +kernel
      have hl : raw42554step2Labels = labelEmbedding1 ∘ raw42554step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42554step2 raw42554step2Labels raw42554step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

theorem canonical42555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42555 raw42555Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw42555 raw42555Labels = mixedMoment B raw42555step0 raw42555step0Labels := by
      have hz : ∀ j, raw42555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42555step0 = (fun i j => raw42555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42555step0 raw42555; decide +kernel
      have hl : raw42555step0Labels = raw42555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42555 raw42555Labels permutation346 hz
    mixedMoment B raw42555step0 raw42555step0Labels = mixedMoment B raw42555step1 raw42555step1Labels := by
      have ha : raw42555step1 = (fun i j => raw42555step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42555step1 raw42555step0; decide +kernel
      have hl : raw42555step1Labels = raw42555step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42555step0 raw42555step0Labels permutation125 permutation6
    _ = mixedMoment B node4475 node4475Labels := by rfl

theorem canonical42556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42556 raw42556Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw42556 raw42556Labels = mixedMoment B raw42556step0 raw42556step0Labels := by
      have hz : ∀ j, raw42556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42556step0 = (fun i j => raw42556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42556step0 raw42556; decide +kernel
      have hl : raw42556step0Labels = raw42556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42556 raw42556Labels permutation346 hz
    mixedMoment B raw42556step0 raw42556step0Labels = mixedMoment B raw42556step1 raw42556step1Labels := by
      have ha : raw42556step1 = (fun i j => raw42556step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42556step1 raw42556step0; decide +kernel
      have hl : raw42556step1Labels = raw42556step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42556step0 raw42556step0Labels permutation134 permutation4
    mixedMoment B raw42556step1 raw42556step1Labels = mixedMoment B raw42556step2 raw42556step2Labels := by
      have ha : raw42556step2 = -raw42556step1 := by apply Matrix.ext; change ∀ i j, raw42556step2 i j = -(raw42556step1 i j); unfold raw42556step2 raw42556step1; decide +kernel
      have hl : raw42556step2Labels = raw42556step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42556step2 raw42556step2Labels = mixedMoment B raw42556step3 raw42556step3Labels := by
      have ha : raw42556step3 = raw42556step2 := by apply Matrix.ext; unfold raw42556step3 raw42556step2; decide +kernel
      have hl : raw42556step2Labels = labelEmbedding1 ∘ raw42556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42556step2 raw42556step2Labels raw42556step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

theorem canonical42557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42557 raw42557Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw42557 raw42557Labels = mixedMoment B raw42557step0 raw42557step0Labels := by
      have hz : ∀ j, raw42557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42557step0 = (fun i j => raw42557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42557step0 raw42557; decide +kernel
      have hl : raw42557step0Labels = raw42557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42557 raw42557Labels permutation346 hz
    mixedMoment B raw42557step0 raw42557step0Labels = mixedMoment B raw42557step1 raw42557step1Labels := by
      have ha : raw42557step1 = (fun i j => raw42557step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42557step1 raw42557step0; decide +kernel
      have hl : raw42557step1Labels = raw42557step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42557step0 raw42557step0Labels permutation137 permutation6
    _ = mixedMoment B node4176 node4176Labels := by rfl

theorem canonical42558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42558 raw42558Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw42558 raw42558Labels = mixedMoment B raw42558step0 raw42558step0Labels := by
      have hz : ∀ j, raw42558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42558step0 = (fun i j => raw42558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42558step0 raw42558; decide +kernel
      have hl : raw42558step0Labels = raw42558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42558 raw42558Labels permutation346 hz
    mixedMoment B raw42558step0 raw42558step0Labels = mixedMoment B raw42558step1 raw42558step1Labels := by
      have ha : raw42558step1 = (fun i j => raw42558step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42558step1 raw42558step0; decide +kernel
      have hl : raw42558step1Labels = raw42558step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42558step0 raw42558step0Labels permutation135 permutation4
    mixedMoment B raw42558step1 raw42558step1Labels = mixedMoment B raw42558step2 raw42558step2Labels := by
      have ha : raw42558step2 = -raw42558step1 := by apply Matrix.ext; change ∀ i j, raw42558step2 i j = -(raw42558step1 i j); unfold raw42558step2 raw42558step1; decide +kernel
      have hl : raw42558step2Labels = raw42558step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42558step2 raw42558step2Labels = mixedMoment B raw42558step3 raw42558step3Labels := by
      have ha : raw42558step3 = raw42558step2 := by apply Matrix.ext; unfold raw42558step3 raw42558step2; decide +kernel
      have hl : raw42558step2Labels = labelEmbedding1 ∘ raw42558step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42558step2 raw42558step2Labels raw42558step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

theorem canonical42559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42559 raw42559Labels = mixedMoment B node4154 node4154Labels := by
  calc
    mixedMoment B raw42559 raw42559Labels = mixedMoment B raw42559step0 raw42559step0Labels := by
      have hz : ∀ j, raw42559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42559step0 = (fun i j => raw42559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42559step0 raw42559; decide +kernel
      have hl : raw42559step0Labels = raw42559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42559 raw42559Labels permutation346 hz
    mixedMoment B raw42559step0 raw42559step0Labels = mixedMoment B raw42559step1 raw42559step1Labels := by
      have ha : raw42559step1 = (fun i j => raw42559step0 (permutation148 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42559step1 raw42559step0; decide +kernel
      have hl : raw42559step1Labels = raw42559step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42559step0 raw42559step0Labels permutation148 permutation6
    _ = mixedMoment B node4154 node4154Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2592 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2592) =
      Integer.Sparse.eval keyMomentRow2592 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2144) := by
    have ha : gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge = raw42496 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42496Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42496 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4665) := by
    have ha : gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge = raw42497 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42497Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42497 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2592).leftCharge (GramAssembly.key 2592).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2592, Integer.Sparse.eval]
  ring

theorem keyMoment2593 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2593) =
      Integer.Sparse.eval keyMomentRow2593 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2171) := by
    have ha : gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge = raw42498 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42498Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42498 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4762) := by
    have ha : gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge = raw42499 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42499Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42499 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2593).leftCharge (GramAssembly.key 2593).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2593, Integer.Sparse.eval]
  ring

theorem keyMoment2594 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2594) =
      Integer.Sparse.eval keyMomentRow2594 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2195) := by
    have ha : gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge = raw42500 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42500Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42500 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4803) := by
    have ha : gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge = raw42501 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42501Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42501 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2594).leftCharge (GramAssembly.key 2594).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2594, Integer.Sparse.eval]
  ring

theorem keyMoment2595 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2595) =
      Integer.Sparse.eval keyMomentRow2595 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2252) := by
    have ha : gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge = raw42502 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42502Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42502 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge = raw42503 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42503Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42503 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2595).leftCharge (GramAssembly.key 2595).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2595, Integer.Sparse.eval]
  ring

theorem keyMoment2596 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2596) =
      Integer.Sparse.eval keyMomentRow2596 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3222) := by
    have ha : gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge = raw42504 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42504Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42504 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4891) := by
    have ha : gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge = raw42505 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42505Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42505 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2596).leftCharge (GramAssembly.key 2596).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2596, Integer.Sparse.eval]
  ring

theorem keyMoment2597 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2597) =
      Integer.Sparse.eval keyMomentRow2597 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3016) := by
    have ha : gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge = raw42506 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42506Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42506 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5254) := by
    have ha : gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge = raw42507 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42507Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42507 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2597).leftCharge (GramAssembly.key 2597).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2597, Integer.Sparse.eval]
  ring

theorem keyMoment2598 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2598) =
      Integer.Sparse.eval keyMomentRow2598 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3803) := by
    have ha : gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge = raw42508 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42508Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42508 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5407) := by
    have ha : gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge = raw42509 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42509Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42509 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2598).leftCharge (GramAssembly.key 2598).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2598, Integer.Sparse.eval]
  ring

theorem keyMoment2599 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2599) =
      Integer.Sparse.eval keyMomentRow2599 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3802) := by
    have ha : gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge = raw42510 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42510Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42510 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5402) := by
    have ha : gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge = raw42511 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42511Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42511 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2599).leftCharge (GramAssembly.key 2599).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2599, Integer.Sparse.eval]
  ring

theorem keyMoment2600 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2600) =
      Integer.Sparse.eval keyMomentRow2600 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2654) := by
    have ha : gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge = raw42512 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42512Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42512 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5216) := by
    have ha : gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge = raw42513 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42513Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42513 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2600).leftCharge (GramAssembly.key 2600).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2600, Integer.Sparse.eval]
  ring

theorem keyMoment2601 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2601) =
      Integer.Sparse.eval keyMomentRow2601 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3025) := by
    have ha : gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge = raw42514 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42514Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42514 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5287) := by
    have ha : gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge = raw42515 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42515Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42515 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2601).leftCharge (GramAssembly.key 2601).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2601, Integer.Sparse.eval]
  ring

theorem keyMoment2602 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2602) =
      Integer.Sparse.eval keyMomentRow2602 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2659) := by
    have ha : gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge = raw42516 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42516Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42516 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4976) := by
    have ha : gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge = raw42517 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42517Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42517 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2602).leftCharge (GramAssembly.key 2602).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2602, Integer.Sparse.eval]
  ring

theorem keyMoment2603 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2603) =
      Integer.Sparse.eval keyMomentRow2603 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3762) := by
    have ha : gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge = raw42518 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42518Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42518 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5360) := by
    have ha : gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge = raw42519 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42519Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42519 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2603).leftCharge (GramAssembly.key 2603).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2603, Integer.Sparse.eval]
  ring

theorem keyMoment2604 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2604) =
      Integer.Sparse.eval keyMomentRow2604 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3553) := by
    have ha : gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge = raw42520 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42520Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42520 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4963) := by
    have ha : gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge = raw42521 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42521Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42521 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2604).leftCharge (GramAssembly.key 2604).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2604, Integer.Sparse.eval]
  ring

theorem keyMoment2605 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2605) =
      Integer.Sparse.eval keyMomentRow2605 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3509) := by
    have ha : gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge = raw42522 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42522Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42522 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4957) := by
    have ha : gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge = raw42523 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42523Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42523 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2605).leftCharge (GramAssembly.key 2605).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2605, Integer.Sparse.eval]
  ring

theorem keyMoment2606 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2606) =
      Integer.Sparse.eval keyMomentRow2606 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2653) := by
    have ha : gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge = raw42524 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42524Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42524 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5215) := by
    have ha : gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge = raw42525 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42525Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42525 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2606).leftCharge (GramAssembly.key 2606).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2606, Integer.Sparse.eval]
  ring

theorem keyMoment2607 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2607) =
      Integer.Sparse.eval keyMomentRow2607 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3761) := by
    have ha : gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge = raw42526 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42526Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42526 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5353) := by
    have ha : gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge = raw42527 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42527Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42527 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2607).leftCharge (GramAssembly.key 2607).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2607, Integer.Sparse.eval]
  ring

theorem keyMoment2608 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2608) =
      Integer.Sparse.eval keyMomentRow2608 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3221) := by
    have ha : gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge = raw42528 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42528Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42528 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4885) := by
    have ha : gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge = raw42529 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42529Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42529 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2608).leftCharge (GramAssembly.key 2608).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2608, Integer.Sparse.eval]
  ring

theorem keyMoment2609 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2609) =
      Integer.Sparse.eval keyMomentRow2609 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3023) := by
    have ha : gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge = raw42530 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42530Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42530 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5286) := by
    have ha : gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge = raw42531 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42531Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42531 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2609).leftCharge (GramAssembly.key 2609).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2609, Integer.Sparse.eval]
  ring

theorem keyMoment2610 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2610) =
      Integer.Sparse.eval keyMomentRow2610 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2655) := by
    have ha : gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge = raw42532 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42532Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42532 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5116) := by
    have ha : gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge = raw42533 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42533Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42533 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2610).leftCharge (GramAssembly.key 2610).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2610, Integer.Sparse.eval]
  ring

theorem keyMoment2611 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2611) =
      Integer.Sparse.eval keyMomentRow2611 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3024) := by
    have ha : gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge = raw42534 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42534Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42534 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5103) := by
    have ha : gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge = raw42535 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42535Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42535 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2611).leftCharge (GramAssembly.key 2611).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2611, Integer.Sparse.eval]
  ring

theorem keyMoment2612 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2612) =
      Integer.Sparse.eval keyMomentRow2612 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2657) := by
    have ha : gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge = raw42536 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42536Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42536 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4548) := by
    have ha : gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge = raw42537 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42537Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42537 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2612).leftCharge (GramAssembly.key 2612).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2612, Integer.Sparse.eval]
  ring

theorem keyMoment2613 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2613) =
      Integer.Sparse.eval keyMomentRow2613 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3464) := by
    have ha : gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge = raw42538 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42538Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42538 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5086) := by
    have ha : gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge = raw42539 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42539Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42539 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2613).leftCharge (GramAssembly.key 2613).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2613, Integer.Sparse.eval]
  ring

theorem keyMoment2614 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2614) =
      Integer.Sparse.eval keyMomentRow2614 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3259) := by
    have ha : gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge = raw42540 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42540Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42540 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4545) := by
    have ha : gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge = raw42541 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42541Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42541 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2614).leftCharge (GramAssembly.key 2614).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2614, Integer.Sparse.eval]
  ring

theorem keyMoment2615 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2615) =
      Integer.Sparse.eval keyMomentRow2615 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3258) := by
    have ha : gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge = raw42542 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42542Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42542 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4529) := by
    have ha : gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge = raw42543 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42543Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42543 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2615).leftCharge (GramAssembly.key 2615).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2615, Integer.Sparse.eval]
  ring

theorem keyMoment2616 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2616) =
      Integer.Sparse.eval keyMomentRow2616 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2652) := by
    have ha : gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge = raw42544 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42544Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42544 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5035) := by
    have ha : gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge = raw42545 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42545Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42545 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2616).leftCharge (GramAssembly.key 2616).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2616, Integer.Sparse.eval]
  ring

theorem keyMoment2617 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2617) =
      Integer.Sparse.eval keyMomentRow2617 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3463) := by
    have ha : gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge = raw42546 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42546Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42546 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5074) := by
    have ha : gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge = raw42547 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42547Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42547 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2617).leftCharge (GramAssembly.key 2617).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2617, Integer.Sparse.eval]
  ring

theorem keyMoment2618 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2618) =
      Integer.Sparse.eval keyMomentRow2618 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2656) := by
    have ha : gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge = raw42548 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42548Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42548 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5217) := by
    have ha : gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge = raw42549 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42549Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42549 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2618).leftCharge (GramAssembly.key 2618).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2618, Integer.Sparse.eval]
  ring

theorem keyMoment2619 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2619) =
      Integer.Sparse.eval keyMomentRow2619 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1716) := by
    have ha : gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge = raw42550 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42550Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42550 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4500) := by
    have ha : gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge = raw42551 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42551Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42551 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2619).leftCharge (GramAssembly.key 2619).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2619, Integer.Sparse.eval]
  ring

theorem keyMoment2620 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2620) =
      Integer.Sparse.eval keyMomentRow2620 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1513) := by
    have ha : gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge = raw42552 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42552Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42552 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4179) := by
    have ha : gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge = raw42553 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42553Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42553 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2620).leftCharge (GramAssembly.key 2620).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2620, Integer.Sparse.eval]
  ring

theorem keyMoment2621 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2621) =
      Integer.Sparse.eval keyMomentRow2621 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1715) := by
    have ha : gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge = raw42554 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42554Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42554 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4475) := by
    have ha : gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge = raw42555 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42555Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42555 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2621).leftCharge (GramAssembly.key 2621).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2621, Integer.Sparse.eval]
  ring

theorem keyMoment2622 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2622) =
      Integer.Sparse.eval keyMomentRow2622 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1512) := by
    have ha : gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge = raw42556 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42556Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42556 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4176) := by
    have ha : gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge = raw42557 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42557Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42557 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2622).leftCharge (GramAssembly.key 2622).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2622, Integer.Sparse.eval]
  ring

theorem keyMoment2623 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2623) =
      Integer.Sparse.eval keyMomentRow2623 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1511) := by
    have ha : gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge = raw42558 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42558Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42558 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4154) := by
    have ha : gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge = raw42559 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42559Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42559 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2623).leftCharge (GramAssembly.key 2623).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2623, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk81
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2592 : keyMomentRows (2592 : Fin 2886) =
    keyMomentRow2592 := by decide +kernel

theorem keyMomentRowsAt2593 : keyMomentRows (2593 : Fin 2886) =
    keyMomentRow2593 := by decide +kernel

theorem keyMomentRowsAt2594 : keyMomentRows (2594 : Fin 2886) =
    keyMomentRow2594 := by decide +kernel

theorem keyMomentRowsAt2595 : keyMomentRows (2595 : Fin 2886) =
    keyMomentRow2595 := by decide +kernel

theorem keyMomentRowsAt2596 : keyMomentRows (2596 : Fin 2886) =
    keyMomentRow2596 := by decide +kernel

theorem keyMomentRowsAt2597 : keyMomentRows (2597 : Fin 2886) =
    keyMomentRow2597 := by decide +kernel

theorem keyMomentRowsAt2598 : keyMomentRows (2598 : Fin 2886) =
    keyMomentRow2598 := by decide +kernel

theorem keyMomentRowsAt2599 : keyMomentRows (2599 : Fin 2886) =
    keyMomentRow2599 := by decide +kernel

theorem keyMomentRowsAt2600 : keyMomentRows (2600 : Fin 2886) =
    keyMomentRow2600 := by decide +kernel

theorem keyMomentRowsAt2601 : keyMomentRows (2601 : Fin 2886) =
    keyMomentRow2601 := by decide +kernel

theorem keyMomentRowsAt2602 : keyMomentRows (2602 : Fin 2886) =
    keyMomentRow2602 := by decide +kernel

theorem keyMomentRowsAt2603 : keyMomentRows (2603 : Fin 2886) =
    keyMomentRow2603 := by decide +kernel

theorem keyMomentRowsAt2604 : keyMomentRows (2604 : Fin 2886) =
    keyMomentRow2604 := by decide +kernel

theorem keyMomentRowsAt2605 : keyMomentRows (2605 : Fin 2886) =
    keyMomentRow2605 := by decide +kernel

theorem keyMomentRowsAt2606 : keyMomentRows (2606 : Fin 2886) =
    keyMomentRow2606 := by decide +kernel

theorem keyMomentRowsAt2607 : keyMomentRows (2607 : Fin 2886) =
    keyMomentRow2607 := by decide +kernel

theorem keyMomentRowsAt2608 : keyMomentRows (2608 : Fin 2886) =
    keyMomentRow2608 := by decide +kernel

theorem keyMomentRowsAt2609 : keyMomentRows (2609 : Fin 2886) =
    keyMomentRow2609 := by decide +kernel

theorem keyMomentRowsAt2610 : keyMomentRows (2610 : Fin 2886) =
    keyMomentRow2610 := by decide +kernel

theorem keyMomentRowsAt2611 : keyMomentRows (2611 : Fin 2886) =
    keyMomentRow2611 := by decide +kernel

theorem keyMomentRowsAt2612 : keyMomentRows (2612 : Fin 2886) =
    keyMomentRow2612 := by decide +kernel

theorem keyMomentRowsAt2613 : keyMomentRows (2613 : Fin 2886) =
    keyMomentRow2613 := by decide +kernel

theorem keyMomentRowsAt2614 : keyMomentRows (2614 : Fin 2886) =
    keyMomentRow2614 := by decide +kernel

theorem keyMomentRowsAt2615 : keyMomentRows (2615 : Fin 2886) =
    keyMomentRow2615 := by decide +kernel

theorem keyMomentRowsAt2616 : keyMomentRows (2616 : Fin 2886) =
    keyMomentRow2616 := by decide +kernel

theorem keyMomentRowsAt2617 : keyMomentRows (2617 : Fin 2886) =
    keyMomentRow2617 := by decide +kernel

theorem keyMomentRowsAt2618 : keyMomentRows (2618 : Fin 2886) =
    keyMomentRow2618 := by decide +kernel

theorem keyMomentRowsAt2619 : keyMomentRows (2619 : Fin 2886) =
    keyMomentRow2619 := by decide +kernel

theorem keyMomentRowsAt2620 : keyMomentRows (2620 : Fin 2886) =
    keyMomentRow2620 := by decide +kernel

theorem keyMomentRowsAt2621 : keyMomentRows (2621 : Fin 2886) =
    keyMomentRow2621 := by decide +kernel

theorem keyMomentRowsAt2622 : keyMomentRows (2622 : Fin 2886) =
    keyMomentRow2622 := by decide +kernel

theorem keyMomentRowsAt2623 : keyMomentRows (2623 : Fin 2886) =
    keyMomentRow2623 := by decide +kernel

theorem keyMomentChunkSound81_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 81) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2592 ∨ k.val = 2593 ∨ k.val = 2594 ∨ k.val = 2595 ∨ k.val = 2596 ∨ k.val = 2597 ∨ k.val = 2598 ∨ k.val = 2599 ∨ k.val = 2600 ∨ k.val = 2601 ∨ k.val = 2602 ∨ k.val = 2603 ∨ k.val = 2604 ∨ k.val = 2605 ∨ k.val = 2606 ∨ k.val = 2607 ∨ k.val = 2608 ∨ k.val = 2609 ∨ k.val = 2610 ∨ k.val = 2611 ∨ k.val = 2612 ∨ k.val = 2613 ∨ k.val = 2614 ∨ k.val = 2615 ∨ k.val = 2616 ∨ k.val = 2617 ∨ k.val = 2618 ∨ k.val = 2619 ∨ k.val = 2620 ∨ k.val = 2621 ∨ k.val = 2622 ∨ k.val = 2623 := by omega
  rcases heq with h2592 | h2593 | h2594 | h2595 | h2596 | h2597 | h2598 | h2599 | h2600 | h2601 | h2602 | h2603 | h2604 | h2605 | h2606 | h2607 | h2608 | h2609 | h2610 | h2611 | h2612 | h2613 | h2614 | h2615 | h2616 | h2617 | h2618 | h2619 | h2620 | h2621 | h2622 | h2623
  · have he : k = (2592 : Fin 2886) := Fin.ext h2592
    subst k
    rw [keyMomentRowsAt2592]
    exact keyMoment2592 B hB
  · have he : k = (2593 : Fin 2886) := Fin.ext h2593
    subst k
    rw [keyMomentRowsAt2593]
    exact keyMoment2593 B hB
  · have he : k = (2594 : Fin 2886) := Fin.ext h2594
    subst k
    rw [keyMomentRowsAt2594]
    exact keyMoment2594 B hB
  · have he : k = (2595 : Fin 2886) := Fin.ext h2595
    subst k
    rw [keyMomentRowsAt2595]
    exact keyMoment2595 B hB
  · have he : k = (2596 : Fin 2886) := Fin.ext h2596
    subst k
    rw [keyMomentRowsAt2596]
    exact keyMoment2596 B hB
  · have he : k = (2597 : Fin 2886) := Fin.ext h2597
    subst k
    rw [keyMomentRowsAt2597]
    exact keyMoment2597 B hB
  · have he : k = (2598 : Fin 2886) := Fin.ext h2598
    subst k
    rw [keyMomentRowsAt2598]
    exact keyMoment2598 B hB
  · have he : k = (2599 : Fin 2886) := Fin.ext h2599
    subst k
    rw [keyMomentRowsAt2599]
    exact keyMoment2599 B hB
  · have he : k = (2600 : Fin 2886) := Fin.ext h2600
    subst k
    rw [keyMomentRowsAt2600]
    exact keyMoment2600 B hB
  · have he : k = (2601 : Fin 2886) := Fin.ext h2601
    subst k
    rw [keyMomentRowsAt2601]
    exact keyMoment2601 B hB
  · have he : k = (2602 : Fin 2886) := Fin.ext h2602
    subst k
    rw [keyMomentRowsAt2602]
    exact keyMoment2602 B hB
  · have he : k = (2603 : Fin 2886) := Fin.ext h2603
    subst k
    rw [keyMomentRowsAt2603]
    exact keyMoment2603 B hB
  · have he : k = (2604 : Fin 2886) := Fin.ext h2604
    subst k
    rw [keyMomentRowsAt2604]
    exact keyMoment2604 B hB
  · have he : k = (2605 : Fin 2886) := Fin.ext h2605
    subst k
    rw [keyMomentRowsAt2605]
    exact keyMoment2605 B hB
  · have he : k = (2606 : Fin 2886) := Fin.ext h2606
    subst k
    rw [keyMomentRowsAt2606]
    exact keyMoment2606 B hB
  · have he : k = (2607 : Fin 2886) := Fin.ext h2607
    subst k
    rw [keyMomentRowsAt2607]
    exact keyMoment2607 B hB
  · have he : k = (2608 : Fin 2886) := Fin.ext h2608
    subst k
    rw [keyMomentRowsAt2608]
    exact keyMoment2608 B hB
  · have he : k = (2609 : Fin 2886) := Fin.ext h2609
    subst k
    rw [keyMomentRowsAt2609]
    exact keyMoment2609 B hB
  · have he : k = (2610 : Fin 2886) := Fin.ext h2610
    subst k
    rw [keyMomentRowsAt2610]
    exact keyMoment2610 B hB
  · have he : k = (2611 : Fin 2886) := Fin.ext h2611
    subst k
    rw [keyMomentRowsAt2611]
    exact keyMoment2611 B hB
  · have he : k = (2612 : Fin 2886) := Fin.ext h2612
    subst k
    rw [keyMomentRowsAt2612]
    exact keyMoment2612 B hB
  · have he : k = (2613 : Fin 2886) := Fin.ext h2613
    subst k
    rw [keyMomentRowsAt2613]
    exact keyMoment2613 B hB
  · have he : k = (2614 : Fin 2886) := Fin.ext h2614
    subst k
    rw [keyMomentRowsAt2614]
    exact keyMoment2614 B hB
  · have he : k = (2615 : Fin 2886) := Fin.ext h2615
    subst k
    rw [keyMomentRowsAt2615]
    exact keyMoment2615 B hB
  · have he : k = (2616 : Fin 2886) := Fin.ext h2616
    subst k
    rw [keyMomentRowsAt2616]
    exact keyMoment2616 B hB
  · have he : k = (2617 : Fin 2886) := Fin.ext h2617
    subst k
    rw [keyMomentRowsAt2617]
    exact keyMoment2617 B hB
  · have he : k = (2618 : Fin 2886) := Fin.ext h2618
    subst k
    rw [keyMomentRowsAt2618]
    exact keyMoment2618 B hB
  · have he : k = (2619 : Fin 2886) := Fin.ext h2619
    subst k
    rw [keyMomentRowsAt2619]
    exact keyMoment2619 B hB
  · have he : k = (2620 : Fin 2886) := Fin.ext h2620
    subst k
    rw [keyMomentRowsAt2620]
    exact keyMoment2620 B hB
  · have he : k = (2621 : Fin 2886) := Fin.ext h2621
    subst k
    rw [keyMomentRowsAt2621]
    exact keyMoment2621 B hB
  · have he : k = (2622 : Fin 2886) := Fin.ext h2622
    subst k
    rw [keyMomentRowsAt2622]
    exact keyMoment2622 B hB
  · have he : k = (2623 : Fin 2886) := Fin.ext h2623
    subst k
    rw [keyMomentRowsAt2623]
    exact keyMoment2623 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound81_e_oai
