-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:04:19.704988+00:00
-- url     : https://prove2.me/submissions/be73ba90-572e-4d0d-a376-b4f3d5086a1c

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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical330
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical42304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42304 raw42304Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw42304 raw42304Labels = mixedMoment B raw42304step0 raw42304step0Labels := by
      have hz : ∀ j, raw42304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42304step0 = (fun i j => raw42304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42304step0 raw42304; decide +kernel
      have hl : raw42304step0Labels = raw42304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42304 raw42304Labels permutation346 hz
    mixedMoment B raw42304step0 raw42304step0Labels = mixedMoment B raw42304step1 raw42304step1Labels := by
      have ha : raw42304step1 = (fun i j => raw42304step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42304step1 raw42304step0; decide +kernel
      have hl : raw42304step1Labels = raw42304step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42304step0 raw42304step0Labels permutation82 permutation4
    mixedMoment B raw42304step1 raw42304step1Labels = mixedMoment B raw42304step2 raw42304step2Labels := by
      have ha : raw42304step2 = -raw42304step1 := by apply Matrix.ext; change ∀ i j, raw42304step2 i j = -(raw42304step1 i j); unfold raw42304step2 raw42304step1; decide +kernel
      have hl : raw42304step2Labels = raw42304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42304step2 raw42304step2Labels = mixedMoment B raw42304step3 raw42304step3Labels := by
      have ha : raw42304step3 = raw42304step2 := by apply Matrix.ext; unfold raw42304step3 raw42304step2; decide +kernel
      have hl : raw42304step2Labels = labelEmbedding1 ∘ raw42304step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42304step2 raw42304step2Labels raw42304step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

theorem canonical42305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42305 raw42305Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw42305 raw42305Labels = mixedMoment B raw42305step0 raw42305step0Labels := by
      have hz : ∀ j, raw42305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42305step0 = (fun i j => raw42305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42305step0 raw42305; decide +kernel
      have hl : raw42305step0Labels = raw42305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42305 raw42305Labels permutation346 hz
    mixedMoment B raw42305step0 raw42305step0Labels = mixedMoment B raw42305step1 raw42305step1Labels := by
      have ha : raw42305step1 = (fun i j => raw42305step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42305step1 raw42305step0; decide +kernel
      have hl : raw42305step1Labels = raw42305step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42305step0 raw42305step0Labels permutation93 permutation6
    _ = mixedMoment B node5164 node5164Labels := by rfl

theorem canonical42306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42306 raw42306Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw42306 raw42306Labels = mixedMoment B raw42306step0 raw42306step0Labels := by
      have hz : ∀ j, raw42306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42306step0 = (fun i j => raw42306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42306step0 raw42306; decide +kernel
      have hl : raw42306step0Labels = raw42306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42306 raw42306Labels permutation346 hz
    mixedMoment B raw42306step0 raw42306step0Labels = mixedMoment B raw42306step1 raw42306step1Labels := by
      have ha : raw42306step1 = (fun i j => raw42306step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42306step1 raw42306step0; decide +kernel
      have hl : raw42306step1Labels = raw42306step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42306step0 raw42306step0Labels permutation83 permutation4
    mixedMoment B raw42306step1 raw42306step1Labels = mixedMoment B raw42306step2 raw42306step2Labels := by
      have ha : raw42306step2 = -raw42306step1 := by apply Matrix.ext; change ∀ i j, raw42306step2 i j = -(raw42306step1 i j); unfold raw42306step2 raw42306step1; decide +kernel
      have hl : raw42306step2Labels = raw42306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42306step2 raw42306step2Labels = mixedMoment B raw42306step3 raw42306step3Labels := by
      have ha : raw42306step3 = raw42306step2 := by apply Matrix.ext; unfold raw42306step3 raw42306step2; decide +kernel
      have hl : raw42306step2Labels = labelEmbedding1 ∘ raw42306step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42306step2 raw42306step2Labels raw42306step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

theorem canonical42307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42307 raw42307Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42307 raw42307Labels = mixedMoment B raw42307step0 raw42307step0Labels := by
      have hz : ∀ j, raw42307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42307step0 = (fun i j => raw42307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42307step0 raw42307; decide +kernel
      have hl : raw42307step0Labels = raw42307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42307 raw42307Labels permutation346 hz
    mixedMoment B raw42307step0 raw42307step0Labels = mixedMoment B raw42307step1 raw42307step1Labels := by
      have ha : raw42307step1 = (fun i j => raw42307step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42307step1 raw42307step0; decide +kernel
      have hl : raw42307step1Labels = raw42307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42307step0 raw42307step0Labels permutation96 permutation6
    _ = mixedMoment B node5282 node5282Labels := by rfl

theorem canonical42308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42308 raw42308Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw42308 raw42308Labels = mixedMoment B raw42308step0 raw42308step0Labels := by
      have hz : ∀ j, raw42308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42308step0 = (fun i j => raw42308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42308step0 raw42308; decide +kernel
      have hl : raw42308step0Labels = raw42308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42308 raw42308Labels permutation346 hz
    mixedMoment B raw42308step0 raw42308step0Labels = mixedMoment B raw42308step1 raw42308step1Labels := by
      have ha : raw42308step1 = (fun i j => raw42308step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42308step1 raw42308step0; decide +kernel
      have hl : raw42308step1Labels = raw42308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42308step0 raw42308step0Labels permutation36 permutation2
    mixedMoment B raw42308step1 raw42308step1Labels = mixedMoment B raw42308step2 raw42308step2Labels := by
      have ha : raw42308step2 = raw42308step1 := by apply Matrix.ext; unfold raw42308step2 raw42308step1; decide +kernel
      have hl : raw42308step1Labels = labelEmbedding1 ∘ raw42308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42308step1 raw42308step1Labels raw42308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

theorem canonical42309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42309 raw42309Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw42309 raw42309Labels = mixedMoment B raw42309step0 raw42309step0Labels := by
      have hz : ∀ j, raw42309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42309step0 = (fun i j => raw42309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42309step0 raw42309; decide +kernel
      have hl : raw42309step0Labels = raw42309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42309 raw42309Labels permutation346 hz
    mixedMoment B raw42309step0 raw42309step0Labels = mixedMoment B raw42309step1 raw42309step1Labels := by
      have ha : raw42309step1 = (fun i j => raw42309step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42309step1 raw42309step0; decide +kernel
      have hl : raw42309step1Labels = raw42309step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42309step0 raw42309step0Labels permutation93 permutation6
    _ = mixedMoment B node5463 node5463Labels := by rfl

theorem canonical42310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42310 raw42310Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw42310 raw42310Labels = mixedMoment B raw42310step0 raw42310step0Labels := by
      have ha : raw42310step0 = (fun i j => raw42310 (permutation447 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42310step0 raw42310; decide +kernel
      have hl : raw42310step0Labels = raw42310Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42310 raw42310Labels permutation447 permutation4
    mixedMoment B raw42310step0 raw42310step0Labels = mixedMoment B raw42310step1 raw42310step1Labels := by
      have ha : raw42310step1 = -raw42310step0 := by apply Matrix.ext; change ∀ i j, raw42310step1 i j = -(raw42310step0 i j); unfold raw42310step1 raw42310step0; decide +kernel
      have hl : raw42310step1Labels = raw42310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42310step1 raw42310step1Labels = mixedMoment B raw42310step2 raw42310step2Labels := by
      have ha : raw42310step2 = raw42310step1 := by apply Matrix.ext; unfold raw42310step2 raw42310step1; decide +kernel
      have hl : raw42310step1Labels = labelEmbedding1 ∘ raw42310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42310step1 raw42310step1Labels raw42310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

theorem canonical42311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42311 raw42311Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw42311 raw42311Labels = mixedMoment B raw42311step0 raw42311step0Labels := by
      have ha : raw42311step0 = (fun i j => raw42311 (permutation500 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42311step0 raw42311; decide +kernel
      have hl : raw42311step0Labels = raw42311Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42311 raw42311Labels permutation500 permutation6
    _ = mixedMoment B node5145 node5145Labels := by rfl

theorem canonical42312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42312 raw42312Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw42312 raw42312Labels = mixedMoment B raw42312step0 raw42312step0Labels := by
      have hz : ∀ j, raw42312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42312step0 = (fun i j => raw42312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42312step0 raw42312; decide +kernel
      have hl : raw42312step0Labels = raw42312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42312 raw42312Labels permutation434 hz
    mixedMoment B raw42312step0 raw42312step0Labels = mixedMoment B raw42312step1 raw42312step1Labels := by
      have ha : raw42312step1 = (fun i j => raw42312step0 (permutation72 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42312step1 raw42312step0; decide +kernel
      have hl : raw42312step1Labels = raw42312step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42312step0 raw42312step0Labels permutation72 permutation4
    mixedMoment B raw42312step1 raw42312step1Labels = mixedMoment B raw42312step2 raw42312step2Labels := by
      have ha : raw42312step2 = raw42312step1 := by apply Matrix.ext; unfold raw42312step2 raw42312step1; decide +kernel
      have hl : raw42312step1Labels = labelEmbedding1 ∘ raw42312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42312step1 raw42312step1Labels raw42312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

theorem canonical42313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42313 raw42313Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw42313 raw42313Labels = mixedMoment B raw42313step0 raw42313step0Labels := by
      have hz : ∀ j, raw42313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42313step0 = (fun i j => raw42313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42313step0 raw42313; decide +kernel
      have hl : raw42313step0Labels = raw42313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42313 raw42313Labels permutation434 hz
    mixedMoment B raw42313step0 raw42313step0Labels = mixedMoment B raw42313step1 raw42313step1Labels := by
      have ha : raw42313step1 = (fun i j => raw42313step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42313step1 raw42313step0; decide +kernel
      have hl : raw42313step1Labels = raw42313step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42313step0 raw42313step0Labels permutation59 permutation6
    mixedMoment B raw42313step1 raw42313step1Labels = mixedMoment B raw42313step2 raw42313step2Labels := by
      have ha : raw42313step2 = -raw42313step1 := by apply Matrix.ext; change ∀ i j, raw42313step2 i j = -(raw42313step1 i j); unfold raw42313step2 raw42313step1; decide +kernel
      have hl : raw42313step2Labels = raw42313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5188 node5188Labels := by rfl

theorem canonical42314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42314 raw42314Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw42314 raw42314Labels = mixedMoment B raw42314step0 raw42314step0Labels := by
      have ha : raw42314step0 = (fun i j => raw42314 (permutation342 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42314step0 raw42314; decide +kernel
      have hl : raw42314step0Labels = raw42314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42314 raw42314Labels permutation342 permutation4
    mixedMoment B raw42314step0 raw42314step0Labels = mixedMoment B raw42314step1 raw42314step1Labels := by
      have ha : raw42314step1 = raw42314step0 := by apply Matrix.ext; unfold raw42314step1 raw42314step0; decide +kernel
      have hl : raw42314step0Labels = labelEmbedding1 ∘ raw42314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42314step0 raw42314step0Labels raw42314step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

theorem canonical42315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42315 raw42315Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw42315 raw42315Labels = mixedMoment B raw42315step0 raw42315step0Labels := by
      have ha : raw42315step0 = (fun i j => raw42315 (permutation286 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42315step0 raw42315; decide +kernel
      have hl : raw42315step0Labels = raw42315Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42315 raw42315Labels permutation286 permutation6
    mixedMoment B raw42315step0 raw42315step0Labels = mixedMoment B raw42315step1 raw42315step1Labels := by
      have ha : raw42315step1 = -raw42315step0 := by apply Matrix.ext; change ∀ i j, raw42315step1 i j = -(raw42315step0 i j); unfold raw42315step1 raw42315step0; decide +kernel
      have hl : raw42315step1Labels = raw42315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5184 node5184Labels := by rfl

theorem canonical42316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42316 raw42316Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw42316 raw42316Labels = mixedMoment B raw42316step0 raw42316step0Labels := by
      have ha : raw42316step0 = (fun i j => raw42316 (permutation329 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42316step0 raw42316; decide +kernel
      have hl : raw42316step0Labels = raw42316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42316 raw42316Labels permutation329 permutation4
    mixedMoment B raw42316step0 raw42316step0Labels = mixedMoment B raw42316step1 raw42316step1Labels := by
      have ha : raw42316step1 = raw42316step0 := by apply Matrix.ext; unfold raw42316step1 raw42316step0; decide +kernel
      have hl : raw42316step0Labels = labelEmbedding1 ∘ raw42316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42316step0 raw42316step0Labels raw42316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

theorem canonical42317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42317 raw42317Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw42317 raw42317Labels = mixedMoment B raw42317step0 raw42317step0Labels := by
      have ha : raw42317step0 = (fun i j => raw42317 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42317step0 raw42317; decide +kernel
      have hl : raw42317step0Labels = raw42317Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42317 raw42317Labels permutation277 permutation6
    mixedMoment B raw42317step0 raw42317step0Labels = mixedMoment B raw42317step1 raw42317step1Labels := by
      have ha : raw42317step1 = -raw42317step0 := by apply Matrix.ext; change ∀ i j, raw42317step1 i j = -(raw42317step0 i j); unfold raw42317step1 raw42317step0; decide +kernel
      have hl : raw42317step1Labels = raw42317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5187 node5187Labels := by rfl

theorem canonical42318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42318 raw42318Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw42318 raw42318Labels = mixedMoment B raw42318step0 raw42318step0Labels := by
      have hz : ∀ j, raw42318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42318step0 = (fun i j => raw42318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42318step0 raw42318; decide +kernel
      have hl : raw42318step0Labels = raw42318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42318 raw42318Labels permutation434 hz
    mixedMoment B raw42318step0 raw42318step0Labels = mixedMoment B raw42318step1 raw42318step1Labels := by
      have ha : raw42318step1 = (fun i j => raw42318step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42318step1 raw42318step0; decide +kernel
      have hl : raw42318step1Labels = raw42318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42318step0 raw42318step0Labels permutation151 permutation2
    mixedMoment B raw42318step1 raw42318step1Labels = mixedMoment B raw42318step2 raw42318step2Labels := by
      have ha : raw42318step2 = -raw42318step1 := by apply Matrix.ext; change ∀ i j, raw42318step2 i j = -(raw42318step1 i j); unfold raw42318step2 raw42318step1; decide +kernel
      have hl : raw42318step2Labels = raw42318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42318step2 raw42318step2Labels = mixedMoment B raw42318step3 raw42318step3Labels := by
      have ha : raw42318step3 = raw42318step2 := by apply Matrix.ext; unfold raw42318step3 raw42318step2; decide +kernel
      have hl : raw42318step2Labels = labelEmbedding1 ∘ raw42318step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42318step2 raw42318step2Labels raw42318step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

theorem canonical42319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42319 raw42319Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw42319 raw42319Labels = mixedMoment B raw42319step0 raw42319step0Labels := by
      have hz : ∀ j, raw42319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42319step0 = (fun i j => raw42319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42319step0 raw42319; decide +kernel
      have hl : raw42319step0Labels = raw42319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42319 raw42319Labels permutation434 hz
    mixedMoment B raw42319step0 raw42319step0Labels = mixedMoment B raw42319step1 raw42319step1Labels := by
      have ha : raw42319step1 = (fun i j => raw42319step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42319step1 raw42319step0; decide +kernel
      have hl : raw42319step1Labels = raw42319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42319step0 raw42319step0Labels permutation144 permutation7
    mixedMoment B raw42319step1 raw42319step1Labels = mixedMoment B raw42319step2 raw42319step2Labels := by
      have ha : raw42319step2 = raw42319step1 := by apply Matrix.ext; unfold raw42319step2 raw42319step1; decide +kernel
      have hl : raw42319step1Labels = labelEmbedding6 ∘ raw42319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42319step1 raw42319step1Labels raw42319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

theorem canonical42320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42320 raw42320Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw42320 raw42320Labels = mixedMoment B raw42320step0 raw42320step0Labels := by
      have ha : raw42320step0 = (fun i j => raw42320 (permutation344 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42320step0 raw42320; decide +kernel
      have hl : raw42320step0Labels = raw42320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42320 raw42320Labels permutation344 permutation4
    mixedMoment B raw42320step0 raw42320step0Labels = mixedMoment B raw42320step1 raw42320step1Labels := by
      have ha : raw42320step1 = raw42320step0 := by apply Matrix.ext; unfold raw42320step1 raw42320step0; decide +kernel
      have hl : raw42320step0Labels = labelEmbedding1 ∘ raw42320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42320step0 raw42320step0Labels raw42320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

theorem canonical42321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42321 raw42321Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw42321 raw42321Labels = mixedMoment B raw42321step0 raw42321step0Labels := by
      have ha : raw42321step0 = (fun i j => raw42321 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42321step0 raw42321; decide +kernel
      have hl : raw42321step0Labels = raw42321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42321 raw42321Labels permutation287 permutation6
    mixedMoment B raw42321step0 raw42321step0Labels = mixedMoment B raw42321step1 raw42321step1Labels := by
      have ha : raw42321step1 = -raw42321step0 := by apply Matrix.ext; change ∀ i j, raw42321step1 i j = -(raw42321step0 i j); unfold raw42321step1 raw42321step0; decide +kernel
      have hl : raw42321step1Labels = raw42321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5185 node5185Labels := by rfl

theorem canonical42322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42322 raw42322Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw42322 raw42322Labels = mixedMoment B raw42322step0 raw42322step0Labels := by
      have hz : ∀ j, raw42322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42322step0 = (fun i j => raw42322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42322step0 raw42322; decide +kernel
      have hl : raw42322step0Labels = raw42322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42322 raw42322Labels permutation434 hz
    mixedMoment B raw42322step0 raw42322step0Labels = mixedMoment B raw42322step1 raw42322step1Labels := by
      have hz : ∀ j, raw42322step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42322step1 = (fun i j => raw42322step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42322step1 raw42322step0; decide +kernel
      have hl : raw42322step1Labels = raw42322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42322step0 raw42322step0Labels permutation80 hz
    mixedMoment B raw42322step1 raw42322step1Labels = mixedMoment B raw42322step2 raw42322step2Labels := by
      have ha : raw42322step2 = (fun i j => raw42322step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42322step2 raw42322step1; decide +kernel
      have hl : raw42322step2Labels = raw42322step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42322step1 raw42322step1Labels permutation31 permutation2
    mixedMoment B raw42322step2 raw42322step2Labels = mixedMoment B raw42322step3 raw42322step3Labels := by
      have ha : raw42322step3 = -raw42322step2 := by apply Matrix.ext; change ∀ i j, raw42322step3 i j = -(raw42322step2 i j); unfold raw42322step3 raw42322step2; decide +kernel
      have hl : raw42322step3Labels = raw42322step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42322step3 raw42322step3Labels = mixedMoment B raw42322step4 raw42322step4Labels := by
      have ha : raw42322step4 = raw42322step3 := by apply Matrix.ext; unfold raw42322step4 raw42322step3; decide +kernel
      have hl : raw42322step3Labels = labelEmbedding1 ∘ raw42322step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42322step3 raw42322step3Labels raw42322step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

theorem canonical42323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42323 raw42323Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw42323 raw42323Labels = mixedMoment B raw42323step0 raw42323step0Labels := by
      have hz : ∀ j, raw42323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42323step0 = (fun i j => raw42323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42323step0 raw42323; decide +kernel
      have hl : raw42323step0Labels = raw42323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42323 raw42323Labels permutation434 hz
    mixedMoment B raw42323step0 raw42323step0Labels = mixedMoment B raw42323step1 raw42323step1Labels := by
      have hz : ∀ j, raw42323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42323step1 = (fun i j => raw42323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42323step1 raw42323step0; decide +kernel
      have hl : raw42323step1Labels = raw42323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42323step0 raw42323step0Labels permutation80 hz
    mixedMoment B raw42323step1 raw42323step1Labels = mixedMoment B raw42323step2 raw42323step2Labels := by
      have ha : raw42323step2 = (fun i j => raw42323step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42323step2 raw42323step1; decide +kernel
      have hl : raw42323step2Labels = raw42323step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42323step1 raw42323step1Labels permutation30 permutation7
    mixedMoment B raw42323step2 raw42323step2Labels = mixedMoment B raw42323step3 raw42323step3Labels := by
      have ha : raw42323step3 = raw42323step2 := by apply Matrix.ext; unfold raw42323step3 raw42323step2; decide +kernel
      have hl : raw42323step2Labels = labelEmbedding6 ∘ raw42323step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42323step2 raw42323step2Labels raw42323step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

theorem canonical42324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42324 raw42324Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw42324 raw42324Labels = mixedMoment B raw42324step0 raw42324step0Labels := by
      have hz : ∀ j, raw42324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42324step0 = (fun i j => raw42324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42324step0 raw42324; decide +kernel
      have hl : raw42324step0Labels = raw42324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42324 raw42324Labels permutation346 hz
    mixedMoment B raw42324step0 raw42324step0Labels = mixedMoment B raw42324step1 raw42324step1Labels := by
      have ha : raw42324step1 = (fun i j => raw42324step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42324step1 raw42324step0; decide +kernel
      have hl : raw42324step1Labels = raw42324step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42324step0 raw42324step0Labels permutation78 permutation4
    mixedMoment B raw42324step1 raw42324step1Labels = mixedMoment B raw42324step2 raw42324step2Labels := by
      have ha : raw42324step2 = raw42324step1 := by apply Matrix.ext; unfold raw42324step2 raw42324step1; decide +kernel
      have hl : raw42324step1Labels = labelEmbedding1 ∘ raw42324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42324step1 raw42324step1Labels raw42324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

theorem canonical42325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42325 raw42325Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw42325 raw42325Labels = mixedMoment B raw42325step0 raw42325step0Labels := by
      have hz : ∀ j, raw42325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42325step0 = (fun i j => raw42325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42325step0 raw42325; decide +kernel
      have hl : raw42325step0Labels = raw42325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42325 raw42325Labels permutation346 hz
    mixedMoment B raw42325step0 raw42325step0Labels = mixedMoment B raw42325step1 raw42325step1Labels := by
      have ha : raw42325step1 = (fun i j => raw42325step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42325step1 raw42325step0; decide +kernel
      have hl : raw42325step1Labels = raw42325step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42325step0 raw42325step0Labels permutation96 permutation6
    _ = mixedMoment B node5147 node5147Labels := by rfl

theorem canonical42326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42326 raw42326Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw42326 raw42326Labels = mixedMoment B raw42326step0 raw42326step0Labels := by
      have hz : ∀ j, raw42326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42326step0 = (fun i j => raw42326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42326step0 raw42326; decide +kernel
      have hl : raw42326step0Labels = raw42326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42326 raw42326Labels permutation346 hz
    mixedMoment B raw42326step0 raw42326step0Labels = mixedMoment B raw42326step1 raw42326step1Labels := by
      have ha : raw42326step1 = (fun i j => raw42326step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42326step1 raw42326step0; decide +kernel
      have hl : raw42326step1Labels = raw42326step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42326step0 raw42326step0Labels permutation74 permutation4
    mixedMoment B raw42326step1 raw42326step1Labels = mixedMoment B raw42326step2 raw42326step2Labels := by
      have ha : raw42326step2 = raw42326step1 := by apply Matrix.ext; unfold raw42326step2 raw42326step1; decide +kernel
      have hl : raw42326step1Labels = labelEmbedding1 ∘ raw42326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42326step1 raw42326step1Labels raw42326step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

theorem canonical42327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42327 raw42327Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw42327 raw42327Labels = mixedMoment B raw42327step0 raw42327step0Labels := by
      have hz : ∀ j, raw42327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42327step0 = (fun i j => raw42327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42327step0 raw42327; decide +kernel
      have hl : raw42327step0Labels = raw42327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42327 raw42327Labels permutation346 hz
    mixedMoment B raw42327step0 raw42327step0Labels = mixedMoment B raw42327step1 raw42327step1Labels := by
      have ha : raw42327step1 = (fun i j => raw42327step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42327step1 raw42327step0; decide +kernel
      have hl : raw42327step1Labels = raw42327step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42327step0 raw42327step0Labels permutation60 permutation6
    mixedMoment B raw42327step1 raw42327step1Labels = mixedMoment B raw42327step2 raw42327step2Labels := by
      have ha : raw42327step2 = -raw42327step1 := by apply Matrix.ext; change ∀ i j, raw42327step2 i j = -(raw42327step1 i j); unfold raw42327step2 raw42327step1; decide +kernel
      have hl : raw42327step2Labels = raw42327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5189 node5189Labels := by rfl

theorem canonical42328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42328 raw42328Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw42328 raw42328Labels = mixedMoment B raw42328step0 raw42328step0Labels := by
      have hz : ∀ j, raw42328 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42328step0 = (fun i j => raw42328 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42328step0 raw42328; decide +kernel
      have hl : raw42328step0Labels = raw42328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42328 raw42328Labels permutation520 hz
    mixedMoment B raw42328step0 raw42328step0Labels = mixedMoment B raw42328step1 raw42328step1Labels := by
      have hz : ∀ j, raw42328step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42328step1 = (fun i j => raw42328step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42328step1 raw42328step0; decide +kernel
      have hl : raw42328step1Labels = raw42328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42328step0 raw42328step0Labels permutation104 hz
    mixedMoment B raw42328step1 raw42328step1Labels = mixedMoment B raw42328step2 raw42328step2Labels := by
      have hz : ∀ j, raw42328step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42328step2 = (fun i j => raw42328step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42328step2 raw42328step1; decide +kernel
      have hl : raw42328step2Labels = raw42328step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42328step1 raw42328step1Labels permutation20 hz
    mixedMoment B raw42328step2 raw42328step2Labels = mixedMoment B raw42328step3 raw42328step3Labels := by
      have ha : raw42328step3 = (fun i j => raw42328step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42328step3 raw42328step2; decide +kernel
      have hl : raw42328step3Labels = raw42328step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42328step2 raw42328step2Labels permutation4 permutation4
    mixedMoment B raw42328step3 raw42328step3Labels = mixedMoment B raw42328step4 raw42328step4Labels := by
      have ha : raw42328step4 = -raw42328step3 := by apply Matrix.ext; change ∀ i j, raw42328step4 i j = -(raw42328step3 i j); unfold raw42328step4 raw42328step3; decide +kernel
      have hl : raw42328step4Labels = raw42328step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42328step4 raw42328step4Labels = mixedMoment B raw42328step5 raw42328step5Labels := by
      have ha : raw42328step5 = raw42328step4 := by apply Matrix.ext; unfold raw42328step5 raw42328step4; decide +kernel
      have hl : raw42328step4Labels = labelEmbedding1 ∘ raw42328step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42328step4 raw42328step4Labels raw42328step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

theorem canonical42329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42329 raw42329Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw42329 raw42329Labels = mixedMoment B raw42329step0 raw42329step0Labels := by
      have hz : ∀ j, raw42329 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42329step0 = (fun i j => raw42329 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42329step0 raw42329; decide +kernel
      have hl : raw42329step0Labels = raw42329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42329 raw42329Labels permutation520 hz
    mixedMoment B raw42329step0 raw42329step0Labels = mixedMoment B raw42329step1 raw42329step1Labels := by
      have hz : ∀ j, raw42329step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42329step1 = (fun i j => raw42329step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42329step1 raw42329step0; decide +kernel
      have hl : raw42329step1Labels = raw42329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42329step0 raw42329step0Labels permutation104 hz
    mixedMoment B raw42329step1 raw42329step1Labels = mixedMoment B raw42329step2 raw42329step2Labels := by
      have hz : ∀ j, raw42329step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42329step2 = (fun i j => raw42329step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42329step2 raw42329step1; decide +kernel
      have hl : raw42329step2Labels = raw42329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42329step1 raw42329step1Labels permutation20 hz
    mixedMoment B raw42329step2 raw42329step2Labels = mixedMoment B raw42329step3 raw42329step3Labels := by
      have ha : raw42329step3 = (fun i j => raw42329step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42329step3 raw42329step2; decide +kernel
      have hl : raw42329step3Labels = raw42329step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42329step2 raw42329step2Labels permutation6 permutation5
    mixedMoment B raw42329step3 raw42329step3Labels = mixedMoment B raw42329step4 raw42329step4Labels := by
      have ha : raw42329step4 = raw42329step3 := by apply Matrix.ext; unfold raw42329step4 raw42329step3; decide +kernel
      have hl : raw42329step3Labels = labelEmbedding9 ∘ raw42329step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42329step3 raw42329step3Labels raw42329step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

theorem canonical42330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42330 raw42330Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw42330 raw42330Labels = mixedMoment B raw42330step0 raw42330step0Labels := by
      have hz : ∀ j, raw42330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42330step0 = (fun i j => raw42330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42330step0 raw42330; decide +kernel
      have hl : raw42330step0Labels = raw42330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42330 raw42330Labels permutation434 hz
    mixedMoment B raw42330step0 raw42330step0Labels = mixedMoment B raw42330step1 raw42330step1Labels := by
      have hz : ∀ j, raw42330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42330step1 = (fun i j => raw42330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42330step1 raw42330step0; decide +kernel
      have hl : raw42330step1Labels = raw42330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42330step0 raw42330step0Labels permutation80 hz
    mixedMoment B raw42330step1 raw42330step1Labels = mixedMoment B raw42330step2 raw42330step2Labels := by
      have ha : raw42330step2 = (fun i j => raw42330step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42330step2 raw42330step1; decide +kernel
      have hl : raw42330step2Labels = raw42330step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42330step1 raw42330step1Labels permutation16 permutation4
    mixedMoment B raw42330step2 raw42330step2Labels = mixedMoment B raw42330step3 raw42330step3Labels := by
      have ha : raw42330step3 = -raw42330step2 := by apply Matrix.ext; change ∀ i j, raw42330step3 i j = -(raw42330step2 i j); unfold raw42330step3 raw42330step2; decide +kernel
      have hl : raw42330step3Labels = raw42330step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42330step3 raw42330step3Labels = mixedMoment B raw42330step4 raw42330step4Labels := by
      have ha : raw42330step4 = raw42330step3 := by apply Matrix.ext; unfold raw42330step4 raw42330step3; decide +kernel
      have hl : raw42330step3Labels = labelEmbedding1 ∘ raw42330step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42330step3 raw42330step3Labels raw42330step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

theorem canonical42331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42331 raw42331Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw42331 raw42331Labels = mixedMoment B raw42331step0 raw42331step0Labels := by
      have hz : ∀ j, raw42331 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42331step0 = (fun i j => raw42331 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42331step0 raw42331; decide +kernel
      have hl : raw42331step0Labels = raw42331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42331 raw42331Labels permutation434 hz
    mixedMoment B raw42331step0 raw42331step0Labels = mixedMoment B raw42331step1 raw42331step1Labels := by
      have hz : ∀ j, raw42331step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42331step1 = (fun i j => raw42331step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42331step1 raw42331step0; decide +kernel
      have hl : raw42331step1Labels = raw42331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42331step0 raw42331step0Labels permutation80 hz
    mixedMoment B raw42331step1 raw42331step1Labels = mixedMoment B raw42331step2 raw42331step2Labels := by
      have ha : raw42331step2 = (fun i j => raw42331step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42331step2 raw42331step1; decide +kernel
      have hl : raw42331step2Labels = raw42331step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42331step1 raw42331step1Labels permutation16 permutation4
    mixedMoment B raw42331step2 raw42331step2Labels = mixedMoment B raw42331step3 raw42331step3Labels := by
      have ha : raw42331step3 = -raw42331step2 := by apply Matrix.ext; change ∀ i j, raw42331step3 i j = -(raw42331step2 i j); unfold raw42331step3 raw42331step2; decide +kernel
      have hl : raw42331step3Labels = raw42331step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42331step3 raw42331step3Labels = mixedMoment B raw42331step4 raw42331step4Labels := by
      have ha : raw42331step4 = raw42331step3 := by apply Matrix.ext; unfold raw42331step4 raw42331step3; decide +kernel
      have hl : raw42331step3Labels = labelEmbedding10 ∘ raw42331step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42331step3 raw42331step3Labels raw42331step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

theorem canonical42332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42332 raw42332Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw42332 raw42332Labels = mixedMoment B raw42332step0 raw42332step0Labels := by
      have hz : ∀ j, raw42332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42332step0 = (fun i j => raw42332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42332step0 raw42332; decide +kernel
      have hl : raw42332step0Labels = raw42332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42332 raw42332Labels permutation434 hz
    mixedMoment B raw42332step0 raw42332step0Labels = mixedMoment B raw42332step1 raw42332step1Labels := by
      have hz : ∀ j, raw42332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42332step1 = (fun i j => raw42332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42332step1 raw42332step0; decide +kernel
      have hl : raw42332step1Labels = raw42332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42332step0 raw42332step0Labels permutation80 hz
    mixedMoment B raw42332step1 raw42332step1Labels = mixedMoment B raw42332step2 raw42332step2Labels := by
      have ha : raw42332step2 = (fun i j => raw42332step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42332step2 raw42332step1; decide +kernel
      have hl : raw42332step2Labels = raw42332step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42332step1 raw42332step1Labels permutation14 permutation4
    mixedMoment B raw42332step2 raw42332step2Labels = mixedMoment B raw42332step3 raw42332step3Labels := by
      have ha : raw42332step3 = -raw42332step2 := by apply Matrix.ext; change ∀ i j, raw42332step3 i j = -(raw42332step2 i j); unfold raw42332step3 raw42332step2; decide +kernel
      have hl : raw42332step3Labels = raw42332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42332step3 raw42332step3Labels = mixedMoment B raw42332step4 raw42332step4Labels := by
      have ha : raw42332step4 = raw42332step3 := by apply Matrix.ext; unfold raw42332step4 raw42332step3; decide +kernel
      have hl : raw42332step3Labels = labelEmbedding1 ∘ raw42332step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42332step3 raw42332step3Labels raw42332step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

theorem canonical42333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42333 raw42333Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw42333 raw42333Labels = mixedMoment B raw42333step0 raw42333step0Labels := by
      have hz : ∀ j, raw42333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42333step0 = (fun i j => raw42333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42333step0 raw42333; decide +kernel
      have hl : raw42333step0Labels = raw42333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42333 raw42333Labels permutation434 hz
    mixedMoment B raw42333step0 raw42333step0Labels = mixedMoment B raw42333step1 raw42333step1Labels := by
      have hz : ∀ j, raw42333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42333step1 = (fun i j => raw42333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42333step1 raw42333step0; decide +kernel
      have hl : raw42333step1Labels = raw42333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42333step0 raw42333step0Labels permutation80 hz
    mixedMoment B raw42333step1 raw42333step1Labels = mixedMoment B raw42333step2 raw42333step2Labels := by
      have ha : raw42333step2 = (fun i j => raw42333step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42333step2 raw42333step1; decide +kernel
      have hl : raw42333step2Labels = raw42333step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42333step1 raw42333step1Labels permutation14 permutation4
    mixedMoment B raw42333step2 raw42333step2Labels = mixedMoment B raw42333step3 raw42333step3Labels := by
      have ha : raw42333step3 = -raw42333step2 := by apply Matrix.ext; change ∀ i j, raw42333step3 i j = -(raw42333step2 i j); unfold raw42333step3 raw42333step2; decide +kernel
      have hl : raw42333step3Labels = raw42333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42333step3 raw42333step3Labels = mixedMoment B raw42333step4 raw42333step4Labels := by
      have ha : raw42333step4 = raw42333step3 := by apply Matrix.ext; unfold raw42333step4 raw42333step3; decide +kernel
      have hl : raw42333step3Labels = labelEmbedding10 ∘ raw42333step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42333step3 raw42333step3Labels raw42333step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

theorem canonical42334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42334 raw42334Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw42334 raw42334Labels = mixedMoment B raw42334step0 raw42334step0Labels := by
      have hz : ∀ j, raw42334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42334step0 = (fun i j => raw42334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42334step0 raw42334; decide +kernel
      have hl : raw42334step0Labels = raw42334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42334 raw42334Labels permutation434 hz
    mixedMoment B raw42334step0 raw42334step0Labels = mixedMoment B raw42334step1 raw42334step1Labels := by
      have hz : ∀ j, raw42334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42334step1 = (fun i j => raw42334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42334step1 raw42334step0; decide +kernel
      have hl : raw42334step1Labels = raw42334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42334step0 raw42334step0Labels permutation80 hz
    mixedMoment B raw42334step1 raw42334step1Labels = mixedMoment B raw42334step2 raw42334step2Labels := by
      have ha : raw42334step2 = (fun i j => raw42334step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42334step2 raw42334step1; decide +kernel
      have hl : raw42334step2Labels = raw42334step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42334step1 raw42334step1Labels permutation15 permutation4
    mixedMoment B raw42334step2 raw42334step2Labels = mixedMoment B raw42334step3 raw42334step3Labels := by
      have ha : raw42334step3 = -raw42334step2 := by apply Matrix.ext; change ∀ i j, raw42334step3 i j = -(raw42334step2 i j); unfold raw42334step3 raw42334step2; decide +kernel
      have hl : raw42334step3Labels = raw42334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42334step3 raw42334step3Labels = mixedMoment B raw42334step4 raw42334step4Labels := by
      have ha : raw42334step4 = raw42334step3 := by apply Matrix.ext; unfold raw42334step4 raw42334step3; decide +kernel
      have hl : raw42334step3Labels = labelEmbedding1 ∘ raw42334step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42334step3 raw42334step3Labels raw42334step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

theorem canonical42335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42335 raw42335Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42335 raw42335Labels = mixedMoment B raw42335step0 raw42335step0Labels := by
      have hz : ∀ j, raw42335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42335step0 = (fun i j => raw42335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42335step0 raw42335; decide +kernel
      have hl : raw42335step0Labels = raw42335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42335 raw42335Labels permutation434 hz
    mixedMoment B raw42335step0 raw42335step0Labels = mixedMoment B raw42335step1 raw42335step1Labels := by
      have hz : ∀ j, raw42335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42335step1 = (fun i j => raw42335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42335step1 raw42335step0; decide +kernel
      have hl : raw42335step1Labels = raw42335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42335step0 raw42335step0Labels permutation80 hz
    mixedMoment B raw42335step1 raw42335step1Labels = mixedMoment B raw42335step2 raw42335step2Labels := by
      have ha : raw42335step2 = (fun i j => raw42335step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42335step2 raw42335step1; decide +kernel
      have hl : raw42335step2Labels = raw42335step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42335step1 raw42335step1Labels permutation15 permutation4
    mixedMoment B raw42335step2 raw42335step2Labels = mixedMoment B raw42335step3 raw42335step3Labels := by
      have ha : raw42335step3 = -raw42335step2 := by apply Matrix.ext; change ∀ i j, raw42335step3 i j = -(raw42335step2 i j); unfold raw42335step3 raw42335step2; decide +kernel
      have hl : raw42335step3Labels = raw42335step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42335step3 raw42335step3Labels = mixedMoment B raw42335step4 raw42335step4Labels := by
      have ha : raw42335step4 = raw42335step3 := by apply Matrix.ext; unfold raw42335step4 raw42335step3; decide +kernel
      have hl : raw42335step3Labels = labelEmbedding10 ∘ raw42335step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42335step3 raw42335step3Labels raw42335step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

theorem canonical42336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42336 raw42336Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw42336 raw42336Labels = mixedMoment B raw42336step0 raw42336step0Labels := by
      have hz : ∀ j, raw42336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42336step0 = (fun i j => raw42336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42336step0 raw42336; decide +kernel
      have hl : raw42336step0Labels = raw42336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42336 raw42336Labels permutation434 hz
    mixedMoment B raw42336step0 raw42336step0Labels = mixedMoment B raw42336step1 raw42336step1Labels := by
      have hz : ∀ j, raw42336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42336step1 = (fun i j => raw42336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42336step1 raw42336step0; decide +kernel
      have hl : raw42336step1Labels = raw42336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42336step0 raw42336step0Labels permutation80 hz
    mixedMoment B raw42336step1 raw42336step1Labels = mixedMoment B raw42336step2 raw42336step2Labels := by
      have ha : raw42336step2 = (fun i j => raw42336step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42336step2 raw42336step1; decide +kernel
      have hl : raw42336step2Labels = raw42336step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42336step1 raw42336step1Labels permutation21 permutation4
    mixedMoment B raw42336step2 raw42336step2Labels = mixedMoment B raw42336step3 raw42336step3Labels := by
      have ha : raw42336step3 = raw42336step2 := by apply Matrix.ext; unfold raw42336step3 raw42336step2; decide +kernel
      have hl : raw42336step2Labels = labelEmbedding1 ∘ raw42336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42336step2 raw42336step2Labels raw42336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2680 node2680Labels := by rfl

theorem canonical42337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42337 raw42337Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw42337 raw42337Labels = mixedMoment B raw42337step0 raw42337step0Labels := by
      have hz : ∀ j, raw42337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42337step0 = (fun i j => raw42337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42337step0 raw42337; decide +kernel
      have hl : raw42337step0Labels = raw42337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42337 raw42337Labels permutation434 hz
    mixedMoment B raw42337step0 raw42337step0Labels = mixedMoment B raw42337step1 raw42337step1Labels := by
      have hz : ∀ j, raw42337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42337step1 = (fun i j => raw42337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42337step1 raw42337step0; decide +kernel
      have hl : raw42337step1Labels = raw42337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42337step0 raw42337step0Labels permutation80 hz
    mixedMoment B raw42337step1 raw42337step1Labels = mixedMoment B raw42337step2 raw42337step2Labels := by
      have ha : raw42337step2 = (fun i j => raw42337step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42337step2 raw42337step1; decide +kernel
      have hl : raw42337step2Labels = raw42337step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42337step1 raw42337step1Labels permutation21 permutation4
    mixedMoment B raw42337step2 raw42337step2Labels = mixedMoment B raw42337step3 raw42337step3Labels := by
      have ha : raw42337step3 = raw42337step2 := by apply Matrix.ext; unfold raw42337step3 raw42337step2; decide +kernel
      have hl : raw42337step2Labels = labelEmbedding10 ∘ raw42337step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42337step2 raw42337step2Labels raw42337step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

theorem canonical42338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42338 raw42338Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw42338 raw42338Labels = mixedMoment B raw42338step0 raw42338step0Labels := by
      have hz : ∀ j, raw42338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42338step0 = (fun i j => raw42338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42338step0 raw42338; decide +kernel
      have hl : raw42338step0Labels = raw42338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42338 raw42338Labels permutation346 hz
    mixedMoment B raw42338step0 raw42338step0Labels = mixedMoment B raw42338step1 raw42338step1Labels := by
      have ha : raw42338step1 = (fun i j => raw42338step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42338step1 raw42338step0; decide +kernel
      have hl : raw42338step1Labels = raw42338step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42338step0 raw42338step0Labels permutation68 permutation4
    mixedMoment B raw42338step1 raw42338step1Labels = mixedMoment B raw42338step2 raw42338step2Labels := by
      have ha : raw42338step2 = -raw42338step1 := by apply Matrix.ext; change ∀ i j, raw42338step2 i j = -(raw42338step1 i j); unfold raw42338step2 raw42338step1; decide +kernel
      have hl : raw42338step2Labels = raw42338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42338step2 raw42338step2Labels = mixedMoment B raw42338step3 raw42338step3Labels := by
      have ha : raw42338step3 = raw42338step2 := by apply Matrix.ext; unfold raw42338step3 raw42338step2; decide +kernel
      have hl : raw42338step2Labels = labelEmbedding1 ∘ raw42338step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42338step2 raw42338step2Labels raw42338step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

theorem canonical42339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42339 raw42339Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42339 raw42339Labels = mixedMoment B raw42339step0 raw42339step0Labels := by
      have hz : ∀ j, raw42339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42339step0 = (fun i j => raw42339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42339step0 raw42339; decide +kernel
      have hl : raw42339step0Labels = raw42339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42339 raw42339Labels permutation346 hz
    mixedMoment B raw42339step0 raw42339step0Labels = mixedMoment B raw42339step1 raw42339step1Labels := by
      have ha : raw42339step1 = (fun i j => raw42339step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42339step1 raw42339step0; decide +kernel
      have hl : raw42339step1Labels = raw42339step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42339step0 raw42339step0Labels permutation68 permutation4
    mixedMoment B raw42339step1 raw42339step1Labels = mixedMoment B raw42339step2 raw42339step2Labels := by
      have ha : raw42339step2 = -raw42339step1 := by apply Matrix.ext; change ∀ i j, raw42339step2 i j = -(raw42339step1 i j); unfold raw42339step2 raw42339step1; decide +kernel
      have hl : raw42339step2Labels = raw42339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42339step2 raw42339step2Labels = mixedMoment B raw42339step3 raw42339step3Labels := by
      have ha : raw42339step3 = raw42339step2 := by apply Matrix.ext; unfold raw42339step3 raw42339step2; decide +kernel
      have hl : raw42339step2Labels = labelEmbedding10 ∘ raw42339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42339step2 raw42339step2Labels raw42339step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

theorem canonical42340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42340 raw42340Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw42340 raw42340Labels = mixedMoment B raw42340step0 raw42340step0Labels := by
      have hz : ∀ j, raw42340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42340step0 = (fun i j => raw42340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42340step0 raw42340; decide +kernel
      have hl : raw42340step0Labels = raw42340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42340 raw42340Labels permutation346 hz
    mixedMoment B raw42340step0 raw42340step0Labels = mixedMoment B raw42340step1 raw42340step1Labels := by
      have ha : raw42340step1 = (fun i j => raw42340step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42340step1 raw42340step0; decide +kernel
      have hl : raw42340step1Labels = raw42340step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42340step0 raw42340step0Labels permutation61 permutation4
    mixedMoment B raw42340step1 raw42340step1Labels = mixedMoment B raw42340step2 raw42340step2Labels := by
      have ha : raw42340step2 = -raw42340step1 := by apply Matrix.ext; change ∀ i j, raw42340step2 i j = -(raw42340step1 i j); unfold raw42340step2 raw42340step1; decide +kernel
      have hl : raw42340step2Labels = raw42340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42340step2 raw42340step2Labels = mixedMoment B raw42340step3 raw42340step3Labels := by
      have ha : raw42340step3 = raw42340step2 := by apply Matrix.ext; unfold raw42340step3 raw42340step2; decide +kernel
      have hl : raw42340step2Labels = labelEmbedding1 ∘ raw42340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42340step2 raw42340step2Labels raw42340step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

theorem canonical42341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42341 raw42341Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42341 raw42341Labels = mixedMoment B raw42341step0 raw42341step0Labels := by
      have hz : ∀ j, raw42341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42341step0 = (fun i j => raw42341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42341step0 raw42341; decide +kernel
      have hl : raw42341step0Labels = raw42341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42341 raw42341Labels permutation346 hz
    mixedMoment B raw42341step0 raw42341step0Labels = mixedMoment B raw42341step1 raw42341step1Labels := by
      have ha : raw42341step1 = (fun i j => raw42341step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42341step1 raw42341step0; decide +kernel
      have hl : raw42341step1Labels = raw42341step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42341step0 raw42341step0Labels permutation61 permutation4
    mixedMoment B raw42341step1 raw42341step1Labels = mixedMoment B raw42341step2 raw42341step2Labels := by
      have ha : raw42341step2 = -raw42341step1 := by apply Matrix.ext; change ∀ i j, raw42341step2 i j = -(raw42341step1 i j); unfold raw42341step2 raw42341step1; decide +kernel
      have hl : raw42341step2Labels = raw42341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42341step2 raw42341step2Labels = mixedMoment B raw42341step3 raw42341step3Labels := by
      have ha : raw42341step3 = raw42341step2 := by apply Matrix.ext; unfold raw42341step3 raw42341step2; decide +kernel
      have hl : raw42341step2Labels = labelEmbedding10 ∘ raw42341step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42341step2 raw42341step2Labels raw42341step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

theorem canonical42342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42342 raw42342Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw42342 raw42342Labels = mixedMoment B raw42342step0 raw42342step0Labels := by
      have hz : ∀ j, raw42342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42342step0 = (fun i j => raw42342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42342step0 raw42342; decide +kernel
      have hl : raw42342step0Labels = raw42342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42342 raw42342Labels permutation346 hz
    mixedMoment B raw42342step0 raw42342step0Labels = mixedMoment B raw42342step1 raw42342step1Labels := by
      have ha : raw42342step1 = (fun i j => raw42342step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42342step1 raw42342step0; decide +kernel
      have hl : raw42342step1Labels = raw42342step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42342step0 raw42342step0Labels permutation74 permutation4
    mixedMoment B raw42342step1 raw42342step1Labels = mixedMoment B raw42342step2 raw42342step2Labels := by
      have ha : raw42342step2 = -raw42342step1 := by apply Matrix.ext; change ∀ i j, raw42342step2 i j = -(raw42342step1 i j); unfold raw42342step2 raw42342step1; decide +kernel
      have hl : raw42342step2Labels = raw42342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42342step2 raw42342step2Labels = mixedMoment B raw42342step3 raw42342step3Labels := by
      have ha : raw42342step3 = raw42342step2 := by apply Matrix.ext; unfold raw42342step3 raw42342step2; decide +kernel
      have hl : raw42342step2Labels = labelEmbedding1 ∘ raw42342step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42342step2 raw42342step2Labels raw42342step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

theorem canonical42343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42343 raw42343Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw42343 raw42343Labels = mixedMoment B raw42343step0 raw42343step0Labels := by
      have hz : ∀ j, raw42343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42343step0 = (fun i j => raw42343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42343step0 raw42343; decide +kernel
      have hl : raw42343step0Labels = raw42343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42343 raw42343Labels permutation346 hz
    mixedMoment B raw42343step0 raw42343step0Labels = mixedMoment B raw42343step1 raw42343step1Labels := by
      have ha : raw42343step1 = (fun i j => raw42343step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42343step1 raw42343step0; decide +kernel
      have hl : raw42343step1Labels = raw42343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42343step0 raw42343step0Labels permutation74 permutation4
    mixedMoment B raw42343step1 raw42343step1Labels = mixedMoment B raw42343step2 raw42343step2Labels := by
      have ha : raw42343step2 = -raw42343step1 := by apply Matrix.ext; change ∀ i j, raw42343step2 i j = -(raw42343step1 i j); unfold raw42343step2 raw42343step1; decide +kernel
      have hl : raw42343step2Labels = raw42343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42343step2 raw42343step2Labels = mixedMoment B raw42343step3 raw42343step3Labels := by
      have ha : raw42343step3 = raw42343step2 := by apply Matrix.ext; unfold raw42343step3 raw42343step2; decide +kernel
      have hl : raw42343step2Labels = labelEmbedding10 ∘ raw42343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42343step2 raw42343step2Labels raw42343step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

theorem canonical42344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42344 raw42344Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw42344 raw42344Labels = mixedMoment B raw42344step0 raw42344step0Labels := by
      have hz : ∀ j, raw42344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42344step0 = (fun i j => raw42344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42344step0 raw42344; decide +kernel
      have hl : raw42344step0Labels = raw42344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42344 raw42344Labels permutation346 hz
    mixedMoment B raw42344step0 raw42344step0Labels = mixedMoment B raw42344step1 raw42344step1Labels := by
      have ha : raw42344step1 = (fun i j => raw42344step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42344step1 raw42344step0; decide +kernel
      have hl : raw42344step1Labels = raw42344step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42344step0 raw42344step0Labels permutation75 permutation4
    mixedMoment B raw42344step1 raw42344step1Labels = mixedMoment B raw42344step2 raw42344step2Labels := by
      have ha : raw42344step2 = -raw42344step1 := by apply Matrix.ext; change ∀ i j, raw42344step2 i j = -(raw42344step1 i j); unfold raw42344step2 raw42344step1; decide +kernel
      have hl : raw42344step2Labels = raw42344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42344step2 raw42344step2Labels = mixedMoment B raw42344step3 raw42344step3Labels := by
      have ha : raw42344step3 = raw42344step2 := by apply Matrix.ext; unfold raw42344step3 raw42344step2; decide +kernel
      have hl : raw42344step2Labels = labelEmbedding1 ∘ raw42344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42344step2 raw42344step2Labels raw42344step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

theorem canonical42345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42345 raw42345Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw42345 raw42345Labels = mixedMoment B raw42345step0 raw42345step0Labels := by
      have hz : ∀ j, raw42345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42345step0 = (fun i j => raw42345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42345step0 raw42345; decide +kernel
      have hl : raw42345step0Labels = raw42345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42345 raw42345Labels permutation346 hz
    mixedMoment B raw42345step0 raw42345step0Labels = mixedMoment B raw42345step1 raw42345step1Labels := by
      have ha : raw42345step1 = (fun i j => raw42345step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42345step1 raw42345step0; decide +kernel
      have hl : raw42345step1Labels = raw42345step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42345step0 raw42345step0Labels permutation75 permutation4
    mixedMoment B raw42345step1 raw42345step1Labels = mixedMoment B raw42345step2 raw42345step2Labels := by
      have ha : raw42345step2 = -raw42345step1 := by apply Matrix.ext; change ∀ i j, raw42345step2 i j = -(raw42345step1 i j); unfold raw42345step2 raw42345step1; decide +kernel
      have hl : raw42345step2Labels = raw42345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42345step2 raw42345step2Labels = mixedMoment B raw42345step3 raw42345step3Labels := by
      have ha : raw42345step3 = raw42345step2 := by apply Matrix.ext; unfold raw42345step3 raw42345step2; decide +kernel
      have hl : raw42345step2Labels = labelEmbedding10 ∘ raw42345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42345step2 raw42345step2Labels raw42345step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

theorem canonical42346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42346 raw42346Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw42346 raw42346Labels = mixedMoment B raw42346step0 raw42346step0Labels := by
      have hz : ∀ j, raw42346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42346step0 = (fun i j => raw42346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42346step0 raw42346; decide +kernel
      have hl : raw42346step0Labels = raw42346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42346 raw42346Labels permutation346 hz
    mixedMoment B raw42346step0 raw42346step0Labels = mixedMoment B raw42346step1 raw42346step1Labels := by
      have ha : raw42346step1 = (fun i j => raw42346step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42346step1 raw42346step0; decide +kernel
      have hl : raw42346step1Labels = raw42346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42346step0 raw42346step0Labels permutation131 permutation4
    mixedMoment B raw42346step1 raw42346step1Labels = mixedMoment B raw42346step2 raw42346step2Labels := by
      have ha : raw42346step2 = raw42346step1 := by apply Matrix.ext; unfold raw42346step2 raw42346step1; decide +kernel
      have hl : raw42346step1Labels = labelEmbedding1 ∘ raw42346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42346step1 raw42346step1Labels raw42346step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

theorem canonical42347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42347 raw42347Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw42347 raw42347Labels = mixedMoment B raw42347step0 raw42347step0Labels := by
      have hz : ∀ j, raw42347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42347step0 = (fun i j => raw42347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42347step0 raw42347; decide +kernel
      have hl : raw42347step0Labels = raw42347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42347 raw42347Labels permutation346 hz
    mixedMoment B raw42347step0 raw42347step0Labels = mixedMoment B raw42347step1 raw42347step1Labels := by
      have ha : raw42347step1 = (fun i j => raw42347step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42347step1 raw42347step0; decide +kernel
      have hl : raw42347step1Labels = raw42347step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42347step0 raw42347step0Labels permutation131 permutation4
    mixedMoment B raw42347step1 raw42347step1Labels = mixedMoment B raw42347step2 raw42347step2Labels := by
      have ha : raw42347step2 = raw42347step1 := by apply Matrix.ext; unfold raw42347step2 raw42347step1; decide +kernel
      have hl : raw42347step1Labels = labelEmbedding10 ∘ raw42347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42347step1 raw42347step1Labels raw42347step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

theorem canonical42348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42348 raw42348Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw42348 raw42348Labels = mixedMoment B raw42348step0 raw42348step0Labels := by
      have hz : ∀ j, raw42348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42348step0 = (fun i j => raw42348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42348step0 raw42348; decide +kernel
      have hl : raw42348step0Labels = raw42348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42348 raw42348Labels permutation346 hz
    mixedMoment B raw42348step0 raw42348step0Labels = mixedMoment B raw42348step1 raw42348step1Labels := by
      have ha : raw42348step1 = (fun i j => raw42348step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42348step1 raw42348step0; decide +kernel
      have hl : raw42348step1Labels = raw42348step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42348step0 raw42348step0Labels permutation62 permutation4
    mixedMoment B raw42348step1 raw42348step1Labels = mixedMoment B raw42348step2 raw42348step2Labels := by
      have ha : raw42348step2 = -raw42348step1 := by apply Matrix.ext; change ∀ i j, raw42348step2 i j = -(raw42348step1 i j); unfold raw42348step2 raw42348step1; decide +kernel
      have hl : raw42348step2Labels = raw42348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42348step2 raw42348step2Labels = mixedMoment B raw42348step3 raw42348step3Labels := by
      have ha : raw42348step3 = raw42348step2 := by apply Matrix.ext; unfold raw42348step3 raw42348step2; decide +kernel
      have hl : raw42348step2Labels = labelEmbedding1 ∘ raw42348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42348step2 raw42348step2Labels raw42348step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

theorem canonical42349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42349 raw42349Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42349 raw42349Labels = mixedMoment B raw42349step0 raw42349step0Labels := by
      have hz : ∀ j, raw42349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42349step0 = (fun i j => raw42349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42349step0 raw42349; decide +kernel
      have hl : raw42349step0Labels = raw42349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42349 raw42349Labels permutation346 hz
    mixedMoment B raw42349step0 raw42349step0Labels = mixedMoment B raw42349step1 raw42349step1Labels := by
      have ha : raw42349step1 = (fun i j => raw42349step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42349step1 raw42349step0; decide +kernel
      have hl : raw42349step1Labels = raw42349step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42349step0 raw42349step0Labels permutation62 permutation4
    mixedMoment B raw42349step1 raw42349step1Labels = mixedMoment B raw42349step2 raw42349step2Labels := by
      have ha : raw42349step2 = -raw42349step1 := by apply Matrix.ext; change ∀ i j, raw42349step2 i j = -(raw42349step1 i j); unfold raw42349step2 raw42349step1; decide +kernel
      have hl : raw42349step2Labels = raw42349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42349step2 raw42349step2Labels = mixedMoment B raw42349step3 raw42349step3Labels := by
      have ha : raw42349step3 = raw42349step2 := by apply Matrix.ext; unfold raw42349step3 raw42349step2; decide +kernel
      have hl : raw42349step2Labels = labelEmbedding10 ∘ raw42349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42349step2 raw42349step2Labels raw42349step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical42350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42350 raw42350Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw42350 raw42350Labels = mixedMoment B raw42350step0 raw42350step0Labels := by
      have hz : ∀ j, raw42350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42350step0 = (fun i j => raw42350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42350step0 raw42350; decide +kernel
      have hl : raw42350step0Labels = raw42350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42350 raw42350Labels permutation346 hz
    mixedMoment B raw42350step0 raw42350step0Labels = mixedMoment B raw42350step1 raw42350step1Labels := by
      have ha : raw42350step1 = (fun i j => raw42350step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42350step1 raw42350step0; decide +kernel
      have hl : raw42350step1Labels = raw42350step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42350step0 raw42350step0Labels permutation56 permutation4
    mixedMoment B raw42350step1 raw42350step1Labels = mixedMoment B raw42350step2 raw42350step2Labels := by
      have ha : raw42350step2 = -raw42350step1 := by apply Matrix.ext; change ∀ i j, raw42350step2 i j = -(raw42350step1 i j); unfold raw42350step2 raw42350step1; decide +kernel
      have hl : raw42350step2Labels = raw42350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42350step2 raw42350step2Labels = mixedMoment B raw42350step3 raw42350step3Labels := by
      have ha : raw42350step3 = raw42350step2 := by apply Matrix.ext; unfold raw42350step3 raw42350step2; decide +kernel
      have hl : raw42350step2Labels = labelEmbedding1 ∘ raw42350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42350step2 raw42350step2Labels raw42350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

theorem canonical42351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42351 raw42351Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw42351 raw42351Labels = mixedMoment B raw42351step0 raw42351step0Labels := by
      have hz : ∀ j, raw42351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42351step0 = (fun i j => raw42351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42351step0 raw42351; decide +kernel
      have hl : raw42351step0Labels = raw42351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42351 raw42351Labels permutation346 hz
    mixedMoment B raw42351step0 raw42351step0Labels = mixedMoment B raw42351step1 raw42351step1Labels := by
      have ha : raw42351step1 = (fun i j => raw42351step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42351step1 raw42351step0; decide +kernel
      have hl : raw42351step1Labels = raw42351step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42351step0 raw42351step0Labels permutation56 permutation4
    mixedMoment B raw42351step1 raw42351step1Labels = mixedMoment B raw42351step2 raw42351step2Labels := by
      have ha : raw42351step2 = -raw42351step1 := by apply Matrix.ext; change ∀ i j, raw42351step2 i j = -(raw42351step1 i j); unfold raw42351step2 raw42351step1; decide +kernel
      have hl : raw42351step2Labels = raw42351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42351step2 raw42351step2Labels = mixedMoment B raw42351step3 raw42351step3Labels := by
      have ha : raw42351step3 = raw42351step2 := by apply Matrix.ext; unfold raw42351step3 raw42351step2; decide +kernel
      have hl : raw42351step2Labels = labelEmbedding10 ∘ raw42351step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42351step2 raw42351step2Labels raw42351step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

theorem canonical42352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42352 raw42352Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw42352 raw42352Labels = mixedMoment B raw42352step0 raw42352step0Labels := by
      have ha : raw42352step0 = (fun i j => raw42352 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42352step0 raw42352; decide +kernel
      have hl : raw42352step0Labels = raw42352Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42352 raw42352Labels permutation337 permutation4
    mixedMoment B raw42352step0 raw42352step0Labels = mixedMoment B raw42352step1 raw42352step1Labels := by
      have ha : raw42352step1 = -raw42352step0 := by apply Matrix.ext; change ∀ i j, raw42352step1 i j = -(raw42352step0 i j); unfold raw42352step1 raw42352step0; decide +kernel
      have hl : raw42352step1Labels = raw42352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42352step1 raw42352step1Labels = mixedMoment B raw42352step2 raw42352step2Labels := by
      have ha : raw42352step2 = raw42352step1 := by apply Matrix.ext; unfold raw42352step2 raw42352step1; decide +kernel
      have hl : raw42352step1Labels = labelEmbedding1 ∘ raw42352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42352step1 raw42352step1Labels raw42352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

theorem canonical42353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42353 raw42353Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw42353 raw42353Labels = mixedMoment B raw42353step0 raw42353step0Labels := by
      have ha : raw42353step0 = (fun i j => raw42353 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42353step0 raw42353; decide +kernel
      have hl : raw42353step0Labels = raw42353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42353 raw42353Labels permutation337 permutation4
    mixedMoment B raw42353step0 raw42353step0Labels = mixedMoment B raw42353step1 raw42353step1Labels := by
      have ha : raw42353step1 = -raw42353step0 := by apply Matrix.ext; change ∀ i j, raw42353step1 i j = -(raw42353step0 i j); unfold raw42353step1 raw42353step0; decide +kernel
      have hl : raw42353step1Labels = raw42353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42353step1 raw42353step1Labels = mixedMoment B raw42353step2 raw42353step2Labels := by
      have ha : raw42353step2 = raw42353step1 := by apply Matrix.ext; unfold raw42353step2 raw42353step1; decide +kernel
      have hl : raw42353step1Labels = labelEmbedding10 ∘ raw42353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42353step1 raw42353step1Labels raw42353step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

theorem canonical42354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42354 raw42354Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw42354 raw42354Labels = mixedMoment B raw42354step0 raw42354step0Labels := by
      have ha : raw42354step0 = (fun i j => raw42354 (permutation313 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42354step0 raw42354; decide +kernel
      have hl : raw42354step0Labels = raw42354Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42354 raw42354Labels permutation313 permutation4
    mixedMoment B raw42354step0 raw42354step0Labels = mixedMoment B raw42354step1 raw42354step1Labels := by
      have ha : raw42354step1 = -raw42354step0 := by apply Matrix.ext; change ∀ i j, raw42354step1 i j = -(raw42354step0 i j); unfold raw42354step1 raw42354step0; decide +kernel
      have hl : raw42354step1Labels = raw42354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42354step1 raw42354step1Labels = mixedMoment B raw42354step2 raw42354step2Labels := by
      have ha : raw42354step2 = raw42354step1 := by apply Matrix.ext; unfold raw42354step2 raw42354step1; decide +kernel
      have hl : raw42354step1Labels = labelEmbedding1 ∘ raw42354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42354step1 raw42354step1Labels raw42354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

theorem canonical42355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42355 raw42355Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw42355 raw42355Labels = mixedMoment B raw42355step0 raw42355step0Labels := by
      have ha : raw42355step0 = (fun i j => raw42355 (permutation313 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42355step0 raw42355; decide +kernel
      have hl : raw42355step0Labels = raw42355Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42355 raw42355Labels permutation313 permutation4
    mixedMoment B raw42355step0 raw42355step0Labels = mixedMoment B raw42355step1 raw42355step1Labels := by
      have ha : raw42355step1 = -raw42355step0 := by apply Matrix.ext; change ∀ i j, raw42355step1 i j = -(raw42355step0 i j); unfold raw42355step1 raw42355step0; decide +kernel
      have hl : raw42355step1Labels = raw42355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42355step1 raw42355step1Labels = mixedMoment B raw42355step2 raw42355step2Labels := by
      have ha : raw42355step2 = raw42355step1 := by apply Matrix.ext; unfold raw42355step2 raw42355step1; decide +kernel
      have hl : raw42355step1Labels = labelEmbedding10 ∘ raw42355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42355step1 raw42355step1Labels raw42355step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

theorem canonical42356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42356 raw42356Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw42356 raw42356Labels = mixedMoment B raw42356step0 raw42356step0Labels := by
      have ha : raw42356step0 = (fun i j => raw42356 (permutation308 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42356step0 raw42356; decide +kernel
      have hl : raw42356step0Labels = raw42356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42356 raw42356Labels permutation308 permutation4
    mixedMoment B raw42356step0 raw42356step0Labels = mixedMoment B raw42356step1 raw42356step1Labels := by
      have ha : raw42356step1 = -raw42356step0 := by apply Matrix.ext; change ∀ i j, raw42356step1 i j = -(raw42356step0 i j); unfold raw42356step1 raw42356step0; decide +kernel
      have hl : raw42356step1Labels = raw42356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42356step1 raw42356step1Labels = mixedMoment B raw42356step2 raw42356step2Labels := by
      have ha : raw42356step2 = raw42356step1 := by apply Matrix.ext; unfold raw42356step2 raw42356step1; decide +kernel
      have hl : raw42356step1Labels = labelEmbedding1 ∘ raw42356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42356step1 raw42356step1Labels raw42356step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

theorem canonical42357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42357 raw42357Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42357 raw42357Labels = mixedMoment B raw42357step0 raw42357step0Labels := by
      have ha : raw42357step0 = (fun i j => raw42357 (permutation308 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42357step0 raw42357; decide +kernel
      have hl : raw42357step0Labels = raw42357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42357 raw42357Labels permutation308 permutation4
    mixedMoment B raw42357step0 raw42357step0Labels = mixedMoment B raw42357step1 raw42357step1Labels := by
      have ha : raw42357step1 = -raw42357step0 := by apply Matrix.ext; change ∀ i j, raw42357step1 i j = -(raw42357step0 i j); unfold raw42357step1 raw42357step0; decide +kernel
      have hl : raw42357step1Labels = raw42357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42357step1 raw42357step1Labels = mixedMoment B raw42357step2 raw42357step2Labels := by
      have ha : raw42357step2 = raw42357step1 := by apply Matrix.ext; unfold raw42357step2 raw42357step1; decide +kernel
      have hl : raw42357step1Labels = labelEmbedding10 ∘ raw42357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42357step1 raw42357step1Labels raw42357step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

theorem canonical42358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42358 raw42358Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw42358 raw42358Labels = mixedMoment B raw42358step0 raw42358step0Labels := by
      have ha : raw42358step0 = (fun i j => raw42358 (permutation314 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42358step0 raw42358; decide +kernel
      have hl : raw42358step0Labels = raw42358Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42358 raw42358Labels permutation314 permutation4
    mixedMoment B raw42358step0 raw42358step0Labels = mixedMoment B raw42358step1 raw42358step1Labels := by
      have ha : raw42358step1 = -raw42358step0 := by apply Matrix.ext; change ∀ i j, raw42358step1 i j = -(raw42358step0 i j); unfold raw42358step1 raw42358step0; decide +kernel
      have hl : raw42358step1Labels = raw42358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42358step1 raw42358step1Labels = mixedMoment B raw42358step2 raw42358step2Labels := by
      have ha : raw42358step2 = raw42358step1 := by apply Matrix.ext; unfold raw42358step2 raw42358step1; decide +kernel
      have hl : raw42358step1Labels = labelEmbedding1 ∘ raw42358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42358step1 raw42358step1Labels raw42358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

theorem canonical42359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42359 raw42359Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw42359 raw42359Labels = mixedMoment B raw42359step0 raw42359step0Labels := by
      have ha : raw42359step0 = (fun i j => raw42359 (permutation314 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42359step0 raw42359; decide +kernel
      have hl : raw42359step0Labels = raw42359Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42359 raw42359Labels permutation314 permutation4
    mixedMoment B raw42359step0 raw42359step0Labels = mixedMoment B raw42359step1 raw42359step1Labels := by
      have ha : raw42359step1 = -raw42359step0 := by apply Matrix.ext; change ∀ i j, raw42359step1 i j = -(raw42359step0 i j); unfold raw42359step1 raw42359step0; decide +kernel
      have hl : raw42359step1Labels = raw42359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42359step1 raw42359step1Labels = mixedMoment B raw42359step2 raw42359step2Labels := by
      have ha : raw42359step2 = raw42359step1 := by apply Matrix.ext; unfold raw42359step2 raw42359step1; decide +kernel
      have hl : raw42359step1Labels = labelEmbedding10 ∘ raw42359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42359step1 raw42359step1Labels raw42359step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

theorem canonical42360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42360 raw42360Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw42360 raw42360Labels = mixedMoment B raw42360step0 raw42360step0Labels := by
      have hz : ∀ j, raw42360 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42360step0 = (fun i j => raw42360 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42360step0 raw42360; decide +kernel
      have hl : raw42360step0Labels = raw42360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42360 raw42360Labels permutation520 hz
    mixedMoment B raw42360step0 raw42360step0Labels = mixedMoment B raw42360step1 raw42360step1Labels := by
      have hz : ∀ j, raw42360step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42360step1 = (fun i j => raw42360step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42360step1 raw42360step0; decide +kernel
      have hl : raw42360step1Labels = raw42360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42360step0 raw42360step0Labels permutation104 hz
    mixedMoment B raw42360step1 raw42360step1Labels = mixedMoment B raw42360step2 raw42360step2Labels := by
      have ha : raw42360step2 = (fun i j => raw42360step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42360step2 raw42360step1; decide +kernel
      have hl : raw42360step2Labels = raw42360step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42360step1 raw42360step1Labels permutation27 permutation4
    mixedMoment B raw42360step2 raw42360step2Labels = mixedMoment B raw42360step3 raw42360step3Labels := by
      have ha : raw42360step3 = raw42360step2 := by apply Matrix.ext; unfold raw42360step3 raw42360step2; decide +kernel
      have hl : raw42360step2Labels = labelEmbedding1 ∘ raw42360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42360step2 raw42360step2Labels raw42360step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

theorem canonical42361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42361 raw42361Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw42361 raw42361Labels = mixedMoment B raw42361step0 raw42361step0Labels := by
      have hz : ∀ j, raw42361 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42361step0 = (fun i j => raw42361 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42361step0 raw42361; decide +kernel
      have hl : raw42361step0Labels = raw42361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42361 raw42361Labels permutation520 hz
    mixedMoment B raw42361step0 raw42361step0Labels = mixedMoment B raw42361step1 raw42361step1Labels := by
      have hz : ∀ j, raw42361step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42361step1 = (fun i j => raw42361step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42361step1 raw42361step0; decide +kernel
      have hl : raw42361step1Labels = raw42361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42361step0 raw42361step0Labels permutation104 hz
    mixedMoment B raw42361step1 raw42361step1Labels = mixedMoment B raw42361step2 raw42361step2Labels := by
      have ha : raw42361step2 = (fun i j => raw42361step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42361step2 raw42361step1; decide +kernel
      have hl : raw42361step2Labels = raw42361step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42361step1 raw42361step1Labels permutation31 permutation3
    mixedMoment B raw42361step2 raw42361step2Labels = mixedMoment B raw42361step3 raw42361step3Labels := by
      have ha : raw42361step3 = -raw42361step2 := by apply Matrix.ext; change ∀ i j, raw42361step3 i j = -(raw42361step2 i j); unfold raw42361step3 raw42361step2; decide +kernel
      have hl : raw42361step3Labels = raw42361step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42361step3 raw42361step3Labels = mixedMoment B raw42361step4 raw42361step4Labels := by
      have ha : raw42361step4 = raw42361step3 := by apply Matrix.ext; unfold raw42361step4 raw42361step3; decide +kernel
      have hl : raw42361step3Labels = labelEmbedding7 ∘ raw42361step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42361step3 raw42361step3Labels raw42361step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

theorem canonical42362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42362 raw42362Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw42362 raw42362Labels = mixedMoment B raw42362step0 raw42362step0Labels := by
      have hz : ∀ j, raw42362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42362step0 = (fun i j => raw42362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42362step0 raw42362; decide +kernel
      have hl : raw42362step0Labels = raw42362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42362 raw42362Labels permutation434 hz
    mixedMoment B raw42362step0 raw42362step0Labels = mixedMoment B raw42362step1 raw42362step1Labels := by
      have ha : raw42362step1 = (fun i j => raw42362step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42362step1 raw42362step0; decide +kernel
      have hl : raw42362step1Labels = raw42362step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42362step0 raw42362step0Labels permutation133 permutation4
    mixedMoment B raw42362step1 raw42362step1Labels = mixedMoment B raw42362step2 raw42362step2Labels := by
      have ha : raw42362step2 = raw42362step1 := by apply Matrix.ext; unfold raw42362step2 raw42362step1; decide +kernel
      have hl : raw42362step1Labels = labelEmbedding1 ∘ raw42362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42362step1 raw42362step1Labels raw42362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

theorem canonical42363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42363 raw42363Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42363 raw42363Labels = mixedMoment B raw42363step0 raw42363step0Labels := by
      have hz : ∀ j, raw42363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42363step0 = (fun i j => raw42363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42363step0 raw42363; decide +kernel
      have hl : raw42363step0Labels = raw42363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42363 raw42363Labels permutation434 hz
    mixedMoment B raw42363step0 raw42363step0Labels = mixedMoment B raw42363step1 raw42363step1Labels := by
      have ha : raw42363step1 = (fun i j => raw42363step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42363step1 raw42363step0; decide +kernel
      have hl : raw42363step1Labels = raw42363step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42363step0 raw42363step0Labels permutation147 permutation5
    mixedMoment B raw42363step1 raw42363step1Labels = mixedMoment B raw42363step2 raw42363step2Labels := by
      have ha : raw42363step2 = raw42363step1 := by apply Matrix.ext; unfold raw42363step2 raw42363step1; decide +kernel
      have hl : raw42363step1Labels = labelEmbedding9 ∘ raw42363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42363step1 raw42363step1Labels raw42363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

theorem canonical42364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42364 raw42364Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw42364 raw42364Labels = mixedMoment B raw42364step0 raw42364step0Labels := by
      have hz : ∀ j, raw42364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42364step0 = (fun i j => raw42364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42364step0 raw42364; decide +kernel
      have hl : raw42364step0Labels = raw42364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42364 raw42364Labels permutation434 hz
    mixedMoment B raw42364step0 raw42364step0Labels = mixedMoment B raw42364step1 raw42364step1Labels := by
      have ha : raw42364step1 = raw42364step0 := by apply Matrix.ext; unfold raw42364step1 raw42364step0; decide +kernel
      have hl : raw42364step0Labels = labelEmbedding1 ∘ raw42364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42364step0 raw42364step0Labels raw42364step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

theorem canonical42365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42365 raw42365Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw42365 raw42365Labels = mixedMoment B raw42365step0 raw42365step0Labels := by
      have hz : ∀ j, raw42365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42365step0 = (fun i j => raw42365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42365step0 raw42365; decide +kernel
      have hl : raw42365step0Labels = raw42365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42365 raw42365Labels permutation434 hz
    mixedMoment B raw42365step0 raw42365step0Labels = mixedMoment B raw42365step1 raw42365step1Labels := by
      have ha : raw42365step1 = (fun i j => raw42365step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42365step1 raw42365step0; decide +kernel
      have hl : raw42365step1Labels = raw42365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42365step0 raw42365step0Labels permutation151 permutation3
    mixedMoment B raw42365step1 raw42365step1Labels = mixedMoment B raw42365step2 raw42365step2Labels := by
      have ha : raw42365step2 = -raw42365step1 := by apply Matrix.ext; change ∀ i j, raw42365step2 i j = -(raw42365step1 i j); unfold raw42365step2 raw42365step1; decide +kernel
      have hl : raw42365step2Labels = raw42365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42365step2 raw42365step2Labels = mixedMoment B raw42365step3 raw42365step3Labels := by
      have ha : raw42365step3 = raw42365step2 := by apply Matrix.ext; unfold raw42365step3 raw42365step2; decide +kernel
      have hl : raw42365step2Labels = labelEmbedding7 ∘ raw42365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42365step2 raw42365step2Labels raw42365step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

theorem canonical42366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42366 raw42366Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw42366 raw42366Labels = mixedMoment B raw42366step0 raw42366step0Labels := by
      have hz : ∀ j, raw42366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42366step0 = (fun i j => raw42366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42366step0 raw42366; decide +kernel
      have hl : raw42366step0Labels = raw42366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42366 raw42366Labels permutation434 hz
    mixedMoment B raw42366step0 raw42366step0Labels = mixedMoment B raw42366step1 raw42366step1Labels := by
      have ha : raw42366step1 = raw42366step0 := by apply Matrix.ext; unfold raw42366step1 raw42366step0; decide +kernel
      have hl : raw42366step0Labels = labelEmbedding1 ∘ raw42366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42366step0 raw42366step0Labels raw42366step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

theorem canonical42367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42367 raw42367Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42367 raw42367Labels = mixedMoment B raw42367step0 raw42367step0Labels := by
      have hz : ∀ j, raw42367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42367step0 = (fun i j => raw42367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42367step0 raw42367; decide +kernel
      have hl : raw42367step0Labels = raw42367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42367 raw42367Labels permutation434 hz
    mixedMoment B raw42367step0 raw42367step0Labels = mixedMoment B raw42367step1 raw42367step1Labels := by
      have ha : raw42367step1 = raw42367step0 := by apply Matrix.ext; unfold raw42367step1 raw42367step0; decide +kernel
      have hl : raw42367step0Labels = labelEmbedding8 ∘ raw42367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42367step0 raw42367step0Labels raw42367step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2496 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2496) =
      Integer.Sparse.eval keyMomentRow2496 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3565) := by
    have ha : gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge = raw42304 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42304Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42304 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5164) := by
    have ha : gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge = raw42305 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42305Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42305 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2496).leftCharge (GramAssembly.key 2496).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2496, Integer.Sparse.eval] <;> ring

theorem keyMoment2497 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2497) =
      Integer.Sparse.eval keyMomentRow2497 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3580) := by
    have ha : gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge = raw42306 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42306Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42306 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5282) := by
    have ha : gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge = raw42307 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42307Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42307 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2497).leftCharge (GramAssembly.key 2497).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2497, Integer.Sparse.eval] <;> ring

theorem keyMoment2498 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2498) =
      Integer.Sparse.eval keyMomentRow2498 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3960) := by
    have ha : gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge = raw42308 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42308Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42308 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5463) := by
    have ha : gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge = raw42309 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42309Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42309 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2498).leftCharge (GramAssembly.key 2498).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2498, Integer.Sparse.eval] <;> ring

theorem keyMoment2499 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2499) =
      Integer.Sparse.eval keyMomentRow2499 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3562) := by
    have ha : gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge = raw42310 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42310Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42310 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5145) := by
    have ha : gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge = raw42311 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42311Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42311 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2499).leftCharge (GramAssembly.key 2499).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2499, Integer.Sparse.eval] <;> ring

theorem keyMoment2500 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2500) =
      Integer.Sparse.eval keyMomentRow2500 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3538) := by
    have ha : gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge = raw42312 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42312Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42312 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5188) := by
    have ha : gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge = raw42313 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42313Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42313 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2500).leftCharge (GramAssembly.key 2500).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2500, Integer.Sparse.eval] <;> ring

theorem keyMoment2501 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2501) =
      Integer.Sparse.eval keyMomentRow2501 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3524) := by
    have ha : gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge = raw42314 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42314Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42314 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5184) := by
    have ha : gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge = raw42315 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42315Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42315 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2501).leftCharge (GramAssembly.key 2501).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2501, Integer.Sparse.eval] <;> ring

theorem keyMoment2502 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2502) =
      Integer.Sparse.eval keyMomentRow2502 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3537) := by
    have ha : gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge = raw42316 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42316Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42316 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5187) := by
    have ha : gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge = raw42317 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42317Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42317 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2502).leftCharge (GramAssembly.key 2502).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2502, Integer.Sparse.eval] <;> ring

theorem keyMoment2503 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2503) =
      Integer.Sparse.eval keyMomentRow2503 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3523) := by
    have ha : gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge = raw42318 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42318Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42318 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5139) := by
    have ha : gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge = raw42319 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42319Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42319 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2503).leftCharge (GramAssembly.key 2503).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2503, Integer.Sparse.eval] <;> ring

theorem keyMoment2504 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2504) =
      Integer.Sparse.eval keyMomentRow2504 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3529) := by
    have ha : gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge = raw42320 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42320Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42320 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5185) := by
    have ha : gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge = raw42321 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42321Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42321 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2504).leftCharge (GramAssembly.key 2504).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2504, Integer.Sparse.eval] <;> ring

theorem keyMoment2505 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2505) =
      Integer.Sparse.eval keyMomentRow2505 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3302) := by
    have ha : gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge = raw42322 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42322Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42322 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4609) := by
    have ha : gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge = raw42323 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42323Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42323 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2505).leftCharge (GramAssembly.key 2505).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2505, Integer.Sparse.eval] <;> ring

theorem keyMoment2506 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2506) =
      Integer.Sparse.eval keyMomentRow2506 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3530) := by
    have ha : gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge = raw42324 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42324Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42324 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5147) := by
    have ha : gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge = raw42325 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42325Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42325 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2506).leftCharge (GramAssembly.key 2506).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2506, Integer.Sparse.eval] <;> ring

theorem keyMoment2507 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2507) =
      Integer.Sparse.eval keyMomentRow2507 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3542) := by
    have ha : gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge = raw42326 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42326Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42326 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5189) := by
    have ha : gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge = raw42327 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42327Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42327 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2507).leftCharge (GramAssembly.key 2507).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2507, Integer.Sparse.eval] <;> ring

theorem keyMoment2508 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2508) =
      Integer.Sparse.eval keyMomentRow2508 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2778) := by
    have ha : gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge = raw42328 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42328Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42328 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4899) := by
    have ha : gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge = raw42329 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42329Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42329 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2508).leftCharge (GramAssembly.key 2508).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2508, Integer.Sparse.eval] <;> ring

theorem keyMoment2509 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2509) =
      Integer.Sparse.eval keyMomentRow2509 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2734) := by
    have ha : gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge = raw42330 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42330Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42330 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5268) := by
    have ha : gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge = raw42331 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42331Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42331 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2509).leftCharge (GramAssembly.key 2509).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2509, Integer.Sparse.eval] <;> ring

theorem keyMoment2510 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2510) =
      Integer.Sparse.eval keyMomentRow2510 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2776) := by
    have ha : gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge = raw42332 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42332Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42332 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5302) := by
    have ha : gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge = raw42333 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42333Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42333 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2510).leftCharge (GramAssembly.key 2510).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2510, Integer.Sparse.eval] <;> ring

theorem keyMoment2511 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2511) =
      Integer.Sparse.eval keyMomentRow2511 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2774) := by
    have ha : gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge = raw42334 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42334Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42334 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5300) := by
    have ha : gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge = raw42335 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42335Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42335 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2511).leftCharge (GramAssembly.key 2511).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2511, Integer.Sparse.eval] <;> ring

theorem keyMoment2512 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2512) =
      Integer.Sparse.eval keyMomentRow2512 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2680) := by
    have ha : gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge = raw42336 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42336Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42336 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5235) := by
    have ha : gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge = raw42337 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42337Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42337 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2512).leftCharge (GramAssembly.key 2512).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2512, Integer.Sparse.eval] <;> ring

theorem keyMoment2513 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2513) =
      Integer.Sparse.eval keyMomentRow2513 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2732) := by
    have ha : gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge = raw42338 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42338Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42338 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5267) := by
    have ha : gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge = raw42339 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42339Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42339 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2513).leftCharge (GramAssembly.key 2513).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2513, Integer.Sparse.eval] <;> ring

theorem keyMoment2514 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2514) =
      Integer.Sparse.eval keyMomentRow2514 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2773) := by
    have ha : gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge = raw42340 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42340Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42340 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5299) := by
    have ha : gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge = raw42341 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42341Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42341 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2514).leftCharge (GramAssembly.key 2514).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2514, Integer.Sparse.eval] <;> ring

theorem keyMoment2515 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2515) =
      Integer.Sparse.eval keyMomentRow2515 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2678) := by
    have ha : gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge = raw42342 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42342Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42342 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5233) := by
    have ha : gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge = raw42343 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42343Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42343 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2515).leftCharge (GramAssembly.key 2515).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2515, Integer.Sparse.eval] <;> ring

theorem keyMoment2516 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2516) =
      Integer.Sparse.eval keyMomentRow2516 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2677) := by
    have ha : gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge = raw42344 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42344Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42344 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5232) := by
    have ha : gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge = raw42345 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42345Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42345 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2516).leftCharge (GramAssembly.key 2516).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2516, Integer.Sparse.eval] <;> ring

theorem keyMoment2517 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2517) =
      Integer.Sparse.eval keyMomentRow2517 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2664) := by
    have ha : gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge = raw42346 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42346Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42346 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5222) := by
    have ha : gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge = raw42347 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42347Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42347 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2517).leftCharge (GramAssembly.key 2517).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2517, Integer.Sparse.eval] <;> ring

theorem keyMoment2518 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2518) =
      Integer.Sparse.eval keyMomentRow2518 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2731) := by
    have ha : gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge = raw42348 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42348Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42348 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge = raw42349 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42349Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42349 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2518).leftCharge (GramAssembly.key 2518).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2518, Integer.Sparse.eval] <;> ring

theorem keyMoment2519 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2519) =
      Integer.Sparse.eval keyMomentRow2519 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2775) := by
    have ha : gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge = raw42350 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42350Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42350 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5301) := by
    have ha : gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge = raw42351 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42351Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42351 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2519).leftCharge (GramAssembly.key 2519).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2519, Integer.Sparse.eval] <;> ring

theorem keyMoment2520 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2520) =
      Integer.Sparse.eval keyMomentRow2520 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2676) := by
    have ha : gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge = raw42352 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42352Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42352 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5231) := by
    have ha : gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge = raw42353 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42353Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42353 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2520).leftCharge (GramAssembly.key 2520).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2520, Integer.Sparse.eval] <;> ring

theorem keyMoment2521 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2521) =
      Integer.Sparse.eval keyMomentRow2521 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2698) := by
    have ha : gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge = raw42354 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42354Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42354 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5244) := by
    have ha : gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge = raw42355 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42355Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42355 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2521).leftCharge (GramAssembly.key 2521).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2521, Integer.Sparse.eval] <;> ring

theorem keyMoment2522 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2522) =
      Integer.Sparse.eval keyMomentRow2522 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2730) := by
    have ha : gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge = raw42356 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42356Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42356 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5265) := by
    have ha : gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge = raw42357 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42357Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42357 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2522).leftCharge (GramAssembly.key 2522).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2522, Integer.Sparse.eval] <;> ring

theorem keyMoment2523 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2523) =
      Integer.Sparse.eval keyMomentRow2523 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2697) := by
    have ha : gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge = raw42358 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42358Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42358 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5243) := by
    have ha : gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge = raw42359 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42359Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42359 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2523).leftCharge (GramAssembly.key 2523).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2523, Integer.Sparse.eval] <;> ring

theorem keyMoment2524 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2524) =
      Integer.Sparse.eval keyMomentRow2524 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3225) := by
    have ha : gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge = raw42360 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42360Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42360 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4896) := by
    have ha : gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge = raw42361 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42361Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42361 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2524).leftCharge (GramAssembly.key 2524).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2524, Integer.Sparse.eval] <;> ring

theorem keyMoment2525 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2525) =
      Integer.Sparse.eval keyMomentRow2525 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3039) := by
    have ha : gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge = raw42362 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42362Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42362 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5266) := by
    have ha : gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge = raw42363 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42363Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42363 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2525).leftCharge (GramAssembly.key 2525).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2525, Integer.Sparse.eval] <;> ring

theorem keyMoment2526 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2526) =
      Integer.Sparse.eval keyMomentRow2526 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3883) := by
    have ha : gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge = raw42364 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42364Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42364 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5411) := by
    have ha : gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge = raw42365 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42365Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42365 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2526).leftCharge (GramAssembly.key 2526).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2526, Integer.Sparse.eval] <;> ring

theorem keyMoment2527 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2527) =
      Integer.Sparse.eval keyMomentRow2527 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 3881) := by
    have ha : gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge = raw42366 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw42366Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42366 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 5446) := by
    have ha : gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge = raw42367 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw42367Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical42367 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2527).leftCharge (GramAssembly.key 2527).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2527, Integer.Sparse.eval] <;> ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk78
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2496 : keyMomentRows (2496 : Fin 2886) =
    keyMomentRow2496 := by decide +kernel

theorem keyMomentRowsAt2497 : keyMomentRows (2497 : Fin 2886) =
    keyMomentRow2497 := by decide +kernel

theorem keyMomentRowsAt2498 : keyMomentRows (2498 : Fin 2886) =
    keyMomentRow2498 := by decide +kernel

theorem keyMomentRowsAt2499 : keyMomentRows (2499 : Fin 2886) =
    keyMomentRow2499 := by decide +kernel

theorem keyMomentRowsAt2500 : keyMomentRows (2500 : Fin 2886) =
    keyMomentRow2500 := by decide +kernel

theorem keyMomentRowsAt2501 : keyMomentRows (2501 : Fin 2886) =
    keyMomentRow2501 := by decide +kernel

theorem keyMomentRowsAt2502 : keyMomentRows (2502 : Fin 2886) =
    keyMomentRow2502 := by decide +kernel

theorem keyMomentRowsAt2503 : keyMomentRows (2503 : Fin 2886) =
    keyMomentRow2503 := by decide +kernel

theorem keyMomentRowsAt2504 : keyMomentRows (2504 : Fin 2886) =
    keyMomentRow2504 := by decide +kernel

theorem keyMomentRowsAt2505 : keyMomentRows (2505 : Fin 2886) =
    keyMomentRow2505 := by decide +kernel

theorem keyMomentRowsAt2506 : keyMomentRows (2506 : Fin 2886) =
    keyMomentRow2506 := by decide +kernel

theorem keyMomentRowsAt2507 : keyMomentRows (2507 : Fin 2886) =
    keyMomentRow2507 := by decide +kernel

theorem keyMomentRowsAt2508 : keyMomentRows (2508 : Fin 2886) =
    keyMomentRow2508 := by decide +kernel

theorem keyMomentRowsAt2509 : keyMomentRows (2509 : Fin 2886) =
    keyMomentRow2509 := by decide +kernel

theorem keyMomentRowsAt2510 : keyMomentRows (2510 : Fin 2886) =
    keyMomentRow2510 := by decide +kernel

theorem keyMomentRowsAt2511 : keyMomentRows (2511 : Fin 2886) =
    keyMomentRow2511 := by decide +kernel

theorem keyMomentRowsAt2512 : keyMomentRows (2512 : Fin 2886) =
    keyMomentRow2512 := by decide +kernel

theorem keyMomentRowsAt2513 : keyMomentRows (2513 : Fin 2886) =
    keyMomentRow2513 := by decide +kernel

theorem keyMomentRowsAt2514 : keyMomentRows (2514 : Fin 2886) =
    keyMomentRow2514 := by decide +kernel

theorem keyMomentRowsAt2515 : keyMomentRows (2515 : Fin 2886) =
    keyMomentRow2515 := by decide +kernel

theorem keyMomentRowsAt2516 : keyMomentRows (2516 : Fin 2886) =
    keyMomentRow2516 := by decide +kernel

theorem keyMomentRowsAt2517 : keyMomentRows (2517 : Fin 2886) =
    keyMomentRow2517 := by decide +kernel

theorem keyMomentRowsAt2518 : keyMomentRows (2518 : Fin 2886) =
    keyMomentRow2518 := by decide +kernel

theorem keyMomentRowsAt2519 : keyMomentRows (2519 : Fin 2886) =
    keyMomentRow2519 := by decide +kernel

theorem keyMomentRowsAt2520 : keyMomentRows (2520 : Fin 2886) =
    keyMomentRow2520 := by decide +kernel

theorem keyMomentRowsAt2521 : keyMomentRows (2521 : Fin 2886) =
    keyMomentRow2521 := by decide +kernel

theorem keyMomentRowsAt2522 : keyMomentRows (2522 : Fin 2886) =
    keyMomentRow2522 := by decide +kernel

theorem keyMomentRowsAt2523 : keyMomentRows (2523 : Fin 2886) =
    keyMomentRow2523 := by decide +kernel

theorem keyMomentRowsAt2524 : keyMomentRows (2524 : Fin 2886) =
    keyMomentRow2524 := by decide +kernel

theorem keyMomentRowsAt2525 : keyMomentRows (2525 : Fin 2886) =
    keyMomentRow2525 := by decide +kernel

theorem keyMomentRowsAt2526 : keyMomentRows (2526 : Fin 2886) =
    keyMomentRow2526 := by decide +kernel

theorem keyMomentRowsAt2527 : keyMomentRows (2527 : Fin 2886) =
    keyMomentRow2527 := by decide +kernel

theorem keyMomentChunkSound78_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 78) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2496 ∨ k.val = 2497 ∨ k.val = 2498 ∨ k.val = 2499 ∨ k.val = 2500 ∨ k.val = 2501 ∨ k.val = 2502 ∨ k.val = 2503 ∨ k.val = 2504 ∨ k.val = 2505 ∨ k.val = 2506 ∨ k.val = 2507 ∨ k.val = 2508 ∨ k.val = 2509 ∨ k.val = 2510 ∨ k.val = 2511 ∨ k.val = 2512 ∨ k.val = 2513 ∨ k.val = 2514 ∨ k.val = 2515 ∨ k.val = 2516 ∨ k.val = 2517 ∨ k.val = 2518 ∨ k.val = 2519 ∨ k.val = 2520 ∨ k.val = 2521 ∨ k.val = 2522 ∨ k.val = 2523 ∨ k.val = 2524 ∨ k.val = 2525 ∨ k.val = 2526 ∨ k.val = 2527 := by omega
  rcases heq with h2496 | h2497 | h2498 | h2499 | h2500 | h2501 | h2502 | h2503 | h2504 | h2505 | h2506 | h2507 | h2508 | h2509 | h2510 | h2511 | h2512 | h2513 | h2514 | h2515 | h2516 | h2517 | h2518 | h2519 | h2520 | h2521 | h2522 | h2523 | h2524 | h2525 | h2526 | h2527
  · have he : k = (2496 : Fin 2886) := Fin.ext h2496
    subst k
    rw [keyMomentRowsAt2496]
    exact keyMoment2496 B hB
  · have he : k = (2497 : Fin 2886) := Fin.ext h2497
    subst k
    rw [keyMomentRowsAt2497]
    exact keyMoment2497 B hB
  · have he : k = (2498 : Fin 2886) := Fin.ext h2498
    subst k
    rw [keyMomentRowsAt2498]
    exact keyMoment2498 B hB
  · have he : k = (2499 : Fin 2886) := Fin.ext h2499
    subst k
    rw [keyMomentRowsAt2499]
    exact keyMoment2499 B hB
  · have he : k = (2500 : Fin 2886) := Fin.ext h2500
    subst k
    rw [keyMomentRowsAt2500]
    exact keyMoment2500 B hB
  · have he : k = (2501 : Fin 2886) := Fin.ext h2501
    subst k
    rw [keyMomentRowsAt2501]
    exact keyMoment2501 B hB
  · have he : k = (2502 : Fin 2886) := Fin.ext h2502
    subst k
    rw [keyMomentRowsAt2502]
    exact keyMoment2502 B hB
  · have he : k = (2503 : Fin 2886) := Fin.ext h2503
    subst k
    rw [keyMomentRowsAt2503]
    exact keyMoment2503 B hB
  · have he : k = (2504 : Fin 2886) := Fin.ext h2504
    subst k
    rw [keyMomentRowsAt2504]
    exact keyMoment2504 B hB
  · have he : k = (2505 : Fin 2886) := Fin.ext h2505
    subst k
    rw [keyMomentRowsAt2505]
    exact keyMoment2505 B hB
  · have he : k = (2506 : Fin 2886) := Fin.ext h2506
    subst k
    rw [keyMomentRowsAt2506]
    exact keyMoment2506 B hB
  · have he : k = (2507 : Fin 2886) := Fin.ext h2507
    subst k
    rw [keyMomentRowsAt2507]
    exact keyMoment2507 B hB
  · have he : k = (2508 : Fin 2886) := Fin.ext h2508
    subst k
    rw [keyMomentRowsAt2508]
    exact keyMoment2508 B hB
  · have he : k = (2509 : Fin 2886) := Fin.ext h2509
    subst k
    rw [keyMomentRowsAt2509]
    exact keyMoment2509 B hB
  · have he : k = (2510 : Fin 2886) := Fin.ext h2510
    subst k
    rw [keyMomentRowsAt2510]
    exact keyMoment2510 B hB
  · have he : k = (2511 : Fin 2886) := Fin.ext h2511
    subst k
    rw [keyMomentRowsAt2511]
    exact keyMoment2511 B hB
  · have he : k = (2512 : Fin 2886) := Fin.ext h2512
    subst k
    rw [keyMomentRowsAt2512]
    exact keyMoment2512 B hB
  · have he : k = (2513 : Fin 2886) := Fin.ext h2513
    subst k
    rw [keyMomentRowsAt2513]
    exact keyMoment2513 B hB
  · have he : k = (2514 : Fin 2886) := Fin.ext h2514
    subst k
    rw [keyMomentRowsAt2514]
    exact keyMoment2514 B hB
  · have he : k = (2515 : Fin 2886) := Fin.ext h2515
    subst k
    rw [keyMomentRowsAt2515]
    exact keyMoment2515 B hB
  · have he : k = (2516 : Fin 2886) := Fin.ext h2516
    subst k
    rw [keyMomentRowsAt2516]
    exact keyMoment2516 B hB
  · have he : k = (2517 : Fin 2886) := Fin.ext h2517
    subst k
    rw [keyMomentRowsAt2517]
    exact keyMoment2517 B hB
  · have he : k = (2518 : Fin 2886) := Fin.ext h2518
    subst k
    rw [keyMomentRowsAt2518]
    exact keyMoment2518 B hB
  · have he : k = (2519 : Fin 2886) := Fin.ext h2519
    subst k
    rw [keyMomentRowsAt2519]
    exact keyMoment2519 B hB
  · have he : k = (2520 : Fin 2886) := Fin.ext h2520
    subst k
    rw [keyMomentRowsAt2520]
    exact keyMoment2520 B hB
  · have he : k = (2521 : Fin 2886) := Fin.ext h2521
    subst k
    rw [keyMomentRowsAt2521]
    exact keyMoment2521 B hB
  · have he : k = (2522 : Fin 2886) := Fin.ext h2522
    subst k
    rw [keyMomentRowsAt2522]
    exact keyMoment2522 B hB
  · have he : k = (2523 : Fin 2886) := Fin.ext h2523
    subst k
    rw [keyMomentRowsAt2523]
    exact keyMoment2523 B hB
  · have he : k = (2524 : Fin 2886) := Fin.ext h2524
    subst k
    rw [keyMomentRowsAt2524]
    exact keyMoment2524 B hB
  · have he : k = (2525 : Fin 2886) := Fin.ext h2525
    subst k
    rw [keyMomentRowsAt2525]
    exact keyMoment2525 B hB
  · have he : k = (2526 : Fin 2886) := Fin.ext h2526
    subst k
    rw [keyMomentRowsAt2526]
    exact keyMoment2526 B hB
  · have he : k = (2527 : Fin 2886) := Fin.ext h2527
    subst k
    rw [keyMomentRowsAt2527]
    exact keyMoment2527 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound78_e_oai
