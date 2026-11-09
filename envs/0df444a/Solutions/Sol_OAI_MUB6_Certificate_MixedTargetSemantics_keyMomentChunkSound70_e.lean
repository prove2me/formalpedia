-- Prove2me | solution 1 for OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T05:01:53.117283+00:00
-- url     : https://prove2.me/submissions/0a3f6e09-c52e-4bdd-a000-d4e5c97b1294

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E112
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
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedSemantics_Canonical326
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem canonical41792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41792 raw41792Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw41792 raw41792Labels = mixedMoment B raw41792step0 raw41792step0Labels := by
      have hz : ∀ j, raw41792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41792step0 = (fun i j => raw41792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41792step0 raw41792; decide +kernel
      have hl : raw41792step0Labels = raw41792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41792 raw41792Labels permutation434 hz
    mixedMoment B raw41792step0 raw41792step0Labels = mixedMoment B raw41792step1 raw41792step1Labels := by
      have ha : raw41792step1 = raw41792step0 := by apply Matrix.ext; unfold raw41792step1 raw41792step0; decide +kernel
      have hl : raw41792step0Labels = labelEmbedding1 ∘ raw41792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41792step0 raw41792step0Labels raw41792step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

theorem canonical41793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41793 raw41793Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw41793 raw41793Labels = mixedMoment B raw41793step0 raw41793step0Labels := by
      have hz : ∀ j, raw41793 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41793step0 = (fun i j => raw41793 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41793step0 raw41793; decide +kernel
      have hl : raw41793step0Labels = raw41793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41793 raw41793Labels permutation434 hz
    mixedMoment B raw41793step0 raw41793step0Labels = mixedMoment B raw41793step1 raw41793step1Labels := by
      have ha : raw41793step1 = (fun i j => raw41793step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41793step1 raw41793step0; decide +kernel
      have hl : raw41793step1Labels = raw41793step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41793step0 raw41793step0Labels permutation50 permutation7
    mixedMoment B raw41793step1 raw41793step1Labels = mixedMoment B raw41793step2 raw41793step2Labels := by
      have ha : raw41793step2 = -raw41793step1 := by apply Matrix.ext; change ∀ i j, raw41793step2 i j = -(raw41793step1 i j); unfold raw41793step2 raw41793step1; decide +kernel
      have hl : raw41793step2Labels = raw41793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41793step2 raw41793step2Labels = mixedMoment B raw41793step3 raw41793step3Labels := by
      have ha : raw41793step3 = raw41793step2 := by apply Matrix.ext; unfold raw41793step3 raw41793step2; decide +kernel
      have hl : raw41793step2Labels = labelEmbedding6 ∘ raw41793step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41793step2 raw41793step2Labels raw41793step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

theorem canonical41794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41794 raw41794Labels = mixedMoment B node2239 node2239Labels := by
  calc
    mixedMoment B raw41794 raw41794Labels = mixedMoment B raw41794step0 raw41794step0Labels := by
      have hz : ∀ j, raw41794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41794step0 = (fun i j => raw41794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41794step0 raw41794; decide +kernel
      have hl : raw41794step0Labels = raw41794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41794 raw41794Labels permutation434 hz
    mixedMoment B raw41794step0 raw41794step0Labels = mixedMoment B raw41794step1 raw41794step1Labels := by
      have ha : raw41794step1 = raw41794step0 := by apply Matrix.ext; unfold raw41794step1 raw41794step0; decide +kernel
      have hl : raw41794step0Labels = labelEmbedding1 ∘ raw41794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41794step0 raw41794step0Labels raw41794step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2239 node2239Labels := by rfl

theorem canonical41795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41795 raw41795Labels = mixedMoment B node4697 node4697Labels := by
  calc
    mixedMoment B raw41795 raw41795Labels = mixedMoment B raw41795step0 raw41795step0Labels := by
      have hz : ∀ j, raw41795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41795step0 = (fun i j => raw41795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41795step0 raw41795; decide +kernel
      have hl : raw41795step0Labels = raw41795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41795 raw41795Labels permutation434 hz
    mixedMoment B raw41795step0 raw41795step0Labels = mixedMoment B raw41795step1 raw41795step1Labels := by
      have ha : raw41795step1 = (fun i j => raw41795step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41795step1 raw41795step0; decide +kernel
      have hl : raw41795step1Labels = raw41795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41795step0 raw41795step0Labels permutation44 permutation7
    mixedMoment B raw41795step1 raw41795step1Labels = mixedMoment B raw41795step2 raw41795step2Labels := by
      have ha : raw41795step2 = -raw41795step1 := by apply Matrix.ext; change ∀ i j, raw41795step2 i j = -(raw41795step1 i j); unfold raw41795step2 raw41795step1; decide +kernel
      have hl : raw41795step2Labels = raw41795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41795step2 raw41795step2Labels = mixedMoment B raw41795step3 raw41795step3Labels := by
      have ha : raw41795step3 = raw41795step2 := by apply Matrix.ext; unfold raw41795step3 raw41795step2; decide +kernel
      have hl : raw41795step2Labels = labelEmbedding6 ∘ raw41795step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41795step2 raw41795step2Labels raw41795step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4697 node4697Labels := by rfl

theorem canonical41796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41796 raw41796Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw41796 raw41796Labels = mixedMoment B raw41796step0 raw41796step0Labels := by
      have ha : raw41796step0 = (fun i j => raw41796 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41796step0 raw41796; decide +kernel
      have hl : raw41796step0Labels = raw41796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41796 raw41796Labels permutation200 permutation2
    mixedMoment B raw41796step0 raw41796step0Labels = mixedMoment B raw41796step1 raw41796step1Labels := by
      have ha : raw41796step1 = raw41796step0 := by apply Matrix.ext; unfold raw41796step1 raw41796step0; decide +kernel
      have hl : raw41796step0Labels = labelEmbedding1 ∘ raw41796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41796step0 raw41796step0Labels raw41796step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

theorem canonical41797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41797 raw41797Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw41797 raw41797Labels = mixedMoment B raw41797step0 raw41797step0Labels := by
      have ha : raw41797step0 = (fun i j => raw41797 (permutation218 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41797step0 raw41797; decide +kernel
      have hl : raw41797step0Labels = raw41797Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41797 raw41797Labels permutation218 permutation7
    mixedMoment B raw41797step0 raw41797step0Labels = mixedMoment B raw41797step1 raw41797step1Labels := by
      have ha : raw41797step1 = -raw41797step0 := by apply Matrix.ext; change ∀ i j, raw41797step1 i j = -(raw41797step0 i j); unfold raw41797step1 raw41797step0; decide +kernel
      have hl : raw41797step1Labels = raw41797step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41797step1 raw41797step1Labels = mixedMoment B raw41797step2 raw41797step2Labels := by
      have ha : raw41797step2 = raw41797step1 := by apply Matrix.ext; unfold raw41797step2 raw41797step1; decide +kernel
      have hl : raw41797step1Labels = labelEmbedding6 ∘ raw41797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41797step1 raw41797step1Labels raw41797step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

theorem canonical41798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41798 raw41798Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw41798 raw41798Labels = mixedMoment B raw41798step0 raw41798step0Labels := by
      have ha : raw41798step0 = (fun i j => raw41798 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41798step0 raw41798; decide +kernel
      have hl : raw41798step0Labels = raw41798Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41798 raw41798Labels permutation200 permutation2
    mixedMoment B raw41798step0 raw41798step0Labels = mixedMoment B raw41798step1 raw41798step1Labels := by
      have ha : raw41798step1 = raw41798step0 := by apply Matrix.ext; unfold raw41798step1 raw41798step0; decide +kernel
      have hl : raw41798step0Labels = labelEmbedding1 ∘ raw41798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41798step0 raw41798step0Labels raw41798step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

theorem canonical41799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41799 raw41799Labels = mixedMoment B node4771 node4771Labels := by
  calc
    mixedMoment B raw41799 raw41799Labels = mixedMoment B raw41799step0 raw41799step0Labels := by
      have ha : raw41799step0 = (fun i j => raw41799 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41799step0 raw41799; decide +kernel
      have hl : raw41799step0Labels = raw41799Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41799 raw41799Labels permutation212 permutation7
    mixedMoment B raw41799step0 raw41799step0Labels = mixedMoment B raw41799step1 raw41799step1Labels := by
      have ha : raw41799step1 = -raw41799step0 := by apply Matrix.ext; change ∀ i j, raw41799step1 i j = -(raw41799step0 i j); unfold raw41799step1 raw41799step0; decide +kernel
      have hl : raw41799step1Labels = raw41799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41799step1 raw41799step1Labels = mixedMoment B raw41799step2 raw41799step2Labels := by
      have ha : raw41799step2 = raw41799step1 := by apply Matrix.ext; unfold raw41799step2 raw41799step1; decide +kernel
      have hl : raw41799step1Labels = labelEmbedding6 ∘ raw41799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41799step1 raw41799step1Labels raw41799step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4771 node4771Labels := by rfl

theorem canonical41800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41800 raw41800Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw41800 raw41800Labels = mixedMoment B raw41800step0 raw41800step0Labels := by
      have ha : raw41800step0 = (fun i j => raw41800 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41800step0 raw41800; decide +kernel
      have hl : raw41800step0Labels = raw41800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41800 raw41800Labels permutation200 permutation2
    mixedMoment B raw41800step0 raw41800step0Labels = mixedMoment B raw41800step1 raw41800step1Labels := by
      have ha : raw41800step1 = raw41800step0 := by apply Matrix.ext; unfold raw41800step1 raw41800step0; decide +kernel
      have hl : raw41800step0Labels = labelEmbedding1 ∘ raw41800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41800step0 raw41800step0Labels raw41800step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

theorem canonical41801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41801 raw41801Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw41801 raw41801Labels = mixedMoment B raw41801step0 raw41801step0Labels := by
      have ha : raw41801step0 = (fun i j => raw41801 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41801step0 raw41801; decide +kernel
      have hl : raw41801step0Labels = raw41801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41801 raw41801Labels permutation212 permutation7
    mixedMoment B raw41801step0 raw41801step0Labels = mixedMoment B raw41801step1 raw41801step1Labels := by
      have ha : raw41801step1 = -raw41801step0 := by apply Matrix.ext; change ∀ i j, raw41801step1 i j = -(raw41801step0 i j); unfold raw41801step1 raw41801step0; decide +kernel
      have hl : raw41801step1Labels = raw41801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41801step1 raw41801step1Labels = mixedMoment B raw41801step2 raw41801step2Labels := by
      have ha : raw41801step2 = raw41801step1 := by apply Matrix.ext; unfold raw41801step2 raw41801step1; decide +kernel
      have hl : raw41801step1Labels = labelEmbedding6 ∘ raw41801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41801step1 raw41801step1Labels raw41801step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4663 node4663Labels := by rfl

theorem canonical41802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41802 raw41802Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw41802 raw41802Labels = mixedMoment B raw41802step0 raw41802step0Labels := by
      have ha : raw41802step0 = (fun i j => raw41802 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41802step0 raw41802; decide +kernel
      have hl : raw41802step0Labels = raw41802Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41802 raw41802Labels permutation157 permutation2
    mixedMoment B raw41802step0 raw41802step0Labels = mixedMoment B raw41802step1 raw41802step1Labels := by
      have ha : raw41802step1 = raw41802step0 := by apply Matrix.ext; unfold raw41802step1 raw41802step0; decide +kernel
      have hl : raw41802step0Labels = labelEmbedding1 ∘ raw41802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41802step0 raw41802step0Labels raw41802step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

theorem canonical41803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41803 raw41803Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw41803 raw41803Labels = mixedMoment B raw41803step0 raw41803step0Labels := by
      have ha : raw41803step0 = (fun i j => raw41803 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41803step0 raw41803; decide +kernel
      have hl : raw41803step0Labels = raw41803Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41803 raw41803Labels permutation247 permutation7
    mixedMoment B raw41803step0 raw41803step0Labels = mixedMoment B raw41803step1 raw41803step1Labels := by
      have ha : raw41803step1 = -raw41803step0 := by apply Matrix.ext; change ∀ i j, raw41803step1 i j = -(raw41803step0 i j); unfold raw41803step1 raw41803step0; decide +kernel
      have hl : raw41803step1Labels = raw41803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41803step1 raw41803step1Labels = mixedMoment B raw41803step2 raw41803step2Labels := by
      have ha : raw41803step2 = raw41803step1 := by apply Matrix.ext; unfold raw41803step2 raw41803step1; decide +kernel
      have hl : raw41803step1Labels = labelEmbedding6 ∘ raw41803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41803step1 raw41803step1Labels raw41803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

theorem canonical41804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41804 raw41804Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw41804 raw41804Labels = mixedMoment B raw41804step0 raw41804step0Labels := by
      have ha : raw41804step0 = (fun i j => raw41804 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41804step0 raw41804; decide +kernel
      have hl : raw41804step0Labels = raw41804Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41804 raw41804Labels permutation157 permutation2
    mixedMoment B raw41804step0 raw41804step0Labels = mixedMoment B raw41804step1 raw41804step1Labels := by
      have ha : raw41804step1 = raw41804step0 := by apply Matrix.ext; unfold raw41804step1 raw41804step0; decide +kernel
      have hl : raw41804step0Labels = labelEmbedding1 ∘ raw41804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41804step0 raw41804step0Labels raw41804step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

theorem canonical41805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41805 raw41805Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw41805 raw41805Labels = mixedMoment B raw41805step0 raw41805step0Labels := by
      have ha : raw41805step0 = (fun i j => raw41805 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41805step0 raw41805; decide +kernel
      have hl : raw41805step0Labels = raw41805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41805 raw41805Labels permutation260 permutation7
    mixedMoment B raw41805step0 raw41805step0Labels = mixedMoment B raw41805step1 raw41805step1Labels := by
      have ha : raw41805step1 = -raw41805step0 := by apply Matrix.ext; change ∀ i j, raw41805step1 i j = -(raw41805step0 i j); unfold raw41805step1 raw41805step0; decide +kernel
      have hl : raw41805step1Labels = raw41805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41805step1 raw41805step1Labels = mixedMoment B raw41805step2 raw41805step2Labels := by
      have ha : raw41805step2 = raw41805step1 := by apply Matrix.ext; unfold raw41805step2 raw41805step1; decide +kernel
      have hl : raw41805step1Labels = labelEmbedding6 ∘ raw41805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41805step1 raw41805step1Labels raw41805step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

theorem canonical41806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41806 raw41806Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw41806 raw41806Labels = mixedMoment B raw41806step0 raw41806step0Labels := by
      have hz : ∀ j, raw41806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41806step0 = (fun i j => raw41806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41806step0 raw41806; decide +kernel
      have hl : raw41806step0Labels = raw41806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41806 raw41806Labels permutation434 hz
    mixedMoment B raw41806step0 raw41806step0Labels = mixedMoment B raw41806step1 raw41806step1Labels := by
      have hz : ∀ j, raw41806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41806step1 = (fun i j => raw41806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41806step1 raw41806step0; decide +kernel
      have hl : raw41806step1Labels = raw41806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41806step0 raw41806step0Labels permutation80 hz
    mixedMoment B raw41806step1 raw41806step1Labels = mixedMoment B raw41806step2 raw41806step2Labels := by
      have ha : raw41806step2 = raw41806step1 := by apply Matrix.ext; unfold raw41806step2 raw41806step1; decide +kernel
      have hl : raw41806step1Labels = labelEmbedding1 ∘ raw41806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41806step1 raw41806step1Labels raw41806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2267 node2267Labels := by rfl

theorem canonical41807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41807 raw41807Labels = mixedMoment B node4881 node4881Labels := by
  calc
    mixedMoment B raw41807 raw41807Labels = mixedMoment B raw41807step0 raw41807step0Labels := by
      have hz : ∀ j, raw41807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41807step0 = (fun i j => raw41807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41807step0 raw41807; decide +kernel
      have hl : raw41807step0Labels = raw41807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41807 raw41807Labels permutation434 hz
    mixedMoment B raw41807step0 raw41807step0Labels = mixedMoment B raw41807step1 raw41807step1Labels := by
      have hz : ∀ j, raw41807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41807step1 = (fun i j => raw41807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41807step1 raw41807step0; decide +kernel
      have hl : raw41807step1Labels = raw41807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41807step0 raw41807step0Labels permutation80 hz
    mixedMoment B raw41807step1 raw41807step1Labels = mixedMoment B raw41807step2 raw41807step2Labels := by
      have ha : raw41807step2 = (fun i j => raw41807step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41807step2 raw41807step1; decide +kernel
      have hl : raw41807step2Labels = raw41807step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41807step1 raw41807step1Labels permutation12 permutation7
    mixedMoment B raw41807step2 raw41807step2Labels = mixedMoment B raw41807step3 raw41807step3Labels := by
      have ha : raw41807step3 = -raw41807step2 := by apply Matrix.ext; change ∀ i j, raw41807step3 i j = -(raw41807step2 i j); unfold raw41807step3 raw41807step2; decide +kernel
      have hl : raw41807step3Labels = raw41807step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41807step3 raw41807step3Labels = mixedMoment B raw41807step4 raw41807step4Labels := by
      have ha : raw41807step4 = raw41807step3 := by apply Matrix.ext; unfold raw41807step4 raw41807step3; decide +kernel
      have hl : raw41807step3Labels = labelEmbedding6 ∘ raw41807step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41807step3 raw41807step3Labels raw41807step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4881 node4881Labels := by rfl

theorem canonical41808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41808 raw41808Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw41808 raw41808Labels = mixedMoment B raw41808step0 raw41808step0Labels := by
      have hz : ∀ j, raw41808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41808step0 = (fun i j => raw41808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41808step0 raw41808; decide +kernel
      have hl : raw41808step0Labels = raw41808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41808 raw41808Labels permutation434 hz
    mixedMoment B raw41808step0 raw41808step0Labels = mixedMoment B raw41808step1 raw41808step1Labels := by
      have hz : ∀ j, raw41808step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41808step1 = (fun i j => raw41808step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41808step1 raw41808step0; decide +kernel
      have hl : raw41808step1Labels = raw41808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41808step0 raw41808step0Labels permutation80 hz
    mixedMoment B raw41808step1 raw41808step1Labels = mixedMoment B raw41808step2 raw41808step2Labels := by
      have ha : raw41808step2 = raw41808step1 := by apply Matrix.ext; unfold raw41808step2 raw41808step1; decide +kernel
      have hl : raw41808step1Labels = labelEmbedding1 ∘ raw41808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41808step1 raw41808step1Labels raw41808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

theorem canonical41809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41809 raw41809Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw41809 raw41809Labels = mixedMoment B raw41809step0 raw41809step0Labels := by
      have hz : ∀ j, raw41809 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41809step0 = (fun i j => raw41809 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41809step0 raw41809; decide +kernel
      have hl : raw41809step0Labels = raw41809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41809 raw41809Labels permutation434 hz
    mixedMoment B raw41809step0 raw41809step0Labels = mixedMoment B raw41809step1 raw41809step1Labels := by
      have hz : ∀ j, raw41809step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41809step1 = (fun i j => raw41809step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41809step1 raw41809step0; decide +kernel
      have hl : raw41809step1Labels = raw41809step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41809step0 raw41809step0Labels permutation80 hz
    mixedMoment B raw41809step1 raw41809step1Labels = mixedMoment B raw41809step2 raw41809step2Labels := by
      have ha : raw41809step2 = (fun i j => raw41809step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41809step2 raw41809step1; decide +kernel
      have hl : raw41809step2Labels = raw41809step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41809step1 raw41809step1Labels permutation29 permutation6
    _ = mixedMoment B node4560 node4560Labels := by rfl

theorem canonical41810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41810 raw41810Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw41810 raw41810Labels = mixedMoment B raw41810step0 raw41810step0Labels := by
      have hz : ∀ j, raw41810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41810step0 = (fun i j => raw41810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41810step0 raw41810; decide +kernel
      have hl : raw41810step0Labels = raw41810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41810 raw41810Labels permutation346 hz
    mixedMoment B raw41810step0 raw41810step0Labels = mixedMoment B raw41810step1 raw41810step1Labels := by
      have ha : raw41810step1 = (fun i j => raw41810step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41810step1 raw41810step0; decide +kernel
      have hl : raw41810step1Labels = raw41810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41810step0 raw41810step0Labels permutation38 permutation2
    mixedMoment B raw41810step1 raw41810step1Labels = mixedMoment B raw41810step2 raw41810step2Labels := by
      have ha : raw41810step2 = raw41810step1 := by apply Matrix.ext; unfold raw41810step2 raw41810step1; decide +kernel
      have hl : raw41810step1Labels = labelEmbedding1 ∘ raw41810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41810step1 raw41810step1Labels raw41810step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

theorem canonical41811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41811 raw41811Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw41811 raw41811Labels = mixedMoment B raw41811step0 raw41811step0Labels := by
      have hz : ∀ j, raw41811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41811step0 = (fun i j => raw41811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41811step0 raw41811; decide +kernel
      have hl : raw41811step0Labels = raw41811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41811 raw41811Labels permutation346 hz
    mixedMoment B raw41811step0 raw41811step0Labels = mixedMoment B raw41811step1 raw41811step1Labels := by
      have ha : raw41811step1 = (fun i j => raw41811step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41811step1 raw41811step0; decide +kernel
      have hl : raw41811step1Labels = raw41811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41811step0 raw41811step0Labels permutation42 permutation7
    mixedMoment B raw41811step1 raw41811step1Labels = mixedMoment B raw41811step2 raw41811step2Labels := by
      have ha : raw41811step2 = -raw41811step1 := by apply Matrix.ext; change ∀ i j, raw41811step2 i j = -(raw41811step1 i j); unfold raw41811step2 raw41811step1; decide +kernel
      have hl : raw41811step2Labels = raw41811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41811step2 raw41811step2Labels = mixedMoment B raw41811step3 raw41811step3Labels := by
      have ha : raw41811step3 = raw41811step2 := by apply Matrix.ext; unfold raw41811step3 raw41811step2; decide +kernel
      have hl : raw41811step2Labels = labelEmbedding6 ∘ raw41811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41811step2 raw41811step2Labels raw41811step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

theorem canonical41812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41812 raw41812Labels = mixedMoment B node2200 node2200Labels := by
  calc
    mixedMoment B raw41812 raw41812Labels = mixedMoment B raw41812step0 raw41812step0Labels := by
      have hz : ∀ j, raw41812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41812step0 = (fun i j => raw41812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41812step0 raw41812; decide +kernel
      have hl : raw41812step0Labels = raw41812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41812 raw41812Labels permutation346 hz
    mixedMoment B raw41812step0 raw41812step0Labels = mixedMoment B raw41812step1 raw41812step1Labels := by
      have ha : raw41812step1 = (fun i j => raw41812step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41812step1 raw41812step0; decide +kernel
      have hl : raw41812step1Labels = raw41812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41812step0 raw41812step0Labels permutation38 permutation2
    mixedMoment B raw41812step1 raw41812step1Labels = mixedMoment B raw41812step2 raw41812step2Labels := by
      have ha : raw41812step2 = raw41812step1 := by apply Matrix.ext; unfold raw41812step2 raw41812step1; decide +kernel
      have hl : raw41812step1Labels = labelEmbedding1 ∘ raw41812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41812step1 raw41812step1Labels raw41812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2200 node2200Labels := by rfl

theorem canonical41813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41813 raw41813Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw41813 raw41813Labels = mixedMoment B raw41813step0 raw41813step0Labels := by
      have hz : ∀ j, raw41813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41813step0 = (fun i j => raw41813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41813step0 raw41813; decide +kernel
      have hl : raw41813step0Labels = raw41813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41813 raw41813Labels permutation346 hz
    mixedMoment B raw41813step0 raw41813step0Labels = mixedMoment B raw41813step1 raw41813step1Labels := by
      have ha : raw41813step1 = (fun i j => raw41813step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41813step1 raw41813step0; decide +kernel
      have hl : raw41813step1Labels = raw41813step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41813step0 raw41813step0Labels permutation137 permutation6
    _ = mixedMoment B node4552 node4552Labels := by rfl

theorem canonical41814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41814 raw41814Labels = mixedMoment B node2149 node2149Labels := by
  calc
    mixedMoment B raw41814 raw41814Labels = mixedMoment B raw41814step0 raw41814step0Labels := by
      have hz : ∀ j, raw41814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41814step0 = (fun i j => raw41814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41814step0 raw41814; decide +kernel
      have hl : raw41814step0Labels = raw41814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41814 raw41814Labels permutation346 hz
    mixedMoment B raw41814step0 raw41814step0Labels = mixedMoment B raw41814step1 raw41814step1Labels := by
      have ha : raw41814step1 = (fun i j => raw41814step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41814step1 raw41814step0; decide +kernel
      have hl : raw41814step1Labels = raw41814step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41814step0 raw41814step0Labels permutation38 permutation2
    mixedMoment B raw41814step1 raw41814step1Labels = mixedMoment B raw41814step2 raw41814step2Labels := by
      have ha : raw41814step2 = raw41814step1 := by apply Matrix.ext; unfold raw41814step2 raw41814step1; decide +kernel
      have hl : raw41814step1Labels = labelEmbedding1 ∘ raw41814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41814step1 raw41814step1Labels raw41814step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2149 node2149Labels := by rfl

theorem canonical41815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41815 raw41815Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw41815 raw41815Labels = mixedMoment B raw41815step0 raw41815step0Labels := by
      have hz : ∀ j, raw41815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41815step0 = (fun i j => raw41815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41815step0 raw41815; decide +kernel
      have hl : raw41815step0Labels = raw41815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41815 raw41815Labels permutation346 hz
    mixedMoment B raw41815step0 raw41815step0Labels = mixedMoment B raw41815step1 raw41815step1Labels := by
      have ha : raw41815step1 = (fun i j => raw41815step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41815step1 raw41815step0; decide +kernel
      have hl : raw41815step1Labels = raw41815step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41815step0 raw41815step0Labels permutation139 permutation6
    _ = mixedMoment B node4536 node4536Labels := by rfl

theorem canonical41816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41816 raw41816Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw41816 raw41816Labels = mixedMoment B raw41816step0 raw41816step0Labels := by
      have hz : ∀ j, raw41816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41816step0 = (fun i j => raw41816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41816step0 raw41816; decide +kernel
      have hl : raw41816step0Labels = raw41816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41816 raw41816Labels permutation346 hz
    mixedMoment B raw41816step0 raw41816step0Labels = mixedMoment B raw41816step1 raw41816step1Labels := by
      have ha : raw41816step1 = (fun i j => raw41816step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41816step1 raw41816step0; decide +kernel
      have hl : raw41816step1Labels = raw41816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41816step0 raw41816step0Labels permutation37 permutation2
    mixedMoment B raw41816step1 raw41816step1Labels = mixedMoment B raw41816step2 raw41816step2Labels := by
      have ha : raw41816step2 = raw41816step1 := by apply Matrix.ext; unfold raw41816step2 raw41816step1; decide +kernel
      have hl : raw41816step1Labels = labelEmbedding1 ∘ raw41816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41816step1 raw41816step1Labels raw41816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

theorem canonical41817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41817 raw41817Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw41817 raw41817Labels = mixedMoment B raw41817step0 raw41817step0Labels := by
      have hz : ∀ j, raw41817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41817step0 = (fun i j => raw41817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41817step0 raw41817; decide +kernel
      have hl : raw41817step0Labels = raw41817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41817 raw41817Labels permutation346 hz
    mixedMoment B raw41817step0 raw41817step0Labels = mixedMoment B raw41817step1 raw41817step1Labels := by
      have ha : raw41817step1 = (fun i j => raw41817step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41817step1 raw41817step0; decide +kernel
      have hl : raw41817step1Labels = raw41817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41817step0 raw41817step0Labels permutation51 permutation7
    mixedMoment B raw41817step1 raw41817step1Labels = mixedMoment B raw41817step2 raw41817step2Labels := by
      have ha : raw41817step2 = -raw41817step1 := by apply Matrix.ext; change ∀ i j, raw41817step2 i j = -(raw41817step1 i j); unfold raw41817step2 raw41817step1; decide +kernel
      have hl : raw41817step2Labels = raw41817step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41817step2 raw41817step2Labels = mixedMoment B raw41817step3 raw41817step3Labels := by
      have ha : raw41817step3 = raw41817step2 := by apply Matrix.ext; unfold raw41817step3 raw41817step2; decide +kernel
      have hl : raw41817step2Labels = labelEmbedding6 ∘ raw41817step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41817step2 raw41817step2Labels raw41817step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

theorem canonical41818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41818 raw41818Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw41818 raw41818Labels = mixedMoment B raw41818step0 raw41818step0Labels := by
      have hz : ∀ j, raw41818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41818step0 = (fun i j => raw41818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41818step0 raw41818; decide +kernel
      have hl : raw41818step0Labels = raw41818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41818 raw41818Labels permutation346 hz
    mixedMoment B raw41818step0 raw41818step0Labels = mixedMoment B raw41818step1 raw41818step1Labels := by
      have ha : raw41818step1 = (fun i j => raw41818step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41818step1 raw41818step0; decide +kernel
      have hl : raw41818step1Labels = raw41818step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41818step0 raw41818step0Labels permutation37 permutation2
    mixedMoment B raw41818step1 raw41818step1Labels = mixedMoment B raw41818step2 raw41818step2Labels := by
      have ha : raw41818step2 = raw41818step1 := by apply Matrix.ext; unfold raw41818step2 raw41818step1; decide +kernel
      have hl : raw41818step1Labels = labelEmbedding1 ∘ raw41818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41818step1 raw41818step1Labels raw41818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

theorem canonical41819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41819 raw41819Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw41819 raw41819Labels = mixedMoment B raw41819step0 raw41819step0Labels := by
      have hz : ∀ j, raw41819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41819step0 = (fun i j => raw41819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41819step0 raw41819; decide +kernel
      have hl : raw41819step0Labels = raw41819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41819 raw41819Labels permutation346 hz
    mixedMoment B raw41819step0 raw41819step0Labels = mixedMoment B raw41819step1 raw41819step1Labels := by
      have ha : raw41819step1 = (fun i j => raw41819step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41819step1 raw41819step0; decide +kernel
      have hl : raw41819step1Labels = raw41819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41819step0 raw41819step0Labels permutation54 permutation7
    mixedMoment B raw41819step1 raw41819step1Labels = mixedMoment B raw41819step2 raw41819step2Labels := by
      have ha : raw41819step2 = -raw41819step1 := by apply Matrix.ext; change ∀ i j, raw41819step2 i j = -(raw41819step1 i j); unfold raw41819step2 raw41819step1; decide +kernel
      have hl : raw41819step2Labels = raw41819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41819step2 raw41819step2Labels = mixedMoment B raw41819step3 raw41819step3Labels := by
      have ha : raw41819step3 = raw41819step2 := by apply Matrix.ext; unfold raw41819step3 raw41819step2; decide +kernel
      have hl : raw41819step2Labels = labelEmbedding6 ∘ raw41819step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41819step2 raw41819step2Labels raw41819step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

theorem canonical41820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41820 raw41820Labels = mixedMoment B node2257 node2257Labels := by
  calc
    mixedMoment B raw41820 raw41820Labels = mixedMoment B raw41820step0 raw41820step0Labels := by
      have hz : ∀ j, raw41820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41820step0 = (fun i j => raw41820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41820step0 raw41820; decide +kernel
      have hl : raw41820step0Labels = raw41820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41820 raw41820Labels permutation346 hz
    mixedMoment B raw41820step0 raw41820step0Labels = mixedMoment B raw41820step1 raw41820step1Labels := by
      have ha : raw41820step1 = (fun i j => raw41820step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41820step1 raw41820step0; decide +kernel
      have hl : raw41820step1Labels = raw41820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41820step0 raw41820step0Labels permutation36 permutation2
    mixedMoment B raw41820step1 raw41820step1Labels = mixedMoment B raw41820step2 raw41820step2Labels := by
      have ha : raw41820step2 = raw41820step1 := by apply Matrix.ext; unfold raw41820step2 raw41820step1; decide +kernel
      have hl : raw41820step1Labels = labelEmbedding1 ∘ raw41820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41820step1 raw41820step1Labels raw41820step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2257 node2257Labels := by rfl

theorem canonical41821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41821 raw41821Labels = mixedMoment B node4701 node4701Labels := by
  calc
    mixedMoment B raw41821 raw41821Labels = mixedMoment B raw41821step0 raw41821step0Labels := by
      have hz : ∀ j, raw41821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41821step0 = (fun i j => raw41821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41821step0 raw41821; decide +kernel
      have hl : raw41821step0Labels = raw41821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41821 raw41821Labels permutation346 hz
    mixedMoment B raw41821step0 raw41821step0Labels = mixedMoment B raw41821step1 raw41821step1Labels := by
      have ha : raw41821step1 = (fun i j => raw41821step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41821step1 raw41821step0; decide +kernel
      have hl : raw41821step1Labels = raw41821step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41821step0 raw41821step0Labels permutation50 permutation7
    mixedMoment B raw41821step1 raw41821step1Labels = mixedMoment B raw41821step2 raw41821step2Labels := by
      have ha : raw41821step2 = -raw41821step1 := by apply Matrix.ext; change ∀ i j, raw41821step2 i j = -(raw41821step1 i j); unfold raw41821step2 raw41821step1; decide +kernel
      have hl : raw41821step2Labels = raw41821step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41821step2 raw41821step2Labels = mixedMoment B raw41821step3 raw41821step3Labels := by
      have ha : raw41821step3 = raw41821step2 := by apply Matrix.ext; unfold raw41821step3 raw41821step2; decide +kernel
      have hl : raw41821step2Labels = labelEmbedding6 ∘ raw41821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41821step2 raw41821step2Labels raw41821step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4701 node4701Labels := by rfl

theorem canonical41822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41822 raw41822Labels = mixedMoment B node2172 node2172Labels := by
  calc
    mixedMoment B raw41822 raw41822Labels = mixedMoment B raw41822step0 raw41822step0Labels := by
      have ha : raw41822step0 = (fun i j => raw41822 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41822step0 raw41822; decide +kernel
      have hl : raw41822step0Labels = raw41822Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41822 raw41822Labels permutation182 permutation2
    mixedMoment B raw41822step0 raw41822step0Labels = mixedMoment B raw41822step1 raw41822step1Labels := by
      have ha : raw41822step1 = raw41822step0 := by apply Matrix.ext; unfold raw41822step1 raw41822step0; decide +kernel
      have hl : raw41822step0Labels = labelEmbedding1 ∘ raw41822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41822step0 raw41822step0Labels raw41822step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2172 node2172Labels := by rfl

theorem canonical41823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41823 raw41823Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw41823 raw41823Labels = mixedMoment B raw41823step0 raw41823step0Labels := by
      have ha : raw41823step0 = (fun i j => raw41823 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41823step0 raw41823; decide +kernel
      have hl : raw41823step0Labels = raw41823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41823 raw41823Labels permutation620 permutation6
    _ = mixedMoment B node4532 node4532Labels := by rfl

theorem canonical41824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41824 raw41824Labels = mixedMoment B node2198 node2198Labels := by
  calc
    mixedMoment B raw41824 raw41824Labels = mixedMoment B raw41824step0 raw41824step0Labels := by
      have ha : raw41824step0 = (fun i j => raw41824 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41824step0 raw41824; decide +kernel
      have hl : raw41824step0Labels = raw41824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41824 raw41824Labels permutation181 permutation2
    mixedMoment B raw41824step0 raw41824step0Labels = mixedMoment B raw41824step1 raw41824step1Labels := by
      have ha : raw41824step1 = raw41824step0 := by apply Matrix.ext; unfold raw41824step1 raw41824step0; decide +kernel
      have hl : raw41824step0Labels = labelEmbedding1 ∘ raw41824step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41824step0 raw41824step0Labels raw41824step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2198 node2198Labels := by rfl

theorem canonical41825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41825 raw41825Labels = mixedMoment B node4772 node4772Labels := by
  calc
    mixedMoment B raw41825 raw41825Labels = mixedMoment B raw41825step0 raw41825step0Labels := by
      have ha : raw41825step0 = (fun i j => raw41825 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41825step0 raw41825; decide +kernel
      have hl : raw41825step0Labels = raw41825Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41825 raw41825Labels permutation195 permutation7
    mixedMoment B raw41825step0 raw41825step0Labels = mixedMoment B raw41825step1 raw41825step1Labels := by
      have ha : raw41825step1 = -raw41825step0 := by apply Matrix.ext; change ∀ i j, raw41825step1 i j = -(raw41825step0 i j); unfold raw41825step1 raw41825step0; decide +kernel
      have hl : raw41825step1Labels = raw41825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41825step1 raw41825step1Labels = mixedMoment B raw41825step2 raw41825step2Labels := by
      have ha : raw41825step2 = raw41825step1 := by apply Matrix.ext; unfold raw41825step2 raw41825step1; decide +kernel
      have hl : raw41825step1Labels = labelEmbedding6 ∘ raw41825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41825step1 raw41825step1Labels raw41825step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4772 node4772Labels := by rfl

theorem canonical41826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41826 raw41826Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw41826 raw41826Labels = mixedMoment B raw41826step0 raw41826step0Labels := by
      have ha : raw41826step0 = (fun i j => raw41826 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41826step0 raw41826; decide +kernel
      have hl : raw41826step0Labels = raw41826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41826 raw41826Labels permutation179 permutation2
    mixedMoment B raw41826step0 raw41826step0Labels = mixedMoment B raw41826step1 raw41826step1Labels := by
      have ha : raw41826step1 = raw41826step0 := by apply Matrix.ext; unfold raw41826step1 raw41826step0; decide +kernel
      have hl : raw41826step0Labels = labelEmbedding1 ∘ raw41826step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41826step0 raw41826step0Labels raw41826step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

theorem canonical41827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41827 raw41827Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw41827 raw41827Labels = mixedMoment B raw41827step0 raw41827step0Labels := by
      have ha : raw41827step0 = (fun i j => raw41827 (permutation192 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41827step0 raw41827; decide +kernel
      have hl : raw41827step0Labels = raw41827Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41827 raw41827Labels permutation192 permutation7
    mixedMoment B raw41827step0 raw41827step0Labels = mixedMoment B raw41827step1 raw41827step1Labels := by
      have ha : raw41827step1 = -raw41827step0 := by apply Matrix.ext; change ∀ i j, raw41827step1 i j = -(raw41827step0 i j); unfold raw41827step1 raw41827step0; decide +kernel
      have hl : raw41827step1Labels = raw41827step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41827step1 raw41827step1Labels = mixedMoment B raw41827step2 raw41827step2Labels := by
      have ha : raw41827step2 = raw41827step1 := by apply Matrix.ext; unfold raw41827step2 raw41827step1; decide +kernel
      have hl : raw41827step1Labels = labelEmbedding6 ∘ raw41827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41827step1 raw41827step1Labels raw41827step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

theorem canonical41828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41828 raw41828Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw41828 raw41828Labels = mixedMoment B raw41828step0 raw41828step0Labels := by
      have ha : raw41828step0 = (fun i j => raw41828 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41828step0 raw41828; decide +kernel
      have hl : raw41828step0Labels = raw41828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41828 raw41828Labels permutation180 permutation2
    mixedMoment B raw41828step0 raw41828step0Labels = mixedMoment B raw41828step1 raw41828step1Labels := by
      have ha : raw41828step1 = raw41828step0 := by apply Matrix.ext; unfold raw41828step1 raw41828step0; decide +kernel
      have hl : raw41828step0Labels = labelEmbedding1 ∘ raw41828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41828step0 raw41828step0Labels raw41828step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

theorem canonical41829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41829 raw41829Labels = mixedMoment B node4774 node4774Labels := by
  calc
    mixedMoment B raw41829 raw41829Labels = mixedMoment B raw41829step0 raw41829step0Labels := by
      have ha : raw41829step0 = (fun i j => raw41829 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41829step0 raw41829; decide +kernel
      have hl : raw41829step0Labels = raw41829Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41829 raw41829Labels permutation194 permutation7
    mixedMoment B raw41829step0 raw41829step0Labels = mixedMoment B raw41829step1 raw41829step1Labels := by
      have ha : raw41829step1 = -raw41829step0 := by apply Matrix.ext; change ∀ i j, raw41829step1 i j = -(raw41829step0 i j); unfold raw41829step1 raw41829step0; decide +kernel
      have hl : raw41829step1Labels = raw41829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41829step1 raw41829step1Labels = mixedMoment B raw41829step2 raw41829step2Labels := by
      have ha : raw41829step2 = raw41829step1 := by apply Matrix.ext; unfold raw41829step2 raw41829step1; decide +kernel
      have hl : raw41829step1Labels = labelEmbedding6 ∘ raw41829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41829step1 raw41829step1Labels raw41829step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4774 node4774Labels := by rfl

theorem canonical41830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41830 raw41830Labels = mixedMoment B node2147 node2147Labels := by
  calc
    mixedMoment B raw41830 raw41830Labels = mixedMoment B raw41830step0 raw41830step0Labels := by
      have ha : raw41830step0 = (fun i j => raw41830 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41830step0 raw41830; decide +kernel
      have hl : raw41830step0Labels = raw41830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41830 raw41830Labels permutation181 permutation2
    mixedMoment B raw41830step0 raw41830step0Labels = mixedMoment B raw41830step1 raw41830step1Labels := by
      have ha : raw41830step1 = raw41830step0 := by apply Matrix.ext; unfold raw41830step1 raw41830step0; decide +kernel
      have hl : raw41830step0Labels = labelEmbedding1 ∘ raw41830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41830step0 raw41830step0Labels raw41830step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2147 node2147Labels := by rfl

theorem canonical41831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41831 raw41831Labels = mixedMoment B node4664 node4664Labels := by
  calc
    mixedMoment B raw41831 raw41831Labels = mixedMoment B raw41831step0 raw41831step0Labels := by
      have ha : raw41831step0 = (fun i j => raw41831 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41831step0 raw41831; decide +kernel
      have hl : raw41831step0Labels = raw41831Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41831 raw41831Labels permutation195 permutation7
    mixedMoment B raw41831step0 raw41831step0Labels = mixedMoment B raw41831step1 raw41831step1Labels := by
      have ha : raw41831step1 = -raw41831step0 := by apply Matrix.ext; change ∀ i j, raw41831step1 i j = -(raw41831step0 i j); unfold raw41831step1 raw41831step0; decide +kernel
      have hl : raw41831step1Labels = raw41831step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41831step1 raw41831step1Labels = mixedMoment B raw41831step2 raw41831step2Labels := by
      have ha : raw41831step2 = raw41831step1 := by apply Matrix.ext; unfold raw41831step2 raw41831step1; decide +kernel
      have hl : raw41831step1Labels = labelEmbedding6 ∘ raw41831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41831step1 raw41831step1Labels raw41831step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4664 node4664Labels := by rfl

theorem canonical41832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41832 raw41832Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw41832 raw41832Labels = mixedMoment B raw41832step0 raw41832step0Labels := by
      have ha : raw41832step0 = (fun i j => raw41832 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41832step0 raw41832; decide +kernel
      have hl : raw41832step0Labels = raw41832Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41832 raw41832Labels permutation180 permutation2
    mixedMoment B raw41832step0 raw41832step0Labels = mixedMoment B raw41832step1 raw41832step1Labels := by
      have ha : raw41832step1 = raw41832step0 := by apply Matrix.ext; unfold raw41832step1 raw41832step0; decide +kernel
      have hl : raw41832step0Labels = labelEmbedding1 ∘ raw41832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41832step0 raw41832step0Labels raw41832step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

theorem canonical41833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41833 raw41833Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw41833 raw41833Labels = mixedMoment B raw41833step0 raw41833step0Labels := by
      have ha : raw41833step0 = (fun i j => raw41833 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41833step0 raw41833; decide +kernel
      have hl : raw41833step0Labels = raw41833Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41833 raw41833Labels permutation194 permutation7
    mixedMoment B raw41833step0 raw41833step0Labels = mixedMoment B raw41833step1 raw41833step1Labels := by
      have ha : raw41833step1 = -raw41833step0 := by apply Matrix.ext; change ∀ i j, raw41833step1 i j = -(raw41833step0 i j); unfold raw41833step1 raw41833step0; decide +kernel
      have hl : raw41833step1Labels = raw41833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41833step1 raw41833step1Labels = mixedMoment B raw41833step2 raw41833step2Labels := by
      have ha : raw41833step2 = raw41833step1 := by apply Matrix.ext; unfold raw41833step2 raw41833step1; decide +kernel
      have hl : raw41833step1Labels = labelEmbedding6 ∘ raw41833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41833step1 raw41833step1Labels raw41833step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4666 node4666Labels := by rfl

theorem canonical41834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41834 raw41834Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw41834 raw41834Labels = mixedMoment B raw41834step0 raw41834step0Labels := by
      have hz : ∀ j, raw41834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41834step0 = (fun i j => raw41834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41834step0 raw41834; decide +kernel
      have hl : raw41834step0Labels = raw41834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41834 raw41834Labels permutation434 hz
    mixedMoment B raw41834step0 raw41834step0Labels = mixedMoment B raw41834step1 raw41834step1Labels := by
      have hz : ∀ j, raw41834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41834step1 = (fun i j => raw41834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41834step1 raw41834step0; decide +kernel
      have hl : raw41834step1Labels = raw41834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41834step0 raw41834step0Labels permutation80 hz
    mixedMoment B raw41834step1 raw41834step1Labels = mixedMoment B raw41834step2 raw41834step2Labels := by
      have hz : ∀ j, raw41834step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41834step2 = (fun i j => raw41834step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41834step2 raw41834step1; decide +kernel
      have hl : raw41834step2Labels = raw41834step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41834step1 raw41834step1Labels permutation14 hz
    mixedMoment B raw41834step2 raw41834step2Labels = mixedMoment B raw41834step3 raw41834step3Labels := by
      have ha : raw41834step3 = (fun i j => raw41834step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41834step3 raw41834step2; decide +kernel
      have hl : raw41834step3Labels = raw41834step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41834step2 raw41834step2Labels permutation4 permutation4
    mixedMoment B raw41834step3 raw41834step3Labels = mixedMoment B raw41834step4 raw41834step4Labels := by
      have ha : raw41834step4 = -raw41834step3 := by apply Matrix.ext; change ∀ i j, raw41834step4 i j = -(raw41834step3 i j); unfold raw41834step4 raw41834step3; decide +kernel
      have hl : raw41834step4Labels = raw41834step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41834step4 raw41834step4Labels = mixedMoment B raw41834step5 raw41834step5Labels := by
      have ha : raw41834step5 = raw41834step4 := by apply Matrix.ext; unfold raw41834step5 raw41834step4; decide +kernel
      have hl : raw41834step4Labels = labelEmbedding1 ∘ raw41834step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41834step4 raw41834step4Labels raw41834step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1747 node1747Labels := by rfl

theorem canonical41835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41835 raw41835Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw41835 raw41835Labels = mixedMoment B raw41835step0 raw41835step0Labels := by
      have hz : ∀ j, raw41835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41835step0 = (fun i j => raw41835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41835step0 raw41835; decide +kernel
      have hl : raw41835step0Labels = raw41835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41835 raw41835Labels permutation434 hz
    mixedMoment B raw41835step0 raw41835step0Labels = mixedMoment B raw41835step1 raw41835step1Labels := by
      have hz : ∀ j, raw41835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41835step1 = (fun i j => raw41835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41835step1 raw41835step0; decide +kernel
      have hl : raw41835step1Labels = raw41835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41835step0 raw41835step0Labels permutation80 hz
    mixedMoment B raw41835step1 raw41835step1Labels = mixedMoment B raw41835step2 raw41835step2Labels := by
      have hz : ∀ j, raw41835step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41835step2 = (fun i j => raw41835step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41835step2 raw41835step1; decide +kernel
      have hl : raw41835step2Labels = raw41835step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41835step1 raw41835step1Labels permutation14 hz
    mixedMoment B raw41835step2 raw41835step2Labels = mixedMoment B raw41835step3 raw41835step3Labels := by
      have ha : raw41835step3 = (fun i j => raw41835step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41835step3 raw41835step2; decide +kernel
      have hl : raw41835step3Labels = raw41835step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41835step2 raw41835step2Labels permutation5 permutation6
    _ = mixedMoment B node4508 node4508Labels := by rfl

theorem canonical41836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41836 raw41836Labels = mixedMoment B node1531 node1531Labels := by
  calc
    mixedMoment B raw41836 raw41836Labels = mixedMoment B raw41836step0 raw41836step0Labels := by
      have hz : ∀ j, raw41836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41836step0 = (fun i j => raw41836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41836step0 raw41836; decide +kernel
      have hl : raw41836step0Labels = raw41836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41836 raw41836Labels permutation434 hz
    mixedMoment B raw41836step0 raw41836step0Labels = mixedMoment B raw41836step1 raw41836step1Labels := by
      have hz : ∀ j, raw41836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41836step1 = (fun i j => raw41836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41836step1 raw41836step0; decide +kernel
      have hl : raw41836step1Labels = raw41836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41836step0 raw41836step0Labels permutation80 hz
    mixedMoment B raw41836step1 raw41836step1Labels = mixedMoment B raw41836step2 raw41836step2Labels := by
      have hz : ∀ j, raw41836step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41836step2 = (fun i j => raw41836step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41836step2 raw41836step1; decide +kernel
      have hl : raw41836step2Labels = raw41836step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41836step1 raw41836step1Labels permutation14 hz
    mixedMoment B raw41836step2 raw41836step2Labels = mixedMoment B raw41836step3 raw41836step3Labels := by
      have ha : raw41836step3 = (fun i j => raw41836step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41836step3 raw41836step2; decide +kernel
      have hl : raw41836step3Labels = raw41836step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41836step2 raw41836step2Labels permutation6 permutation4
    mixedMoment B raw41836step3 raw41836step3Labels = mixedMoment B raw41836step4 raw41836step4Labels := by
      have ha : raw41836step4 = -raw41836step3 := by apply Matrix.ext; change ∀ i j, raw41836step4 i j = -(raw41836step3 i j); unfold raw41836step4 raw41836step3; decide +kernel
      have hl : raw41836step4Labels = raw41836step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41836step4 raw41836step4Labels = mixedMoment B raw41836step5 raw41836step5Labels := by
      have ha : raw41836step5 = raw41836step4 := by apply Matrix.ext; unfold raw41836step5 raw41836step4; decide +kernel
      have hl : raw41836step4Labels = labelEmbedding1 ∘ raw41836step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41836step4 raw41836step4Labels raw41836step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1531 node1531Labels := by rfl

theorem canonical41837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41837 raw41837Labels = mixedMoment B node4193 node4193Labels := by
  calc
    mixedMoment B raw41837 raw41837Labels = mixedMoment B raw41837step0 raw41837step0Labels := by
      have hz : ∀ j, raw41837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41837step0 = (fun i j => raw41837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41837step0 raw41837; decide +kernel
      have hl : raw41837step0Labels = raw41837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41837 raw41837Labels permutation434 hz
    mixedMoment B raw41837step0 raw41837step0Labels = mixedMoment B raw41837step1 raw41837step1Labels := by
      have hz : ∀ j, raw41837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41837step1 = (fun i j => raw41837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41837step1 raw41837step0; decide +kernel
      have hl : raw41837step1Labels = raw41837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41837step0 raw41837step0Labels permutation80 hz
    mixedMoment B raw41837step1 raw41837step1Labels = mixedMoment B raw41837step2 raw41837step2Labels := by
      have hz : ∀ j, raw41837step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41837step2 = (fun i j => raw41837step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41837step2 raw41837step1; decide +kernel
      have hl : raw41837step2Labels = raw41837step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41837step1 raw41837step1Labels permutation14 hz
    mixedMoment B raw41837step2 raw41837step2Labels = mixedMoment B raw41837step3 raw41837step3Labels := by
      have ha : raw41837step3 = (fun i j => raw41837step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41837step3 raw41837step2; decide +kernel
      have hl : raw41837step3Labels = raw41837step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41837step2 raw41837step2Labels permutation7 permutation6
    _ = mixedMoment B node4193 node4193Labels := by rfl

theorem canonical41838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41838 raw41838Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw41838 raw41838Labels = mixedMoment B raw41838step0 raw41838step0Labels := by
      have hz : ∀ j, raw41838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41838step0 = (fun i j => raw41838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41838step0 raw41838; decide +kernel
      have hl : raw41838step0Labels = raw41838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41838 raw41838Labels permutation346 hz
    mixedMoment B raw41838step0 raw41838step0Labels = mixedMoment B raw41838step1 raw41838step1Labels := by
      have hz : ∀ j, raw41838step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41838step1 = (fun i j => raw41838step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41838step1 raw41838step0; decide +kernel
      have hl : raw41838step1Labels = raw41838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41838step0 raw41838step0Labels permutation56 hz
    mixedMoment B raw41838step1 raw41838step1Labels = mixedMoment B raw41838step2 raw41838step2Labels := by
      have ha : raw41838step2 = (fun i j => raw41838step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41838step2 raw41838step1; decide +kernel
      have hl : raw41838step2Labels = raw41838step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41838step1 raw41838step1Labels permutation20 permutation4
    mixedMoment B raw41838step2 raw41838step2Labels = mixedMoment B raw41838step3 raw41838step3Labels := by
      have ha : raw41838step3 = -raw41838step2 := by apply Matrix.ext; change ∀ i j, raw41838step3 i j = -(raw41838step2 i j); unfold raw41838step3 raw41838step2; decide +kernel
      have hl : raw41838step3Labels = raw41838step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41838step3 raw41838step3Labels = mixedMoment B raw41838step4 raw41838step4Labels := by
      have ha : raw41838step4 = raw41838step3 := by apply Matrix.ext; unfold raw41838step4 raw41838step3; decide +kernel
      have hl : raw41838step3Labels = labelEmbedding1 ∘ raw41838step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41838step3 raw41838step3Labels raw41838step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1746 node1746Labels := by rfl

theorem canonical41839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41839 raw41839Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw41839 raw41839Labels = mixedMoment B raw41839step0 raw41839step0Labels := by
      have hz : ∀ j, raw41839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41839step0 = (fun i j => raw41839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41839step0 raw41839; decide +kernel
      have hl : raw41839step0Labels = raw41839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41839 raw41839Labels permutation346 hz
    mixedMoment B raw41839step0 raw41839step0Labels = mixedMoment B raw41839step1 raw41839step1Labels := by
      have hz : ∀ j, raw41839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41839step1 = (fun i j => raw41839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41839step1 raw41839step0; decide +kernel
      have hl : raw41839step1Labels = raw41839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41839step0 raw41839step0Labels permutation56 hz
    mixedMoment B raw41839step1 raw41839step1Labels = mixedMoment B raw41839step2 raw41839step2Labels := by
      have ha : raw41839step2 = (fun i j => raw41839step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41839step2 raw41839step1; decide +kernel
      have hl : raw41839step2Labels = raw41839step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41839step1 raw41839step1Labels permutation25 permutation6
    _ = mixedMoment B node4478 node4478Labels := by rfl

theorem canonical41840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41840 raw41840Labels = mixedMoment B node1530 node1530Labels := by
  calc
    mixedMoment B raw41840 raw41840Labels = mixedMoment B raw41840step0 raw41840step0Labels := by
      have hz : ∀ j, raw41840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41840step0 = (fun i j => raw41840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41840step0 raw41840; decide +kernel
      have hl : raw41840step0Labels = raw41840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41840 raw41840Labels permutation346 hz
    mixedMoment B raw41840step0 raw41840step0Labels = mixedMoment B raw41840step1 raw41840step1Labels := by
      have hz : ∀ j, raw41840step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41840step1 = (fun i j => raw41840step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41840step1 raw41840step0; decide +kernel
      have hl : raw41840step1Labels = raw41840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41840step0 raw41840step0Labels permutation56 hz
    mixedMoment B raw41840step1 raw41840step1Labels = mixedMoment B raw41840step2 raw41840step2Labels := by
      have ha : raw41840step2 = (fun i j => raw41840step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41840step2 raw41840step1; decide +kernel
      have hl : raw41840step2Labels = raw41840step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41840step1 raw41840step1Labels permutation26 permutation4
    mixedMoment B raw41840step2 raw41840step2Labels = mixedMoment B raw41840step3 raw41840step3Labels := by
      have ha : raw41840step3 = -raw41840step2 := by apply Matrix.ext; change ∀ i j, raw41840step3 i j = -(raw41840step2 i j); unfold raw41840step3 raw41840step2; decide +kernel
      have hl : raw41840step3Labels = raw41840step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41840step3 raw41840step3Labels = mixedMoment B raw41840step4 raw41840step4Labels := by
      have ha : raw41840step4 = raw41840step3 := by apply Matrix.ext; unfold raw41840step4 raw41840step3; decide +kernel
      have hl : raw41840step3Labels = labelEmbedding1 ∘ raw41840step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41840step3 raw41840step3Labels raw41840step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1530 node1530Labels := by rfl

theorem canonical41841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41841 raw41841Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw41841 raw41841Labels = mixedMoment B raw41841step0 raw41841step0Labels := by
      have hz : ∀ j, raw41841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41841step0 = (fun i j => raw41841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41841step0 raw41841; decide +kernel
      have hl : raw41841step0Labels = raw41841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41841 raw41841Labels permutation346 hz
    mixedMoment B raw41841step0 raw41841step0Labels = mixedMoment B raw41841step1 raw41841step1Labels := by
      have hz : ∀ j, raw41841step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41841step1 = (fun i j => raw41841step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41841step1 raw41841step0; decide +kernel
      have hl : raw41841step1Labels = raw41841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41841step0 raw41841step0Labels permutation56 hz
    mixedMoment B raw41841step1 raw41841step1Labels = mixedMoment B raw41841step2 raw41841step2Labels := by
      have ha : raw41841step2 = (fun i j => raw41841step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41841step2 raw41841step1; decide +kernel
      have hl : raw41841step2Labels = raw41841step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41841step1 raw41841step1Labels permutation29 permutation6
    _ = mixedMoment B node4184 node4184Labels := by rfl

theorem canonical41842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41842 raw41842Labels = mixedMoment B node1529 node1529Labels := by
  calc
    mixedMoment B raw41842 raw41842Labels = mixedMoment B raw41842step0 raw41842step0Labels := by
      have hz : ∀ j, raw41842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41842step0 = (fun i j => raw41842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41842step0 raw41842; decide +kernel
      have hl : raw41842step0Labels = raw41842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41842 raw41842Labels permutation346 hz
    mixedMoment B raw41842step0 raw41842step0Labels = mixedMoment B raw41842step1 raw41842step1Labels := by
      have hz : ∀ j, raw41842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41842step1 = (fun i j => raw41842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41842step1 raw41842step0; decide +kernel
      have hl : raw41842step1Labels = raw41842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41842step0 raw41842step0Labels permutation56 hz
    mixedMoment B raw41842step1 raw41842step1Labels = mixedMoment B raw41842step2 raw41842step2Labels := by
      have ha : raw41842step2 = (fun i j => raw41842step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41842step2 raw41842step1; decide +kernel
      have hl : raw41842step2Labels = raw41842step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41842step1 raw41842step1Labels permutation27 permutation4
    mixedMoment B raw41842step2 raw41842step2Labels = mixedMoment B raw41842step3 raw41842step3Labels := by
      have ha : raw41842step3 = -raw41842step2 := by apply Matrix.ext; change ∀ i j, raw41842step3 i j = -(raw41842step2 i j); unfold raw41842step3 raw41842step2; decide +kernel
      have hl : raw41842step3Labels = raw41842step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41842step3 raw41842step3Labels = mixedMoment B raw41842step4 raw41842step4Labels := by
      have ha : raw41842step4 = raw41842step3 := by apply Matrix.ext; unfold raw41842step4 raw41842step3; decide +kernel
      have hl : raw41842step3Labels = labelEmbedding1 ∘ raw41842step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41842step3 raw41842step3Labels raw41842step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1529 node1529Labels := by rfl

theorem canonical41843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41843 raw41843Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw41843 raw41843Labels = mixedMoment B raw41843step0 raw41843step0Labels := by
      have hz : ∀ j, raw41843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41843step0 = (fun i j => raw41843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41843step0 raw41843; decide +kernel
      have hl : raw41843step0Labels = raw41843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41843 raw41843Labels permutation346 hz
    mixedMoment B raw41843step0 raw41843step0Labels = mixedMoment B raw41843step1 raw41843step1Labels := by
      have hz : ∀ j, raw41843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41843step1 = (fun i j => raw41843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41843step1 raw41843step0; decide +kernel
      have hl : raw41843step1Labels = raw41843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41843step0 raw41843step0Labels permutation56 hz
    mixedMoment B raw41843step1 raw41843step1Labels = mixedMoment B raw41843step2 raw41843step2Labels := by
      have ha : raw41843step2 = (fun i j => raw41843step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41843step2 raw41843step1; decide +kernel
      have hl : raw41843step2Labels = raw41843step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41843step1 raw41843step1Labels permutation31 permutation6
    _ = mixedMoment B node4162 node4162Labels := by rfl

theorem canonical41844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41844 raw41844Labels = mixedMoment B node1687 node1687Labels := by
  calc
    mixedMoment B raw41844 raw41844Labels = mixedMoment B raw41844step0 raw41844step0Labels := by
      have hz : ∀ j, raw41844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41844step0 = (fun i j => raw41844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41844step0 raw41844; decide +kernel
      have hl : raw41844step0Labels = raw41844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41844 raw41844Labels permutation346 hz
    mixedMoment B raw41844step0 raw41844step0Labels = mixedMoment B raw41844step1 raw41844step1Labels := by
      have hz : ∀ j, raw41844step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41844step1 = (fun i j => raw41844step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41844step1 raw41844step0; decide +kernel
      have hl : raw41844step1Labels = raw41844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41844step0 raw41844step0Labels permutation56 hz
    mixedMoment B raw41844step1 raw41844step1Labels = mixedMoment B raw41844step2 raw41844step2Labels := by
      have ha : raw41844step2 = (fun i j => raw41844step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41844step2 raw41844step1; decide +kernel
      have hl : raw41844step2Labels = raw41844step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41844step1 raw41844step1Labels permutation16 permutation4
    mixedMoment B raw41844step2 raw41844step2Labels = mixedMoment B raw41844step3 raw41844step3Labels := by
      have ha : raw41844step3 = -raw41844step2 := by apply Matrix.ext; change ∀ i j, raw41844step3 i j = -(raw41844step2 i j); unfold raw41844step3 raw41844step2; decide +kernel
      have hl : raw41844step3Labels = raw41844step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41844step3 raw41844step3Labels = mixedMoment B raw41844step4 raw41844step4Labels := by
      have ha : raw41844step4 = raw41844step3 := by apply Matrix.ext; unfold raw41844step4 raw41844step3; decide +kernel
      have hl : raw41844step3Labels = labelEmbedding1 ∘ raw41844step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41844step3 raw41844step3Labels raw41844step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1687 node1687Labels := by rfl

theorem canonical41845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41845 raw41845Labels = mixedMoment B node4362 node4362Labels := by
  calc
    mixedMoment B raw41845 raw41845Labels = mixedMoment B raw41845step0 raw41845step0Labels := by
      have hz : ∀ j, raw41845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41845step0 = (fun i j => raw41845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41845step0 raw41845; decide +kernel
      have hl : raw41845step0Labels = raw41845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41845 raw41845Labels permutation346 hz
    mixedMoment B raw41845step0 raw41845step0Labels = mixedMoment B raw41845step1 raw41845step1Labels := by
      have hz : ∀ j, raw41845step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41845step1 = (fun i j => raw41845step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41845step1 raw41845step0; decide +kernel
      have hl : raw41845step1Labels = raw41845step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41845step0 raw41845step0Labels permutation56 hz
    mixedMoment B raw41845step1 raw41845step1Labels = mixedMoment B raw41845step2 raw41845step2Labels := by
      have ha : raw41845step2 = (fun i j => raw41845step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41845step2 raw41845step1; decide +kernel
      have hl : raw41845step2Labels = raw41845step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41845step1 raw41845step1Labels permutation17 permutation6
    _ = mixedMoment B node4362 node4362Labels := by rfl

theorem canonical41846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41846 raw41846Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw41846 raw41846Labels = mixedMoment B raw41846step0 raw41846step0Labels := by
      have hz : ∀ j, raw41846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41846step0 = (fun i j => raw41846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41846step0 raw41846; decide +kernel
      have hl : raw41846step0Labels = raw41846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41846 raw41846Labels permutation346 hz
    mixedMoment B raw41846step0 raw41846step0Labels = mixedMoment B raw41846step1 raw41846step1Labels := by
      have hz : ∀ j, raw41846step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41846step1 = (fun i j => raw41846step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41846step1 raw41846step0; decide +kernel
      have hl : raw41846step1Labels = raw41846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41846step0 raw41846step0Labels permutation56 hz
    mixedMoment B raw41846step1 raw41846step1Labels = mixedMoment B raw41846step2 raw41846step2Labels := by
      have ha : raw41846step2 = (fun i j => raw41846step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41846step2 raw41846step1; decide +kernel
      have hl : raw41846step2Labels = raw41846step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41846step1 raw41846step1Labels permutation14 permutation4
    mixedMoment B raw41846step2 raw41846step2Labels = mixedMoment B raw41846step3 raw41846step3Labels := by
      have ha : raw41846step3 = -raw41846step2 := by apply Matrix.ext; change ∀ i j, raw41846step3 i j = -(raw41846step2 i j); unfold raw41846step3 raw41846step2; decide +kernel
      have hl : raw41846step3Labels = raw41846step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41846step3 raw41846step3Labels = mixedMoment B raw41846step4 raw41846step4Labels := by
      have ha : raw41846step4 = raw41846step3 := by apply Matrix.ext; unfold raw41846step4 raw41846step3; decide +kernel
      have hl : raw41846step3Labels = labelEmbedding1 ∘ raw41846step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41846step3 raw41846step3Labels raw41846step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1745 node1745Labels := by rfl

theorem canonical41847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41847 raw41847Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw41847 raw41847Labels = mixedMoment B raw41847step0 raw41847step0Labels := by
      have hz : ∀ j, raw41847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41847step0 = (fun i j => raw41847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41847step0 raw41847; decide +kernel
      have hl : raw41847step0Labels = raw41847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41847 raw41847Labels permutation346 hz
    mixedMoment B raw41847step0 raw41847step0Labels = mixedMoment B raw41847step1 raw41847step1Labels := by
      have hz : ∀ j, raw41847step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41847step1 = (fun i j => raw41847step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41847step1 raw41847step0; decide +kernel
      have hl : raw41847step1Labels = raw41847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41847step0 raw41847step0Labels permutation56 hz
    mixedMoment B raw41847step1 raw41847step1Labels = mixedMoment B raw41847step2 raw41847step2Labels := by
      have ha : raw41847step2 = (fun i j => raw41847step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41847step2 raw41847step1; decide +kernel
      have hl : raw41847step2Labels = raw41847step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41847step1 raw41847step1Labels permutation17 permutation6
    _ = mixedMoment B node4464 node4464Labels := by rfl

theorem canonical41848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41848 raw41848Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw41848 raw41848Labels = mixedMoment B raw41848step0 raw41848step0Labels := by
      have hz : ∀ j, raw41848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41848step0 = (fun i j => raw41848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41848step0 raw41848; decide +kernel
      have hl : raw41848step0Labels = raw41848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41848 raw41848Labels permutation346 hz
    mixedMoment B raw41848step0 raw41848step0Labels = mixedMoment B raw41848step1 raw41848step1Labels := by
      have hz : ∀ j, raw41848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41848step1 = (fun i j => raw41848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41848step1 raw41848step0; decide +kernel
      have hl : raw41848step1Labels = raw41848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41848step0 raw41848step0Labels permutation56 hz
    mixedMoment B raw41848step1 raw41848step1Labels = mixedMoment B raw41848step2 raw41848step2Labels := by
      have ha : raw41848step2 = (fun i j => raw41848step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41848step2 raw41848step1; decide +kernel
      have hl : raw41848step2Labels = raw41848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41848step1 raw41848step1Labels permutation13 permutation2
    mixedMoment B raw41848step2 raw41848step2Labels = mixedMoment B raw41848step3 raw41848step3Labels := by
      have ha : raw41848step3 = raw41848step2 := by apply Matrix.ext; unfold raw41848step3 raw41848step2; decide +kernel
      have hl : raw41848step2Labels = labelEmbedding1 ∘ raw41848step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41848step2 raw41848step2Labels raw41848step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

theorem canonical41849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41849 raw41849Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw41849 raw41849Labels = mixedMoment B raw41849step0 raw41849step0Labels := by
      have hz : ∀ j, raw41849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41849step0 = (fun i j => raw41849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41849step0 raw41849; decide +kernel
      have hl : raw41849step0Labels = raw41849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41849 raw41849Labels permutation346 hz
    mixedMoment B raw41849step0 raw41849step0Labels = mixedMoment B raw41849step1 raw41849step1Labels := by
      have hz : ∀ j, raw41849step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41849step1 = (fun i j => raw41849step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41849step1 raw41849step0; decide +kernel
      have hl : raw41849step1Labels = raw41849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41849step0 raw41849step0Labels permutation56 hz
    mixedMoment B raw41849step1 raw41849step1Labels = mixedMoment B raw41849step2 raw41849step2Labels := by
      have ha : raw41849step2 = (fun i j => raw41849step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41849step2 raw41849step1; decide +kernel
      have hl : raw41849step2Labels = raw41849step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41849step1 raw41849step1Labels permutation13 permutation7
    mixedMoment B raw41849step2 raw41849step2Labels = mixedMoment B raw41849step3 raw41849step3Labels := by
      have ha : raw41849step3 = -raw41849step2 := by apply Matrix.ext; change ∀ i j, raw41849step3 i j = -(raw41849step2 i j); unfold raw41849step3 raw41849step2; decide +kernel
      have hl : raw41849step3Labels = raw41849step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41849step3 raw41849step3Labels = mixedMoment B raw41849step4 raw41849step4Labels := by
      have ha : raw41849step4 = raw41849step3 := by apply Matrix.ext; unfold raw41849step4 raw41849step3; decide +kernel
      have hl : raw41849step3Labels = labelEmbedding6 ∘ raw41849step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41849step3 raw41849step3Labels raw41849step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4705 node4705Labels := by rfl

theorem canonical41850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41850 raw41850Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw41850 raw41850Labels = mixedMoment B raw41850step0 raw41850step0Labels := by
      have hz : ∀ j, raw41850 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41850step0 = (fun i j => raw41850 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41850step0 raw41850; decide +kernel
      have hl : raw41850step0Labels = raw41850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41850 raw41850Labels permutation265 hz
    mixedMoment B raw41850step0 raw41850step0Labels = mixedMoment B raw41850step1 raw41850step1Labels := by
      have ha : raw41850step1 = (fun i j => raw41850step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41850step1 raw41850step0; decide +kernel
      have hl : raw41850step1Labels = raw41850step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41850step0 raw41850step0Labels permutation132 permutation4
    mixedMoment B raw41850step1 raw41850step1Labels = mixedMoment B raw41850step2 raw41850step2Labels := by
      have ha : raw41850step2 = -raw41850step1 := by apply Matrix.ext; change ∀ i j, raw41850step2 i j = -(raw41850step1 i j); unfold raw41850step2 raw41850step1; decide +kernel
      have hl : raw41850step2Labels = raw41850step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41850step2 raw41850step2Labels = mixedMoment B raw41850step3 raw41850step3Labels := by
      have ha : raw41850step3 = raw41850step2 := by apply Matrix.ext; unfold raw41850step3 raw41850step2; decide +kernel
      have hl : raw41850step2Labels = labelEmbedding1 ∘ raw41850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41850step2 raw41850step2Labels raw41850step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

theorem canonical41851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41851 raw41851Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw41851 raw41851Labels = mixedMoment B raw41851step0 raw41851step0Labels := by
      have hz : ∀ j, raw41851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41851step0 = (fun i j => raw41851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41851step0 raw41851; decide +kernel
      have hl : raw41851step0Labels = raw41851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41851 raw41851Labels permutation265 hz
    mixedMoment B raw41851step0 raw41851step0Labels = mixedMoment B raw41851step1 raw41851step1Labels := by
      have ha : raw41851step1 = (fun i j => raw41851step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41851step1 raw41851step0; decide +kernel
      have hl : raw41851step1Labels = raw41851step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41851step0 raw41851step0Labels permutation149 permutation6
    _ = mixedMoment B node4157 node4157Labels := by rfl

theorem canonical41852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41852 raw41852Labels = mixedMoment B node1686 node1686Labels := by
  calc
    mixedMoment B raw41852 raw41852Labels = mixedMoment B raw41852step0 raw41852step0Labels := by
      have hz : ∀ j, raw41852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41852step0 = (fun i j => raw41852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41852step0 raw41852; decide +kernel
      have hl : raw41852step0Labels = raw41852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41852 raw41852Labels permutation265 hz
    mixedMoment B raw41852step0 raw41852step0Labels = mixedMoment B raw41852step1 raw41852step1Labels := by
      have ha : raw41852step1 = (fun i j => raw41852step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41852step1 raw41852step0; decide +kernel
      have hl : raw41852step1Labels = raw41852step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41852step0 raw41852step0Labels permutation92 permutation4
    mixedMoment B raw41852step1 raw41852step1Labels = mixedMoment B raw41852step2 raw41852step2Labels := by
      have ha : raw41852step2 = -raw41852step1 := by apply Matrix.ext; change ∀ i j, raw41852step2 i j = -(raw41852step1 i j); unfold raw41852step2 raw41852step1; decide +kernel
      have hl : raw41852step2Labels = raw41852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41852step2 raw41852step2Labels = mixedMoment B raw41852step3 raw41852step3Labels := by
      have ha : raw41852step3 = raw41852step2 := by apply Matrix.ext; unfold raw41852step3 raw41852step2; decide +kernel
      have hl : raw41852step2Labels = labelEmbedding1 ∘ raw41852step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41852step2 raw41852step2Labels raw41852step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1686 node1686Labels := by rfl

theorem canonical41853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41853 raw41853Labels = mixedMoment B node4353 node4353Labels := by
  calc
    mixedMoment B raw41853 raw41853Labels = mixedMoment B raw41853step0 raw41853step0Labels := by
      have hz : ∀ j, raw41853 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41853step0 = (fun i j => raw41853 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41853step0 raw41853; decide +kernel
      have hl : raw41853step0Labels = raw41853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41853 raw41853Labels permutation265 hz
    mixedMoment B raw41853step0 raw41853step0Labels = mixedMoment B raw41853step1 raw41853step1Labels := by
      have ha : raw41853step1 = (fun i j => raw41853step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41853step1 raw41853step0; decide +kernel
      have hl : raw41853step1Labels = raw41853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41853step0 raw41853step0Labels permutation95 permutation6
    _ = mixedMoment B node4353 node4353Labels := by rfl

theorem canonical41854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41854 raw41854Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw41854 raw41854Labels = mixedMoment B raw41854step0 raw41854step0Labels := by
      have hz : ∀ j, raw41854 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41854step0 = (fun i j => raw41854 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41854step0 raw41854; decide +kernel
      have hl : raw41854step0Labels = raw41854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41854 raw41854Labels permutation265 hz
    mixedMoment B raw41854step0 raw41854step0Labels = mixedMoment B raw41854step1 raw41854step1Labels := by
      have ha : raw41854step1 = (fun i j => raw41854step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41854step1 raw41854step0; decide +kernel
      have hl : raw41854step1Labels = raw41854step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41854step0 raw41854step0Labels permutation83 permutation4
    mixedMoment B raw41854step1 raw41854step1Labels = mixedMoment B raw41854step2 raw41854step2Labels := by
      have ha : raw41854step2 = -raw41854step1 := by apply Matrix.ext; change ∀ i j, raw41854step2 i j = -(raw41854step1 i j); unfold raw41854step2 raw41854step1; decide +kernel
      have hl : raw41854step2Labels = raw41854step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41854step2 raw41854step2Labels = mixedMoment B raw41854step3 raw41854step3Labels := by
      have ha : raw41854step3 = raw41854step2 := by apply Matrix.ext; unfold raw41854step3 raw41854step2; decide +kernel
      have hl : raw41854step2Labels = labelEmbedding1 ∘ raw41854step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41854step2 raw41854step2Labels raw41854step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

theorem canonical41855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41855 raw41855Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw41855 raw41855Labels = mixedMoment B raw41855step0 raw41855step0Labels := by
      have hz : ∀ j, raw41855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41855step0 = (fun i j => raw41855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41855step0 raw41855; decide +kernel
      have hl : raw41855step0Labels = raw41855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41855 raw41855Labels permutation265 hz
    mixedMoment B raw41855step0 raw41855step0Labels = mixedMoment B raw41855step1 raw41855step1Labels := by
      have ha : raw41855step1 = (fun i j => raw41855step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41855step1 raw41855step0; decide +kernel
      have hl : raw41855step1Labels = raw41855step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41855step0 raw41855step0Labels permutation97 permutation6
    _ = mixedMoment B node4442 node4442Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeySound70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem keyMoment2240 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2240) =
      Integer.Sparse.eval keyMomentRow2240 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2246) := by
    have ha : gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge = raw41792 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41792Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41792 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4879) := by
    have ha : gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge = raw41793 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41793Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41793 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2240).leftCharge (GramAssembly.key 2240).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2240, Integer.Sparse.eval]
  ring

theorem keyMoment2241 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2241) =
      Integer.Sparse.eval keyMomentRow2241 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2239) := by
    have ha : gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge = raw41794 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41794Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41794 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4697) := by
    have ha : gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge = raw41795 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41795Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41795 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2241).leftCharge (GramAssembly.key 2241).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2241, Integer.Sparse.eval]
  ring

theorem keyMoment2242 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2242) =
      Integer.Sparse.eval keyMomentRow2242 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2192) := by
    have ha : gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge = raw41796 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41796Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41796 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4815) := by
    have ha : gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge = raw41797 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41797Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41797 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2242).leftCharge (GramAssembly.key 2242).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2242, Integer.Sparse.eval]
  ring

theorem keyMoment2243 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2243) =
      Integer.Sparse.eval keyMomentRow2243 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2189) := by
    have ha : gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge = raw41798 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41798Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41798 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4771) := by
    have ha : gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge = raw41799 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41799Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41799 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2243).leftCharge (GramAssembly.key 2243).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2243, Integer.Sparse.eval]
  ring

theorem keyMoment2244 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2244) =
      Integer.Sparse.eval keyMomentRow2244 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2140) := by
    have ha : gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge = raw41800 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41800Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41800 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4663) := by
    have ha : gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge = raw41801 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41801Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41801 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2244).leftCharge (GramAssembly.key 2244).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2244, Integer.Sparse.eval]
  ring

theorem keyMoment2245 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2245) =
      Integer.Sparse.eval keyMomentRow2245 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2238) := by
    have ha : gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge = raw41802 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41802Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41802 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4696) := by
    have ha : gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge = raw41803 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41803Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41803 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2245).leftCharge (GramAssembly.key 2245).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2245, Integer.Sparse.eval]
  ring

theorem keyMoment2246 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2246) =
      Integer.Sparse.eval keyMomentRow2246 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2240) := by
    have ha : gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge = raw41804 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41804Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41804 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4851) := by
    have ha : gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge = raw41805 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41805Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41805 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2246).leftCharge (GramAssembly.key 2246).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2246, Integer.Sparse.eval]
  ring

theorem keyMoment2247 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2247) =
      Integer.Sparse.eval keyMomentRow2247 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2267) := by
    have ha : gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge = raw41806 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41806Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41806 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4881) := by
    have ha : gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge = raw41807 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41807Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41807 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2247).leftCharge (GramAssembly.key 2247).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2247, Integer.Sparse.eval]
  ring

theorem keyMoment2248 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2248) =
      Integer.Sparse.eval keyMomentRow2248 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2258) := by
    have ha : gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge = raw41808 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41808Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41808 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4560) := by
    have ha : gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge = raw41809 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41809Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41809 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2248).leftCharge (GramAssembly.key 2248).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2248, Integer.Sparse.eval]
  ring

theorem keyMoment2249 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2249) =
      Integer.Sparse.eval keyMomentRow2249 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2207) := by
    have ha : gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge = raw41810 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41810Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41810 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4817) := by
    have ha : gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge = raw41811 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41811Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41811 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2249).leftCharge (GramAssembly.key 2249).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2249, Integer.Sparse.eval]
  ring

theorem keyMoment2250 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2250) =
      Integer.Sparse.eval keyMomentRow2250 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2200) := by
    have ha : gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge = raw41812 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41812Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41812 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4552) := by
    have ha : gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge = raw41813 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41813Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41813 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2250).leftCharge (GramAssembly.key 2250).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2250, Integer.Sparse.eval]
  ring

theorem keyMoment2251 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2251) =
      Integer.Sparse.eval keyMomentRow2251 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2149) := by
    have ha : gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge = raw41814 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41814Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41814 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4536) := by
    have ha : gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge = raw41815 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41815Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41815 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2251).leftCharge (GramAssembly.key 2251).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2251, Integer.Sparse.eval]
  ring

theorem keyMoment2252 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2252) =
      Integer.Sparse.eval keyMomentRow2252 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2256) := by
    have ha : gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge = raw41816 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41816Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41816 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4699) := by
    have ha : gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge = raw41817 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41817Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41817 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2252).leftCharge (GramAssembly.key 2252).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2252, Integer.Sparse.eval]
  ring

theorem keyMoment2253 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2253) =
      Integer.Sparse.eval keyMomentRow2253 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2259) := by
    have ha : gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge = raw41818 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41818Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41818 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4853) := by
    have ha : gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge = raw41819 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41819Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41819 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2253).leftCharge (GramAssembly.key 2253).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2253, Integer.Sparse.eval]
  ring

theorem keyMoment2254 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2254) =
      Integer.Sparse.eval keyMomentRow2254 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2257) := by
    have ha : gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge = raw41820 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41820Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41820 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4701) := by
    have ha : gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge = raw41821 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41821Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41821 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2254).leftCharge (GramAssembly.key 2254).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2254, Integer.Sparse.eval]
  ring

theorem keyMoment2255 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2255) =
      Integer.Sparse.eval keyMomentRow2255 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2172) := by
    have ha : gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge = raw41822 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41822Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41822 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4532) := by
    have ha : gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge = raw41823 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41823Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41823 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2255).leftCharge (GramAssembly.key 2255).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2255, Integer.Sparse.eval]
  ring

theorem keyMoment2256 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2256) =
      Integer.Sparse.eval keyMomentRow2256 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2198) := by
    have ha : gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge = raw41824 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41824Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41824 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4772) := by
    have ha : gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge = raw41825 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41825Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41825 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2256).leftCharge (GramAssembly.key 2256).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2256, Integer.Sparse.eval]
  ring

theorem keyMoment2257 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2257) =
      Integer.Sparse.eval keyMomentRow2257 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2201) := by
    have ha : gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge = raw41826 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41826Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41826 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4792) := by
    have ha : gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge = raw41827 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41827Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41827 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2257).leftCharge (GramAssembly.key 2257).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2257, Integer.Sparse.eval]
  ring

theorem keyMoment2258 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2258) =
      Integer.Sparse.eval keyMomentRow2258 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2199) := by
    have ha : gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge = raw41828 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41828Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41828 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4774) := by
    have ha : gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge = raw41829 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41829Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41829 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2258).leftCharge (GramAssembly.key 2258).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2258, Integer.Sparse.eval]
  ring

theorem keyMoment2259 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2259) =
      Integer.Sparse.eval keyMomentRow2259 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2147) := by
    have ha : gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge = raw41830 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41830Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41830 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4664) := by
    have ha : gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge = raw41831 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41831Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41831 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2259).leftCharge (GramAssembly.key 2259).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2259, Integer.Sparse.eval]
  ring

theorem keyMoment2260 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2260) =
      Integer.Sparse.eval keyMomentRow2260 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2148) := by
    have ha : gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge = raw41832 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41832Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41832 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4666) := by
    have ha : gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge = raw41833 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41833Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41833 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2260).leftCharge (GramAssembly.key 2260).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2260, Integer.Sparse.eval]
  ring

theorem keyMoment2261 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2261) =
      Integer.Sparse.eval keyMomentRow2261 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1747) := by
    have ha : gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge = raw41834 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41834Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41834 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4508) := by
    have ha : gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge = raw41835 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41835Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41835 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2261).leftCharge (GramAssembly.key 2261).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2261, Integer.Sparse.eval]
  ring

theorem keyMoment2262 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2262) =
      Integer.Sparse.eval keyMomentRow2262 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1531) := by
    have ha : gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge = raw41836 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41836Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41836 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4193) := by
    have ha : gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge = raw41837 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41837Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41837 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2262).leftCharge (GramAssembly.key 2262).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2262, Integer.Sparse.eval]
  ring

theorem keyMoment2263 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2263) =
      Integer.Sparse.eval keyMomentRow2263 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1746) := by
    have ha : gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge = raw41838 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41838Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41838 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4478) := by
    have ha : gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge = raw41839 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41839Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41839 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2263).leftCharge (GramAssembly.key 2263).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2263, Integer.Sparse.eval]
  ring

theorem keyMoment2264 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2264) =
      Integer.Sparse.eval keyMomentRow2264 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1530) := by
    have ha : gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge = raw41840 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41840Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41840 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4184) := by
    have ha : gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge = raw41841 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41841Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41841 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2264).leftCharge (GramAssembly.key 2264).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2264, Integer.Sparse.eval]
  ring

theorem keyMoment2265 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2265) =
      Integer.Sparse.eval keyMomentRow2265 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1529) := by
    have ha : gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge = raw41842 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41842Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41842 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4162) := by
    have ha : gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge = raw41843 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41843Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41843 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2265).leftCharge (GramAssembly.key 2265).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2265, Integer.Sparse.eval]
  ring

theorem keyMoment2266 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2266) =
      Integer.Sparse.eval keyMomentRow2266 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1687) := by
    have ha : gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge = raw41844 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41844Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41844 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4362) := by
    have ha : gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge = raw41845 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41845Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41845 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2266).leftCharge (GramAssembly.key 2266).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2266, Integer.Sparse.eval]
  ring

theorem keyMoment2267 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2267) =
      Integer.Sparse.eval keyMomentRow2267 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1745) := by
    have ha : gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge = raw41846 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41846Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41846 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4464) := by
    have ha : gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge = raw41847 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41847Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41847 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2267).leftCharge (GramAssembly.key 2267).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2267, Integer.Sparse.eval]
  ring

theorem keyMoment2268 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2268) =
      Integer.Sparse.eval keyMomentRow2268 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 2286) := by
    have ha : gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge = raw41848 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41848Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41848 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4705) := by
    have ha : gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge = raw41849 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41849Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41849 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2268).leftCharge (GramAssembly.key 2268).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2268, Integer.Sparse.eval]
  ring

theorem keyMoment2269 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2269) =
      Integer.Sparse.eval keyMomentRow2269 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1528) := by
    have ha : gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge = raw41850 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41850Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41850 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4157) := by
    have ha : gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge = raw41851 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41851Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41851 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2269).leftCharge (GramAssembly.key 2269).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2269, Integer.Sparse.eval]
  ring

theorem keyMoment2270 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2270) =
      Integer.Sparse.eval keyMomentRow2270 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1686) := by
    have ha : gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge = raw41852 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41852Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41852 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4353) := by
    have ha : gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge = raw41853 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41853Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41853 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2270).leftCharge (GramAssembly.key 2270).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2270, Integer.Sparse.eval]
  ring

theorem keyMoment2271 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    5 * GramNormalization.eval B (GramAssembly.key 2271) =
      Integer.Sparse.eval keyMomentRow2271 (originalVector B) := by
  have hfirst : mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 1) =
      originalVector B (Sum.inl 1744) := by
    have ha : gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge = raw41854 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 1 = (Fin.castLEEmb (by decide : 2 ≤ 6)) ∘ raw41854Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41854 B hB).trans rfl
  have hsecond : mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 2) =
      originalVector B (Sum.inl 4442) := by
    have ha : gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge = raw41855 := by
      apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> decide +kernel
    have hl : gramLabels 1 2 = (Fin.castLEEmb (by decide : 3 ≤ 6)) ∘ raw41855Labels := by decide +kernel
    rw [ha, hl, mixedMoment_label_embedding (by decide)]
    exact (canonical41855 B hB).trans rfl
  change 5 * ((1/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 1) +
      (4/5 : ℝ) * mixedMoment B (gramCharges (GramAssembly.key 2271).leftCharge (GramAssembly.key 2271).rightCharge) (gramLabels 1 2)) = _
  rw [hfirst, hsecond]
  norm_num [keyMomentRow2271, Integer.Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_MixedTargets_KeyChunk70
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

theorem keyMomentRowsAt2240 : keyMomentRows (2240 : Fin 2886) =
    keyMomentRow2240 := by decide +kernel

theorem keyMomentRowsAt2241 : keyMomentRows (2241 : Fin 2886) =
    keyMomentRow2241 := by decide +kernel

theorem keyMomentRowsAt2242 : keyMomentRows (2242 : Fin 2886) =
    keyMomentRow2242 := by decide +kernel

theorem keyMomentRowsAt2243 : keyMomentRows (2243 : Fin 2886) =
    keyMomentRow2243 := by decide +kernel

theorem keyMomentRowsAt2244 : keyMomentRows (2244 : Fin 2886) =
    keyMomentRow2244 := by decide +kernel

theorem keyMomentRowsAt2245 : keyMomentRows (2245 : Fin 2886) =
    keyMomentRow2245 := by decide +kernel

theorem keyMomentRowsAt2246 : keyMomentRows (2246 : Fin 2886) =
    keyMomentRow2246 := by decide +kernel

theorem keyMomentRowsAt2247 : keyMomentRows (2247 : Fin 2886) =
    keyMomentRow2247 := by decide +kernel

theorem keyMomentRowsAt2248 : keyMomentRows (2248 : Fin 2886) =
    keyMomentRow2248 := by decide +kernel

theorem keyMomentRowsAt2249 : keyMomentRows (2249 : Fin 2886) =
    keyMomentRow2249 := by decide +kernel

theorem keyMomentRowsAt2250 : keyMomentRows (2250 : Fin 2886) =
    keyMomentRow2250 := by decide +kernel

theorem keyMomentRowsAt2251 : keyMomentRows (2251 : Fin 2886) =
    keyMomentRow2251 := by decide +kernel

theorem keyMomentRowsAt2252 : keyMomentRows (2252 : Fin 2886) =
    keyMomentRow2252 := by decide +kernel

theorem keyMomentRowsAt2253 : keyMomentRows (2253 : Fin 2886) =
    keyMomentRow2253 := by decide +kernel

theorem keyMomentRowsAt2254 : keyMomentRows (2254 : Fin 2886) =
    keyMomentRow2254 := by decide +kernel

theorem keyMomentRowsAt2255 : keyMomentRows (2255 : Fin 2886) =
    keyMomentRow2255 := by decide +kernel

theorem keyMomentRowsAt2256 : keyMomentRows (2256 : Fin 2886) =
    keyMomentRow2256 := by decide +kernel

theorem keyMomentRowsAt2257 : keyMomentRows (2257 : Fin 2886) =
    keyMomentRow2257 := by decide +kernel

theorem keyMomentRowsAt2258 : keyMomentRows (2258 : Fin 2886) =
    keyMomentRow2258 := by decide +kernel

theorem keyMomentRowsAt2259 : keyMomentRows (2259 : Fin 2886) =
    keyMomentRow2259 := by decide +kernel

theorem keyMomentRowsAt2260 : keyMomentRows (2260 : Fin 2886) =
    keyMomentRow2260 := by decide +kernel

theorem keyMomentRowsAt2261 : keyMomentRows (2261 : Fin 2886) =
    keyMomentRow2261 := by decide +kernel

theorem keyMomentRowsAt2262 : keyMomentRows (2262 : Fin 2886) =
    keyMomentRow2262 := by decide +kernel

theorem keyMomentRowsAt2263 : keyMomentRows (2263 : Fin 2886) =
    keyMomentRow2263 := by decide +kernel

theorem keyMomentRowsAt2264 : keyMomentRows (2264 : Fin 2886) =
    keyMomentRow2264 := by decide +kernel

theorem keyMomentRowsAt2265 : keyMomentRows (2265 : Fin 2886) =
    keyMomentRow2265 := by decide +kernel

theorem keyMomentRowsAt2266 : keyMomentRows (2266 : Fin 2886) =
    keyMomentRow2266 := by decide +kernel

theorem keyMomentRowsAt2267 : keyMomentRows (2267 : Fin 2886) =
    keyMomentRow2267 := by decide +kernel

theorem keyMomentRowsAt2268 : keyMomentRows (2268 : Fin 2886) =
    keyMomentRow2268 := by decide +kernel

theorem keyMomentRowsAt2269 : keyMomentRows (2269 : Fin 2886) =
    keyMomentRow2269 := by decide +kernel

theorem keyMomentRowsAt2270 : keyMomentRows (2270 : Fin 2886) =
    keyMomentRow2270 := by decide +kernel

theorem keyMomentRowsAt2271 : keyMomentRows (2271 : Fin 2886) =
    keyMomentRow2271 := by decide +kernel

theorem keyMomentChunkSound70_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (k : Fin 2886) (hk : k.val / 32 = 70) :
    5 * GramNormalization.eval B (GramAssembly.key k) =
      Integer.Sparse.eval (keyMomentRows k) (originalVector B) := by
  have heq : k.val = 2240 ∨ k.val = 2241 ∨ k.val = 2242 ∨ k.val = 2243 ∨ k.val = 2244 ∨ k.val = 2245 ∨ k.val = 2246 ∨ k.val = 2247 ∨ k.val = 2248 ∨ k.val = 2249 ∨ k.val = 2250 ∨ k.val = 2251 ∨ k.val = 2252 ∨ k.val = 2253 ∨ k.val = 2254 ∨ k.val = 2255 ∨ k.val = 2256 ∨ k.val = 2257 ∨ k.val = 2258 ∨ k.val = 2259 ∨ k.val = 2260 ∨ k.val = 2261 ∨ k.val = 2262 ∨ k.val = 2263 ∨ k.val = 2264 ∨ k.val = 2265 ∨ k.val = 2266 ∨ k.val = 2267 ∨ k.val = 2268 ∨ k.val = 2269 ∨ k.val = 2270 ∨ k.val = 2271 := by omega
  rcases heq with h2240 | h2241 | h2242 | h2243 | h2244 | h2245 | h2246 | h2247 | h2248 | h2249 | h2250 | h2251 | h2252 | h2253 | h2254 | h2255 | h2256 | h2257 | h2258 | h2259 | h2260 | h2261 | h2262 | h2263 | h2264 | h2265 | h2266 | h2267 | h2268 | h2269 | h2270 | h2271
  · have he : k = (2240 : Fin 2886) := Fin.ext h2240
    subst k
    rw [keyMomentRowsAt2240]
    exact keyMoment2240 B hB
  · have he : k = (2241 : Fin 2886) := Fin.ext h2241
    subst k
    rw [keyMomentRowsAt2241]
    exact keyMoment2241 B hB
  · have he : k = (2242 : Fin 2886) := Fin.ext h2242
    subst k
    rw [keyMomentRowsAt2242]
    exact keyMoment2242 B hB
  · have he : k = (2243 : Fin 2886) := Fin.ext h2243
    subst k
    rw [keyMomentRowsAt2243]
    exact keyMoment2243 B hB
  · have he : k = (2244 : Fin 2886) := Fin.ext h2244
    subst k
    rw [keyMomentRowsAt2244]
    exact keyMoment2244 B hB
  · have he : k = (2245 : Fin 2886) := Fin.ext h2245
    subst k
    rw [keyMomentRowsAt2245]
    exact keyMoment2245 B hB
  · have he : k = (2246 : Fin 2886) := Fin.ext h2246
    subst k
    rw [keyMomentRowsAt2246]
    exact keyMoment2246 B hB
  · have he : k = (2247 : Fin 2886) := Fin.ext h2247
    subst k
    rw [keyMomentRowsAt2247]
    exact keyMoment2247 B hB
  · have he : k = (2248 : Fin 2886) := Fin.ext h2248
    subst k
    rw [keyMomentRowsAt2248]
    exact keyMoment2248 B hB
  · have he : k = (2249 : Fin 2886) := Fin.ext h2249
    subst k
    rw [keyMomentRowsAt2249]
    exact keyMoment2249 B hB
  · have he : k = (2250 : Fin 2886) := Fin.ext h2250
    subst k
    rw [keyMomentRowsAt2250]
    exact keyMoment2250 B hB
  · have he : k = (2251 : Fin 2886) := Fin.ext h2251
    subst k
    rw [keyMomentRowsAt2251]
    exact keyMoment2251 B hB
  · have he : k = (2252 : Fin 2886) := Fin.ext h2252
    subst k
    rw [keyMomentRowsAt2252]
    exact keyMoment2252 B hB
  · have he : k = (2253 : Fin 2886) := Fin.ext h2253
    subst k
    rw [keyMomentRowsAt2253]
    exact keyMoment2253 B hB
  · have he : k = (2254 : Fin 2886) := Fin.ext h2254
    subst k
    rw [keyMomentRowsAt2254]
    exact keyMoment2254 B hB
  · have he : k = (2255 : Fin 2886) := Fin.ext h2255
    subst k
    rw [keyMomentRowsAt2255]
    exact keyMoment2255 B hB
  · have he : k = (2256 : Fin 2886) := Fin.ext h2256
    subst k
    rw [keyMomentRowsAt2256]
    exact keyMoment2256 B hB
  · have he : k = (2257 : Fin 2886) := Fin.ext h2257
    subst k
    rw [keyMomentRowsAt2257]
    exact keyMoment2257 B hB
  · have he : k = (2258 : Fin 2886) := Fin.ext h2258
    subst k
    rw [keyMomentRowsAt2258]
    exact keyMoment2258 B hB
  · have he : k = (2259 : Fin 2886) := Fin.ext h2259
    subst k
    rw [keyMomentRowsAt2259]
    exact keyMoment2259 B hB
  · have he : k = (2260 : Fin 2886) := Fin.ext h2260
    subst k
    rw [keyMomentRowsAt2260]
    exact keyMoment2260 B hB
  · have he : k = (2261 : Fin 2886) := Fin.ext h2261
    subst k
    rw [keyMomentRowsAt2261]
    exact keyMoment2261 B hB
  · have he : k = (2262 : Fin 2886) := Fin.ext h2262
    subst k
    rw [keyMomentRowsAt2262]
    exact keyMoment2262 B hB
  · have he : k = (2263 : Fin 2886) := Fin.ext h2263
    subst k
    rw [keyMomentRowsAt2263]
    exact keyMoment2263 B hB
  · have he : k = (2264 : Fin 2886) := Fin.ext h2264
    subst k
    rw [keyMomentRowsAt2264]
    exact keyMoment2264 B hB
  · have he : k = (2265 : Fin 2886) := Fin.ext h2265
    subst k
    rw [keyMomentRowsAt2265]
    exact keyMoment2265 B hB
  · have he : k = (2266 : Fin 2886) := Fin.ext h2266
    subst k
    rw [keyMomentRowsAt2266]
    exact keyMoment2266 B hB
  · have he : k = (2267 : Fin 2886) := Fin.ext h2267
    subst k
    rw [keyMomentRowsAt2267]
    exact keyMoment2267 B hB
  · have he : k = (2268 : Fin 2886) := Fin.ext h2268
    subst k
    rw [keyMomentRowsAt2268]
    exact keyMoment2268 B hB
  · have he : k = (2269 : Fin 2886) := Fin.ext h2269
    subst k
    rw [keyMomentRowsAt2269]
    exact keyMoment2269 B hB
  · have he : k = (2270 : Fin 2886) := Fin.ext h2270
    subst k
    rw [keyMomentRowsAt2270]
    exact keyMoment2270 B hB
  · have he : k = (2271 : Fin 2886) := Fin.ext h2271
    subst k
    rw [keyMomentRowsAt2271]
    exact keyMoment2271 B hB

end MUB6.Certificate.MixedTargetSemantics

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e_oai := @OAI.MUB6.Certificate.MixedTargetSemantics.keyMomentChunkSound70_e_oai
